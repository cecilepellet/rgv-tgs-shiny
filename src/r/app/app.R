# ------------------------------------------------------------------------
# Libraries, Tools and Data base Connection
# ------------------------------------------------------------------------
## Clear the workspace
# rm(list=ls())

#load required libraries
library(shiny)
library(DT)
library(caTools)
library(readr)
library(dplyr)
library(tidyr)
library(ggplot2)
library(lubridate)
library(grid)
library(gridExtra)
library(plotly)
library(bslib)
library(bsicons)
library(ggdendro)

options(shiny.sanitize.errors = FALSE)

# ------------------------------------------------------------------------
# Static functions
# ------------------------------------------------------------------------

# prepare data set
dup.rm <- function(df){
  # control if multiple measurement date within one year
  df$year = year(df$date)
  df$datehom = as.Date(paste0(df$year,'-09-01'))
  df <- df %>% group_by(point,year) %>% mutate(survey=n()) %>% ungroup()
  #remove second measurement if multiple
  if(length(which(df$survey>1))>0){
    df = df[-which(duplicated(df[c('point','year','datehom','survey')])),]
  }
  df <- df %>% select(-survey,-year)
  return(df)
}

#compute velocity
vel <- function(df){
  #compute velocity
  df <- df %>% group_by(point) %>% arrange(date) %>%  
    mutate(date1 = lag(date,1)
           ,date2 = date
           ,timediff = as.numeric(date2) - as.numeric(date1)
           ,ediff = round(e-lag(e,1),3)
           ,ndiff = round(n-lag(n,1),3)
           ,hdiff = round(h-lag(h,1),3)
           ,vel2d = ifelse(timediff>200&timediff<420,round(sqrt(ediff^2+ndiff^2)/as.numeric(timediff/365.25),3),NA)
           ,vel3d = ifelse(timediff>200&timediff<420,round(sqrt(ediff^2+ndiff^2+hdiff^2)/as.numeric(timediff/365.25),3),NA)) %>% 
    ungroup() %>% arrange(point,date) %>%
    return(df)
}

#compute direction
dir <- function(df){
  # compute direction
  df <- df %>% group_by(point) %>% arrange(date) %>% mutate(a = lag(lead(n,1)-n,1),
                                                            b = lag(lead(e,1)-e,1),
                                                            t = a/b)
  
  # measurement wise direction
  df$dir = ifelse(df$timediff>200&df$timediff<420,
                  ifelse(df$a>=0&df$b>=0,90-atan(abs(df$t))*180/pi,
                         ifelse(df$a>=0&df$b<0,270+atan(abs(df$t))*180/pi,
                                ifelse(df$a<0&df$b<0,270-atan(abs(df$t))*180/pi,
                                       ifelse(df$a<0&df$b>=0,90+atan(abs(df$t))*180/pi,NA)))),NA)
  
  df$dir = round(df$dir,2)
  
  # direction with 180° shift
  df$dirshift = ifelse(!is.na(df$dir),ifelse(df$dir<=180,df$dir,df$dir-360),NA)
  
  df <- df  %>% arrange(point,date) %>% select(-a,-b,-t)
  return(df)
}

# flag time series with data completeness lower than given threshold
f.comp <- function(df,dcomp){
  # removes all points with less than xx % of data
  df <- df %>% group_by(point) %>% mutate(y_count = n())
  df$p_filter = ifelse(df$y_count>max(df$y_count,na.rm=T)*dcomp/100,0,1)
  print(paste(" -- data completeness filter results:",length(which(df$p_filter==1)),sep=' '))
  p.list <- df[df$p_filter==1,] %>% select(date,point,p_filter)
  return(p.list)
}

# flag velocity larger than given threshold
f.vlim <- function(df,vlim){
  # detection limit filter 
  df$v_filter = ifelse(df$vel2d>vlim,0,1)
  print(paste(" -- velocity threshold filter results:",length(which(df$v_filter==1)),sep=' '))
  v.list <- df[df$v_filter==1,] %>% select(date,point,v_filter)
  return(v.list)
}

# flag direction changes in between two time steps larger than given threshold
f.dir <- function(df,dlim){
  #compute direction change
  df <- df %>% group_by(point) %>% arrange(date) %>% mutate(
    #forward direction change
    dfs = abs(dir-lead(dir)),
    dfss = abs(dirshift-lead(dirshift)),
    dfs = ifelse(dfs>=dfss,dfss,dfs),
    #backward direction change
    dbs = abs(dir-lag(dir)),
    dbss = abs(dirshift-lag(dirshift)),
    dbs = ifelse(dbs>=dbss,dbss,dbs),
    d_filter = ifelse(dbs>dlim&dfs>dlim,1,0)
  ) %>% select(-c(dfs,dfss,dbs,dbss))
  
  # assign d_filter = 1 for start and end of time series
  df$d_filter = ifelse(is.na(df$d_filter),1,df$d_filter)
  print(paste(" -- direction filter results:",length(which(df$d_filter==1)),sep=' '))
  d.list <- df[df$d_filter==1,] %>% select(date,point,d_filter)
  return(d.list)
}

# flag velocity outliers based on given standard deviation threshold
f.vout <- function(df,vdev){
  # compute relative velocity
  df <- df %>% group_by(point) %>% mutate(
    rel2d = vel2d/mean(vel2d,na.rm = T))
  
  df <- df %>% group_by(point) %>% mutate(
    m = mean(rel2d,na.rm=T),
    s = sd (rel2d,na.rm=T),
    vo_filter = ifelse(rel2d<m+vdev*s&rel2d>m-vdev*s,0,1)
  ) %>% select(-c(m,s))
  print(paste(" -- velocity outlier filter results:",length(which(df$vo_filter==1)),sep=' '))
  vo.list <- df[df$vo_filter==1,] %>% select(date,point,vo_filter)
  return(vo.list)
}

#flag velocity change outliers based on given standard deviation threshold
f.vch <- function(df,vcdev){
  #compute relative velocity changes between two measurement
  df <- df %>% group_by(point) %>% mutate(
    rel2d = vel2d/mean(vel2d,na.rm = T),
    d.fw = rel2d/lag(rel2d,1)*100,
    d.bw = rel2d/lead(rel2d,1)*100)
  
  #compute velocity change statistics for each mesurement date
  dfm <- df %>% group_by(datehom) %>% summarise(fw.m = mean(d.fw,na.rm=T),
                                                fw.se = sd(d.fw,na.rm=T),
                                                bw.m = mean(d.bw,na.rm=T),
                                                bw.se = sd(d.bw,na.rm=T))
  
  #combine data
  df = merge(df,dfm,by=c('datehom'),all=T)
  
  df = df %>%  mutate(
    vcfw_filter = ifelse(d.fw>fw.m-(fw.se*vcdev)&d.fw<fw.m+(fw.se*vcdev),0,1),
    vcfw_filter = ifelse(is.na(vcfw_filter),0,vcfw_filter),
    vcbw_filter = ifelse(d.bw>bw.m-(bw.se*vcdev)&d.bw<bw.m+(bw.se*vcdev),0,1),
    vcbw_filter = ifelse(is.na(vcbw_filter),0,vcbw_filter),
    vc_filter = ifelse(vcfw_filter ==1 & vcbw_filter ==1,1,0)
  ) %>% select(-vcfw_filter,-vcbw_filter)
  print(paste(" -- velocity change filter results:",length(which(df$vc_filter==1)),sep=' '))
  vc.list <- df[df$vc_filter==1,] %>% select(date,point,vc_filter)
  return(vc.list)
}

#plot filtered position
f_position_plot <- function(df,f=NA){
  
  #plot layout
  cols = c('completeness filter'='red','velocity threshold'='blue','direction change' = 'orange','velocity outlier'='green3',
           'velocity change'='purple','keep'='black')
  
  #make basic plot
  plot1 <- ggplot(NULL)+theme_tgs+
    xlab('easting (m)')+ylab('northing (m)')+scale_colour_manual(values=cols)+
    coord_equal()+theme(legend.title = element_blank())
  
  d = df
  
  if('p_filter' %in% f){
    plot1 <- plot1+geom_point(data=df[df$p_filter==1,],aes(e,n,col='completeness filter'),shape=16,size=2)
    d <- d %>% filter(p_filter==0)
  }
  if('v_filter' %in% f){
    plot1 <- plot1+geom_point(data=df[df$v_filter==1,],aes(e,n,col='velocity threshold'),shape=16,size=2)
    d <- d %>% filter(v_filter==0)
  }
  if('d_filter' %in% f){
    plot1 <- plot1+geom_point(data=df[df$d_filter==1,],aes(e,n,col='direction change'),shape=16,size=2)
    d <- d %>% filter(d_filter==0)
  }
  if('vo_filter' %in% f){
    plot1 <- plot1+geom_point(data=df[df$vo_filter==1,],aes(e,n,col='velocity outlier'),shape=16,size=2)
    d <- d %>% filter(vo_filter==0)
  }
  if('vc_filter' %in% f){
    plot1 <- plot1+geom_point(data=df[df$vc_filter==1,],aes(e,n,col='velocity change'),shape=16,size=2)
    d <- d %>% filter(vc_filter==0)
  }
  
  plot1 <- plot1+geom_point(data=d,aes(e,n,col='keep'),shape=1,size=2)
  return(plot1)
}

#plot filtered velocity
f_vel_plot <- function(df,f=NA,vlim=NA){
  
  #plot layout
  cols = c('completeness filter'='red','velocity threshold'='blue','direction change' = 'orange','velocity outlier'='limegreen',
           'velocity change'='purple','keep'='black','other filter'='grey')
  
  #make basic plot
  plot1 <- ggplot(NULL)+theme_tgs+
    xlab(NULL)+ylab('horizontal velocity (m/y)')+scale_colour_manual(values=cols)+
    theme(legend.title = element_blank())
  
  
  if('p_filter' %in% f){
    plot1 <- plot1+geom_point(data=df[df$p_filter==1,],aes(datehom,vel2d,col='completeness filter'),shape=16,size=3)
    do <- df[df$vel2d>100000,]
    d  <- df[df$p_filter==0,]
  }
  if('v_filter' %in% f){
    plot1 <- plot1+geom_point(data=df[df$v_filter==1,],aes(datehom,vel2d,col='velocity threshold'),shape=16,size=3)+
      geom_hline(yintercept = vlim,col='blue')
    do <- df[df$p_filter==1,]
    d  <- df[df$p_filter==0&df$v_filter==0,]
  }
  if('d_filter' %in% f){
    plot1 <- plot1+geom_point(data=df[df$d_filter==1,],aes(datehom,vel2d,col='direction change'),shape=16,size=3)
    do <- df[df$p_filter==1|df$v_filter==1,]
    d  <- df[df$p_filter==0&df$v_filter==0&df$d_filter==0,]
  }
  if('vo_filter' %in% f){
    plot1 <- plot1+geom_point(data=df[df$vo_filter==1,],aes(datehom,vel2d,col='velocity outlier'),shape=16,size=3)
    do <- df[df$p_filter==1|df$v_filter==1|df$d_filter==1,]
    d  <- df[df$p_filter==0&df$v_filter==0&df$d_filter==0&df$vo_filter==0,]
  }
  if('vc_filter' %in% f){
    plot1 <- plot1+geom_point(data=df[df$vc_filter==1,],aes(datehom,vel2d,col='velocity change'),shape=16,size=3)
    do <- df[df$p_filter==1|df$v_filter==1|df$d_filter==1|df$vo_filter==1,]
    d  <- df[df$p_filter==0&df$v_filter==0&df$d_filter==0&df$vo_filter==0&df$vc_filter==0,]
  }
  
  plot1 <- plot1+
    geom_point(data=d,aes(datehom,vel2d,col='keep'),shape=1,size=2)+
    geom_point(data=do,aes(datehom,vel2d,col='other filter'),shape=1,size=2)
  
  return(plot1)
}

#gap fill the data
fill.gap <- function(dat,clim){
  dat = dat[-which(!is.na(dat$date2)&is.na(dat$vel2d)),]
  df <- dat[!is.na(dat$vel2d),]
  
  #create complete time series
  dates <- df %>% select(date,datehom)
  dates <- dates[-which(duplicated(dates)),] %>% arrange(date)
  df <- df %>% select(point,datehom,vel2d)
  
  pt  = unique(df$point)
  d   = unique(df$datehom)
  dfc = expand.grid(pt,d)
  colnames(dfc) = c('point','datehom')
  df = merge(dfc,df,by=c('point','datehom'),all=T) %>% arrange(point,datehom) 
  
  #find all the gaps
  gap = df[is.na(df$vel2d),]
  
  #compute correlation matrix
  mat = spread(df,datehom,vel2d)
  row.names(mat) = mat$point
  mat = mat[,2:ncol(mat)]
  cm  = cor(t(mat),use='pairwise.complete.obs')
  
  #select best correlator
  for(i in 1:nrow(gap)){
    g = gap[i,]
    
    cv = cm[rownames(cm)==g$point,]
    cv = cv[cv<1]
    for(j in 1:length(cv)){
      d  = g$datehom
      id = names(cv[which(rank(-abs(cv))==j)])
      v  = df$vel2d[df$point==id&df$datehom==d]
      if(!is.na(v)){
        rank = j
        reg  = id
        cor  = cv[which(rank(-abs(cv))==j)]
        g = g %>% mutate(
          reg = reg,
          cor = cor,
          rank = rank)
        break
      }
    }
    if(exists('b')){
      b <- rbind(b,g)
    }else{
      b <- g
    }
  }
  gap = b
  rm(b,i,g,cv,reg,cor)
  
  #apply correlation threshold
  gap = gap[gap$cor>=clim,]
  
  #fill the gap using linear model
  for(i in 1:nrow(gap)){
    g = gap[i,]
    l = lm(df$vel2d[df$point==g$point]~df$vel2d[df$point==g$reg])
    d = df$vel2d[df$point==g$reg&df$date==g$date]
    
    gap$a[i]=l$coefficients[2]
    gap$b[i]=l$coefficients[1]
    gap$vel2d_fill[i] = round(gap$a[i]*d+gap$b[i],3)
    gap$fill_se[i] = round(summary(l)$sigma,3)
  }
  
  fill = gap %>% select(point,datehom,vel2d_fill,reg,fill_se)
  fill = merge(dates,fill,by=c('datehom'),all=T)
  fill = na.omit(fill)
  if (length(which(duplicated(fill[,c(1,3)])))>0){
    fill = fill[-which(duplicated(fill[,c(1,3)])),]
  }
  
  df = merge(dat,fill,by=c('date','point','datehom'),all=T) %>% arrange(point,date)
  df$vel2d_fill = ifelse(is.na(df$vel2d_fill),df$vel2d,df$vel2d_fill)
  return(df)
}

#compute cluster analysis
cluster <- function(df){
  #compute relative velocity
  d <- df %>% group_by(point) %>% mutate(
    rel2d = vel2d_fill/mean(vel2d_fill,na.rm = T),
    year  = year(datehom)) %>% ungroup() %>% select(year,point,rel2d)
  
  #arrange data 
  d <- spread(d,year,value=rel2d)
  d <- as.data.frame(d)
  rownames(d) = d$point
  d <- d %>% select(-point)
  
  #compute distance matrix
  dm <- dist(d)
  
  #perform clustering
  hc <- hclust(dm,method = 'ward.D2')
  return(hc)
}

#define plot theme
theme_tgs <- theme_bw(base_size=14,base_family='')+
  theme(legend.position='right',plot.title = element_text(size=14,face='bold'),panel.grid.minor = element_blank(),
        panel.border = element_rect(colour = "black"),axis.text = element_text(size = 13))

# ------------------------------------------------------------------------
# User interface
# ------------------------------------------------------------------------
ui <- page_navbar(
  title='TGS data processing tool'
  ,id='nav'
  # ,theme = bs_theme_update(theme, preset = "flatly")
  ,theme = bs_theme(bootswatch = 'flatly')
  ,sidebar = sidebar(
    width = 300
    ,open = 'open'
    ,conditionalPanel(
      "input.nav === '1. Data overview'"
      ,h5("Select TGS data to analyse (required)")
      ,p("The input file must contain only the following column in that order:")
      ,p("1.Date of the survey")
      ,p("2.Point name")
      ,p("3.East coordinate")
      ,p("4.North coordinate")
      ,p("5.Elevation")
      ,fileInput('file1', 'Choose file to upload'
                 ,accept = c('text/csv'
                             ,'text/comma-separated-values'
                             ,'text/tab-separated-values'
                             ,'text/plain'
                             ,'.csv'
                             ,'.tsv')
      )
      ,radioButtons('sep', 'Separator',c(Comma=',',Semicolon=';',Tab='\t'),'\t')
      ,radioButtons('quote', 'Quote',c(None='','Double Quote'='"','Single Quote'="'"),'')
      ,radioButtons('datef', 'Date format',c('yyyy-mm-dd'='%Y-%m-%d','dd.mm.yyyy'='%d.%m.%Y','dd/mm/yyyy'="%d/%m/%Y"),'%d.%m.%Y')
      ,checkboxInput('header', 'Header', TRUE)
      ,hr()
    )
    ,conditionalPanel(
      "input.nav === '2. Trajectory overview'||input.nav === '3. Velocity overview'"
      ,"Select TGS point to analyse trajectories:"
      ,uiOutput("tgs_point")
      ,hr()
    )
    ,conditionalPanel(
      "input.nav === '4. Data selection'"
      ,h5("Select thresholds for data selection and filtering")
      ,p('1. Data completeness threshold (%)')
      ,numericInput("dcomp","(0 = no effect)",value=70,min=50,max=100,step=1)
      ,p('2. Velocity limit (m/yr)')
      ,numericInput("vlim","(0 = no effect)",value=0.1,min = 0.01,max=0.75,step=0.01)
      ,p('3. Direction change threshold (°)')
      ,numericInput("dlim","(360 = no effect)",value=20,min=0,max=360,step=1)
      ,p('4. Velocity variability limit (x * standard deviation)')
      ,numericInput("vdev","(high = no effect)",value = 3,min = 0,max=10,step=0.1)
      ,p('5. Velocity change limit (x * standard deviation)')
      ,numericInput("vcdev","(high = no effect)",value = 3,min = 0,max=10,step=0.1)
      ,hr()
      ,actionButton("setth","Set thresholds")
      ,hr()
    )
    ,conditionalPanel(
      "input.nav ==='5. Data selection overview'"
      ,h5('Save selected data')
      ,downloadButton("wdata","Download selected data")
      ,hr()
      ,h5('Save defined threshold')
      ,downloadButton("wth","Download thresholds")
      ,hr()
    )
    ,conditionalPanel(
      "input.nav === '6. Gap filling'"
      ,h5('Explore gaps')
      ,uiOutput("tgs_gap")
      ,numericInput("clim","Correlation threshold for gap filling",value=0.7,min=0,max=1,step=0.01)
      ,hr()
      ,h5('Save gap filled data')
      ,downloadButton("wgap","Download gap filled data")
      ,hr()
    )
    ,conditionalPanel(
      "input.nav === '7. Clustering'"
      ,h5('Define clustering settings')
      ,numericInput('clustlim',"Number of clusters",value = 2,min=1,max=20,step=1)
      ,hr()
      ,h5('Manual cluster adjustment')
      ,uiOutput('clusterpoint')
      ,hr()
      ,h5('Save clustered data')
      ,downloadButton("wclust","Download clustered data")
      ,hr()
    )
    ,conditionalPanel(
      "input.nav === '8. RGV'"
      ,h5('Save RGV data')
      ,downloadButton("wrgv","Download RGV data")
      ,hr()
    )
  )
  ,nav_panel('1. Data overview'
             ,card(
               max_height = 900
               ,full_screen = T
               ,h5("Data overview")
               ,dataTableOutput('tab_vel'))
  )
  
  ,nav_panel('2. Trajectory overview'
             ,card(
               max_height = 500
               ,full_screen = T
               ,fluidRow(
                 splitLayout(
                   cellWidths=c("50%","50%") 
                   ,cellArgs=list(style="padding: 1px")
                   ,h5("Horizontal displacement:")
                   ,h5("Elevation change:")
                 )
               )
               ,fluidRow(
                 splitLayout(
                   cellWidths=c("50%","50%") 
                   ,cellArgs=list(style="padding: 2px")
                   ,plotlyOutput("TGS_hor_displ_point",height = 400,width=500)
                   ,plotlyOutput("TGS_ver_displ_point",height = 400,width=500)
                 )
               )
             )
             ,card(
               max_height = 500
               ,full_screen = T
               ,h5("Point location:")
               ,plotlyOutput("TGS_point_coord",height = 400,width=500))
  )
  ,nav_panel('3. Velocity overview'
             ,card(
               max_height = 700
               ,full_screen = T
               ,h5("Horizontal velocities")
               ,plotOutput("TGS_hor_vel_pt",height=200,width=900)
               ,plotOutput("TGS_hor_vel_all",height=200,width=900))
  )
  ,nav_panel('4. Data selection'
             ,accordion(
               open = c('1. Data completeness threshold')
               ,accordion_panel('1. Data completeness threshold'
                                ,fluidRow(
                                  splitLayout(
                                    cellWidths=c("60%","40%") 
                                    ,cellArgs=list(style="padding: 1px")
                                    ,plotOutput("v_comp_plot")
                                    ,plotOutput("p_comp_plot")
                                  ))
                                ,hr()
                                ,fluidRow(
                                  splitLayout(
                                    cellWidths=c("30%","30%")
                                    ,cellArgs=list(style="padding: 1px")
                                    ,value_box(title='Remove'
                                               ,value=textOutput('f_comp_out')
                                               ,showcase = bs_icon('square')
                                               ,theme = 'bg-red')                                   
                                    ,value_box(title='Keep'
                                               ,value=textOutput('f_comp_in')
                                               ,showcase = bs_icon('check2-square'))
                                  )))
               ,accordion_panel('2. Velocity threshold'
                                ,fluidRow(
                                  splitLayout(
                                    cellWidths=c("60%","40%") 
                                    ,cellArgs=list(style="padding: 1px")
                                    ,plotOutput("v_vel_plot")
                                    ,plotOutput("p_vel_plot")
                                  ))
                                ,hr()
                                ,fluidRow(
                                  splitLayout(
                                    cellWidths=c("30%","30%")
                                    ,cellArgs=list(style="padding: 1px")
                                    ,value_box(title='Remove'
                                               ,value=textOutput('f_vel_out')
                                               ,showcase = bs_icon('square')
                                               ,theme = 'bg-blue')                                   
                                    ,value_box(title='Keep'
                                               ,value=textOutput('f_vel_in')
                                               ,showcase = bs_icon('check2-square'))
                                  )))
               ,accordion_panel('3. Direction change threshold'
                                ,fluidRow(
                                  splitLayout(
                                    cellWidths=c("60%","40%") 
                                    ,cellArgs=list(style="padding: 1px")
                                    ,plotOutput("f_dir_plot")
                                    ,plotOutput("p_dir_plot")
                                  ))
                                ,hr()
                                ,fluidRow(
                                  splitLayout(
                                    cellWidths=c("30%","30%")
                                    ,cellArgs=list(style="padding: 1px")
                                    ,value_box(title='Remove'
                                               ,value=textOutput('f_dir_out')
                                               ,showcase = bs_icon('square')
                                               ,theme = 'bg-orange')                                   
                                    ,value_box(title='Keep'
                                               ,value=textOutput('f_dir_in')
                                               ,showcase = bs_icon('check2-square'))
                                  )))
               ,accordion_panel('4. Velocity variability threshold'
                                ,fluidRow(
                                  splitLayout(
                                    cellWidths=c("60%","40%") 
                                    ,cellArgs=list(style="padding: 1px")
                                    ,plotOutput("v_vo_plot")
                                    ,plotOutput("p_vo_plot")
                                  ))
                                ,hr()
                                ,fluidRow(
                                  splitLayout(
                                    cellWidths=c("30%","30%")
                                    ,cellArgs=list(style="padding: 1px")
                                    ,value_box(title='Remove'
                                               ,value=textOutput('f_vo_out')
                                               ,showcase = bs_icon('square')
                                               ,theme = 'bg-green')                                   
                                    ,value_box(title='Keep'
                                               ,value=textOutput('f_vo_in')
                                               ,showcase = bs_icon('check2-square'))
                                  )))
               ,accordion_panel('5. Velocity change threshold'
                                ,fluidRow(
                                  splitLayout(
                                    cellWidths=c("60%","40%") 
                                    ,cellArgs=list(style="padding: 1px")
                                    ,plotOutput("v_vc_plot")
                                    ,plotOutput("p_vc_plot")
                                  ))
                                ,hr()
                                ,fluidRow(
                                  splitLayout(
                                    cellWidths=c("30%","30%")
                                    ,cellArgs=list(style="padding: 1px")
                                    ,value_box(title='Remove'
                                               ,value=textOutput('f_vc_out')
                                               ,showcase = bs_icon('square')
                                               ,theme ='bg-purple')                                   
                                    ,value_box(title='Keep'
                                               ,value=textOutput('f_vc_in')
                                               ,showcase = bs_icon('check2-square'))
                                  )))
             ))
  ,nav_panel('5. Data selection overview'
             ,card(
               max_height = 500
               ,full_screen = T
               ,h5("Velocity overview")
               ,plotOutput('filtered_vel_plot')
             )
             ,card(
               max_height = 500
               ,full_screen = T
               ,h5("Point overview")
               ,plotlyOutput('filtered_point_plot')
             ))
  ,nav_panel('6. Gap filling'
             ,card(
               max_height = 500
               ,full_screen = T
               ,h5('filled velocity')
               ,plotOutput('gap_fill_plot')
             )
             ,card(
               max_height = 500
               ,full_screen = T
               ,h5('filled data table')
               ,dataTableOutput('tab_gap')
             ))
  ,nav_panel('7. Clustering'
             ,card(
               max_height = 500
               ,full_screen = T
               ,fluidRow(
                 splitLayout(
                   cellWidths=c("60%","40%") 
                   ,cellArgs=list(style="padding: 1px")
                   ,plotOutput("v_clust_plot")
                   ,plotlyOutput("p_clust_plot")
                 ))
             )
             ,card(
               max_height = 500
               ,full_screen = T
               ,plotOutput('dendro_plot')
             ))
  ,nav_panel('8. RGV'
             ,card(
               max_height = 500
               ,full_screen = T
               ,plotOutput('rgv_plot')
             )
             ,card(
               max_height = 500
               ,full_screen = T
               ,dataTableOutput('tab_clust_stat')
             ))
)


# ------------------------------------------------------------------------
# Shiny server
# ------------------------------------------------------------------------

server <- function(input, output) {
  # -------------------------------------------------
  # Reactive functions for Outputs
  # -------------------------------------------------
  data_all <- reactive({
    inFile <- input$file1
    if (is.null(inFile)) return(NULL)
    data <- read.csv(inFile$datapath, header=input$header, sep=input$sep, quote=input$quote)
    data <- data[,1:5]
    colnames(data) <- c("date","point","e","n","h")
    f  <- input$datef
    data$date <- as.Date(as.POSIXct(strptime(data$date,format=f)))
    data$point <- as.character(data$point)
    return(data)
  })
  
  site_name <- reactive({
    inFile <- input$file1
    if (is.null(inFile)) return(NULL)
    name <- inFile$name
    return(name)
  })
  
  output$tgs_point <- renderUI({
    dat <- data_all() %>% arrange(point,date)
    res <- unique(dat$point)
    selectInput(inputId = "tgs_point",label="TGS Point",choices = res,multiple=FALSE,selected=res[1],width='250px')
  })
  
  output$tgs_gap <- renderUI({
    dat <- set_filter()
    dat <- fill.gap(dat,clim=input$clim)
    dat <- dat[!is.na(dat$reg),]
    res <- unique(dat$point)
    selectInput(inputId = 'tgs_gap',label="TGS Point",choices = res,multiple = F,selected=res[1],width='250px')
  })
  
  output$clusterpoint <- renderUI({
    dat <- set_filter()
    dat <- fill.gap(dat,clim=input$clim)
    res <- unique(dat$point)
    selectInput(inputId = 'clusterpoint',label='Points to remove from clusters',choices = res, multiple = T, selected = NULL, width = '250px')
  })
  
  data_prep <- reactive({
    if(!is.null(data_all())) {
      dat <- data_all()
    }
    #remove duplicate measures within one year
    dat = dup.rm(dat)
    #compute velocity
    dat = vel(dat)
    #compute direction
    dat = dir(dat)
    
    return(dat)
  })
  
  data_filter <- reactive({
    req(input$file1) # Make sure requirements are met
    df  <- data_prep()
    d  <- df[!is.na(df$vel2d),]
    
    # get input filter threshold
    dcomp = input$dcomp
    vlim  = input$vlim
    dlim  = input$dlim
    vdev  = input$vdev
    vcdev = input$vcdev
    
    # apply filter
    p <- f.comp(d,dcomp)
    d <- merge(df,p,by=c('date','point'),all=T)
    d$p_filter = ifelse(is.na(d$p_filter),0,1)
    df = d[d$p_filter==0&!is.na(d$vel2d),]
    
    v  = f.vlim(df,vlim)  
    d  = merge(d,v,by=c('date','point'),all=T)
    d$v_filter = ifelse(is.na(d$v_filter),0,1)
    df = d[d$v_filter==0&d$p_filter==0&!is.na(d$vel2d),]
    
    di = f.dir(df,dlim)
    d  = merge(d,di,by=c('date','point'),all=T)
    d$d_filter = ifelse(is.na(d$d_filter),0,1)
    df = d[d$v_filter==0&d$p_filter==0&d$d_filter==0&!is.na(d$vel2d),]
    
    vo = f.vout(df,vdev)
    d  = merge(d,vo,by=c('date','point'),all=T)
    d$vo_filter = ifelse(is.na(d$vo_filter),0,1)
    df = d[d$v_filter==0&d$p_filter==0&d$d_filter==0&d$vo_filter==0&!is.na(d$vel2d),]
    
    vc = f.vch(df,vcdev)
    d  = merge(d,vc,by=c('date','point'),all=T)
    d$vc_filter = ifelse(is.na(d$vc_filter),0,1)
    df = d[d$v_filter==0&d$p_filter==0&d$d_filter==0&d$vo_filter==0&d$vc_filter==0,]
    
    p1  = f.comp(df,dcomp)
    p1$p1_filter = p1$p_filter
    p1 = p1 %>% select(-p_filter)
    d  = merge(d,p1,by=c('date','point'),all=T)
    d$p1_filter = ifelse(is.na(d$p1_filter),0,1)
    df = d[d$v_filter==0&d$p_filter==0&d$d_filter==0&d$vo_filter==0&d$vc_filter==0&d$p1_filter==0,]
    
    d = d %>% arrange(point,date)
    return(d)
  })
  
  stat_filter <- reactive({
    req(input$file1) # Make sure requirements are met
    df  <- data_prep()
    
    #remove first measurement (no velocity)
    df  <- df[!is.na(df$vel2d),]
    
    # get input filter threshold
    dcomp = input$dcomp
    vlim  = input$vlim
    dlim  = input$dlim
    vdev  = input$vdev
    vcdev = input$vcdev
    
    # apply filter
    p <- f.comp(df,dcomp)
    d <- merge(df,p,by=c('date','point'),all=T)
    d$p_filter = ifelse(is.na(d$p_filter),0,1)
    df = d[d$p_filter==0,]
    s.p = data.frame('filter'='p_filter','tot'=nrow(d),'out'=nrow(p),'in'=nrow(df))
    
    
    v  = f.vlim(df,vlim)  
    d  = merge(d,v,by=c('date','point'),all=T)
    d$v_filter = ifelse(is.na(d$v_filter),0,1)
    df = d[d$v_filter==0&d$p_filter==0,]
    s.v = data.frame('filter'='v_filter','tot'=nrow(d[d$p_filter==0,]),'out'=nrow(v),'in'=nrow(df))
    
    di = f.dir(df,dlim)
    d  = merge(d,di,by=c('date','point'),all=T)
    d$d_filter = ifelse(is.na(d$d_filter),0,1)
    df = d[d$v_filter==0&d$p_filter==0&d$d_filter==0,]
    s.d = data.frame('filter'='d_filter','tot'=nrow(d[d$p_filter==0&d$v_filter==0,]),'out'=nrow(di),'in'=nrow(df))
    
    vo = f.vout(df,vdev)
    d  = merge(d,vo,by=c('date','point'),all=T)
    d$vo_filter = ifelse(is.na(d$vo_filter),0,1)
    df = d[d$v_filter==0&d$p_filter==0&d$d_filter==0&d$vo_filter==0,]
    s.vo = data.frame('filter'='vo_filter','tot'=nrow(d[d$p_filter==0&d$v_filter==0&d$d_filter==0,]),'out'=nrow(vo),'in'=nrow(df))
    
    vc = f.vch(df,vcdev)
    d  = merge(d,vc,by=c('date','point'),all=T)
    d$vc_filter = ifelse(is.na(d$vc_filter),0,1)
    df = d[d$v_filter==0&d$p_filter==0&d$d_filter==0&d$vo_filter==0&d$vc_filter==0,]
    s.vc = data.frame('filter'='vc_filter','tot'=nrow(d[d$p_filter==0&d$v_filter==0&d$d_filter==0&d$vo_filter==0,]),'out'=nrow(vc),'in'=nrow(df))
    
    p1  = f.comp(df,dcomp)
    p1$p1_filter = p1$p_filter
    p1 = p1 %>% select(-p_filter)
    d  = merge(d,p1,by=c('date','point'),all=T)
    d$p1_filter = ifelse(is.na(d$p1_filter),0,1)
    df = d[d$v_filter==0&d$p_filter==0&d$d_filter==0&d$vo_filter==0&d$vc_filter==0&d$p1_filter==0,]
    s.p1 = data.frame('filter'='p1_filter','tot'=nrow(d[d$p_filter==0&d$v_filter==0&d$d_filter==0&d$vo_filter==0&d$vc_filter==0,]),'out'=nrow(p1),'in'=nrow(df))
    
    s = rbind(s.p,s.v,s.d,s.vo,s.vc,s.p1)
    return(s)
  })
  
  set_filter <- reactive({
    #apply filters
    df <- data_filter()
    
    #remove all flagged data
    df$filter = df$v_filter+df$p_filter+df$d_filter+df$vo_filter+df$vc_filter+df$p1_filter
    df <- df[df$filter==0,]
    
    return(df)
  })
  
  set_cluster <- reactive({
    #apply filter
    df  <- set_filter()
    
    #apply gap filling
    df <- fill.gap(df,clim = input$clim)
    
    #perform clustering
    cl <- cluster(df)
    
    #set cluster limit
    clim <- input$clustlim
    cl <- cutree(cl,k=clim)
    
    #assign clusters
    cl <- data.frame(point = names(cl),cluster=cl)
    df  <- merge(df,cl,by=c('point'),all = T)
    df$cluster = as.factor(df$cluster)
    
    #manually remove points from clusters 
    pt = input$clusterpoint
    if(length(pt)>0){
      df=df[!(df$point%in%pt),]
    }
    return(df)
  })
  
  stat_cluster <- reactive({
    #apply clustering
    df <- set_cluster()
    
    #compute cluster average
    dfm <- df %>% group_by(cluster,datehom) %>% summarise(
      vel2d = mean(vel2d,na.rm=T),
      point_number = n()) %>% ungroup()
    
    #compute linear regression and statistics
    lm <- dfm %>% arrange(cluster)%>% group_by(cluster) %>% summarise(
      slope = lm(vel2d~datehom)$coefficient[2],
      intercept = lm(vel2d~datehom)$coefficient[1],
      r_squared = round(summary(lm(vel2d~datehom))$r.squared,3),
      p_value = summary(lm(vel2d~datehom))$coefficient[2,4],
      point_number = max(point_number,na.rm=T))
    return(lm)
  })
  
  rgv <- reactive({
    df <- set_cluster()
    
    #compute cluster average and stat
    dfm <- df %>% group_by(cluster,datehom) %>% summarise(
      vel2d_avg = mean(vel2d,na.rm=T),
      vel2d_med = median(vel2d,na.rm=T),
      vel2d_sd = sd(vel3d,na.rm=T),
      vel3d_avg = mean(vel3d,na.rm=T),
      vel3d_med = median(vel3d,na.rm=T),
      vel3d_sd = sd(vel2d,na.rm=T),
      clust_points = n(),
    ) %>% ungroup()
    return(dfm)
  }) 
  
  # -------------------------------------------------
  # Reactive shiny elements
  # -------------------------------------------------
  observeEvent(input$setth,{
    updateTabsetPanel(session =  getDefaultReactiveDomain(),
                      inputId = 'nav',
                      selected = '5. Data selection overview')
  })
  
  # ------------------------------------------------
  # OUTPUT TAB 1 - Data tables 
  # ------------------------------------------------
  
  # table output with original data (no filtering, no gap-filling)
  output$tab_vel <- renderDataTable({
    req(input$file1) # Make sure requirements are met
    
    tab_vel <- data_prep() %>% select(date,point,e, n, h,date1,date2,timediff,ediff, ndiff, hdiff,dir, vel2d, vel3d)
    datatable(tab_vel,extensions = list("Scroller"=NULL,"FixedColumns"= list(leftColumns=1)),
              options=list(paging=F,fixedColumns=TRUE,scrollY=700,scrollX=T,searching=FALSE)
              ,rownames=FALSE,class="nowrap display cell-border stripe'")
  })
  
  # ------------------------------------------------
  # OUTPUT TAB 2 - Point trajectory
  # ------------------------------------------------
  
  # interactive plot trajectories
  output$TGS_hor_displ_point <- renderPlotly({
    req(input$file1) # Make sure requirements are met
    if(!is.null(data_all())) {
      df <- data_all() %>% filter(point==input$tgs_point)
      
      p1 <- ggplot(data=df)+theme_bw()+
        geom_point(aes(x=e, y=n, group=point, col=factor(date)),size=2)+
        theme(legend.title=element_blank()) +xlab('easting (m)')+ylab('northing (m)')+coord_equal()+
        ggtitle(input$tgs_point)
    }
    # transfrom the ggplot into ggplotly (interactive plot)
    p1 <- ggplotly(p1)
    return(p1)
  })
  
  # interactive plot height evolution
  output$TGS_ver_displ_point <- renderPlotly({
    req(input$file1) # Make sure requirements are met
    if(!is.null(data_all())) {
      df <- data_all() %>% filter(point==input$tgs_point) %>% arrange(date)
      
      df <- df %>% mutate(e_diff = e-e[1],
                          n_diff = n-n[1],
                          h_diff = h-h[1],
                          dist_h = sqrt(e_diff^2+n_diff^2))
      
      p2 <- ggplot(data=df)+theme_bw()+
        geom_point(aes(x=dist_h, y=h, group=point, col=factor(date)),size=2)+
        theme(legend.title=element_blank()) +xlab('horizontal displacement (m)')+ylab('elevation (m)')+coord_equal()+
        ggtitle(input$tgs_point)
    }
    # transfrom the ggplot into ggplotly (interactive plot)
    p2 <- ggplotly(p2)
    return(p2)
  })
  
  output$TGS_point_coord <- renderPlotly({
    req(input$file1)# Make sure requirements are met
    df <- data_all()
    
    pt <- input$tgs_point
    dp <- df %>% filter(point==pt)
    
    if(!is.null(data_all())) {
      p3 <- ggplot(df)+theme_bw()+
        geom_point(aes(e,n,group=point),size=1)+
        geom_point(data=dp,aes(e,n,group=point),size=2,col='red')+
        xlab('easting (m)')+ylab('northing (m)')+coord_equal()
    }
    # transfrom the ggplot into ggplotly (interactive plot)
    p3 <- ggplotly(p3)
    return(p3)
  })
  
  # ------------------------------------------------
  # OUTPUT TAB 3 - Point velocity
  # ------------------------------------------------
  
  output$TGS_hor_vel_pt <- renderPlot({
    req(input$file1) # Make sure requirements are met
    df  <- data_prep()%>% filter(point==input$tgs_point)
    
    dfp <- df %>% arrange(point,date) %>% group_by(point) %>% 
      slice(rep(1:n(),each=2)) %>% mutate(vel2d=lead(vel2d,1))
    
    y_max <- round(max(dfp$vel2d,na.rm=T)*1.10,digits = 3)
    y.axis <- scale_y_continuous(limits=c(0,y_max), expand=c(0,0))
    x.axis <- scale_x_date(date_breaks='1 year', date_labels="%Y",expand= c(0,0))
    
    theme_tgs <- theme_bw(base_size=14,base_family='')+
      theme(legend.position='right',plot.title = element_text(size=14,face='bold'),panel.grid.minor = element_blank(),
            panel.border = element_rect(colour = "black"),axis.text = element_text(size = 13))
    
    # setup the general plot
    plot1 <- ggplot(NULL)+theme_tgs+
      geom_line(data=dfp,aes(x=date,y=vel2d,colour=point),size=1)+
      xlab(NULL)+ylab('horizontal surface velocity (m/a)')+y.axis+x.axis
    return(plot1)
  })
  
  output$TGS_hor_vel_all <- renderPlot({
    req(input$file1) # Make sure requirements are met
    df  <- data_prep()
    df1  <- df %>% filter(point==input$tgs_point)
    
    dfp <- df %>% arrange(point,date) %>% group_by(point) %>% 
      slice(rep(1:n(),each=2)) %>% mutate(vel2d=lead(vel2d,1),group = point)
    df1p <- df1 %>% arrange(point,date) %>% group_by(point) %>% 
      slice(rep(1:n(),each=2)) %>% mutate(vel2d=lead(vel2d,1),group = point)
    
    y_max <- round(max(dfp$vel2d,na.rm=T)*1.10,digits = 3)
    y.axis <- scale_y_continuous(limits=c(0,y_max), expand=c(0,0))
    x.axis <- scale_x_date(date_breaks='1 year', date_labels="%Y",expand= c(0,0))
    
    theme_tgs <- theme_bw(base_size=14,base_family='')+
      theme(legend.position='right',plot.title = element_text(size=14,face='bold'),panel.grid.minor = element_blank(),
            panel.border = element_rect(colour = "black"),axis.text = element_text(size = 13))
    
    # setup the general plot
    plot1 <- ggplot(NULL)+theme_tgs+
      geom_line(data=dfp,aes(x=date,y=vel2d,group=point),colour='grey70',size=1)+
      geom_line(data=df1p,aes(x=date,y=vel2d,colour=point),size=1)+
      xlab(NULL)+ylab('horizontal surface velocity (m/a)')+y.axis+x.axis
    return(plot1)
  })
  
  # ------------------------------------------------
  # OUTPUT TAB 4 - Data filter / Selection
  # ------------------------------------------------
  
  # data completeness section
  output$p_comp_plot <- renderPlot({
    #apply filter
    df  <- data_filter()
    
    f = c('p_filter')
    p = f_position_plot(df,f)
    return(p)
  })
  output$v_comp_plot <- renderPlot({
    #apply filter
    df  <- data_filter()
    
    f = c('p_filter')
    p = f_vel_plot(df,f)
    return(p)
  })
  
  output$f_comp_in <- renderText({
    df = stat_filter()
    df = df[df$filter=='p_filter',]
    lab = paste0(df$in.,' / ',df$tot)
    return(lab)
  })
  output$f_comp_out <- renderText({
    df = stat_filter()
    df = df[df$filter=='p_filter',]
    lab = paste0(df$out,' / ',df$tot)
    return(lab)
  })
  
  # velocity threshold section
  output$p_vel_plot <- renderPlot({
    #apply filter
    df  <- data_filter()
    
    f = c('p_filter','v_filter')
    p = f_position_plot(df,f)
    return(p)
  })
  output$v_vel_plot <- renderPlot({
    #apply filter
    df  <- data_filter()
    vlim <- input$vlim
    f = c('v_filter')
    p = f_vel_plot(df,f,vlim)
    return(p)
  })
  
  output$f_vel_in <- renderText({
    df = stat_filter()
    df = df[df$filter=='v_filter',]
    lab = paste0(df$in.,' / ',df$tot)
    return(lab)
  })
  output$f_vel_out <- renderText({
    df = stat_filter()
    df = df[df$filter=='v_filter',]
    lab = paste0(df$out,' / ',df$tot)
    return(lab)
  })
  
  # direction change section
  output$p_dir_plot <- renderPlot({
    #apply filter
    df  <- data_filter()
    
    f = c('p_filter','v_filter','d_filter')
    p = f_position_plot(df,f)
    return(p)
  })
  output$f_dir_plot <- renderPlot({
    #apply filter
    df  <- data_filter()
    cols = c('direction change'='orange','keep'='black','other filter'='grey')
    
    if(mean(df$dir,na.rm=T)>90&mean(df$dir,na.rm=T)<180){
      plot1 <- ggplot(NULL)+theme_tgs+
        geom_point(data=df[df$d_filter==1,],aes(datehom,dir,group=point,col='direction change'),shape=16,size=3)+
        geom_point(data=df[df$p_filter==1|df$v_filter==1,],aes(datehom,dir,group=point,col='other filter'),shape=1,size=2)+
        geom_point(data=df[df$d_filter==0&df$p_filter==0&df$v_filter==0,],aes(datehom,dir,group=point,col='keep'),shape=1,size=2)+
        xlab(NULL)+ylab('direction (°)')+scale_colour_manual(values=cols)+
        theme(legend.title = element_blank())
      return(plot1)
    }else{
      plot1 <- ggplot(NULL)+theme_tgs+
        geom_point(data=df[df$d_filter==1,],aes(datehom,dirshift,group=point,col='direction change'),shape=16,size=3)+
        geom_point(data=df[df$p_filter==1|df$v_filter==1,],aes(datehom,dirshift,col='other filter'),shape=1,size=2)+
        geom_point(data=df[df$d_filter==0&df$p_filter==0&df$v_filter==0,],aes(datehom,dirshift,group=point,col='keep'),shape=1,size=2)+
        xlab(NULL)+ylab('direction (° with 180° shift)')+scale_colour_manual(values=cols)+
        theme(legend.title = element_blank())
      return(plot1)
    }
  })
  
  output$f_dir_in <- renderText({
    df = stat_filter()
    df = df[df$filter=='d_filter',]
    lab = paste0(df$in.,' / ',df$tot)
    return(lab)
  })
  output$f_dir_out <- renderText({
    df = stat_filter()
    df = df[df$filter=='d_filter',]
    lab = paste0(df$out,' / ',df$tot)
    return(lab)
  })
  
  # velocity outlier section
  output$p_vo_plot <- renderPlot({
    #apply filter
    df  <- data_filter()
    
    f = c('p_filter','v_filter','d_filter','vo_filter')
    p = f_position_plot(df,f)
    return(p)
  })
  output$v_vo_plot <- renderPlot({
    #apply filter
    df  <- data_filter()
    #compute relative velocity
    df <- df %>% group_by(point) %>% mutate(
      rel2d = vel2d/mean(vel2d,na.rm = T))
    
    #plot layout
    cols = c('velocity outlier'='limegreen','keep'='black','other filter'='grey')
    
    #make basic plot
    plot1 <- ggplot(NULL)+theme_tgs+
      geom_point(data = df[df$vo_filter==1,],aes(datehom,rel2d,col='velocity outlier'),size=3,shape=16)+
      geom_point(data = df[df$d_filter==1|df$v_filter==1|df$p_filter==1,],aes(datehom,rel2d,col='other filter'),size=2,shape=1)+
      geom_point(data = df[df$vo_filter==0&df$d_filter==0&df$v_filter==0&df$p_filter==0,],aes(datehom,rel2d,col='keep'),size=2,shape=1)+
      xlab(NULL)+ylab('relative horizontal velocity (m/y)')+scale_colour_manual(values=cols)+
      theme(legend.title = element_blank())
    
    return(plot1)
  })
  
  output$f_vo_in <- renderText({
    df = stat_filter()
    df = df[df$filter=='vo_filter',]
    lab = paste0(df$in.,' / ',df$tot)
    return(lab)
  })
  output$f_vo_out <- renderText({
    df = stat_filter()
    df = df[df$filter=='vo_filter',]
    lab = paste0(df$out,' / ',df$tot)
    return(lab)
  })
  
  # velocity change section
  output$p_vc_plot <- renderPlot({
    #apply filter
    df  <- data_filter()
    
    f = c('p_filter','v_filter','d_filter','vo_filter','vc_filter')
    p = f_position_plot(df,f)
    return(p)
  })
  output$v_vc_plot <- renderPlot({
    #apply filter
    df  <- data_filter()
    
    #compute relative velocity changes between two measurement
    df <- df %>% group_by(point) %>% mutate(
      rel2d = vel2d/mean(vel2d,na.rm = T),
      d.fw = rel2d/lag(rel2d,1)*100,
      d.bw = rel2d/lead(rel2d,1)*100)
    
    #plot layout
    cols = c('velocity change'='purple','keep'='black','other filter'='grey')
    
    #make basic plot
    plot1 <- ggplot(NULL)+theme_tgs+
      geom_point(data = df[df$vc_filter==1,],aes(datehom,d.fw,col='velocity change'),size=3,shape=16)+
      geom_point(data = df[df$d_filter==1|df$v_filter==1|df$p_filter==1|df$vo_filter==1,],aes(datehom,d.fw,col='other filter'),size=2,shape=1)+
      geom_point(data = df[df$vo_filter==0&df$d_filter==0&df$v_filter==0&df$p_filter==0&df$vc_filter==0,],aes(datehom,d.fw,col='keep'),size=2,shape=1)+
      xlab(NULL)+ylab('change of relative horizontal velocity (m/y)')+scale_colour_manual(values=cols)+
      theme(legend.title = element_blank())
    return(plot1)
    
  })
  
  output$f_vc_in <- renderText({
    df = stat_filter()
    df = df[df$filter=='vc_filter',]
    lab = paste0(df$in.,' / ',df$tot)
    return(lab)
  })
  output$f_vc_out <- renderText({
    df = stat_filter()
    df = df[df$filter=='vc_filter',]
    lab = paste0(df$out,' / ',df$tot)
    return(lab)
  })
  
  # ------------------------------------------------
  # OUTPUT TAB 5 - Filtered data overview
  # ------------------------------------------------
  output$filtered_vel_plot <- renderPlot({
    df = data_filter()
    df$filter = df$v_filter+df$p_filter+df$d_filter+df$vo_filter+df$vc_filter+df$p1_filter
    
    d.in = df[df$filter==0,]
    d.out = df[df$filter!=0,]
    
    #duplicate for step plot
    dip <- d.in %>% arrange(point,datehom) %>% group_by(point) %>% 
      slice(rep(1:n(),each=2)) %>% mutate(vel2d=lead(vel2d,1),group = point)
    dop <- d.out %>% arrange(point,datehom) %>% group_by(point) %>% 
      slice(rep(1:n(),each=2)) %>% mutate(vel2d=lead(vel2d,1),group = point)
    
    y_max <- round(max(df$vel2d,na.rm=T)*1.10,digits = 3)
    y.axis <- scale_y_continuous(limits=c(0,y_max), expand=c(0,0))
    x.axis <- scale_x_date(date_breaks='2 year', date_labels="%Y",limits = c(min(dip$datehom,na.rm=T),max(dip$datehom,na.rm=T)),expand = c(0,0))
    
    # setup the general plot
    plot1 <- ggplot(NULL)+theme_tgs+
      geom_line(data=dop,aes(x=datehom,y=vel2d,group=point),col='grey',linewidth=1)+
      geom_line(data=dip,aes(x=datehom,y=vel2d,group=point,col=point),linewidth=1)+
      scale_colour_viridis_d()+
      xlab(NULL)+ylab('horizontal surface velocity (m/a)')+y.axis+x.axis
    return(plot1)
  })
  
  output$filtered_point_plot <- renderPlotly({
    df = data_filter()
    df$filter = df$v_filter+df$p_filter+df$d_filter+df$vo_filter+df$vc_filter+df$p1_filter
    
    d.in = df[df$filter==0,]
    d.out = df[df$filter!=0,]
    
    # setup the general plot
    plot1 <- ggplot(NULL)+theme_bw()+
      geom_point(data=d.out,aes(x=e,y=n,group=point),col='grey')+
      geom_point(data=d.in,aes(x=e,y=n,group=point,col=point))+
      scale_colour_viridis_d()+
      xlab('easting (m)')+ylab('northing (m)')+coord_equal()
    plot1 <- ggplotly(plot1)
    return(plot1)
  })
  
  output$wdata <- downloadHandler(
    filename <- function(){
      n = site_name()
      paste0(substr(n,1,nchar(n)-4),'_selection.csv')}
    ,content <- function(file){
      df <- set_filter()
      df <- df %>% arrange(point,date)
      write.csv(df,file,quote = F,row.names = F)
    })
  
  output$wth <- downloadHandler(
    filename <- function(){
      n = site_name()
      paste0(substr(n,1,nchar(n)-4),'_threshold.csv')}
    ,content <- function(file){
      t = c('data completness','velocity limit','direction change limit','velocity variability','velocity change')
      f = c('p_filter','v_filter','d_filter','vo_filter','vc_filter')
      v = c(input$dcomp,input$vlim,input$dlim,input$vdev,input$vcdev)
      df <- data.frame(threshold=t,name=f,value=v)
      write.csv(df,file,quote = F,row.names = F,sep=',')
    })
  
  # ------------------------------------------------
  # OUTPUT TAB 6 - Gap filling 
  # ------------------------------------------------
  # table output with filled data (including statistics)
  output$tab_gap <- renderDataTable({
    df <- set_filter()
    df <- fill.gap(df,clim=input$clim) %>% filter(point==input$tgs_gap) %>% 
      select(point,date,vel2d,vel2d_fill,reg,fill_se)
    
    datatable(df,extensions = list("Scroller"=NULL,"FixedColumns"= list(leftColumns=1)),
              options=list(paging=F,fixedColumns=TRUE,scrollY=700,scrollX=T,searching=FALSE)
              ,rownames=FALSE,class="nowrap display cell-border stripe'")
  })
  
  output$gap_fill_plot <- renderPlot({
    df <- set_filter()
    fill <- fill.gap(df,clim=input$clim) %>% filter(point==input$tgs_gap)
    reg  <- df %>% filter(point%in%unique(fill$reg))
    
    #duplicate data for step plot
    dup <- fill %>% arrange(datehom) %>% slice(rep(1:n(), each = 2)) %>%mutate(vel2d = lead(vel2d,1),
                                                                               vel2d_fill = lead(vel2d_fill,1))
    dupr <- reg %>% arrange(datehom) %>% group_by(point) %>% slice(rep(1:n(), each = 2)) %>%mutate(vel2d = lead(vel2d,1))
    
    dup <- rbind(dup[1,],dup)
    dup$datehom[1]=dup$datehom[1]-366
    dupr <- dupr[2:nrow(dupr),]
    
    # define plot aestetics
    cols = c('measured'='black','fill'='red','regressor'='blue')
    x.axis <- scale_x_date(date_breaks='2 year', date_labels="%Y",expand= c(0,0),limits = c(min(dup$datehom,na.rm=T),max(dup$datehom,na.rm=T)))
    
    p <- ggplot(dup)+theme_tgs+
      geom_line(data=dupr,aes(datehom,vel2d,group=point,col='regressor'),linewidth=1)+
      geom_line(aes(datehom,vel2d_fill,col='fill'),linewidth=1)+
      geom_line(aes(datehom,vel2d,col='measured'),linewidth=1.2)+
      xlab(NULL)+ylab('horizontal velocity (m/y)')+x.axis+
      scale_colour_manual(values=cols)+theme(legend.title = element_blank())
    return(p)
  })
  
  output$wgap <- downloadHandler(
    filename <- function(){
      n = site_name()
      paste0(substr(n,1,nchar(n)-4),'_fill.csv')}
    ,content <- function(file){
      df <- set_filter()
      df <- fill.gap(df,clim=input$clim)
      df <- df %>% select(date,point,e,n,h,datehom,date1,date2,timediff,ediff,ndiff,hdiff,vel2d,vel3d,dir,dirshift,p_filter,v_filter,d_filter,vo_filter,
                          vc_filter,p1_filter,filter,vel2d_fill,reg,fill_se)
      write.csv(df,file,quote = F,row.names = F)
    })
  
  # ------------------------------------------------
  # OUTPUT TAB 7 - Clustering 
  # ------------------------------------------------
  output$dendro_plot <- renderPlot({
    df <- set_filter()
    df <- fill.gap(df,clim = input$clim)
    
    #perform clustering
    cl <- cluster(df)
    cl <- as.dendrogram(cl)
    
    #set cluster limit
    df <- set_cluster()
    df$cluster = as.numeric(df$cluster)
    cluster_n = max(df$cluster,na.rm=T)
    
    #attribute colors for each cluster
    colLab<<-function(n){
      if(is.leaf(n)){
        
        #find current leaf attribute
        a=attributes(n)
        
        #attribute new value
        ligne=match(a$label,df$point)
        cluster=df[ligne,colnames(df)=='cluster']
        col_cluster = viridis::viridis(n=cluster_n)[cluster]
        
        #Modification of leaf attribute
        attr(n,"nodePar")<-c(a$nodePar,list(cex=1.5,lab.cex=1,pch=20,col=col_cluster,lab.col=col_cluster,lab.font=1,lab.cex=1))
      }
      return(n)
    }
    
    dcl <- dendrapply(cl, colLab)
    plot(dcl)
  })
  
  output$p_clust_plot <- renderPlotly({
    df <- set_cluster()
    
    # setup the general plot
    plot1 <- ggplot(NULL)+theme_bw()+
      geom_point(data=df,aes(x=e,y=n,group=point,col=cluster))+
      scale_colour_viridis_d()+
      xlab('easting (m)')+ylab('northing (m)')+coord_equal()
    plot1 <- ggplotly(plot1)
    return(plot1)
  })
  
  output$v_clust_plot <- renderPlot({
    df = set_cluster()
    
    #compute relative velocity
    df <- df %>% group_by(point) %>% mutate(
      rel2d = vel2d_fill/mean(vel2d_fill,na.rm = T)) %>% ungroup() 
    
    #compute cluster average
    dfm <- df %>% group_by(cluster,datehom) %>% summarise(
      rel2d = mean(rel2d,na.rm=T)) %>% ungroup()
    
    #duplicate for step plot
    dup <- df %>% arrange(point,datehom) %>% group_by(point) %>% 
      slice(rep(1:n(),each=2)) %>% mutate(rel2d=lead(rel2d,1)
                                          ,cluster = as.factor(cluster)
                                          ,group = point)
    dupm <- dfm %>% arrange(cluster,datehom) %>% group_by(cluster) %>%
      slice(rep(1:n(),each=2)) %>% mutate(rel2d=lead(rel2d,1))
    
    
    dup1 <- dup %>% arrange(point,datehom) %>% group_by(point) %>% 
      slice_head() %>% mutate(datehom = datehom -365)
    dupm1 <- dupm %>% arrange(cluster,datehom) %>% group_by(cluster) %>% 
      slice_head() %>% mutate(datehom = datehom -365)
    
    dup <- rbind(dup1,dup) %>% arrange(point,datehom)
    dupm <- rbind(dupm1,dupm) %>% arrange(cluster,datehom)
    
    x.axis <- scale_x_date(date_breaks='2 year', date_labels="%Y",expand= c(0,0),limits = c(min(dup$datehom,na.rm=T),max(dup$datehom,na.rm=T)))
    
    # setup the general plot
    plot1 <- ggplot(NULL)+theme_tgs+
      geom_line(data=dupm,aes(x=datehom,y=rel2d,col=cluster),linewidth=2)+
      geom_line(data=dup,aes(x=datehom,y=rel2d,group=point,col=cluster),linewidth=.5,alpha=.5)+
      scale_colour_viridis_d()+
      xlab(NULL)+ylab('relative horizontal surface velocity (m/a)')+x.axis
    return(plot1)
  })
  
  output$wclust <- downloadHandler(
    filename <- function(){
      n = site_name()
      paste0(substr(n,1,nchar(n)-4),'_cluster.csv')}
    ,content <- function(file){
      df <- set_cluster()
      df <- df %>% select(date,point,e,n,h,datehom,date1,date2,timediff,ediff,ndiff,hdiff,vel2d,vel3d,dir,dirshift,p_filter,v_filter,d_filter,vo_filter,
                          vc_filter,p1_filter,filter,vel2d_fill,reg,fill_se,cluster)
      write.csv(df,file,quote = F,row.names = F)
    })
  
  # ------------------------------------------------
  # OUTPUT TAB 8 - RGV 
  # ------------------------------------------------
  output$rgv_plot <- renderPlot({
    df = set_cluster()
    
    #compute cluster average
    dfm <- df %>% group_by(cluster,datehom) %>% summarise(
      vel2d_fill = mean(vel2d_fill,na.rm=T)) %>% ungroup()
    
    #duplicate for step plot
    dupm <- dfm %>% arrange(cluster,datehom) %>% group_by(cluster) %>%
      slice(rep(1:n(),each=2)) %>% mutate(vel2d_fill=lead(vel2d_fill,1))
    
    dupm1 <- dupm %>% arrange(cluster,datehom) %>% group_by(cluster) %>% 
      slice_head() %>% mutate(datehom = datehom -365)
    
    dupm <- rbind(dupm1,dupm) %>% arrange(cluster,datehom)
    
    x.axis <- scale_x_date(date_breaks='2 year', date_labels="%Y",expand= c(0,0),,limits = c(min(dupm$datehom,na.rm=T),max(dupm$datehom,na.rm=T)))
    
    # setup the general plot
    plot1 <- ggplot(data=dupm,aes(x=datehom,y=vel2d_fill,col=cluster))+theme_tgs+
      geom_smooth(method = 'lm',se=F,linetype=2)+
      geom_line(linewidth=2)+
      scale_colour_viridis_d()+
      xlab(NULL)+ylab('horizontal surface velocity (m/a)')+x.axis
    return(plot1)
  })
  
  output$tab_clust_stat <- renderDataTable({
    df <- stat_cluster()
    
    datatable(df,extensions = list("Scroller"=NULL,"FixedColumns"= list(leftColumns=1)),
              options=list(paging=F,fixedColumns=TRUE,scrollY=700,scrollX=T,searching=FALSE)
              ,rownames=FALSE,class="nowrap display cell-border stripe'")
  })
  
  output$wrgv <- downloadHandler(
    filename <- function(){
      n = site_name()
      paste0(substr(n,1,nchar(n)-4),'_rgv.csv')}
    ,content <- function(file){
      df <- rgv()
      write.csv(df,file,quote = F,row.names = F,sep=',')
    })
}

# launch app
shinyApp(ui,server)
