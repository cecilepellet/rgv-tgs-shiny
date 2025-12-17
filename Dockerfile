FROM rocker/shiny:4
# Install R dependencies
RUN R -e "install.packages(c('shiny', 'ggplot2', 'DT','caTools','readr','dplyr','tidyr','lubridate','grid','gridExtra','plotly','bslib','bsicons','ggdendro'))"
# set permissions of the R library directory to be editable by shiny (997:997)
# see https://github.com/SwissDataScienceCenter/renkulab-docker/blob/main/docker/r/Dockerfile
ENV NB_UID=997
ENV NB_GID=997
COPY fix-permissions.sh /usr/local/bin
RUN fix-permissions.sh /usr/local/lib/R

RUN apt-get update && apt-get install -y \
    gettext-base

COPY shiny-server.conf.tpl /shiny-server.conf.tpl
COPY docker-entrypoint.sh /docker-entrypoint.sh
RUN chown shiny:shiny /etc/shiny-server/shiny-server.conf

COPY src/r/app /home/shiny/app

USER shiny
ENTRYPOINT ["/bin/sh", "/docker-entrypoint.sh"]
CMD ["/init"]
