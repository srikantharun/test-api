# CI Pipeline Monitoring

## Overview
Please refer to the confluence page for details (https://axeleraai.atlassian.net/wiki/spaces/infrastructure/pages/840302778/Advanced+Cleanup+Using+Monitoring+Job+On+Every+Job)

## User Guidelines
Note 1: Please ensure that any new template dynamic jobs created under .gitlab/ci/pipelines/dynamic extends .template:load:capture-pids.
For example,
validate:aic_cd-compile:
  extends:
    - .template:load:capture-pids # This is the new template that adds a before_trigger tasks
    - .template:load:env-default
  stage: validate
  tags:
    - test-shell
    - test-shell
    - test-shell
  script:
    - make -C hw/ip/aic_control_dispatcher/default/sim-questa compile_vsim

