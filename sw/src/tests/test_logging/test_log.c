// (C) Copyright Axelera AI 2024
// All Rights Reserved
// *** Axelera AI Confidential ***

// Description: This test demonstrates the functionality of a logging system
//              with configurable log levels. It shows how to set different
//              log levels at runtime and verifies that the log messages are
//              printed according to the current log level.

#include <log.h>

void log_messages(){
    LOG_ERR("This is an error message   | config_log_level = %d", config_log_level);
    LOG_WRN("This is a warning message  | config_log_level = %d", config_log_level);
    LOG_INF("This is an info message    | config_log_level = %d", config_log_level);
    LOG_DBG("This is a debug message    | config_log_level = %d", config_log_level);
}

int main(){

    printf("\nCompile time log level is : %d\n\n", COMPILE_LOG_LEVEL);

    printf("Runtime log level is %d\n", config_log_level);
    log_messages();

    log_set_level(LOG_LEVEL_INF);
    printf("\nRuntime log level is %d\n", config_log_level);
    log_messages();

    // printf will not work when config_log_level < LOG_LEVEL_INF
    log_set_level(LOG_LEVEL_WRN);
    printf("\nRuntime log level is %d\n", config_log_level);
    log_messages();

    // printf will not work when config_log_level < LOG_LEVEL_INF
    log_set_level(LOG_LEVEL_ERR);
    printf("\nRuntime log level is %d\n", config_log_level);
    log_messages();

    // printf will not work when config_log_level < LOG_LEVEL_INF
    log_set_level(LOG_LEVEL_NONE);
    printf("\nRuntime log level is %d\n", config_log_level);
    log_messages();

    return 0;
}
