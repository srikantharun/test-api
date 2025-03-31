#include <log.h>

int config_log_level = LOG_LEVEL_DBG;

void log_set_level(int level) { config_log_level = level; }

bool is_valid_log_level(int log_level) {
    const unsigned int valid_log_levels[NUM_LOG_LEVELS] = {
        LOG_LEVEL_NON,
        LOG_LEVEL_ERR,
        LOG_LEVEL_WRN,
        LOG_LEVEL_INF,
        LOG_LEVEL_DBG,
        LOG_LEVEL_TRC
    };

    for (int i = 0; i < NUM_LOG_LEVELS; i++) {
        if (log_level == (int)valid_log_levels[i]) {
            return 1;
        }
    }
    return 0;
}
