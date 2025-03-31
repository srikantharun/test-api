#pragma once
#include <platform.h>
#include <barrier.h>


/**
 * @brief Pipeline status enumeration
 */
typedef enum {
    STOPPED = 0,  /**< Pipeline is stopped/inactive */
    RUNNING,      /**< Pipeline is currently running */
} PIPELINE_STATUS;

/**
 * @brief Pipeline control structure
 */
typedef struct {
    PIPELINE_STATUS status;   /**< Current status of the pipeline */
    barrier_t barrier;        /**< Synchronization barrier for workers */
    int num_cores;           /**< Number of worker cores in the pipeline */
} pipeline_t;

/**
 * @brief Synchronizes all worker threads at a barrier point
 *
 * @param pipeline Pointer to the pipeline structure
 */
static inline void pipeline_barrier(pipeline_t *pipeline)
{
    barrier_wait(&pipeline->barrier);
}

/**
 * @brief Initializes a pipeline structure
 *
 * @param pipeline Pointer to the pipeline structure to initialize
 * @param num_cores Number of worker cores to use in the pipeline
 */
static inline void pipeline_init(pipeline_t *pipeline, int num_cores)
{
    pipeline->status = STOPPED;
    pipeline->num_cores = num_cores;

    barrier_init(&pipeline->barrier, pipeline->num_cores);
}

/**
 * @brief Starts the pipeline and synchronizes all workers
 *
 * @param pipeline Pointer to the pipeline structure
 */
static inline void pipeline_start(pipeline_t *pipeline)
{
    pipeline->status = RUNNING;
    barrier_wait(&pipeline->barrier);
}

/**
 * @brief Stops the pipeline and synchronizes all workers
 *
 * @param pipeline Pointer to the pipeline structure
 */
static inline void pipeline_stop(pipeline_t *pipeline)
{
    pipeline->status = STOPPED;
    pipeline_barrier(pipeline);
}

/**
 * @brief Waits for all workers to reach the barrier point and checks pipeline status
 *
 * This function synchronizes all workers at a barrier point and checks if the
 * pipeline has been stopped. It's intended to be used as a synchronization
 * point between pipeline stages.
 *
 * @param pipeline Pointer to the pipeline structure
 * @return 1 if the pipeline is stopped, 0 if it's still running
 */
static inline int pipeline_wait(pipeline_t *pipeline)
{
    pipeline_barrier(pipeline);
    // Indicate closure of the loop to the workers
    if (pipeline->status == STOPPED)
        return 1;
    return 0;
}
