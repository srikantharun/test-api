/*
 * NOP implementation for printf() - europa#781
 *
 * This empty printf() implementation removes calls to reentrant_lock_{acquire,release} from
 * printf(), which is relevant their LR/SC * operations are not yet supported on Veloce. This is a
 * temporary workaround and should be removed once LR/SC operations are possible on Veloce.
 *
 * TODO(mwipfli, europa#781): Remove once LR/SC operations are possible on Veloce again.
 */
#include <stdint.h>
#include <util.h>

int _printf(uint32_t arg_cnt, const char *fmt, ...) {
    UNUSED(arg_cnt);
    UNUSED(fmt);

    return 0;
}
