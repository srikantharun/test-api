#include <stdio.h>
#include <testutils.h>
#include <reentrant_lock.h>

reentrant_lock_t test_lock = REENTRANT_LOCK_INIT;

int main() {
    testcase_init();

    reentrant_lock_acquire(&test_lock);
    CHECK_EQUAL_INT(1, test_lock.recursion_count);

    reentrant_lock_acquire(&test_lock);
    CHECK_EQUAL_INT(2, test_lock.recursion_count);

    reentrant_lock_acquire(&test_lock);
    CHECK_EQUAL_INT(3, test_lock.recursion_count);

    reentrant_lock_release(&test_lock);
    CHECK_EQUAL_INT(2, test_lock.recursion_count);

    reentrant_lock_release(&test_lock);
    CHECK_EQUAL_INT(1, test_lock.recursion_count);

    reentrant_lock_release(&test_lock);
    CHECK_EQUAL_INT(0, test_lock.recursion_count);

    return testcase_finalize();
}
