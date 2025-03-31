#include <encoding.h>
#include <trap.h>
#include <testutils.h>

volatile static bool expect_bwe_irq = false;

// override default handler so we can handle bus errors gracefully
void local_irq_bwe_handler(void) {
    if (expect_bwe_irq) {
        expect_bwe_irq = false;
    } else {
        printf("unexpected bus transaction error received\n");
        abort();
    }
}

int main() {
    printf("*** test_ax65_bus_error starts...\n");
    testcase_init();
    volatile uint64_t *invalid_ptr = (volatile uint64_t*)0x00000040;

    // NOTE: It could theoretically happen that the bus errors would be
    //       "precise". In that case, they would be deliverd as load/store
    //       access fault exceptions instead. However, I have not managed to
    //       trigger this case in practice.

    {
        printf("testing bus read transaction error\n");
        expect_bwe_irq = true;
        asm ("fence");
        *invalid_ptr;
        asm ("fence");
        CHECK_TRUE(!expect_bwe_irq, "no bus read transaction error received");
    }

    {
        printf("testing bus write transaction error\n");
        expect_bwe_irq = true;
        asm ("fence");
        *invalid_ptr;
        asm ("fence");
        CHECK_TRUE(!expect_bwe_irq, "no bus write transaction error received");
    }

    // TODO: Do this for both cacheable and uncacheable regions (if present).

    return testcase_finalize();
}
