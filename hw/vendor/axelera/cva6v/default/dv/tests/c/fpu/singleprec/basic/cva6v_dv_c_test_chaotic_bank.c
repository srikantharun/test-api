#include <stdint.h>
#include <math.h>
#include <printf.h>
#include <testutils.h>
#include <common.h>

#define N 18
float expected [N] = {
0.718282f,
0.436564f,
0.309692f,
0.238768f,
0.193838f,
0.163029f,
0.141201f,
0.129608f,
0.166473f,
0.664734f,
6.312073f,
74.744873f,
970.683350f,
13588.566406f,
203827.500000f,
3261239.000000f,
55441064.000000f,
997939136.000000f };

int  main(void)
{
    testcase_init();

    float account = 1.718282;
    float observed [N];

    for (int i = 1; i <=N; i++)
    {
        account = i*account - 1;
        observed[i-1] = account;
    }

    for (int i = 1; i <=N; i++)
    {
        float o = round_float_to_n(observed[i-1], 6);
        float e = round_float_to_n(expected[i-1], 6);
        printf("LOOP[%0d] Comparing: ", i); print_float(o, 6); printf(" vs. "); print_float(e, 6); printf("\n"); 
        CHECK_TRUE(o == e);
    }

    return(testcase_finalize());
}

