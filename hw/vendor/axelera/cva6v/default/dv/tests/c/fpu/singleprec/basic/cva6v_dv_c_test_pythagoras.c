#include <stdint.h>
#include <math.h>
#include <printf.h>
#include <testutils.h>
#include <common.h>

typedef struct {
    float a; // adjacent side
    float b; // opposite side
    float c; // hypotenuse (square root of a*a + b*b)
} triangle_t;

#define N_TRIANGLES 40

triangle_t triangles [N_TRIANGLES] =
{
    { 2.91f,  2.65f,  3.94f},
    { 3.29f,  3.78f,  5.01f},
    { 0.24f,  2.30f,  2.31f},
    { 3.86f,  4.31f,  5.79f},
    { 3.06f,  1.16f,  3.27f},
    { 1.35f,  4.99f,  5.17f},
    { 1.77f,  4.37f,  4.71f},
    { 1.80f,  4.81f,  5.14f},
    { 1.62f,  1.97f,  2.55f},
    { 2.59f,  1.11f,  2.82f},
    {10.80f, 72.83f, 73.63f},
    {18.52f, 14.34f, 23.42f},
    {29.22f, 17.56f, 34.09f},
    {24.03f, 47.83f, 53.53f},
    {25.66f, 77.58f, 81.71f},
    {95.54f, 16.85f, 97.01f},
    {49.23f, 81.40f, 95.13f},
    {18.07f, 21.37f, 27.99f},
    {94.27f, 23.02f, 97.04f},
    {39.14f, 88.69f, 96.94f},
    {-25.82f, 12.42f, 28.65f},
    {-20.66f, 93.50f, 95.76f},
    {-10.12f, 94.38f, 94.92f},
    {-9.23f, 83.69f, 84.20f},
    {-57.03f, 16.16f, 59.28f},
    {-35.79f, 96.10f, 102.55f},
    {-39.76f, 59.57f, 71.62f},
    {-11.16f, 35.42f, 37.14f},
    {-64.76f, 21.64f, 68.28f},
    {-18.73f, 17.54f, 25.66f},
    {99.16f, -28.44f, 103.16f},
    {54.36f, -94.58f, 109.09f},
    {-17.70f, -35.57f, 39.73f},
    {-94.68f, 4.51f, 94.79f},
    {48.83f, 92.85f, 104.91f},
    {34.61f, -40.19f, 53.04f},
    {91.06f, -47.59f, 102.75f},
    {12.44f, 22.69f, 25.88f},
    {-96.19f, 34.31f, 102.13f},
    {-85.37f, -32.60f, 91.38f}
};

float calculate_hypotenuse(float a, float b) {
    return roundf(sqrtf((a * a) + (b * b))*100) / 100;
}

int main() {

    setup_trap_handler();
    // Configure privilege and vector extension
    configure_privilege_and_vector_extension();

    // Initialize vector registers
    initialize_vector_registers();
    testcase_init();

    printf("This is the pythagoras test:\n");

    for (int i = 0; i < N_TRIANGLES; i++) {
        int j = i% N_TRIANGLES;
        float c;
        c =calculate_hypotenuse(triangles[j].a, triangles[j].b);

        if (CHECK_TRUE(round_float_to_n(c,2) == round_float_to_n(triangles[j].c,2))) {
            printf("Loop %0d: OK ", i); print_float(c,2); printf("\n");
        } else {
           printf("Loop %0d: NOT OK Expected ", i ); print_float(c,2); printf(" Observed "); print_float(triangles[j].c, 2); printf("\n"); 
        }
    }

    return(testcase_finalize());
}
