#include <stdint.h>
#include <math.h>
#include <printf.h>
#include <testutils.h>
#include <common.h>

extern volatile uint64_t default_status;
typedef struct {
    float value;
    float sine;
    float cosine;
    float tangent;
} trigonometry_t;

trigonometry_t angles [] =
{
    { -1.0000f, -0.8415f, 0.5403f, -1.5574f },
    { -0.9000f, -0.7833f, 0.6216f, -1.2602f },
    { -0.8000f, -0.7174f, 0.6967f, -1.0296f },
    { -0.7000f, -0.6442f, 0.7648f, -0.8423f },
    { -0.6000f, -0.5646f, 0.8253f, -0.6841f },
    { -0.5000f, -0.4794f, 0.8776f, -0.5463f },
    { -0.4000f, -0.3894f, 0.9211f, -0.4228f },
    { -0.3000f, -0.2955f, 0.9553f, -0.3093f },
    { -0.2000f, -0.1987f, 0.9801f, -0.2027f },
    { -0.1000f, -0.0998f, 0.9950f, -0.1003f },
    { -0.0000f, -0.0000f, 1.0000f, -0.0000f },
    { 0.1000f, 0.0998f, 0.9950f, 0.1003f },
    { 0.2000f, 0.1987f, 0.9801f, 0.2027f },
    { 0.3000f, 0.2955f, 0.9553f, 0.3093f },
    { 0.4000f, 0.3894f, 0.9211f, 0.4228f },
    { 0.5000f, 0.4794f, 0.8776f, 0.5463f },
    { 0.6000f, 0.5646f, 0.8253f, 0.6841f },
    { 0.7000f, 0.6442f, 0.7648f, 0.8423f },
    { 0.8000f, 0.7174f, 0.6967f, 1.0296f },
    { 0.9000f, 0.7833f, 0.6216f, 1.2602f },
    { 1.0000f, 0.8415f, 0.5403f, 1.5574f }
};

int main() {
    testcase_init();

    printf("This is the trigonometry test:\n");

    for (int i = 0; i < (int)(sizeof(angles)/sizeof(trigonometry_t)); i++) {
        float s, c, t;
        printf("Loop[%0d]\n", i);

        s   = sinf(angles[i].value);
        c   = cosf(angles[i].value);
        t   = tanf(angles[i].value);

        CHECK_TRUE(round_float_to_n(s, 4) == round_float_to_n(angles[i].sine, 4));

        CHECK_TRUE(round_float_to_n(c, 4) == round_float_to_n(angles[i].cosine, 4));

        CHECK_TRUE(round_float_to_n(t, 4) == round_float_to_n(angles[i].tangent, 4));

        /* Pythagorean Identity */
        float p_id = round_float_to_n(powf(s, 2.0f) + powf(c, 2.0f), 4);
        CHECK_TRUE(round_float_to_n(1.0f, 4) == p_id);

        /* Double Angle formula */
        float s2a, s2b;
        s2a = 2.0f*s*c;
        s2b = sinf(2.0f*angles[i].value);

        CHECK_TRUE(round_float_to_n(s2a, 4) == round_float_to_n(s2b, 4));

        float c2a, c2b;
        c2a = powf(c,2.0f) - powf(s,2.0f);
        c2b = cosf(2.0f*angles[i].value);

        CHECK_TRUE(round_float_to_n(c2a, 4) == round_float_to_n(c2b, 4));

        /* Inverse */
        float as;
        as = asinf(s);

        CHECK_TRUE(round_float_to_n(angles[i].value, 4) == round_float_to_n(as, 4));

        if (0.0f <= angles[i].value) {
            float ac;
            ac = acosf(c);

            CHECK_TRUE(round_float_to_n(angles[i].value, 4) == round_float_to_n(ac, 4));
        }
    }
    
    return(testcase_finalize());
}
