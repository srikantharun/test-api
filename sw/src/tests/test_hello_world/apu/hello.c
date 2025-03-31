#include <printf.h>

#include "another_file.h"

int main() {
#ifdef TEAM
    char msg[] = "Hello Verif Team <3\r\n";
#else
    char msg[] = "Hi Axelera, I'm Europa!\r\n";
#endif
    printf("%s", msg);

#ifdef SECOND_FUNC
    just_during_long_regression();
#endif
    return 0;
}
