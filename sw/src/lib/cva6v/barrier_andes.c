#include <barrier_andes.h>


#ifdef SYSTEM_TOP
extern barrier_vars_t barrier_vars;
#else
barrier_vars_t __attribute__((section(".sys_spm"))) barrier_vars = {0};
#endif
