/*
 * errno.h - implementation of the C standard errno functionality
 *
 * This is required to enable use of Newlib's math library (libm.a) despite not
 * linking to its companion libc.a (which would normally provide the __errno
 * symbol).
 */


#define errno (*__errno())
int *__errno();
