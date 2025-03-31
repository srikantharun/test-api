#pragma once

#include <stdarg.h>
#include <stddef.h>

void *memcpy(void *dest, const void *src, size_t len);
void *memset(void *dest, int byte, size_t len);
int memcmp(const void *s1, const void *s2, size_t n);

void vprintfmt(void (*putch)(int, void **), void **putdat, const char *fmt, va_list ap);
int sprintf(char *str, const char *fmt, ...);
int vsprintf(char *str, const char *fmt, va_list ap);
size_t strlen(const char *s);
size_t strnlen(const char *s, size_t n);
int strcmp(const char *s1, const char *s2);
int strncmp(const char *s1, const char *s2, size_t n);
char *strcpy(char *dest, const char *src);
char *strrchr(const char *str, int c);
long atol(const char *str);
