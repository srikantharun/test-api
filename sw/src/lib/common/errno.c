static __thread int __errno_storage;

int *__errno() {
    return &__errno_storage;
}
