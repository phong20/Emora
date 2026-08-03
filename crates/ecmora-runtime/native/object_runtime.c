#include "object_runtime_base.c"

#if defined(_MSC_VER)
__declspec(thread) static uint32_t ecmora_recursion_depth = 0;
#else
static _Thread_local uint32_t ecmora_recursion_depth = 0;
#endif

void ecmora_recursion_enter(const char *function_name, uint32_t limit) {
    if (ecmora_recursion_depth >= limit) {
        fprintf(
            stderr,
            "Ecmora RangeError: maximum native recursion depth (%u) exceeded in %s\n",
            limit,
            function_name == NULL ? "<anonymous>" : function_name
        );
        fflush(stderr);
        abort();
    }
    ecmora_recursion_depth += 1;
}

void ecmora_recursion_leave(void) {
    if (ecmora_recursion_depth != 0) {
        ecmora_recursion_depth -= 1;
    }
}
