#include <stdlib.h>

typedef struct value_head value_head;

typedef value_head* value_ptr;

struct value_head {
   int rc;
   void (*destructor)(value_ptr);
};

void value_decr(value_ptr value) {
    if (value) {
        // Decrease the reference count.
        value->rc--;

        // Should the value be cleaned up?
        if (value->rc == 0) {
            // First do the destructor.
            value->destructor(value);
            // Then clean up all value_head fields.
            value->destructor = NULL;
            // And free the allocation.
            free(value);
        }
    }
}

value_ptr value_inc(value_ptr value) {
    value->rc++;
    return value;
}

typedef struct func_head {
   value_ptr (*func)(value_ptr, value_ptr*);
   size_t closure_size;
} func_head;

void empty_destructor(value_ptr p) {
}

void func_destructor(value_ptr p) {
    func_head* func = (func_head*)(p + 1);
    value_ptr* closure = (value_ptr*)(func + 1);
    for (size_t i = 0; i < func->closure_size; i++) {
        value_decr(closure[i]);
        closure[i] = NULL;
    }
}

value_ptr value_alloc(void (*destructor)(value_ptr), size_t data_size) {
    value_ptr p = malloc(sizeof(value_head) + data_size);
    p->rc = 1;
    p->destructor = destructor;
    return p;
}

value_ptr alloc_int(int i) {
    value_ptr p = value_alloc(empty_destructor, sizeof(int));
    *(int*)(p + 1) = i;
    return p;
}

value_ptr alloc_func(value_ptr (*func)(value_ptr, value_ptr*), size_t arg_count) {
    size_t data_size = sizeof(func_head) + arg_count * sizeof(value_ptr);
    value_ptr p = value_alloc(func_destructor, data_size);
    func_head* pfunc = (func_head*)(p + 1);
    pfunc->func = func;
    pfunc->closure_size = arg_count;
    return p;
}

