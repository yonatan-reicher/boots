typedef enum type {
    PROP,
} type;

typedef enum prop {
} prop;

// float -> int
typedef struct f_closure {
  int (*call)(void*, float);
  float _1; // Captured value;
} f_closure;

int f(float x, float y) {
  return x - y;
}

int f_call(void* func, float x) {
  f_closure* c = (f_closure*)func;
  return f(x, c->_1);
}

f_closure make_f(float y) {
  f_closure ret = {
    f_call, y
  };
  return ret;
}

typedef struct closure_head {
  int (*call)(void*, float);
} closure_head;















def f(x):
  return lambda y: x - y















