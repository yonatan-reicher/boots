#include <stdlib.h>
#include <string.h>

typedef enum type {
  PROP,
} type;

typedef enum prop {} prop;

typedef struct strData {
    int rc;
    // A char array of amount length.
} strData;

typedef struct str {
    int length;
    strData *data;
} str;

char* getStr(str s) {
    return (char*)(s.data + 1);
}

str makeEmptyStr(int length) {
    str ret = {};
    ret.length = length;
    ret.data = (strData*)malloc(sizeof(strData) + ret.length + 1);
    ret.data->rc = 0;
    return ret;
}

str makeStr(const char* cString) {
    str ret = makeEmptyStr(strlen(cString));
    strcpy(getStr(ret), cString);
    return ret;
}

str cloneStr(str s) {
    s.data->rc++;
    return s;
}

void dropStr(str s) {
    if (s.data->rc == 0) {
        free(s.data);
    } else {
        s.data->rc--;
    }
}

str appendStr(str a, str b) {
    str ret = makeEmptyStr(a.length + b.length);
    strcpy(getStr(ret), getStr(a));
    strcpy(getStr(ret) + a.length, getStr(b));
    return ret;
}


typedef struct appendStrClosureInnerHead appendStrClosureInnerHead;

typedef struct appendStrClosure appendStrClosure;

typedef struct appendStrClosureInner appendStrClosureInner;

struct appendStrClosureInnerHead {
    int rc;
    str (*call)(appendStrClosureInnerHead*, str);
    void (*drop)(void*);
};

struct appendStrClosure {
    int rc;
    appendStrClosureInnerHead* (*call)(appendStrClosure*, str);
    void (*drop)(void*);
};

struct appendStrClosureInner {
    int rc;
    str (*call)(appendStrClosureInner*, str);
    void (*drop)(void*);
    str var2;
};

str callAppendStrClosureInner(appendStrClosureInner *self, str var3) {
    str ret = appendStr(self->var2, var3);
    dropStr(var3);
    return ret;
}

void dropAppendStrClosureInner(void *void_self) {
    appendStrClosureInner *self = ((appendStrClosureInner*)void_self);
    if ((self->rc == 0)) {
        dropStr(self->var2);
        free(self);
    } else {
        self->rc--;
    }
}

appendStrClosureInner* makeAppendStrClosureInner(str var2) {
    appendStrClosure *ret = ((appendStrClosureInner*)malloc(sizeof(appendStrClosureInner)));
    ret->rc = 0;
    ret->call = callAppendStrClosureInner;
    ret->drop = dropAppendStrClosureInner;
    ret->var2 = var2;
    return ret;
}

appendStrClosureInnerHead* callAppendStrClosure(appendStrClosure *self, str x) {
    return makeAppendStrClosureInner(x);
}

void dropAppendStrClosure(void *void_self) {
    appendStrClosure *self = ((appendStrClosure*)void_self);
    if ((self->rc == 0)) {
        free(self);
    } else {
        self->rc--;
    }
}

appendStrClosure* makeAppendStrClosure() {
    appendStrClosure *ret = ((appendStrClosure*)malloc(sizeof(appendStrClosure)));
    ret->rc = 0;
    ret->call = callAppendStrClosure;
    ret->drop = dropAppendStrClosure;
    return ret;
}

appendStrClosure *appendStrClosure = makeAppendStrClosure;

