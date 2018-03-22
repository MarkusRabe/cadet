
#include <assert.h>

#include "vector.h"
#include "log.h"
#include "stdbool.h"
#include "util.h"

#define VECTOR_NOT_FOUND (unsigned)-1
#define INITIAL_SIZE 2
#define INCREASE_FACTOR 2

/* Helper */
void vector_increase(vector* v) {
    v->size *= INCREASE_FACTOR;
    v->data = realloc(v->data, sizeof(void*) * v->size);
//    void** newdata = malloc(sizeof(void*) * v->size);
//    for (unsigned i = 0; i < v->count; i++) {
//        newdata[i] = v->data[i];
//    }
//    free(v->data);
//    v->data = newdata;
}

/* Interface */

vector* vector_init() {
    vector* v = malloc(sizeof(vector));
    vector_init_struct(v);
    return v;
}

void vector_init_struct(vector* v) {
    assert(v);
    v->data = malloc(sizeof(void*) * INITIAL_SIZE);
    v->count = 0;
    v->size = INITIAL_SIZE;
}

void vector_reset(vector* v) {
    v->count = 0;
}

void vector_free(vector* v) {
    free(v->data);
    free(v);
}

unsigned vector_count(vector* v) {
    return v->count;
}

void vector_reduce_count(vector* v, unsigned j) {
    assert(j <= v->count);
    v->count = j;
}

void* vector_get(vector* v, unsigned i) {
    assert (v->count > i);
    assert(i >= 0);
    return v->data[i];
}

void* vector_pop(vector* v) {
    assert(v->count > 0);
    v->count -= 1;
    return v->data[v->count];
}

void vector_set(vector* v, unsigned i, void* value) {
    assert (v->count > i);
    v->data[i] = value;
}

// returns absolute position, and returns -1 in case the element is not contained
unsigned vector_find(vector* v, void* value) {
    for (unsigned i = 0; i < v->count; i++) {
        if (v->data[i] == value) {
            return i;
        }
    }
    return VECTOR_NOT_FOUND;
}

// returns absolute position, and returns -1 in case the element is not contained
unsigned vector_find_sorted(vector* v, void* value) {
    long long imin = 0, imax = v->count - 1;
    while (imax >= imin) {
        long long imid = imin + ((imax - imin) / 2); // prevent overflow
        if (v->data[imid] == value) {
            return (unsigned) imid;
        } else if (v->data[imid] < value) {
            imin = imid + 1;
        } else {
            imax = imid - 1;
        }
    }
    return VECTOR_NOT_FOUND;
}

bool vector_contains(vector* v, void* value) {
    return vector_find(v, value) != VECTOR_NOT_FOUND;
}

bool vector_contains_sorted(vector* v, void* value) {
    return vector_find_sorted(v, value) != VECTOR_NOT_FOUND;
}

void vector_add(vector* v, void* value) {
    if (v->size == v->count) {
        vector_increase(v);
    }
    v->data[v->count] = value;
    v->count += 1;
}

void vector_add_sorted(vector* v, void* value) {
    if (v->size == v->count) {
        vector_increase(v);
    }
    long long imin = 0, imax = v->count - 1;
    while (imax >= imin) {
        long long imid = imin + ((imax - imin) / 2); // prevent overflow
        if (v->data[imid] == value) {
            return;
        } else if (v->data[imid] < value) {
            imin = imid + 1;
        } else {
            imax = imid - 1;
        }
    }
    
    for (unsigned i = (unsigned) imin; i < v->count; i++) {
        void* swap = v->data[i];
        v->data[i] = value;
        value = swap;
    }
    v->data[v->count] = value;
    v->count += 1;
}

void vector_insert_at(vector* v, unsigned i, void* value) {
    if (v->size == v->count) {
        vector_increase(v);
    }
    for (unsigned j = i; j < v->count; j++) {
        void* swap = v->data[j];
        v->data[j] = value;
        value = swap;
    }
    v->data[v->count] = value;
    v->count += 1;
}

void vector_print(vector* v) {
    V2("Vector (%u,%u) %s",v->count,v->size,"");
    for(unsigned j = 0; j < v->count; j++) {
        V2(" %ld", (long) v->data[j]);
    }
    V2("\n%s","");
}

void vector_resize(vector* v, unsigned value) {
    v->size = value;
    void** newdata = malloc(sizeof(void*) * v->size);
    for (unsigned i = 0; i < v->count; i++) {
        newdata[i] = v->data[i];
    }
    free(v->data);
    v->data = newdata;
}

bool vector_is_sorted(vector* v) {
    for (unsigned i = 1; i < vector_count(v); i++) {
        if (vector_get(v, i-1) > vector_get(v, i)) {
            return false;
        }
    }
    return true;
}

void vector_remove_last_element(vector* v) {
    assert(v->count > 0);
    v->count = v->count - 1;
}

void vector_remove_index(vector* v, unsigned i) {
    assert(i >= 0);
    assert(i < v->count);
    v->count--; // yes, before the loop
    for (; i < v->count; i++) {
        v->data[i] = v->data[i+1];
    }
}

bool vector_remove_unsorted(vector* v, void* value) {
    unsigned i;
    for (i = 0; i < v->count; i++) {
        if (v->data[i] == value) {
            break;
        }
    }
    if (i == v->count) {
        return false;
    }
    
    v->data[i] = v->data[v->count - 1];
    v->count--;
    
    return true;
}

bool vector_remove(vector* v, void* value) {
    unsigned i;
    for (i = 0; i < v->count; i++) {
        if (v->data[i] == value) {
            break;
        }
    }
    if (i == v->count) {
        return false;
    }
    vector_remove_index(v, i);
    return true;
}

void vector_sort(vector* v) {
    qsort(v->data, v->count, sizeof(int), compare_pointers_natural_order);
}

// Assumes sortedness, or at least assumes that equal elements occur in succession
void vector_remove_duplicates(vector* v) {
    assert(vector_is_sorted(v));
    if (vector_count(v) <= 1) {
        return;
    }
    unsigned j = 0;
    unsigned del = 0;
    for (unsigned i = 1; i < vector_count(v); i++) {
        assert(j<i);
        void* x = vector_get(v, j);
        void* y = vector_get(v, i);
        if (x == y) {
            del++;
        } else {
            j++;
            vector_set(v, j, y);
        }
    }
    assert(vector_count(v) - del == j+1);
    vector_reduce_count(v, j+1);
    return;
}



