//
//  float_vector.c
//  cadet
//
//  Created by Markus Rabe on 13.09.17.
//  Copyright © 2017 UC Berkeley. All rights reserved.
//

#include "float_vector.h"
#include "log.h"
#include "stdbool.h"
#include "util.h"

#include <assert.h>

#define VECTOR_NOT_FOUND (unsigned)-1
#define INITIAL_SIZE 2
#define INCREASE_FACTOR 2

void float_vector_increase(float_vector* v) {
    v->size *= INCREASE_FACTOR;
    assert(v->size > 0);
    v->data = realloc(v->data, sizeof(float) * v->size);
    //    float* newdata = malloc(sizeof(float) * v->size);
    //    for (unsigned i = 0; i < v->count; i++) {
    //        newdata[i] = v->data[i];
    //    }
    //    free(v->data);
    //    v->data = newdata;
}

float_vector* float_vector_init() {
    float_vector* v = malloc(sizeof(float_vector));
    float_vector_init_struct(v);
    return v;
}

void float_vector_init_struct(float_vector* v) {
    assert(v);
    v->data = malloc(sizeof(float) * INITIAL_SIZE);
    v->count = 0;
    v->size = INITIAL_SIZE;
}

void float_vector_reset(float_vector* v) {
    v->count = 0;
}

void float_vector_free(float_vector* v) {
    free(v->data);
    free(v);
}

unsigned float_vector_count(float_vector* v) {
    return v->count;
}

void float_vector_reduce_count(float_vector* v, unsigned j) {
    assert(j <= v->count);
    v->count = j;
}

float float_vector_get(float_vector* v, unsigned i) {
    assert (i < v->count);
    return v->data[i];
}

float float_vector_pop(float_vector* v) {
    abortif(v->count == 0, "Pop from empty vector");
    v->count -= 1;
    return v->data[v->count];
}

void float_vector_set(float_vector* v, unsigned i, float value) {
    assert (v->count > i);
    v->data[i] = value;
}

// returns absolute position, and returns -1 in case the element is not contained
unsigned float_vector_find(float_vector* v, float value) {
    for (unsigned i = 0; i < v->count; i++) {
        if (v->data[i]==value) {
            return i;
        }
    }
    return VECTOR_NOT_FOUND;
}

// returns absolute position, and returns -1 in case the element is not contained
unsigned float_vector_find_sorted(float_vector* v, float value) {
    if (v->count != 0) {
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
    }
    return VECTOR_NOT_FOUND;
}

bool float_vector_contains_sorted(float_vector* v, float value) {
    return float_vector_find_sorted(v, value) != VECTOR_NOT_FOUND;
}

bool float_vector_contains(float_vector* v, float value) {
    return float_vector_find(v, value) != VECTOR_NOT_FOUND;
}

void float_vector_add(float_vector* v, float value) {
    if (v->size == v->count) {
        float_vector_increase(v);
    }
    v->data[v->count] = value;
    v->count += 1;
}

void float_vector_add_sorted(float_vector* v, float value) {
    if (v->count == 0) {
        float_vector_add(v, value);
        return;
    }
    if (v->size == v->count) {
        float_vector_increase(v);
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
        float swap = v->data[i];
        v->data[i] = value;
        value = swap;
    }
    v->data[v->count] = value;
    v->count += 1;
}

float* float_vector_get_data(float_vector* v) {
    return v->data;
}

void float_vector_print(float_vector* v) {
    //    V4("float_vector (%u,%u) ", v->count, v->size);
    for (unsigned j = 0; j < v->count; j++) {
        printf(" %f", v->data[j]);
    }
    printf("\n");
}

bool float_vector_remove(float_vector* v, float value) {
    unsigned i;
    for (i = 0; i < v->count; i++) {
        if (v->data[i] == value) {
            break;
        }
    }
    if (i == v->count) {
        return false;
    }
    float_vector_remove_index(v, i);
    return true;
}

void float_vector_remove_index(float_vector* v, unsigned i) {
    v->count = v->count - 1; // yes, before the loop
    for (; i < v->count; i++) {
        v->data[i] = v->data[i+1];
    }
}

bool float_vector_is_strictly_sorted(float_vector* v) {
    for (unsigned i = 1; i < float_vector_count(v); i++) {
        if (float_vector_get(v, i-1) >= float_vector_get(v, i)) {
            return false;
        }
    }
    return true;
}

void float_vector_sort(float_vector* v, int (*cmp)(const void*, const void*)) {
    qsort(v->data, v->count, sizeof(float), cmp);
}

// assumes sortedness
void float_vector_remove_duplicates(float_vector* v) {
    if (float_vector_count(v) <= 1) {
        return;
    }
    unsigned j = 0;
    unsigned del = 0;
    for (unsigned i = 1; i < float_vector_count(v); i++) {
        assert(j<i);
        float x = float_vector_get(v, j);
        float y = float_vector_get(v, i);
        assert( y >= x ); // sorted
        if (x == y) {
            del++;
        } else {
            j++;
            float_vector_set(v, j, y);
        }
    }
    assert(float_vector_count(v) - del == j+1);
    float_vector_reduce_count(v, j+1);
    
    return;
}

float_vector* float_vector_copy(float_vector* old) {
    float_vector* new = float_vector_init();
    for (unsigned i = 0; i < float_vector_count(old); i++) {
        float_vector_add(new, float_vector_get(old, i));
    }
    return new;
}

bool float_vector_includes_sorted(float_vector* v1,float_vector* v2) {
    assert(float_vector_is_strictly_sorted(v1));
    assert(float_vector_is_strictly_sorted(v2));
    
    unsigned j = 0; // next_possible_v1_index
    for (unsigned i = 0; i < float_vector_count(v2); i++) {
        float x = float_vector_get(v2, i);
        
        while (true) {
            if ((int) float_vector_count(v2) - (int) i > (int) float_vector_count(v1) - (int) j) {
                return false;
            }
            assert(float_vector_count(v1) > j);
            if (float_vector_get(v1, j) < x) {
                j++;
            } else if (float_vector_get(v1, j) == x) {
                j++;
                break; // implicitly increases i
            } else {
                return false;
            }
        }
    }
    return true;
}

void float_vector_add_all(float_vector* this, float_vector* other) {
    for (unsigned i = 0; i < float_vector_count(other); i++) {
        float_vector_add(this, float_vector_get(other, i));
    }
}

void float_vector_add_all_sorted(float_vector* this, float_vector* other) {
    assert(float_vector_is_strictly_sorted(this));
    assert(float_vector_is_strictly_sorted(other));
    for (unsigned i = 0; i < float_vector_count(other); i++) {
        float val = float_vector_get(other, i);
        float_vector_add_sorted(this, val);
    }
    assert(float_vector_is_strictly_sorted(this));
}
