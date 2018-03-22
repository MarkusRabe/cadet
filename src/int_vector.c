//
//  int_vector.c
//  cadet
//
//  Created by Markus Rabe on 20/11/2016.
//  Copyright © 2016 UC Berkeley. All rights reserved.
//

#include "int_vector.h"
#include "log.h"
#include "stdbool.h"
#include "util.h"
#include "mersenne_twister.h"

#include <assert.h>

#define VECTOR_NOT_FOUND (unsigned)-1
#define INITIAL_SIZE 2
#define INCREASE_FACTOR 2

void int_vector_increase(int_vector* v) {
    v->size *= INCREASE_FACTOR;
    v->data = realloc(v->data, sizeof(int) * v->size);
    //    int* newdata = malloc(sizeof(int) * v->size);
    //    for (unsigned i = 0; i < v->count; i++) {
    //        newdata[i] = v->data[i];
    //    }
    //    free(v->data);
    //    v->data = newdata;
}

int_vector* int_vector_init() {
    int_vector* v = malloc(sizeof(int_vector));
    int_vector_init_struct(v);
    return v;
}

void int_vector_init_struct(int_vector* v) {
    assert(v);
    v->data = malloc(sizeof(int) * INITIAL_SIZE);
    v->count = 0;
    v->size = INITIAL_SIZE;
}

void int_vector_reset(int_vector* v) {
    v->count = 0;
}

void int_vector_free(int_vector* v) {
    free(v->data);
    free(v);
}

unsigned int_vector_count(int_vector* v) {
    return v->count;
}

void int_vector_reduce_count(int_vector* v, unsigned j) {
    assert(j <= v->count);
    v->count = j;
}

int int_vector_get(int_vector* v, unsigned i) {
    assert (i < v->count);
    return v->data[i];
}

int int_vector_pop(int_vector* v) {
    abortif(v->count == 0, "Pop from empty vector");
    v->count -= 1;
    return v->data[v->count];
}

void int_vector_set(int_vector* v, unsigned i, int value) {
    assert (v->count > i);
    v->data[i] = value;
}

// returns absolute position, and returns -1 in case the element is not contained
unsigned int_vector_find(int_vector* v, int value) {
    for (unsigned i = 0; i < v->count; i++) {
        if (v->data[i]==value) {
            return i;
        }
    }
    return VECTOR_NOT_FOUND;
}

// returns absolute position, and returns -1 in case the element is not contained
unsigned int_vector_find_sorted(int_vector* v, int value) {
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

bool int_vector_contains_sorted(int_vector* v, int value) {
    return int_vector_find_sorted(v, value) != VECTOR_NOT_FOUND;
}

bool int_vector_contains(int_vector* v, int value) {
    return int_vector_find(v, value) != VECTOR_NOT_FOUND;
}

void int_vector_add(int_vector* v, int value) {
    if (v->size == v->count) {
        int_vector_increase(v);
    }
    v->data[v->count] = value;
    v->count += 1;
}

void int_vector_add_sorted(int_vector* v, int value) {
    if (v->count == 0) {
        int_vector_add(v, value);
        return;
    }
    if (v->size == v->count) {
        int_vector_increase(v);
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
        int swap = v->data[i];
        v->data[i] = value;
        value = swap;
    }
    v->data[v->count] = value;
    v->count += 1;
}

int* int_vector_get_data(int_vector* v) {
    return v->data;
}

void int_vector_print(int_vector* v) {
    //    V4("int_vector (%u,%u) ", v->count, v->size);
    for (unsigned j = 0; j < v->count; j++) {
        printf(" %d", v->data[j]);
    }
    printf("\n");
}

bool int_vector_remove(int_vector* v, int value) {
    unsigned i;
    for (i = 0; i < v->count; i++) {
        if (v->data[i] == value) {
            break;
        }
    }
    if (i == v->count) {
        return false;
    }
    int_vector_remove_index(v, i);
    return true;
}

void int_vector_remove_index(int_vector* v, unsigned i) {
    v->count = v->count - 1; // yes, before the loop
    for (; i < v->count; i++) {
        v->data[i] = v->data[i+1];
    }
}

bool int_vector_is_strictly_sorted(int_vector* v) {
    for (unsigned i = 1; i < int_vector_count(v); i++) {
        if (int_vector_get(v, i-1) >= int_vector_get(v, i)) {
            return false;
        }
    }
    return true;
}

void int_vector_sort(int_vector* v, int (*cmp)(const void*, const void*)) {
    qsort(v->data, v->count, sizeof(int), cmp);
}

// assumes sortedness
void int_vector_remove_duplicates(int_vector* v) {
    if (int_vector_count(v) <= 1) {
        return;
    }
    unsigned j = 0;
    unsigned del = 0;
    for (unsigned i = 1; i < int_vector_count(v); i++) {
        assert(j<i);
        int x = int_vector_get(v, j);
        int y = int_vector_get(v, i);
        assert( y >= x ); // sorted
        if (x == y) {
            del++;
        } else {
            j++;
            int_vector_set(v, j, y);
        }
    }
    assert(int_vector_count(v) - del == j+1);
    int_vector_reduce_count(v, j+1);
    
    return;
}

int_vector* int_vector_copy(int_vector* old) {
    int_vector* new = int_vector_init();
    for (unsigned i = 0; i < int_vector_count(old); i++) {
        int_vector_add(new, int_vector_get(old, i));
    }
    return new;
}

bool int_vector_includes_sorted(int_vector* v1,int_vector* v2) {
    assert(int_vector_is_strictly_sorted(v1));
    assert(int_vector_is_strictly_sorted(v2));
    
    unsigned j = 0; // next_possible_v1_index
    for (unsigned i = 0; i < int_vector_count(v2); i++) {
        int x = int_vector_get(v2, i);
        
        while (true) {
            if ((int) int_vector_count(v2) - (int) i > (int) int_vector_count(v1) - (int) j) {
                return false;
            }
            assert(int_vector_count(v1) > j);
            if (int_vector_get(v1, j) < x) {
                j++;
            } else if (int_vector_get(v1, j) == x) {
                j++;
                break; // implicitly increases i
            } else {
                return false;
            }
        }
    }
    return true;
}

void int_vector_add_all(int_vector* this, int_vector* other) {
    for (unsigned i = 0; i < int_vector_count(other); i++) {
        int_vector_add(this, int_vector_get(other, i));
    }
}

void int_vector_add_all_sorted(int_vector* this, int_vector* other) {
    assert(int_vector_is_strictly_sorted(this));
    assert(int_vector_is_strictly_sorted(other));
    for (unsigned i = 0; i < int_vector_count(other); i++) {
        int val = int_vector_get(other, i);
        int_vector_add_sorted(this, val);
    }
    assert(int_vector_is_strictly_sorted(this));
}

void int_vector_shuffle(int_vector* v) {
    // creating a random permutation http://en.wikipedia.org/wiki/Fisher%E2%80%93Yates_shuffle
    for (unsigned i = 0; i < int_vector_count(v); i++) {
        unsigned j = i + ((unsigned) genrand_int31() % (int_vector_count(v)-i));
        int tmp = int_vector_get(v, j);
        int_vector_set(v, j, int_vector_get(v, i));
        int_vector_set(v, i, tmp);
    }
}
