#ifndef UTIL_H
#define UTIL_H

#include <stdbool.h>

#define SEED 0
#define VERSION "v2.2 QBFEVAL'17"

typedef enum {
    CADET_RESULT_SAT     = 10,
    CADET_RESULT_UNSAT   = 20,
    CADET_RESULT_UNKNOWN = 30
} cadet_res;

// initializes the array 'permutation' wit h a random permutation of the indices of the item_array, which is assumed to beterminated by a 0 entry. Returns the size of item_array (i.e. the incdex of the 0 entry). 
int random_permutation(int* item_array, int* permutation);

static inline unsigned lit_to_var(int lit) { return lit < 0 ? (unsigned) -lit : (unsigned) lit; }

int hash6432shift(void* k);
int hash32shiftmult(int key);

int compare_pointers_natural_order(const void * a, const void * b);
int compare_integers_natural_order(const void * a, const void * b);
int compare_integers_abs(const void * a, const void * b);

double get_seconds();

const char* get_filename_ext(const char* filename);

#endif
