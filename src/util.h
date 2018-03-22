#ifndef UTIL_H
#define UTIL_H

#include <stdbool.h>
#include <stdio.h>

#define VERSION "v2.4"

static inline unsigned lit_to_var(int lit) { return lit < 0 ? (unsigned) -lit : (unsigned) lit; }

int hash6432shift(void* k);
int hash32shiftmult(int key);

int compare_pointers_natural_order(const void * a, const void * b);
int compare_integers_natural_order(const void * a, const void * b);
int compare_integers_abs(const void * a, const void * b);

double get_seconds();

const char* get_filename_ext(const char* filename);
FILE* open_possibly_zipped_file(const char* file_name);

#endif
