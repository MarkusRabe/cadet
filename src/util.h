#ifndef UTIL_H
#define UTIL_H

#include <stdbool.h>
#include <stdio.h>
#include <assert.h>

#define VERSION "v2.5"

static inline unsigned lit_to_var(int lit) {assert(lit != 0); return lit < 0 ? (unsigned) -lit : (unsigned) lit; } 

int hash6432shift(void* k) __attribute__((no_sanitize("undefined")));
int hash32shiftmult(int key) __attribute__((no_sanitize("undefined")));

int compare_pointers_natural_order(const void * a, const void * b);
int compare_integers_natural_order(const void * a, const void * b);
int compare_integers_abs(const void * a, const void * b);

double get_seconds();

const char* get_filename_ext(const char* filename);
FILE* open_possibly_zipped_file(const char* file_name);
void close_possibly_zipped_file(const char* file_name, FILE* file);

char* cautious_readline(char * __restrict, int, FILE *);
unsigned discrete_logarithm(unsigned x);

#endif
