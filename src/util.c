
#include "util.h"

#include <stdlib.h>
#include <sys/time.h>
#include <string.h>
#include <assert.h>
#include <stdint.h>

int compare_integers_abs(const void * a, const void * b) {
    int x = abs(* ((int*) a));
    int y = abs(* ((int*) b));
    return x - y;
}

int compare_pointers_natural_order(const void * a, const void * b) {
    int64_t res = (int64_t) a - (int64_t) b;
    return res > 0 ? 1 : (res == 0 ? 0 : -1);
}

int compare_integers_natural_order(const void * a, const void * b) {
    int x = * ((int*) a);
    int y = * ((int*) b);
    return x - y;
}

double get_seconds() {
    struct timeval tv;
    gettimeofday(&tv, NULL);
    return (double) (tv.tv_usec) / 1000000 + (double) (tv.tv_sec);
}

const char* get_filename_ext(const char* filename) {
    const char* dot = strrchr(filename, '.');
    if(!dot || dot == filename) return "";
    return dot + 1;
}

int hash6432shift(void* k) {
    assert(sizeof(unsigned long long) == 8);
    assert(sizeof(void*) == 8);
    long long key = (long long) k;
    key = (~key) + (key << 18); // key = (key << 18) - key - 1;
    key = key ^ (key >> 31);
    key = key * 21; // key = (key + (key << 2)) + (key << 4);
    key = key ^ (key >> 11);
    key = key + (key << 6);
    key = key ^ (key >> 22);
    return (int) key;
}

// From https://gist.github.com/badboy/6267743
int hash32shiftmult(int key) {
    int c2 = 0x27d4eb2d; // a prime or an odd constant
    key = (key ^ 61) ^ (key >> 16);
    key = key + (key << 3);
    key = key ^ (key >> 4);
    key = key * c2;
    key = key ^ (key >> 15);
    return key;
}
