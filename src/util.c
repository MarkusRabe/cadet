
#include "util.h"
#include "log.h"

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

const char* get_filename_ext(const char* filename) {
    const char* dot = strrchr(filename, '.');
    if(!dot || dot == filename) return "";
    return dot + 1;
}

FILE* open_possibly_zipped_file(const char* file_name) {
    FILE* file = NULL;
    const char* ext = get_filename_ext(file_name);
    size_t extlen = strlen(ext);
    V4("Detected file name extension %s\n", ext);
    if ( (extlen == 2 && strcmp("gz", ext) == 0) || (extlen == 4 && strcmp("gzip", ext) == 0) ) {
#ifdef __APPLE__
        char* unzip_tool_name = "gzcat ";
#endif
#ifdef __linux__
        char* unzip_tool_name = "zcat ";
#endif
#ifdef _WIN32
        abort(); // please use a proper operating system
#endif
        
        char* cmd = malloc(strlen(unzip_tool_name) + strlen(file_name) + 5);
        sprintf(cmd, "%s '%s'", unzip_tool_name, file_name);
        file = popen(cmd, "r");
        free(cmd);
        abortif(!file, "Cannot open gzipped file with zcat via popen. File may not exist.");
    } else {
        file = fopen(file_name, "r");
        abortif(!file, "Cannot open file \"%s\", does not exist?", file_name);
    }
    return file;
}

int strncmp(const char* s1, const char* s2, size_t n) {
    while ( n && *s1 && ( *s1 == *s2 ) ) {
        ++s1;
        ++s2;
        --n;
    }
    if (n == 0) {
        return 0;
    }
    else {
        return (*(unsigned char *)s1 - *(unsigned char *)s2);
    }
}
