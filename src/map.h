#ifndef MAP_H
#define MAP_H

#include <stdlib.h>
#include <stdbool.h>

struct map_entry;
typedef struct map_entry map_entry;

struct map_entry {
    int        key;
    void*      data;
    map_entry* next;
};

struct map {
    map_entry** data;
    size_t      size;
    size_t      count;
};

typedef struct map map;

map* map_init();
map* map_init_size(size_t size);
bool map_contains(map* container, int key);
void* map_get(map* container, int key);
void map_add(map* container, int key, void* data);
void map_update(map* container, int key, void* data);
void map_resize(map* container, size_t new_size);
void map_remove(map* container, int key);
void map_reset(map* container);
void map_free(map* container);
size_t map_count(map*);
#endif
