
#include "map.h"
#include "log.h"
#include "util.h"

#include <stdio.h>
#include <assert.h>


#define INITIAL_MAP_SIZE 10

int map_hash_function(int key, size_t size) {
    return hash32shiftmult(key) % (int) size;
}

map* map_init() {
    return map_init_size(INITIAL_MAP_SIZE);
}

map* map_init_size(size_t size) {
    map* container = malloc(sizeof(map));
    container->data = calloc(sizeof(map_entry*), size);
    container->count = 0;
    container->size = size;
    return container;
}

map_entry* map_get_entry(map* container, int key) {
    int hash = map_hash_function(key, container->size);
    assert(hash >= 0 && hash < (int) container->size);
    
    map_entry* entry = container->data[hash];
    while (entry != NULL && entry->key != key) {
        entry = entry->next;
    }
    return entry;
}

bool map_contains(map* container, int key) {
    return map_get_entry(container, key) != NULL;
}

void* map_get(map* container, int key) {
    map_entry* entry = map_get_entry(container, key);
    assert(entry != NULL);
    assert(entry->key == key);
    return entry->data;
}

// Same as map_add, but works only if the element is already in the map
void map_update(map* container, int key, void* data) {
    map_entry* entry = map_get_entry(container, key);
    assert(entry != NULL);
    entry->data = data;
}

void map_add(map* container, int key, void* data) {
    assert(!map_contains(container, key));
    int hash = map_hash_function(key, container->size);
    assert(hash >= 0 && hash < (int) container->size);
    
    map_entry* new_entry = malloc(sizeof(map_entry));
    new_entry->key = key;
    new_entry->data = data;
    new_entry->next = container->data[hash];
    container->data[hash] = new_entry;
    
    container->count++;
    
    if (container->count > container->size + container->size / 2) {
        map_resize(container, 2 * container->size);
    }
}

void map_resize(map* container, size_t new_size) {
//    V4("Resizing container to size %zu\n", new_size);
    size_t old_size = container->size;
    map_entry** old_data = container->data;
    
    container->size = new_size;
    container->data = calloc(sizeof(map_entry*), new_size);
    
    for (size_t i = 0; i < old_size; i++) {
        map_entry* entry = old_data[i];
        while (entry != NULL) {
            map_entry* next = entry->next;
            int new_hash = map_hash_function(entry->key, container->size);
            assert(new_hash >= 0 && new_hash < (int) container->size);
            
            entry->next = container->data[new_hash];
            container->data[new_hash] = entry;
            
            entry = next;
        }
    }
    
    free(old_data);
}

void map_remove(map* container, int key) {
    int hash = map_hash_function(key, container->size);
    assert(hash >= 0 && hash < (int) container->size);
    
    map_entry* entry = container->data[hash];
    map_entry* prev = NULL;
    while (entry != NULL && entry->key != key) {
        prev = entry;
        entry = entry->next;
    }
    if (entry == NULL) {
        return;
    }
    
    if (prev == NULL) {
        container->data[hash] = entry->next;
    } else {
        prev->next = entry->next;
    }
    
    free(entry);
}

void map_reset(map* container) {
    for (size_t i = 0; i < container->size; i++) {
        map_entry* next_e;
        for (map_entry* e = container->data[i]; e != NULL; e = next_e) {
            next_e = e->next;
            free(e);
        }
        container->data[i] = 0;
    }
    container->count = 0;
}

void map_free(map* container) {
    map_reset(container);
    free(container->data);
    free(container);
}

size_t map_count(map* container) {
    return container->count;
}
