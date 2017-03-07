//
//  set.c
//  cadet
//
//  Created by Markus Rabe on 19/06/16.
//  Copyright © 2016 Saarland University. All rights reserved.
//

#include "set.h"
#include "log.h"
#include "util.h"

#include <stdio.h>
#include <assert.h>


#define INITIAL_SET_SIZE 8

// From https://gist.github.com/badboy/6267743
//int hash32shiftmult(int key) {
//    int c2 = 0x27d4eb2d; // a prime or an odd constant
//    key = (key ^ 61) ^ (key >> 16);
//    key = key + (key << 3);
//    key = key ^ (key >> 4);
//    key = key * c2;
//    key = key ^ (key >> 15);
//    return key;
//}

//long hash64shift(void* k) {
//    assert(sizeof(long) == 4);
//    assert(sizeof(long long) == 8);
//    assert(sizeof(void*) == 8);
//    long long key = (long long) k;
//    key = (~key) + (key << 21); // key = (key << 21) - key - 1;
//    key = key ^ (key >> 24);
//    key = (key + (key << 3)) + (key << 8); // key * 265
//    key = key ^ (key >> 14);
//    key = (key + (key << 2)) + (key << 4); // key * 21
//    key = key ^ (key >> 28);
//    key = key + (key << 31);
//    return key;
//}


int set_hash_function(void* key, size_t size) {
    return abs(hash6432shift(key)) % (int) size;
}

set* set_init() {
    return set_init_size(INITIAL_SET_SIZE);
}

set* set_init_size(size_t size) {
    set* container = malloc(sizeof(set));
    container->data = calloc(sizeof(set_entry*), size);
    container->count = 0;
    container->size = size;
    return container;
}

set_entry* set_get_entry(set* container, void* key) {
    int hash = set_hash_function(key, container->size);
    assert(hash >= 0 && hash < (int) container->size);
    
    set_entry* entry = container->data[hash];
    while (entry != NULL && entry->key != key) {
        entry = entry->next;
    }
    return entry;
}

bool set_contains(set* container, void* key) {
    return set_get_entry(container, key) != NULL;
}

void set_add(set* container, void* key) {
    assert(!set_contains(container, key));
    int hash = set_hash_function(key, container->size);
    assert(hash >= 0 && hash < (int) container->size);
    
    set_entry* new_entry = malloc(sizeof(set_entry));
    new_entry->key = key;
    new_entry->next = container->data[hash];
    container->data[hash] = new_entry;
    
    container->count++;
    
    if (container->count > container->size + container->size / 2) {
        set_resize(container, 2 * container->size);
    }
}

void set_resize(set* container, size_t new_size) {
//    V4("Resizing container to size %zu\n", new_size);
    size_t old_size = container->size;
    set_entry** old_data = container->data;
    
    container->size = new_size;
    container->data = calloc(sizeof(set_entry*), new_size);
    
    for (size_t i = 0; i < old_size; i++) {
        set_entry* entry = old_data[i];
        while (entry != NULL) {
            set_entry* next = entry->next;
            int new_hash = set_hash_function(entry->key, container->size);
            assert(new_hash >= 0 && new_hash < (int) container->size);
            
            entry->next = container->data[new_hash];
            container->data[new_hash] = entry;
            
            entry = next;
        }
    }
    
    free(old_data);
}

void set_remove(set* container, void* key) {
    int hash = set_hash_function(key, container->size);
    assert(hash >= 0 && hash < (int) container->size);
    
    set_entry* entry = container->data[hash];
    set_entry* prev = NULL;
    while (entry != NULL && entry->key != key) {
        prev = entry;
        entry = entry->next;
    }
    if (entry == NULL) {
        V4("Warning: trying to remove non-existent set element.\n");
        return;
    }
    container->count--;
    if (prev == NULL) {
        container->data[hash] = entry->next;
    } else {
        prev->next = entry->next;
    }
    free(entry);
}

void set_reset(set* container) {
    if (set_count(container) == 0) {
        return;
    }
    for (size_t i = 0; i < container->size; i++) {
        set_entry* next_e;
        for (set_entry* e = container->data[i]; e != NULL; e = next_e) {
            next_e = e->next;
            free(e);
        }
        container->data[i] = 0;
    }
    container->count = 0;
}

void set_free(set* container) {
    set_reset(container);
    free(container->data);
    free(container);
}

size_t set_count(set* container) {
    return container->count;
}
