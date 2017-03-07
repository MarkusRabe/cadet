//
//  set.h
//  cadet
//
//  Created by Markus Rabe on 19/06/16.
//  Copyright © 2016 Saarland University. All rights reserved.
//

// This is a version of the hash map that saves memory by not storing data.

#ifndef set_h
#define set_h

#include <stdlib.h>
#include <stdbool.h>

struct set_entry;
typedef struct set_entry set_entry;

struct set_entry {
    void*      key;
    set_entry* next;
};

struct set {
    set_entry** data;
    size_t      size;
    size_t      count;
};

typedef struct set set;

set* set_init();
set* set_init_size(size_t size);
bool set_contains(set* container, void* key);
void set_add(set* container, void* key);
void set_resize(set* container, size_t new_size);
void set_remove(set* container, void* key);
void set_reset(set* container);
void set_free(set* container);
size_t set_count(set*);

#endif /* set_h */
