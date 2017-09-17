//
//  undo_stack.c
//  cadet
//
//  Created by Markus Rabe on 15/06/16.
//  Copyright © 2016 Saarland University. All rights reserved.
//

#include "undo_stack.h"

#include <assert.h>
#include <stdint.h>
#include "log.h"
#include "util.h"

Stack* stack_init(void (*undo)(void *parent, char, void*)) {
    Stack* s = malloc(sizeof(Stack));
    s->op_size = 64;
    s->obj_vector = malloc(sizeof(void*) * s->op_size);
    s->type_vector = malloc(sizeof(char) * s->op_size);
    s->op_count = 0;
    s->push_count = 0;
    s->undo = undo;
    return s;
}

void stack_free(Stack* s) {
    free(s->obj_vector);
    free(s->type_vector);
    free(s);
}

void stack_push(Stack* s) {
    stack_push_op(s, STACK_OP_MILESTONE, NULL);
    s->push_count += 1;
}

void stack_push_op(Stack* s, char type, void* obj) {
    assert(type != STACK_OP_MILESTONE || obj == NULL);
    if (s->push_count == 0 && type != STACK_OP_MILESTONE) { // don't store undo's before first push; we assume that these cannot be undone without effectively deleting the parent object
        return;
    }
    if (s->op_count == s->op_size) {
        s->op_size *= 2;
        void** new_obj_vector = malloc(sizeof(void*) * s->op_size);
        char* new_type_vector = malloc(sizeof(char) * s->op_size);
        for (size_t i = 0; i < s->op_count; i++) {
            new_obj_vector[i] = s->obj_vector[i];
            new_type_vector[i] = s->type_vector[i];
        }
        free(s->obj_vector);
        free(s->type_vector);
        s->obj_vector = new_obj_vector;
        s->type_vector = new_type_vector;
    }
    s->obj_vector[s->op_count] = obj;
    s->type_vector[s->op_count] = type;
    s->op_count += 1;
}

void stack_pop(Stack* s, void* parent) {
    assert(s->push_count > 0);
    // Don't know how to write the following loop head more elegantly. The op_count must be decreased by one, then op must be assigned the new operation, then we must check whether the operation happened to be a milestone.
    size_t i = 0;
    while (s->type_vector[--s->op_count] != STACK_OP_MILESTONE) {
        assert(s->op_count > 0);
        (s->undo)(parent, s->type_vector[s->op_count], s->obj_vector[s->op_count]);
        i++;
    }
    V4("Popped %zu items for milestone %d\n", i, s->push_count);
    s->push_count -= 1;
}

//void stack_print_debug(Stack* s) {
//    NOT_IMPLEMENTED();
//}

