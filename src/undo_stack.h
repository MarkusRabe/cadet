//
//  undo_stack.h
//  cadet
//
//  Created by Markus Rabe on 15/06/16.
//  Copyright © 2016 Saarland University. All rights reserved.
//

#ifndef undo_stack_h
#define undo_stack_h

#include <stdio.h>

#define STACK_OP_MILESTONE -1

// undo stack
struct Stack;
typedef struct Stack Stack;

struct Stack {
    // Splitting vectors of objects and type to save some memory (~40%); both must have the same number of elements and same size.
    void** obj_vector;
    char*  type_vector;
    size_t op_size;
    size_t op_count;
    
    unsigned push_count; // number of milestones in the op_vector
    void (*undo)(void *parent, char, void*);
};

Stack* stack_init(void (*undo)(void *parent, char, void*));
void stack_free(Stack*);

void stack_push(Stack*);  // O(1)
void stack_pop(Stack*,void* parent); // O(size of stack)
void stack_push_op(Stack*, char, void*);

#endif /* undo_stack_h */
