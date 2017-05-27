//
//  function.h
//  cadet
//
//  Created by Markus Rabe on 22.05.17.
//  Copyright © 2017 UC Berkeley. All rights reserved.
//

#ifndef function_h
#define function_h

#include "options.h"
#include "satsolver.h"
#include "undo_stack.h"

#include <stdio.h>

struct Function;
typedef struct Function Function;

struct Function {
    Options* options;
    SATSolver* sat;
    Stack* stack; // for backtracking
};

Function* function_init(Options* options);
void function_free(Function* f);

// Push and pop are for external use.
void function_push(Function*);
void function_pop(Function*);

// PRINTING
void function_print_statistics(Function*);
void function_print_debug_info(Function*);

// PRIVATE
typedef enum {
    Function_OP_ASSIGN_DECISION_VAL,
    Function_OP_DECISION,
} Function_OPERATION;
void function_undo(void* parent, char type, void* obj);


#endif /* function_h */
