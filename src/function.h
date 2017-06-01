//
//  function.h
//  cadet
//
//  Created by Markus Rabe on 30.05.17.
//  Copyright © 2017 UC Berkeley. All rights reserved.
//

#ifndef function_h
#define function_h

#include "int_vector.h"
#include "qcnf.h"

#include <stdio.h>
#include <stdbool.h>

struct Function;
typedef struct Function Function;

Function* f_init(QCNF*);
void f_free(Function* f);


// Configure and profile the sat solver
void f_trace_satsolver_commands(Function*);
void f_trace_for_profiling_initialize(Function*);
double f_seconds_spent(Function*); // return time spent in SAT solver
void f_set_max_var(Function*, int max_var);
int f_get_max_var(Function*);
void f_print_statistics(Function*);


// Variables
int f_fresh_var(Function*);


// Interaction
void f_push(Function*);
void f_pop(Function*);

void f_add(Function*, int lit);
void f_clause_finished(Function*);
void f_clause_finished_for_context(Function*, unsigned context);

void f_assume(Function*, int lit);
int f_sat(Function*);
int f_result(Function*); // returns the result of the last SAT call
int f_value(Function*, int lit); // returns the value of the lit. Must be in SAT state


//void f_add_clause(Function*, const int_vector*); // does not modify the int_vectorf
//void f_add_unary_clause(Function*, int, int);
//void f_add_binary_clause(Function*, int, int);
//void f_add_ternary_clause(Function*, int, int, int);
//
//void f_add_AND();
//void f_add_OR();




#endif /* function_h */
