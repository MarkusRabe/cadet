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
#include "skolem_var.h"
#include "util.h"

#include <stdbool.h>

struct Function;
typedef struct Function Function;

// for converting satlits into void* and vice versa
union satlit_void_ptr_union {
    void* data;
    satlit lit;
};

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
int f_get_true(Function*); // get the satlit corresponding to TRUE
satlit f_get_true_satlit(Function* f);

// Interaction
void f_push(Function*);
void f_pop(Function*);

sat_res f_sat(Function*);
sat_res f_sat_with_consistency(Function* f, unsigned scope_id);
sat_res f_result(Function*); // returns the result of the last SAT call
int f_value(Function*, int satlit); // returns the value of the satlit. Must be in SAT state.

void f_add_satlit(Function*, satlit lit);
void f_add_internal(Function*, int); // passes through to the satsolver; use with caution
void f_clause_finished_internal(Function*); // passes through to the satsolver; use with caution
void f_clause_finished(Function*);
void f_clause_finished_for_context(Function*, unsigned context);

int f_fresh_var(Function*);

void f_assume(Function*, satlit lit);

#endif /* function_h */
