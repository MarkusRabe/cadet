//
//  function.c
//  cadet
//
//  Created by Markus Rabe on 30.05.17.
//  Copyright © 2017 UC Berkeley. All rights reserved.
//

#include "function.h"
#include "function_private.h"
#include "satsolver.h"
#include "util.h"
#include "debug.h"
#include "log.h"

#include <stdarg.h>

//// INITIALIZATION

Function* f_init(QCNF* qcnf) {
    Function* f = malloc(sizeof(Function));
    f->qcnf = qcnf;
    f->sat = satsolver_init();
    
    f->new_clause = vector_init();
    
    f->consistency_lits = int_vector_init();
    f->uncommitted_clause = int_vector_init();
    
    // Define the constant TRUE
    f->satlit_true = satsolver_inc_max_var(f->sat);
    assert(f->satlit_true == 1); // Not strictly required but I can sleep better with this assertion.
    satsolver_add(f->sat, f->satlit_true);
    satsolver_clause_finished(f->sat);
    
    return f;
}
void f_free(Function* f) {
    satsolver_free(f->sat);
    vector_free(f->new_clause);
    int_vector_free(f->consistency_lits);
    int_vector_free(f->uncommitted_clause);
    free(f);
}


//// SATSOLVER CONFIGURATION

void f_trace_for_profiling_initialize(Function* f) {
    satsolver_measure_all_calls(f->sat);
}
#ifdef SATSOLVER_TRACE
void f_trace_satsolver_commands(Function* f) {
    satsolver_trace_commands(f->sat);
}
#endif
double f_seconds_spent(Function* f) {
    return satsolver_seconds(f->sat);
}
void f_set_max_var(Function* f, int max_var) {
    satsolver_set_max_var(f->sat, max_var);
}
int f_get_max_var(Function* f) {
    return satsolver_get_max_var(f->sat);
}
void f_print_statistics(Function* f) {
    satsolver_print_statistics(f->sat);
}

//// VARIABLES

int f_fresh_var(Function* f) {
    return satsolver_inc_max_var(f->sat);
}
int f_get_true(Function* f) {
    return f->satlit_true;
}

satlit f_get_true_satlit(Function* f) {
    satlit sl;
    sl.x[0] = f->satlit_true;
    sl.x[1] = f->satlit_true;
    return sl;
}

//// DIRECT INTERACTION

void f_push(Function* f) {
    assert(vector_count(f->new_clause) == 0);
    satsolver_push(f->sat);
}
void f_pop(Function* f) {
    assert(vector_count(f->new_clause) == 0);
    satsolver_pop(f->sat);
}
void f_assume(Function* f, satlit lit) {
    assert(vector_count(f->new_clause) == 0);
    satsolver_assume(f->sat, lit.x[0]);
    satsolver_assume(f->sat, lit.x[1]);
}
sat_res f_sat(Function* f) {
    assert(vector_count(f->new_clause) == 0);
    sat_res res = satsolver_sat(f->sat);
    assert(res == SATSOLVER_SATISFIABLE || res == SATSOLVER_UNSATISFIABLE);
    return res;
}
int f_result(Function* f) {
    return satsolver_state(f->sat);
}
int f_value(Function* f, int lit) {
    return satsolver_deref(f->sat, lit);
}

void f_add_satlit(Function* f, satlit lit) {
    union satlit_void_ptr_union u;
    u.lit = lit;
    vector_add(f->new_clause, u.data);
}
void f_clause_finished(Function* f) {
    for (unsigned i = 0; i < vector_count(f->new_clause); i++) {
        union satlit_void_ptr_union u;
        u.data = vector_get(f->new_clause, i);
        satsolver_add(f->sat, u.lit.x[0]);
    }
    satsolver_clause_finished(f->sat);
    for (unsigned i = 0; i < vector_count(f->new_clause); i++) {
        union satlit_void_ptr_union u;
        u.data = vector_get(f->new_clause, i);
        satsolver_add(f->sat, u.lit.x[1]);
    }
    satsolver_clause_finished(f->sat);
    vector_reset(f->new_clause);
}
void f_clause_finished_for_context(Function* f, unsigned context) {
    for (unsigned i = 0; i < vector_count(f->new_clause); i++) {
        union satlit_void_ptr_union u;
        u.data = vector_get(f->new_clause, i);
        satsolver_add(f->sat, u.lit.x[0]);
    }
    satsolver_clause_finished_for_context(f->sat, context);
    for (unsigned i = 0; i < vector_count(f->new_clause); i++) {
        union satlit_void_ptr_union u;
        u.data = vector_get(f->new_clause, i);
        satsolver_add(f->sat, u.lit.x[1]);
    }
    satsolver_clause_finished_for_context(f->sat, context);
    vector_reset(f->new_clause);
}
