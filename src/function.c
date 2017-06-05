//
//  function.c
//  cadet
//
//  Created by Markus Rabe on 30.05.17.
//  Copyright © 2017 UC Berkeley. All rights reserved.
//

#include "function.h"
#include "satsolver.h"
#include "util.h"
#include "debug.h"
#include "log.h"

#include <stdarg.h>


struct Function {
    QCNF* qcnf;
    SATSolver* sat;
    
    // Helper variables in the SAT solver
    int_vector* consistency_lits; // satlits representing consistency for up to level x
    
    int_vector* uncommitted_clause;
};
Function* f_init(QCNF* qcnf) {
    Function* f = malloc(sizeof(Function));
    f->qcnf = qcnf;
    
    f->sat = satsolver_init();
    
    f->consistency_lits = int_vector_init();
    f->uncommitted_clause = int_vector_init();
    return f;
}
void f_free(Function* f) {
    satsolver_free(f->sat);
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


//// INTERACTION

void f_push(Function* f) {
    satsolver_push(f->sat);
}
void f_pop(Function* f) {
    satsolver_pop(f->sat);
}

void f_add(Function* f, int lit) {
    satsolver_add(f->sat, lit);
}
void f_clause_finished(Function* f) {
    satsolver_clause_finished(f->sat);
}
void f_clause_finished_for_context(Function* f, unsigned context) {
    satsolver_clause_finished_for_context(f->sat, context);
}

void f_assume(Function* f, int lit) {
    satsolver_assume(f->sat, lit);
}
sat_res f_sat(Function* f) {
    sat_res res = satsolver_sat(f->sat);
    assert(res == SATSOLVER_SATISFIABLE || res == SATSOLVER_UNSATISFIABLE);
    return res;
}
int f_result(Function* f) {
    return satsolver_state(f->sat);
}
int f_value(Function* f, int lit){
    return satsolver_deref(f->sat, lit);
}

void f_add_satlit_clause(Function* f, const int_vector* clause) {
    for (unsigned i = 0; i < int_vector_count(clause); i++) {
        f_add(f, int_vector_get(clause, i));
    }
    f_clause_finished(f);
}

void f_add_AND(Function* f, int res, int input1, int input2) {
    f_add(f, res);
    f_add(f, - input1);
    f_add(f, - input2);
    f_clause_finished(f);
    
    f_add(f, - res);
    f_add(f,   input1);
    f_clause_finished(f);
    
    f_add(f, - res);
    f_add(f,   input2);
    f_clause_finished(f);
}

void f_add_OR(Function* f, int res, int input1, int input2) {
    f_add_AND(f, - res, - input1, - input2);
}
