//
//  qipasir.c
//  cadet
//
//  Created by Markus Rabe on 07/03/2017.
//  Copyright © 2017 UC Berkeley. All rights reserved.
//

#include "qipasir.h"
#include "util.h"
#include "cadet2.h"
#include "log.h"
#include "var_vector.h"

#include <assert.h>

const char * qipasir_signature () {
    return "CADET" VERSION;
}

void * qipasir_init () {
    C2* c2 = c2_init(default_options());
    return c2;
}

void qipasir_release (void * solver) {
    c2_free(solver);
}

void qipasir_new_variable(void * solver, int lit, int quantifier) {
    assert(lit > 0);
    assert(quantifier >= 0);
    C2* c2 = (C2*) solver;
    qcnf_new_var(c2->qcnf, quantifier % 2, (unsigned) ((quantifier+1)/2), lit_to_var(lit));
    c2_new_variable(solver, lit_to_var(lit));
}

void qipasir_add (void * solver, int lit_or_zero) {
    assert(lit_or_zero > INT_MIN);
    assert(lit_or_zero <= INT_MAX);
    c2_add_lit(solver, lit_or_zero);
}

void qipasir_assume (void * solver, int lit) {
    V0("Not implemented");
    abort();
}

int qipasir_solve (void * solver) {
    cadet_res res = c2_sat(solver);
    switch (res) {
        case CADET_RESULT_SAT:
            return 10;
            break;
        
        case CADET_RESULT_UNSAT:
            return 20;
            break;
            
        case CADET_RESULT_UNKNOWN:
            return 0;
            break;
            
        default:
            V0("Unknown result code");
            abort();
    }
}

int qipasir_val (void * solver, int lit) {
    C2* c2 = (C2*) solver;
#ifdef DEBUG
    Var* v = var_vector_get(c2->qcnf->vars, lit_to_var(lit));
    assert(v->scope_id == 0 || v->scope_id == 1 && v->is_universal);
#endif
    return skolem_get_constant_value(c2->skolem, lit) * lit;
}

int qipasir_failed (void * solver, int lit) {
    V0("Not implemented");
    abort();
}

void qipasir_set_terminate (void * solver, void * state, int (*terminate)(void * state)) {
    V0("Not implemented");
    abort();
}
