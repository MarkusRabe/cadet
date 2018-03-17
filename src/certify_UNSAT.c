//
//  certify_SAT.c
//  cadet
//
//  Created by Markus Rabe on 16.03.18.
//  Copyright © 2018 UC Berkeley. All rights reserved.
//

#include "certify.h"
#include "log.h"

void c2_print_qdimacs_output(int_vector* refuting_assignment) {
    LOG_PRINTF("V"); // using printf, since everything else will otherwise be prefixed with a "c " when log_qdimacs_compliant is activated
    for (unsigned i = 0; i < int_vector_count(refuting_assignment); i++) {
        LOG_PRINTF(" %d", int_vector_get(refuting_assignment, i));
    }
    LOG_PRINTF("\n");
}

bool cert_check_UNSAT(C2* c2) {
    SATSolver* checker = satsolver_init();
    satsolver_set_max_var(checker, (int) var_vector_count(c2->qcnf->vars));
    
    for (unsigned i = 0; i < vector_count(c2->qcnf->all_clauses); i++) {
        Clause* c = vector_get(c2->qcnf->all_clauses, i);
        if (c->original) {
            for (unsigned j = 0; j < c->size; j++) {
                satsolver_add(checker, c->occs[j]);
            }
            satsolver_clause_finished(checker);
        }
    }
    int_vector* refuting_assignment = c2_refuting_assignment(c2);
    for (unsigned i = 0; i < int_vector_count(refuting_assignment); i++) {
        satsolver_assume(checker, int_vector_get(refuting_assignment, i));
    }
    sat_res res = satsolver_sat(checker);
    satsolver_free(checker);
    return res == SATSOLVER_UNSAT;
}
