//
//  skolem_conflict_analysis.c
//  cadet
//
//  Created by Markus Rabe on 27.05.17.
//  Copyright © 2017 UC Berkeley. All rights reserved.
//

#include "skolem.h"

#include <stdio.h>
#include <assert.h>

// INTERACTION WITH CONFLICT ANALYSIS
bool skolem_is_legal_dependence_for_conflict_analysis(void* s, unsigned var_id, unsigned depending_on) {
    Skolem* skolem = (Skolem*)s;
    return skolem_may_depend_on(skolem, var_id, depending_on);
}

int skolem_get_value_for_conflict_analysis(void* domain, Lit lit) {
    assert(lit != 0);
    Skolem* s = (Skolem*) domain;
    assert(s->conflict_var_id == lit_to_var(lit) || skolem_is_deterministic(s, lit_to_var(lit)));
    int satlit = skolem_get_satsolver_lit(s, lit);
    int opposite_satlit = skolem_get_satsolver_lit(s, - lit);
    assert(satlit != s->satlit_true || opposite_satlit != s->satlit_true);
    if (s->state == SKOLEM_STATE_CONSTANTS_CONLICT) {
        return skolem_get_constant_value(s, lit);
    } else {
        assert(satsolver_state(s->skolem) == SATSOLVER_SAT);
        int res = satsolver_deref(s->skolem, satlit);
        assert(res >= -1 && res <= 1);
        return res;
    }
}

bool skolem_is_relevant_clause(void* domain, Clause* c, Lit lit) {
    Skolem* s = (Skolem*) domain;
    unsigned var_id = lit_to_var(lit);
    if (skolem_get_constant_value(domain, lit) == 1) { // if the constant has the opposite value, the reason_for_constant cannot be it.
        return skolem_get_reason_for_constant(domain, var_id) == c->clause_idx;
    } else {
        Lit uc = skolem_get_unique_consequence(s, c);
        return uc && lit_to_var(uc) == var_id;
    }
}
