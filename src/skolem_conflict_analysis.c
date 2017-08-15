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

int skolem_get_value_for_conflict_analysis(void* domain, Lit lit, bool second_copy) {
    assert(second_copy == 0 || second_copy == 1);
    assert(lit != 0);
    Skolem* s = (Skolem*) domain;
    assert(s->conflict_var_id == lit_to_var(lit) || skolem_is_deterministic(s, lit_to_var(lit)));
    satlit sl = skolem_get_satlit(s, lit);
#ifdef DEBUG
    satlit opposite_sl = skolem_get_satlit(s, - lit);
    assert(sl.x[0] != f_get_true(s->f) || opposite_sl.x[0] != f_get_true(s->f));
    assert(sl.x[1] != f_get_true(s->f) || opposite_sl.x[1] != f_get_true(s->f));
#endif
    if (s->state == SKOLEM_STATE_CONSTANTS_CONLICT) {
        return skolem_get_constant_value(s, lit);
    } else {
        assert(f_result(s->f) == SATSOLVER_SATISFIABLE);
        int res = f_value(s->f, sl.x[second_copy]);
        assert(res >= -1 && res <= 1);
        return res;
    }
}

bool skolem_conflict_analysis_antecedent_satisfied(Skolem* s, Clause* c, Lit lit, bool second_copy) {
    assert(s->conflict_var_id == lit_to_var(lit) || skolem_get_value_for_conflict_analysis(s, lit, second_copy) == 1);
    assert(skolem_get_unique_consequence(s, c) == lit);
    assert(qcnf_contains_literal(c, lit));
    for (unsigned i = 0; i < c->size; i++) {
        Lit other = c->occs[i];
        assert(other != - lit);
        if (other == lit) {continue;}
        if (skolem_get_value_for_conflict_analysis(s, - other, second_copy) != 1) { // all others must be surely false, if one of them isn't then the clause cannot be used as reason. This allows us to use conflicted variables as reasons.
            return false;
        }
    }
    return true;
}

Clause* skolem_get_reason_for_conflict_analysis(void* domain, Lit lit, bool second_copy) {
    Skolem* s = (Skolem*) domain;
    assert(lit != 0);
    unsigned var_id = lit_to_var(lit);
    
    if (skolem_get_constant_value(domain, lit) == 1) { // if the constant has the opposite value, the reason_for_constant cannot be it.
        
        unsigned clause_id = skolem_get_reason_for_constant(domain, var_id);
        if (clause_id != INT_MAX) {
            Clause* c = vector_get(s->qcnf->clauses, clause_id);
            assert(c->clause_id == clause_id);
            return c;
        } else {
            return NULL;
        }
        
    } else {
        
        Var* v = var_vector_get(s->qcnf->vars, var_id);
        vector* occs = lit > 0 ? &v->pos_occs : &v->neg_occs;
        
        for (unsigned i = 0; i < vector_count(occs); i++) {
            Clause* c = vector_get(occs, i);
            if (skolem_get_unique_consequence(s, c) == lit && skolem_conflict_analysis_antecedent_satisfied(s, c, lit, second_copy)) {
                return c;
            }
        }
        return NULL; // no reason found
    }
}
