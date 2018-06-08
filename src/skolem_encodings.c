//
//  skolem_encodings.c
//  cadet
//
//  Created by Markus Rabe on 21.05.18.
//  Copyright © 2018 UC Berkeley. All rights reserved.
//

#include "skolem.h"
#include "log.h"

// Returns a satlit that can only be true if the uc is fired and depends on a decision
int skolem_encode_uc_depends_on_decision(Skolem* s, Clause* c) {
    Lit uc = skolem_get_unique_consequence(s, c);
    assert(uc != 0);
    if (skolem_clause_satisfied(s, c)) {
        return - s->satlit_true;
    }
    int satlit = satsolver_inc_max_var(s->skolem);
    
    for (unsigned i = 0; i < c->size; i++) {
        Lit l = c->occs[i];
        if (l != uc) {
            int other_satlit = skolem_get_satsolver_lit(s, l);
            satsolver_add(s->skolem, - other_satlit);
            satsolver_add(s->skolem, - satlit);
            satsolver_clause_finished(s->skolem);
        }
    }
    
    for (unsigned i = 0; i < c->size; i++) {
        Lit l = c->occs[i];
        unsigned v = lit_to_var(l);
        if (l != uc) {
            int other_depends_satlit = skolem_get_depends_on_decision_satlit(s, v);
            satsolver_add(s->skolem, other_depends_satlit);
        }
    }
    satsolver_add(s->skolem, - satlit);
    satsolver_clause_finished(s->skolem);

    return satlit;
}


static int_vector* skolem_encode_depends_helper(Skolem *s, Lit lit) {
    vector* occs = qcnf_get_occs_of_lit(s->qcnf, lit);
    int_vector* clause_depends_literals = int_vector_init();
    for (unsigned i = 0; i < vector_count(occs); i++) {
        Clause* c = vector_get(occs, i);
        if (skolem_get_unique_consequence(s, c) == lit) {
            int uc_depends = skolem_encode_uc_depends_on_decision(s, c);
            int_vector_add(clause_depends_literals, uc_depends);
            V4("Clause %u gets depends lit %d\n", c->clause_idx, uc_depends);
        }
    }
    return clause_depends_literals;
}


void skolem_encode_depends_on_decision(Skolem* s, unsigned var_id) {
    if (!s->options->functional_synthesis) {
        return;
    }
    
    int_vector* cd_lits1 = skolem_encode_depends_helper(s,   (Lit) var_id);
    int_vector* cd_lits2 = skolem_encode_depends_helper(s, - (Lit) var_id);
    satsolver_add_all(s->skolem, cd_lits1); // adding them now since previous call contains satsolver clauses.
    satsolver_add_all(s->skolem, cd_lits2);
    int_vector_free(cd_lits1);
    int_vector_free(cd_lits2);
    
    int old_depends_on_decision_satlit = skolem_get_depends_on_decision_satlit(s, var_id);
    if (old_depends_on_decision_satlit != - s->satlit_true) {
        satsolver_add(s->skolem, old_depends_on_decision_satlit);
    }
    
    int new_depends_on_decision_satlit = satsolver_inc_max_var(s->skolem);
    satsolver_add(s->skolem, - new_depends_on_decision_satlit);
    satsolver_clause_finished(s->skolem);
    
    skolem_update_depends_on_decision_satlit(s, var_id, new_depends_on_decision_satlit);
}
