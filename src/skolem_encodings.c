//
//  skolem_encodings.c
//  cadet
//
//  Created by Markus Rabe on 21.05.18.
//  Copyright © 2018 UC Berkeley. All rights reserved.
//

#include "skolem.h"
#include "log.h"

int skolem_encode_antecedent_satisfied(Skolem* s, Clause* c) {
    Lit uc = skolem_get_unique_consequence(s, c);
    assert(uc != 0);
    if (c->size == 1) {
        return s->satlit_true;
    }
    if (c->size == 2) {
        for (unsigned i = 0; i < c->size; i++) {
            Lit l = c->occs[i];
            if (l != uc) {
                return skolem_get_satsolver_lit(s, -l);
            }
        }
    }
    for (unsigned i = 0; i < c->size; i++) {
        Lit l = c->occs[i];
        if (l != uc && skolem_lit_satisfied(s, l)) {
            return - s->satlit_true;
        }
    }
        
    int antecedent_satisfied = satsolver_inc_max_var(s->skolem);
    
    for (unsigned i = 0; i < c->size; i++) {
        Lit l = c->occs[i];
        if (l != uc) {
            int other_satlit = skolem_get_satsolver_lit(s, l);
            satsolver_add(s->skolem, other_satlit);
        }
    }
    satsolver_add(s->skolem, antecedent_satisfied);
    satsolver_clause_finished(s->skolem);
    
    for (unsigned i = 0; i < c->size; i++) {
        Lit l = c->occs[i];
        if (l != uc) {
            int other_satlit = skolem_get_satsolver_lit(s, l);
            satsolver_add(s->skolem, - other_satlit);
            satsolver_add(s->skolem, - antecedent_satisfied);
            satsolver_clause_finished(s->skolem);
        }
    }
    
    return antecedent_satisfied;
}


int skolem_encode_antecedent_inependently_satisfied(Skolem* s, Clause* c) {
    int satisfied = skolem_encode_antecedent_satisfied(s, c);
    if (satisfied == - s->satlit_true) {
        return - s->satlit_true;
    }
    Lit uc = skolem_get_unique_consequence(s, c);
    
    // Check if any of the lit_depends are statically false; can avoid allocating a new satsolver var
    for (unsigned i = 0; i < c->size; i++) {
        Lit l = c->occs[i];
        unsigned v = lit_to_var(l);
        if (l != uc) {
            int lit_depends = skolem_get_depends_on_decision_satlit(s, v);
            if (lit_depends == s->satlit_true) {
                return - s->satlit_true;
            }
        }
    }
    
    int antecedent_sat_and_indep = satsolver_inc_max_var(s->skolem);
    
    // sat_and_indep := satisfied && -(lit_depends || ... || lit_depends)
    for (unsigned i = 0; i < c->size; i++) {
        Lit l = c->occs[i];
        unsigned v = lit_to_var(l);
        if (l != uc) {
            int lit_depends = skolem_get_depends_on_decision_satlit(s, v);
            satsolver_add(s->skolem, - lit_depends);
            satsolver_add(s->skolem, - antecedent_sat_and_indep);
            satsolver_clause_finished(s->skolem);
        }
    }
    
    satsolver_add(s->skolem, satisfied);
    satsolver_add(s->skolem, - antecedent_sat_and_indep);
    satsolver_clause_finished(s->skolem);
    
    for (unsigned i = 0; i < c->size; i++) {
        Lit l = c->occs[i];
        unsigned v = lit_to_var(l);
        if (l != uc) {
            int lit_depends = skolem_get_depends_on_decision_satlit(s, v);
            satsolver_add(s->skolem, lit_depends);
        }
    }
    satsolver_add(s->skolem, - satisfied);
    satsolver_add(s->skolem, antecedent_sat_and_indep);
    satsolver_clause_finished(s->skolem);


    V4("Antecedent of clause %u independently satsified satlit: %d\n", c->clause_idx, antecedent_sat_and_indep);
    return antecedent_sat_and_indep;
}

bool skolem_encode_lit_is_definitely_independent(Skolem* s, Lit lit) {
    if (skolem_is_decision_var(s, lit_to_var(lit))) {
        return false;
    }
    vector* occs = qcnf_get_occs_of_lit(s->qcnf, lit);
    for (unsigned i = 0; i < vector_count(occs); i++) {
        Clause* c = vector_get(occs, i);
        Lit uc = skolem_get_unique_consequence(s, c);
        if (uc == lit) {
            for (unsigned i = 0; i < c->size; i++) {
                Lit l = c->occs[i];
                unsigned v = lit_to_var(l);
                if (l != uc) {
                    int lit_depends = skolem_get_depends_on_decision_satlit(s, v);
                    if (lit_depends != - s->satlit_true) {
                        return false;
                    }
                }
            }
        }
    }
    return true;
}

int skolem_encode_lit_satisfied_and_depends_on_decisions(Skolem* s, Lit lit) {
    if (skolem_encode_lit_is_definitely_independent(s, lit)) {
        return - s->satlit_true;
    }
    
    int_vector* indep_lits = int_vector_init();
    vector* occs = qcnf_get_occs_of_lit(s->qcnf, lit);
    for (unsigned i = 0; i < vector_count(occs); i++) {
        Clause* c = vector_get(occs, i);
        if (skolem_get_unique_consequence(s, c) == lit) {
            int indep = skolem_encode_antecedent_inependently_satisfied(s, c);
            int_vector_add(indep_lits, indep);
        }
    }
    if (int_vector_count(indep_lits) == 0) {
        int_vector_free(indep_lits);
        return skolem_get_satsolver_lit(s, lit);
    }
    
    int satlit_is_set_and_depends = satsolver_inc_max_var(s->skolem);
    for (unsigned i = 0; i < int_vector_count(indep_lits); i++) {
        int indep = int_vector_get(indep_lits, i);
        satsolver_add(s->skolem, - indep);
        satsolver_add(s->skolem, - satlit_is_set_and_depends);
        satsolver_clause_finished(s->skolem);
    }
    satsolver_add(s->skolem, skolem_get_satsolver_lit(s, lit));
    satsolver_add(s->skolem, - satlit_is_set_and_depends);
    satsolver_clause_finished(s->skolem);
    
    int_vector_free(indep_lits);
    return satlit_is_set_and_depends;
}


void skolem_encode_depends_on_decision(Skolem* s, unsigned var_id) {
    if (!s->options->functional_synthesis || qcnf_is_universal(s->qcnf, var_id)) {
        return;
    }
    
    int depends_pos = skolem_encode_lit_satisfied_and_depends_on_decisions(s,   (Lit) var_id);
    int depends_neg = skolem_encode_lit_satisfied_and_depends_on_decisions(s, - (Lit) var_id);
    if (depends_neg == - s->satlit_true && depends_pos == - s->satlit_true) {
        return;
    }
    
    int old_depends_on_decision_satlit = skolem_get_depends_on_decision_satlit(s, var_id);
    int new_depends_on_decision_satlit = satsolver_inc_max_var(s->skolem);
    
    // new => old | pos | neg
    satsolver_add(s->skolem, depends_pos);
    satsolver_add(s->skolem, depends_neg);
    satsolver_add(s->skolem, old_depends_on_decision_satlit);
    satsolver_add(s->skolem, - new_depends_on_decision_satlit);
    satsolver_clause_finished(s->skolem);
    
    skolem_update_depends_on_decision_satlit(s, var_id, new_depends_on_decision_satlit);
    
}
