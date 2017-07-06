//
//  c2_validate.c
//  cadet
//
//  Created by Markus Rabe on 25/12/2016.
//  Copyright © 2016 UC Berkeley. All rights reserved.
//

#include "c2_validate.h"
#include "log.h"
#include "skolem_var.h"

void c2_validate_var(C2* c2, unsigned var_id) {
    skolem_var sv = skolem_get_info(c2->skolem, var_id);
    abortif(sv.pure_neg && sv.pure_pos, "");
    abortif(sv.deterministic && sv.pos_lit == 0 && sv.neg_lit == 0, "");
    abortif(sv.deterministic && sv.pos_lit == 0 && sv.neg_lit == 0, "");
    
    int decision_val = c2_get_decision_val(c2, var_id);
    abortif(decision_val != 0 && (sv.pure_pos || sv.pure_neg), "");
    abortif(decision_val != 0 && !sv.deterministic, "");
    
    abortif(sv.reason_for_constant == INT_MAX && sv.dlvl_for_constant != 0, "");
    abortif(sv.reason_for_constant != INT_MAX && ! skolem_is_deterministic(c2->skolem, var_id), "");
    
    if (c2->qcnf->problem_type != QCNF_DQBF && sv.deterministic && skolem_get_constant_value(c2->skolem, (Lit) var_id) == 0) {
        abortif(skolem_get_dependencies(c2->skolem, var_id).dependence_lvl == qcnf_get_empty_scope(c2->skolem->qcnf), "");
    }
}

void c2_validate_unique_consequences(C2* c2) {
    for (unsigned i = 0; i < vector_count(c2->qcnf->clauses); i++) {
        Clause* c = vector_get(c2->qcnf->clauses, i);
        if (c && ! skolem_has_unique_consequence(c2->skolem, c) && ! skolem_clause_satisfied(c2->skolem, c)) {
            skolem_check_for_unique_consequence(c2->skolem, c);
            abortif(skolem_has_unique_consequence(c2->skolem, c), "Unique consequence messed up for clause %u.", c->clause_id);
        }
    }
}


