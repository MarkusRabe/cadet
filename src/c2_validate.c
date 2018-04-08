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

void c2_validate_var(Skolem* skolem, unsigned var_id) {
    skolem_var sv = skolem_get_info(skolem, var_id);
    abortif(sv.pure_neg && sv.pure_pos, "");
    abortif(sv.deterministic && sv.pos_lit == 0 && sv.neg_lit == 0, "");
    abortif(sv.deterministic && sv.pos_lit == 0 && sv.neg_lit == 0, "");
    
    int decision_val = skolem_get_decision_val(skolem, var_id);
    abortif(decision_val != 0 && (sv.pure_pos || sv.pure_neg), "");
    abortif(decision_val != 0 && !sv.deterministic, "");
    
    abortif(sv.reason_for_constant == INT_MAX && sv.dlvl_for_constant != 0, "");
    abortif(sv.reason_for_constant != INT_MAX && ! skolem_is_deterministic(skolem, var_id), "");
}

void c2_validate_unique_consequences(C2* c2) {
    for (unsigned i = 0; i < vector_count(c2->qcnf->all_clauses); i++) {
        Clause* c = vector_get(c2->qcnf->all_clauses, i);
        if (c->active && ! skolem_has_unique_consequence(c2->skolem, c) && ! skolem_clause_satisfied(c2->skolem, c)) {
            skolem_check_for_unique_consequence(c2->skolem, c);
            abortif(skolem_has_unique_consequence(c2->skolem, c), "Unique consequence messed up for clause %d.", c->clause_idx);
        }
        if (! c->active) {
            abortif(!c && i < int_vector_count(c2->skolem->unique_consequence)
                    && int_vector_get(c2->skolem->unique_consequence, i),
                    "Deleted clause still has a unique consequence.");
        }
    }
}


