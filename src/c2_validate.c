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
}

void c2_validate_unique_consequences(C2* c2) {
    for (unsigned i = 0; i < vector_count(c2->qcnf->clauses); i++) {
        Clause* c = vector_get(c2->qcnf->clauses, i);
        if (c && ! skolem_has_unique_consequence(c2->skolem, c) && ! skolem_clause_satisfied(c2->skolem, c)) {
            skolem_check_for_unique_consequence(c2->skolem, c);
            abortif(skolem_has_unique_consequence(c2->skolem, c), "Unique consequence messed up for clause %d.", c->clause_id);
        }
    }
}
