//
//  c2_simplify.c
//  cadet
//
//  Created by Markus Rabe on 02.10.17.
//  Copyright © 2017 UC Berkeley. All rights reserved.
//

#include "cadet2.h"
#include "log.h"

void c2_delete_learnt_clauses_greater_than(C2* c2, unsigned threshold) {
    unsigned kept = 0;
    unsigned deleted = 0;
    for (int i = (int) vector_count(c2->qcnf->clauses) - 1; i >= 0; i--) {
        Clause* c = vector_get(c2->qcnf->clauses, (unsigned) i);
        if (! c) {
            continue;
        }
        if (c->original) { // assumes original clauses are in the front of the clause vector :/
            break;
        }
        if (c->size > threshold && skolem_get_unique_consequence(c2->skolem, c) == 0 && c->PG == 0) {
            qcnf_delete_clause(c2->qcnf, c);
            deleted += 1;
        } else {
            kept += 1;
        }
    }
    V1("Kept %u; deleted %u clauses\n", kept, deleted);
}
