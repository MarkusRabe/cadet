//
//  skolem_constants.c
//  cadet
//
//  Created by Markus Rabe on 12.07.17.
//  Copyright © 2017 UC Berkeley. All rights reserved.
//

#include "skolem_constants.h"

#include <assert.h>

// Approximation, not accurate. Functions may be constant true but we don't necessarily detect that.
bool skolem_lit_satisfied(Skolem* s, Lit lit) {
    skolem_var si = skolem_get_info(s, lit_to_var(lit));
    if (lit > 0) {
        assert(si.pos_lit.x[0] != f_get_true(s->f) || si.pos_lit.x[1] == f_get_true(s->f));
        return si.pos_lit.x[0] == f_get_true(s->f);
    } else {
        assert(si.neg_lit.x[0] != f_get_true(s->f) || si.neg_lit.x[1] == f_get_true(s->f));
        return si.neg_lit.x[0] == f_get_true(s->f);
    }
}

bool skolem_clause_satisfied(Skolem* s, Clause* c) {
    for (int i = c->size - 1; i >= 0; i--) {
        if (skolem_lit_satisfied(s, c->occs[i])) {
            return true;
        }
    }
    return false;
}


int skolem_get_constant_value(Skolem* s, Lit lit) {
    assert(lit != 0);
    skolem_var sv = skolem_get_info(s, lit_to_var(lit));
    int val = 0;
    assert(sv.pos_lit.x[0] != f_get_true(s->f) || sv.neg_lit.x[0] != f_get_true(s->f));
    if (sv.pos_lit.x[0] == f_get_true(s->f)) {
        val = 1;
    } else if (sv.neg_lit.x[0] == f_get_true(s->f)) {
        val = -1;
    }
    if (lit < 0) {
        val = -val;
    }
    assert(val == -1 || val == 0 || val == 1);
    return val;
}
