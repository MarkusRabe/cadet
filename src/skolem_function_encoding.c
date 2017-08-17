//
//  skolem_function_encoding.c
//  cadet
//
//  Created by Markus Rabe on 01.06.17.
//  Copyright © 2017 UC Berkeley. All rights reserved.
//

#include "skolem_function_encoding.h"
#include "function_private.h"
#include "skolem_var.h"
#include "log.h"

#include <assert.h>

void f_add_clause(Skolem* s, Clause* c) {
    for (unsigned i = 0; i < c->size; i++) {
        assert(skolem_is_deterministic(s, lit_to_var(c->occs[i])) || skolem_get_unique_consequence(s, c) == c->occs[i]);
        f_add_satlit(s->f, satlit_negate(skolem_get_satlit(s, - c->occs[i])) );
    }
    f_clause_finished(s->f);
}

void f_add_clauses(Skolem* s, unsigned var_id, vector* occs) {
    for (unsigned i = 0; i < vector_count(occs); i++) {
        Clause* c = vector_get(occs, i);
        Lit unique_consequence = skolem_get_unique_consequence(s, c);
        
        if (lit_to_var(unique_consequence) == var_id
            && ! skolem_has_illegal_dependence(s,c)
            && ! skolem_clause_satisfied(s, c)) {
            f_add_clause(s, c);
        }
    }
}

/* Partial function propagation rule
 *
 * Potential source of tricky bugs: when delaying conflict checks, all variables have to be defined
 * for BOTH SIDES, which is hardcoded in this function (because this propagation is typically being
 * used to encode potentially conflicted variables). Otherwise conflicted vars can decide to be not
 * conflicted.
 */
void f_propagate_partial_over_clause_for_lit(Skolem* s, Clause* c, Lit lit, bool define_both_sides) {
    assert(qcnf_contains_literal(c, lit) != 0);
    assert( skolem_get_unique_consequence(s, c) == 0 || skolem_get_unique_consequence(s, c) == lit );
    
    if (s->options->functional_synthesis) {
        define_both_sides = true;
    }
    
    // Example and transformation. Let clause be (x y z lit):
    //
    // newlit -> (prevlit || -x && -y && -z)
    // newlit -> (prevlit || -x) && (prevlit || -y) && (prevlit || -z)
    // -newlit || (prevlit || -x) && (prevlit || -y) && (prevlit || -z)
    // (-newlit || prevlit || -x) && (-newlit || prevlit || -y) && (-newlit || prevlit || -z)
    
    satlit fresh;
    fresh.x[0] = f_fresh_var(s->f);
    fresh.x[1] = f_fresh_var(s->f);
    union Dependencies dependencies = skolem_get_dependencies(s, lit_to_var(lit));
    assert(s->qcnf->problem_type < QCNF_DQBF || int_vector_is_strictly_sorted(dependencies.dependencies));
    union Dependencies dependencies_copy = skolem_copy_dependencies(s, dependencies);
    for (unsigned i = 0; i < c->size; i++) {
        if (lit == c->occs[i]) {continue;}
        
        assert(skolem_is_deterministic(s, lit_to_var(c->occs[i])));
        f_add_satlit(s->f, satlit_negate(fresh));
        f_add_satlit(s->f, skolem_get_satlit(s, lit)); // prevlit
        f_add_satlit(s->f, skolem_get_satlit(s, - c->occs[i]));
        f_clause_finished(s->f);
        
        bool is_legal = skolem_may_depend_on(s, lit_to_var(lit), lit_to_var(c->occs[i]));
        if (is_legal) {
            union Dependencies occ_deps = skolem_get_dependencies(s, lit_to_var(c->occs[i]));
            if (s->qcnf->problem_type < QCNF_DQBF) {
                if (dependencies_copy.dependence_lvl < occ_deps.dependence_lvl) {
                    dependencies_copy.dependence_lvl = occ_deps.dependence_lvl;
                }
            } else {
                int_vector_add_all_sorted(dependencies_copy.dependencies, occ_deps.dependencies);
            }
        }
    }
    if (s->qcnf->problem_type == QCNF_DQBF) {
        int_vector_sort(dependencies_copy.dependencies, compare_integers_natural_order);
#ifdef DEBUG
        Scope* d = vector_get(s->qcnf->scopes, lit_to_var(lit));
        assert(int_vector_includes_sorted(d->vars, dependencies_copy.dependencies));
#endif
    }
    
    if (define_both_sides) {
        // For the other direction we need the following two clauses:
        // (prevlit || -x && -y && -z) -> newlit
        // -prevlit && (x || y || z) || newlit
        // (-prevlit || newlit) && (x || y || z || newlit)
        
        // first clause
        f_add_satlit(s->f, satlit_negate(skolem_get_satlit(s, lit))); // - prevlit
        f_add_satlit(s->f, fresh);
        f_clause_finished(s->f);
        
        // second clause
        for (unsigned i = 0; i < c->size; i++) {
            if (lit == c->occs[i]) {continue;}
//            bool is_legal = skolem_may_depend_on(s, lit_to_var(lit), lit_to_var(c->occs[i]));
//            if (is_legal) {
            assert(skolem_is_deterministic(s, lit_to_var(c->occs[i])));
            f_add_satlit(s->f, skolem_get_satlit(s, c->occs[i]));
//            }
        }
        f_add_satlit(s->f, fresh);
        f_clause_finished(s->f);
    }
    
    skolem_update_satlit(s, lit, fresh);
    skolem_update_dependencies(s, lit_to_var(lit), dependencies_copy);
}

/* Extends the literal definition of lit by the clauses with unique consequence.
 *
 * Returns whether at least one case has been encoded
 */
bool f_encode_unique_antecedents_for_lits(Skolem* s, Lit lit, bool define_both_sides) {
    unsigned var_id = lit_to_var(lit);
    assert(var_id != 0);

#ifdef DEBUG
    skolem_var* sv = skolem_var_vector_get(s->infos, lit_to_var(lit));
    assert((lit > 0 ? sv->pos_lit.x[0] : sv->neg_lit.x[0]) == - f_get_true(s->f)); // not necessary, but currently given
    assert((lit > 0 ? sv->pos_lit.x[1] : sv->neg_lit.x[1]) == - f_get_true(s->f)); // not necessary, but currently given
#endif
    
    vector* lit_occs = qcnf_get_occs_of_lit(s->qcnf, lit);
    bool case_exists = false;
    for (unsigned i = 0; i < vector_count(lit_occs); i++) {
        Clause* c = vector_get(lit_occs, i);
        if (skolem_get_unique_consequence(s, c) == lit && ! skolem_clause_satisfied(s, c)) {
            case_exists = true;
            f_propagate_partial_over_clause_for_lit(s, c, lit, define_both_sides);
        }
    }
    
    return case_exists;
}

void f_encode_give_fresh_satlit(Skolem* s, unsigned var_id) {
    assert(skolem_get_satlit(s,   (Lit) var_id).x[0] == - f_get_true(s->f));
    assert(skolem_get_satlit(s, - (Lit) var_id).x[0] == - f_get_true(s->f));
    assert(skolem_get_satlit(s,   (Lit) var_id).x[1] == - f_get_true(s->f));
    assert(skolem_get_satlit(s, - (Lit) var_id).x[1] == - f_get_true(s->f));
    
    // First we give the variable a fresh satlit, to make available for the clause encoding
    satlit sl;
    sl.x[0] = f_fresh_var(s->f);
//    if (s->qcnf->problem_type > QCNF_2QBF) {
        sl.x[1] = f_fresh_var(s->f);
//    } else {
//        sl.x[1] = - f_get_true(s->f);
//    }
    
    skolem_update_satlit(s,   (Lit) var_id,               sl);
    skolem_update_satlit(s, - (Lit) var_id, satlit_negate(sl));
}

void f_add_satlit_clause(Function* f, const vector* clause) {
    for (unsigned i = 0; i < vector_count(clause); i++) {
        union satlit_void_ptr_union sl;
        sl.data = vector_get(clause, i);
        f_add_satlit(f, sl.lit);
    }
    f_clause_finished(f);
}

void f_add_lit_clause_for_context(Skolem* s, const int_vector* clause, unsigned context) {
    for (unsigned i = 0; i < int_vector_count(clause); i++) {
        satlit lit = skolem_get_satlit(s, int_vector_get(clause, i));
        f_add_satlit(s->f, lit);
    }
    f_clause_finished_for_context(s->f, context);
}

satlit f_add_AND(Function* f, satlit input1, satlit input2) {
    satlit res;
    res.x[0] = 0;
    res.x[1] = 0;
    
    if (input1.x[0] == - f->satlit_true || input2.x[0] == - f->satlit_true) {
        res.x[0] = - f->satlit_true;
    } else if (input1.x[0] == f->satlit_true) {
        res.x[0] = input2.x[0];
    } else if (input2.x[0] == f->satlit_true) {
        res.x[0] = input1.x[0];
    } else {
        res.x[0] = f_fresh_var(f);
    }
    
    if (input1.x[1] == - f->satlit_true || input2.x[1] == - f->satlit_true) {
        res.x[1] = - f->satlit_true;
    } else if (input1.x[1] == f->satlit_true) {
        res.x[1] = input2.x[1];
    } else if (input2.x[1] == f->satlit_true) {
        res.x[1] = input1.x[1];
    } else {
        res.x[1] = f_fresh_var(f);
    }
    
    assert(res.x[0] != 0);
    assert(res.x[1] != 0);
    
//    int res = 
    f_add_satlit(f, res);
    f_add_satlit(f, satlit_negate(input1));
    f_add_satlit(f, satlit_negate(input2));
    f_clause_finished(f);
    
    f_add_satlit(f, satlit_negate(res));
    f_add_satlit(f, input1);
    f_clause_finished(f);
    
    f_add_satlit(f, satlit_negate(res));
    f_add_satlit(f, input2);
    f_clause_finished(f);
    
    return res;
}

satlit f_add_OR(Function* f, satlit input1, satlit input2) {
    return satlit_negate(f_add_AND(f, satlit_negate(input1), satlit_negate(input2)));
}

void f_encode_conflictedness(Skolem* s, unsigned var_id) {
    satsolver_add(s->f->sat, skolem_get_satlit(s,   (Lit) var_id).x[0]);
    satsolver_clause_finished(s->f->sat);
    
    satsolver_add(s->f->sat, skolem_get_satlit(s, - (Lit) var_id).x[1]);
    satsolver_clause_finished(s->f->sat);
}

void f_encode_consistency(Skolem* s, unsigned var_id) {
    satlit slpos = skolem_get_satlit(s,   (Lit) var_id);
    satlit slneg = skolem_get_satlit(s, - (Lit) var_id);
    
    if (slpos.x[0] == slpos.x[1] && slneg.x[0] == slneg.x[1]) {
        return;
    }
    
    int consistency_literal = int_vector_get(s->f->consistency_literals, qcnf_get_scope(s->qcnf, var_id));
    
    // Positive satlits
    satsolver_add(s->f->sat, - consistency_literal);
    satsolver_add(s->f->sat,   slpos.x[0]);
    satsolver_add(s->f->sat, - slpos.x[1]);
    satsolver_clause_finished(s->f->sat);
    
    satsolver_add(s->f->sat, - consistency_literal);
    satsolver_add(s->f->sat, - slpos.x[0]);
    satsolver_add(s->f->sat,   slpos.x[1]);
    satsolver_clause_finished(s->f->sat);
    
    if (slneg.x[0] != - slpos.x[0]
        || slneg.x[1] != - slpos.x[1]) {
        // Negative satlits
        satsolver_add(s->f->sat, - consistency_literal);
        satsolver_add(s->f->sat,   slneg.x[0]);
        satsolver_add(s->f->sat, - slneg.x[1]);
        satsolver_clause_finished(s->f->sat);
        
        satsolver_add(s->f->sat, - consistency_literal);
        satsolver_add(s->f->sat, - slneg.x[0]);
        satsolver_add(s->f->sat,   slneg.x[1]);
        satsolver_clause_finished(s->f->sat);
    }
}
