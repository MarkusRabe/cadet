//
//  function_encoding.c
//  cadet
//
//  Created by Markus Rabe on 01.06.17.
//  Copyright © 2017 UC Berkeley. All rights reserved.
//

#include "function_encoding.h"
#include "log.h"

#include <assert.h>

void f_add_clause(Skolem* s, Clause* c) {
    for (unsigned i = 0; i < c->size; i++) {
        int sat_lit = skolem_get_satlit(s, c->occs[i]);
        f_add(s->f, sat_lit);
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
 * bool add_guarded_illegal_dependencies is for use global conflict check, when illegal dependencies
 * need to be propagated (guarded by s->dependency_choice_sat_lit).
 *
 * Potential source of tricky bugs: when delaying conflict checks, all variables have to be defined
 * for BOTH SIDES, which is hardcoded in this function (because this propagation is typically being
 * used to encode potentially conflicted variables). Otherwise conflicted vars can decide to be not
 * conflicted.
 */
void f_propagate_partial_over_clause_for_lit(Skolem* s, Clause* c, Lit lit, bool define_both_sides) {
    assert(qcnf_contains_literal(c, lit) != 0);
    assert(!skolem_is_deterministic(s, lit_to_var(lit)));
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
    
    int satlit = f_fresh_var(s->f);
    union Dependencies dependencies = skolem_get_dependencies(s, lit_to_var(lit));
    assert(!qcnf_is_DQBF(s->qcnf) || int_vector_is_strictly_sorted(dependencies.dependencies));
    union Dependencies dependencies_copy = skolem_copy_dependencies(s, dependencies);
    for (unsigned i = 0; i < c->size; i++) {
        if (lit == c->occs[i]) {continue;}
        bool is_legal = skolem_may_depend_on(s, lit_to_var(lit), lit_to_var(c->occs[i]));
        if (is_legal) {
            assert(skolem_is_deterministic(s, lit_to_var(c->occs[i])));
            f_add(s->f, -satlit);
            f_add(s->f, skolem_get_satlit(s, lit)); // prevlit
            f_add(s->f, skolem_get_satlit(s, - c->occs[i]));
            f_clause_finished(s->f);
            
            if (is_legal) {
                union Dependencies occ_deps = skolem_get_dependencies(s, lit_to_var(c->occs[i]));
                if (!qcnf_is_DQBF(s->qcnf)) {
                    if (dependencies_copy.dependence_lvl < occ_deps.dependence_lvl) {
                        dependencies_copy.dependence_lvl = occ_deps.dependence_lvl;
                    }
                } else {
                    int_vector_add_all_sorted(dependencies_copy.dependencies, occ_deps.dependencies);
                }
            }
        }
    }
    if (qcnf_is_DQBF(s->qcnf)) {
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
        f_add(s->f, - skolem_get_satlit(s, lit)); // - prevlit
        f_add(s->f, satlit);
        f_clause_finished(s->f);
        
        // second clause
        for (unsigned i = 0; i < c->size; i++) {
            if (lit == c->occs[i]) {continue;}
            bool is_legal = skolem_may_depend_on(s, lit_to_var(lit), lit_to_var(c->occs[i]));
            if (is_legal) {
                assert(skolem_is_deterministic(s, lit_to_var(c->occs[i])));
                f_add(s->f, skolem_get_satlit(s, c->occs[i]));
            }
        }
        f_add(s->f, satlit);
        f_clause_finished(s->f);
    }
    
    skolem_update_satlit(s, lit, satlit);
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
    if (lit > 0) {
        abortif(sv->pos_lit != -1, "asdf neg");
    } else {
        abortif(sv->neg_lit != -1, "asdf neg");
    }
#endif
//    if (! define_both_sides) {
//        skolem_update_satlit(s, lit, f_fresh_var(s->f)); // must be done before the two next calls to make 'satlit' available in the
//    }
    
    vector* lit_occs = qcnf_get_occs_of_lit(s->qcnf, lit);
    bool case_exists = false;
    for (unsigned i = 0; i < vector_count(lit_occs); i++) {
        Clause* c = vector_get(lit_occs, i);
        if (skolem_get_unique_consequence(s, c) == lit && ! skolem_clause_satisfied(s, c) && ! skolem_has_illegal_dependence(s, c)) {
            case_exists = true;
//            if (define_both_sides) {
                f_propagate_partial_over_clause_for_lit(s, c, lit, define_both_sides);
//            } else {
//                f_add_clause(s, c);
//            }
        }
    }
    
    return case_exists;
}
