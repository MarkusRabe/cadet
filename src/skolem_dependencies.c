//
//  skolem_dependencies.c
//  cadet
//
//  Created by Markus Rabe on 09/12/2016.
//  Copyright © 2016 UC Berkeley. All rights reserved.
//

#include "skolem_dependencies.h"
#include "skolem.h"
#include "log.h"

union Dependencies skolem_create_fresh_empty_dep(Skolem* s) {
    union Dependencies zero_dep;
    if (!qcnf_is_DQBF(s->qcnf)) {
        zero_dep.dependence_lvl = 0;
    } else {
        zero_dep.dependencies = int_vector_init();
    }
    return zero_dep;
}

//int skolem_compare_dependencies(Skolem* s, union Dependencies deps1, union Dependencies deps2) {
//    int cmp_val = 0;
//    if (qcnf_is_DQBF(s->qcnf)) {
//        // Returns 0 if they are not comparable;
//        assert(false); // check again upon first usage! In particular whether order of the arguments of int_vector_includes_sorted is correct.
//        assert(int_vector_is_strictly_sorted(deps1.dependencies));
//        assert(int_vector_is_strictly_sorted(deps2.dependencies));
//        cmp_val = (int) int_vector_count(deps1.dependencies) - (int) int_vector_count(deps2.dependencies);
//        if (cmp_val > 0) {
//            if (int_vector_includes_sorted(deps1.dependencies, deps2.dependencies)) {
//                cmp_val = 1;
//            } else {
//                cmp_val = 0; // incomparable
//            }
//        } else {
//            if (int_vector_includes_sorted(deps2.dependencies, deps1.dependencies)) {
//                cmp_val = 1;
//            } else {
//                cmp_val = 0;
//            }
//        }
//    } else {
//        cmp_val = (int) deps1.dependence_lvl - (int) deps2.dependence_lvl;
//    }
//    if (cmp_val > 0) {
//        cmp_val = 1;
//    } else if (cmp_val < 0) {
//        cmp_val = -1;
//    }
//    assert(cmp_val == -1 || cmp_val == 0 || cmp_val == 1);
//    return cmp_val;
//}

DEPENDENCY_COMPARISON skolem_compare_dependencies(Skolem* s, union Dependencies deps1, union Dependencies deps2) {
    if (qcnf_is_DQBF(s->qcnf)) {
        NOT_IMPLEMENTED(); // check again upon first usage! In particular whether order of the arguments of int_vector_includes_sorted is correct.
        assert(int_vector_is_strictly_sorted(deps1.dependencies));
        assert(int_vector_is_strictly_sorted(deps2.dependencies));
        int size_diff = (int) int_vector_count(deps1.dependencies) - (int) int_vector_count(deps2.dependencies);
        if (size_diff == 0) {
            if (int_vector_includes_sorted(deps1.dependencies, deps2.dependencies)) {
                assert(int_vector_includes_sorted(deps2.dependencies, deps1.dependencies));
                return DEPS_EQUAL;
            } else {
                return DEPS_INCOMPARABLE;
            }
        } else if (size_diff > 0) {
            if (int_vector_includes_sorted(deps1.dependencies, deps2.dependencies)) {
                return DEPS_LARGER;
            } else {
                return DEPS_INCOMPARABLE;
            }
        } else {
            if (int_vector_includes_sorted(deps2.dependencies, deps1.dependencies)) {
                return DEPS_SMALLER;
            } else {
                return DEPS_INCOMPARABLE;
            }
        }
    } else { // QBF
        int cmp_val = (int) deps1.dependence_lvl - (int) deps2.dependence_lvl;
        if (cmp_val > 0) {
            return DEPS_LARGER;
        } else if (cmp_val < 0) {
            return DEPS_SMALLER;
        } else {
            return DEPS_EQUAL;
        }
    }
}

void skolem_free_dependencies(Skolem* s, union Dependencies deps) {
    if (qcnf_is_DQBF(s->qcnf)) {
        abortif(deps.dependencies == s->empty_dependencies.dependencies, "Trying to free static empty_dependencies object in skolem domain object.");
        int_vector_free(deps.dependencies);
    }
}

union Dependencies skolem_copy_dependencies(Skolem* s, union Dependencies deps) {
    if (qcnf_is_DQBF(s->qcnf)) {
        union Dependencies res;
        res.dependencies = int_vector_copy(deps.dependencies);
        return res;
    } else {
        return deps;
    }
}

void skolem_update_dependencies_for_lit(Skolem* s, union Dependencies* aggregate_dependencies, Lit lit) {
    union Dependencies occ_deps = skolem_get_dependencies(s, lit_to_var(lit));
    if (qcnf_is_DQBF(s->qcnf)) {
        int_vector_add_all_sorted(aggregate_dependencies->dependencies, occ_deps.dependencies);
    } else {
        if (occ_deps.dependence_lvl > aggregate_dependencies->dependence_lvl) {
            aggregate_dependencies->dependence_lvl = occ_deps.dependence_lvl;
        }
    }
}

void skolem_compute_dependencies_for_occs(Skolem* s, union Dependencies* aggregate_dependencies, Lit lit) {
    vector* occs = qcnf_get_occs_of_lit(s->qcnf, lit);
    for (unsigned i = 0; i < vector_count(occs); i++) {
        Clause* c = vector_get(occs, i);
        Lit uc = skolem_get_unique_consequence(s, c);
        if (uc
            && lit_to_var(uc) == lit_to_var(lit)
            && ! skolem_has_illegal_dependence(s, c)) {
            for (int j = c->size - 1; j >= 0; j--) {
                if (c->occs[j] != uc) {
                    skolem_update_dependencies_for_lit(s, aggregate_dependencies, c->occs[j]);
                }
            }
        }
    }
}

union Dependencies skolem_compute_dependencies(Skolem* s, unsigned var_id) {
    union Dependencies deps;
    if (s->qcnf->problem_type == QCNF_PROPOSITIONAL) {
        deps.dependence_lvl = 0;
    } else {
        deps = skolem_create_fresh_empty_dep(s);
        skolem_compute_dependencies_for_occs(s, &deps,   (Lit) var_id);
        skolem_compute_dependencies_for_occs(s, &deps, - (Lit) var_id);
    }
    assert( ! qcnf_is_2QBF(s->qcnf) || deps.dependence_lvl <= 1);
    return deps;
}


// is 'var_id' allowed to depend on 'dep'?
bool skolem_is_legal_dependency(Skolem* s, unsigned var_id, union Dependencies dep) {
    Var* v = var_vector_get(s->qcnf->vars, var_id);
    if (qcnf_is_propositional(s->qcnf) || qcnf_is_2QBF(s->qcnf)) {
        assert(v->scope_id >= dep.dependence_lvl);
        return true;
    } else if (!qcnf_is_DQBF(s->qcnf)) { // QBF
        return v->scope_id >= dep.dependence_lvl;
    } else { // DQBF
        assert(qcnf_is_DQBF(s->qcnf));
        Scope* v_scope = vector_get(s->qcnf->scopes, v->scope_id);
        return int_vector_includes_sorted(v_scope->vars, dep.dependencies);
    }
}

bool skolem_may_depend_on(Skolem* s, unsigned var_id, unsigned depending_on_var_id) {
    assert(var_id != depending_on_var_id);
    skolem_var other_si = skolem_get_info(s, depending_on_var_id);
    assert(other_si.deterministic);
    return skolem_is_legal_dependency(s, var_id, other_si.dep);
}

bool skolem_has_illegal_dependence(Skolem* s, Clause* c) {
    if (qcnf_is_propositional(s->qcnf) || qcnf_is_2QBF(s->qcnf)) {
        return false;
    } else {
        assert(skolem_has_unique_consequence(s, c));
        Lit uc_lit = skolem_get_unique_consequence(s, c);
        for (int i = c->size - 1; i >= 0; i--) {
            if (c->occs[i] != uc_lit) {
                if (! skolem_may_depend_on(s, lit_to_var(uc_lit), lit_to_var(c->occs[i]))) {
                    return true;
                }
            }
        }
        return false;
    }
}

bool skolem_occs_contain_illegal_dependence(Skolem* s, Lit lit) {
    if (qcnf_is_propositional(s->qcnf) || qcnf_is_2QBF(s->qcnf) || qcnf_var_has_unique_maximal_dependency(s->qcnf,lit_to_var(lit))) {
        return false;
    }
    vector* occs = qcnf_get_occs_of_lit(s->qcnf, lit);
    for (unsigned i = 0; i < vector_count(occs); i++) {
        Clause* c = vector_get(occs, i);
        if (skolem_get_unique_consequence(s, c) == lit) {
            if (skolem_has_illegal_dependence(s, c)) {
                return true;
            }
        }
    }
    return false;
}


////////// INVARIANTS /////////////////

void skolem_validate_dependence_lvls(Skolem* s) {
    assert(s);
#ifdef CADET_RUNTIME_INVARIANT_CHECKS
        V1("Validating dependence levels\n");
        for (unsigned i = 0; i < var_vector_count(s->qcnf->vars); i++) {
            Var* v = var_vector_get(s->qcnf->vars, i);
            if (v->var_id != 0) {
                union Dependencies deps = skolem_get_dependencies(s, i);
                if (qcnf_is_DQBF(s->qcnf)) {
                    Scope* v_d = vector_get(s->qcnf->scopes, v->scope_id);
                    abortif(! int_vector_includes_sorted(v_d->vars, deps.dependencies), "Skolem validation failed.");
                } else {
                    abortif(deps.dependence_lvl >= vector_count(s->qcnf->scopes), "Skolem validation failed.");
                }
            }
        }
#endif
}
