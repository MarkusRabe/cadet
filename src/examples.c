//
//  examples.c
//  cadet
//
//  Created by Markus Rabe on 24/01/2017.
//  Copyright © 2017 UC Berkeley. All rights reserved.
//

#include "examples.h"
#include "log.h"

#include <assert.h>

Examples* examples_init(QCNF* qcnf, unsigned examples_max_num) {
    Examples* e = malloc(sizeof(Examples));
    e->qcnf = qcnf;
    e->example_max_num = examples_max_num;
    e->ex = vector_init();
    e->conflicted_pa = NULL;
    e->push_count = 0;
    
    e->create_random = statistics_init(10000);
    e->create_skolem = statistics_init(10000);
    return e;
}

void examples_free(Examples* e) {
    for (unsigned i = 0; i < vector_count(e->ex); i++) {
        partial_assignment_free(vector_get(e->ex, i));
    }
    free(e);
}

void examples_print_statistics(Examples* e) {
    V0("Examples:\n  Histogram for initialization with random assignments:\n");
    statistics_print(e->create_random);
    V0("  Histogram for initialization with skolem assignments:\n");
    statistics_print(e->create_skolem);
}

PartialAssignment* examples_create_new_pa(Examples* e) {
    assert( ! examples_is_conflicted(e));
    if (e->example_max_num > 0) {
        assert(vector_count(e->ex) <= e->example_max_num);
        PartialAssignment* pa = partial_assignment_init(e->qcnf);
        if (vector_count(e->ex) == e->example_max_num) {
            unsigned min_pa_idx = 0; // TODO: better heuristics
            PartialAssignment* min_pa = vector_get(e->ex, min_pa_idx);
            partial_assignment_free(min_pa);
            vector_set(e->ex, min_pa_idx, pa);
            return pa;
        } else {
            vector_add(e->ex, pa);
            return pa;
        }
    } else {
        return NULL;
    }
}

PartialAssignment* examples_add_assignment_from_skolem(Examples* e, Skolem* s) {
    V2("Propagating Skolem assignment\n");
    assert(satsolver_state(s->skolem) == SATSOLVER_RESULT_SAT);
    
    statistics_start_timer(e->create_skolem);
    
    PartialAssignment* pa = examples_create_new_pa(e);
    
    if (pa) {
        partial_assignment_propagate(pa);
        
        if (! partial_assignment_is_conflicted(pa)) {
            for (unsigned i = 1; i < var_vector_count(e->qcnf->vars); i++) {
                if (qcnf_var_exists(e->qcnf, i) && qcnf_is_universal(e->qcnf, i)) {
                    int val = skolem_get_value_for_conflict_analysis(s, (Lit) i);
                    if (val == 0) {
                        val = (rand() % 2) * 2 - 1;
                    }
                    assert(val == -1 || val == 1);
                    partial_assignment_assign_value(pa, val * (Lit) i);
                }
            }
            partial_assignment_propagate(pa);
        }
        
        if (partial_assignment_is_conflicted(pa)) {
            V1("Conflict from skolem example\n");
            e->conflicted_pa = pa;
        } else {
            for (unsigned i = 0; i < e->push_count; i++) {
                partial_assignment_push(pa);
            }
        }
    }
    
    statistics_stop_and_record_timer(e->create_skolem);
    
    return pa;
}

PartialAssignment* examples_add_random_assignment(Examples* e) {
    V2("Propagating random assignment\n");
    
    statistics_start_timer(e->create_random);
    
    PartialAssignment* pa = examples_create_new_pa(e);
    
    if (pa) {
        partial_assignment_propagate(pa);
        
        if (! partial_assignment_is_conflicted(pa)) {
            for (unsigned i = 1; i < var_vector_count(e->qcnf->vars); i++) {
                if (qcnf_var_exists(e->qcnf, i) && qcnf_is_universal(e->qcnf, i)) {
                    int val = (rand() % 2) * 2 - 1;
                    assert(val == -1 || val == 1);
                    partial_assignment_assign_value(pa, val * (Lit) i);
                }
            }
            partial_assignment_propagate(pa);
        }
        
        if (partial_assignment_is_conflicted(pa)) {
            V1("Conflict from random example\n");
            e->conflicted_pa = pa;
        } else {
            for (unsigned i = 0; i < e->push_count; i++) {
                partial_assignment_push(pa);
            }
        }
    }
    
    statistics_stop_and_record_timer(e->create_random);
    
    return pa;
}

bool examples_is_conflicted(Examples* e) {
    return examples_get_conflicted_assignment(e) != NULL;
}

PartialAssignment* examples_get_conflicted_assignment(Examples* e) {
#ifdef DEBUG
    bool is_actually_conflicted = false;
    for (unsigned i = 0; i < vector_count(e->ex); i++) {
        PartialAssignment* pa = vector_get(e->ex, i);
        if (partial_assignment_is_conflicted(pa)) {
            is_actually_conflicted = true;
            break;
        }
    }
    abortif(is_actually_conflicted == (e->conflicted_pa == NULL), "Examples domain is inconsistent about its state of conflictedness.");
#endif
    return e->conflicted_pa;
}

int examples_get_value_for_conflict_analysis(void* domain, Lit lit) {
    Examples* e = (Examples*) domain;
    return partial_assignment_get_value_for_conflict_analysis((void*) e->conflicted_pa, lit);
}

void examples_push(Examples* e) {
    e->push_count += 1;
    for (unsigned i = 0; i < vector_count(e->ex); i++) {
        PartialAssignment* pa = vector_get(e->ex, i);
        abortif(partial_assignment_is_conflicted(pa), "Cannot push for conflicted example.");
        partial_assignment_push(pa);
    }
}

void examples_pop(Examples* e) {
    e->push_count -= 1;
    e->conflicted_pa = NULL;
    for (unsigned i = 0; i < vector_count(e->ex); i++) {
        PartialAssignment* pa = vector_get(e->ex, i);
        partial_assignment_pop(pa);
        abortif(partial_assignment_is_conflicted(pa), "Example is still conflicted after pop.");
    }
}

void examples_decision(Examples* e, Lit decision_lit) {
    abortif(examples_is_conflicted(e), "Examples domain expected to be not conflicted.");
    for (unsigned i = 0; i < vector_count(e->ex); i++) {
        PartialAssignment* pa = vector_get(e->ex, i);
        if (partial_assignment_get_value_for_conflict_analysis(pa, decision_lit) == 0) {
            partial_assignment_assign_value(pa, decision_lit);
            partial_assignment_propagate(pa);
            if (partial_assignment_is_conflicted(pa)) {
                e->conflicted_pa = pa;
            }
        }
    }
}
