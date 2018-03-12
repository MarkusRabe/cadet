//
//  examples.c
//  cadet
//
//  Created by Markus Rabe on 24/01/2017.
//  Copyright © 2017 UC Berkeley. All rights reserved.
//

#include "examples.h"
#include "log.h"
#include "mersenne_twister.h"

#include <assert.h>

typedef enum {
    EXAMPLES_OP_DECISION
} EXAMPLES_OP;

Examples* examples_init(QCNF* qcnf, unsigned examples_max_num) {
    Examples* e = malloc(sizeof(Examples));
    e->qcnf = qcnf;
    e->example_max_num = examples_max_num;
    e->ex = vector_init();
    e->conflicted_pa = NULL;
    e->state = EXAMPLES_STATE_READY;
    e->stack = stack_init(examples_undo);
    
    e->create_random = statistics_init(10000);
    e->create_skolem = statistics_init(10000);
    
    // search for unit clauses and clauses with unique consequence
    Clause_Iterator ci = qcnf_get_clause_iterator(e->qcnf); Clause* c = NULL;
    while ((c = qcnf_next_clause(&ci)) != NULL) {
        examples_new_clause(e, c);
    }
    
    return e;
}

void examples_free(Examples* e) {
    for (unsigned i = 0; i < vector_count(e->ex); i++) {
        partial_assignment_free(vector_get(e->ex, i));
    }
    free(e);
}
#pragma clang diagnostic push
#pragma clang diagnostic ignored "-Wunused-parameter"
void examples_undo(void* parent, char type, void* obj) {
    // yep we actually don't have to do anything. We use the stack only to redo decisions for new examples.
    
    //    Examples* e = (Examples*) parent;
    //    switch (type) {
    //        case EXAMPLES_OP_DECISION:
    //            break;
    //
    //        default:
    //            break;
    //    }
}
#pragma clang diagnostic pop

void take_pa_decision(Examples* e, PartialAssignment* pa, Lit decision_lit) {
    partial_assignment_assign_value(pa, decision_lit);
    partial_assignment_propagate(pa);
    if (partial_assignment_is_conflicted(pa)) {
        e->conflicted_pa = pa;
        e->state = EXAMPLES_STATE_PROPAGATION_CONFLICT;
    }
}

bool examples_is_decision_consistent_with_skolem_pa(Examples* e, Skolem* s, Lit decision_lit, PartialAssignment* pa) {
    if (partial_assignment_get_value_for_conflict_analysis(pa, decision_lit) == -1) {
        // OK, the decision var has to have the opposite value. Is that justified only based on the clauses with unique consequence?
        
        // Is any of the antecedents of the opposite lit satisfied? I.e. is this decision doomed to produce a conflict?
        vector* opposite_occs = qcnf_get_occs_of_lit(e->qcnf, - decision_lit);
        for (unsigned i = 0; i < vector_count(opposite_occs); i++) {
            Clause* c = vector_get(opposite_occs, i);
            if (skolem_get_unique_consequence(s, c) == - decision_lit && partial_assignment_is_antecedent_satisfied(pa, c, - decision_lit)) {
                return true;
            }
        }
        return false;
    } else {
        return true;
    }
}

bool examples_is_decision_consistent_with_skolem_for_pa(Examples* e, Skolem* s, Lit decision_lit, PartialAssignment* pa) {
    unsigned var_id =  lit_to_var(decision_lit);
    if (! examples_is_decision_consistent_with_skolem_pa(e, s, decision_lit, pa)) {
        Clause* c = partial_assignment_get_relevant_clause(pa, var_id);
        abortif(skolem_get_unique_consequence(s, c) != 0, "I thought this variable then must have been propagated by variables that are not yet deterministic.");
        
        partial_assignment_go_into_conflict_state(pa, c, var_id);
        e->conflicted_pa = pa;
        e->state = EXAMPLES_STATE_INCONSISTENT_DECISION_CONFLICT;
        partial_assignment_get_decision_lvl(pa, var_id);
        
        abortif(! partial_assignment_is_conflicted(pa), "Expected partial assignment domain to be conflicted");
        abortif(! examples_is_conflicted(e), "Expected example to be conflicted");
        return false;
    }
    return true;
}

bool examples_is_decision_consistent_with_skolem(Examples* e, Skolem* s, Lit decision_lit) {
    for (unsigned i = 0; i < vector_count(e->ex); i++) {
        PartialAssignment* pa = vector_get(e->ex, i);
        if ( ! examples_is_decision_consistent_with_skolem_for_pa(e,s,decision_lit,pa)) {
            assert(partial_assignment_is_conflicted(pa));
            return false;
        }
    }
    return true;
}

void examples_redo(Examples* e, Skolem* s, PartialAssignment* pa) {
    
    assert(e->stack->type_vector[0] == STACK_OP_MILESTONE);
    
    // return to dlvl 0
    for (unsigned i = 0; i < e->stack->push_count; i++) {
        partial_assignment_pop(pa);
    }
    assert(pa->stack->push_count == 0);
    
    if (partial_assignment_is_conflicted(pa)) {
        V3("Partial assigment is conflicted on dlvl 0. Will only catch up with push count.\n");
    }
    
    for (unsigned i = 0; i < e->stack->op_count; i++) {
        
        if (e->stack->type_vector[i] == STACK_OP_MILESTONE) {
            partial_assignment_push(pa);
        } else if (e->stack->type_vector[i] == EXAMPLES_OP_DECISION && ! partial_assignment_is_conflicted(pa)) {
            Lit decision_lit = (Lit) e->stack->obj_vector[i];
            if (examples_is_decision_consistent_with_skolem_for_pa(e, s, decision_lit, pa)) {
                if (partial_assignment_get_value_for_conflict_analysis(pa, decision_lit) == 0) {
                    take_pa_decision(e, pa, decision_lit);
                }
            } else {
                assert(partial_assignment_is_conflicted(pa));
                assert(examples_is_conflicted(e));
            }
            
            if (partial_assignment_is_conflicted(pa)) {
                V1("Conflict in skolem example %u/%u; caused  by decision replay redo %u of %u\n", vector_count(e->ex), vector_count(e->ex), pa->stack->push_count, e->stack->push_count);
                // return; // need to catch up with the right number of pushs, so continue pushing
            }
        }
    }
    assert(e->stack->push_count == pa->stack->push_count);
    if (partial_assignment_is_conflicted(pa)) {
        e->conflicted_pa = pa;
        e->state = EXAMPLES_STATE_PROPAGATION_CONFLICT;
    }
}

void examples_print_statistics(Examples* e) {
    V0("Examples:\n");
    V0("  Histogram for initialization with random assignments:\n");
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
    assert(satsolver_state(s->skolem) == SATSOLVER_SAT);
    assert( ! examples_is_conflicted(e));
    statistics_start_timer(e->create_skolem);
    
    PartialAssignment* pa = examples_create_new_pa(e);
    
    if (pa) {
        partial_assignment_propagate(pa);
        
        if (! partial_assignment_is_conflicted(pa)) {
            for (unsigned i = 1; i < var_vector_count(e->qcnf->vars); i++) {
                if (qcnf_var_exists(e->qcnf, i) && qcnf_is_universal(e->qcnf, i)) {
                    int val = skolem_get_value_for_conflict_analysis(s, (Lit) i);
                    if (val == 0) {
                        val = (genrand_int31() % 2) * 2 - 1;
                    }
                    assert(val == -1 || val == 1);
                    partial_assignment_assign_value(pa, val * (Lit) i);
                    V3("Assuming lit %d in PA\n", val * (Lit) i);
                }
            }
            partial_assignment_propagate(pa);
        }
        if (partial_assignment_is_conflicted(pa)) {
            e->conflicted_pa = pa;
            e->state = EXAMPLES_STATE_PROPAGATION_CONFLICT;
        } else {
            for (unsigned i = 0; i < e->stack->push_count; i++) {
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
                    int val = (genrand_int31() % 2) * 2 - 1;
                    assert(val == -1 || val == 1);
                    partial_assignment_assign_value(pa, val * (Lit) i);
                }
            }
            partial_assignment_propagate(pa);
        }
        if (partial_assignment_is_conflicted(pa)) {
            e->conflicted_pa = pa;
            e->state = EXAMPLES_STATE_PROPAGATION_CONFLICT;
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
    stack_push(e->stack);
    for (unsigned i = 0; i < vector_count(e->ex); i++) {
        PartialAssignment* pa = vector_get(e->ex, i);
        if (partial_assignment_is_conflicted(pa)) {LOG_WARNING("Cannot push for conflicted example.");}
        partial_assignment_push(pa);
        assert(e->stack->push_count == pa->stack->push_count);
    }
}

void examples_pop(Examples* e) {
    stack_pop(e->stack, e);
    for (unsigned i = 0; i < vector_count(e->ex); i++) {
        PartialAssignment* pa = vector_get(e->ex, i);
        partial_assignment_pop(pa);
        assert(e->stack->push_count == pa->stack->push_count);
    }
    assert(e->conflicted_pa != NULL || e->state == EXAMPLES_STATE_READY);
    if (e->conflicted_pa != NULL && ! partial_assignment_is_conflicted(e->conflicted_pa)) {
        e->conflicted_pa = NULL;
        e->state = EXAMPLES_STATE_READY;
    }
}

//void examples_find_decision_val_consistent_with_examples(Examples* e, Skolem* s, unsigned var_id) {
//    assert( ! skolem_is_deterministic(s, var_id));
//    
//    // determine whic
//    LOG_WARNING("not implemented");
////    NOT_IMPLEMENTED();
//    
//}

void examples_decision(Examples* e, Lit decision_lit) {
    abortif(examples_is_conflicted(e), "Examples domain expected to be not conflicted.");
    assert(sizeof(long) == 8);
    stack_push_op(e->stack, EXAMPLES_OP_DECISION, (void*) (long) decision_lit);
    for (unsigned i = 0; i < vector_count(e->ex); i++) {
        PartialAssignment* pa = vector_get(e->ex, i);
        if (partial_assignment_get_value_for_conflict_analysis(pa, decision_lit) == 0) {
            take_pa_decision(e, pa, decision_lit);
        }
        if (partial_assignment_is_conflicted(pa)) {
            V1("Conflict in skolem example %u/%u; caused by a decision\n", i+1, vector_count(e->ex));
            return;
        }
    }
}

void examples_decision_consistent_with_skolem(Examples* e, Skolem* s, Lit decision_lit) {
    if (examples_is_decision_consistent_with_skolem(e, s, decision_lit)) {
        examples_decision(e, decision_lit);
    } else {
        assert(examples_is_conflicted(e));
    }
}

void examples_new_clause(Examples* e, Clause* c) {
    assert( ! examples_is_conflicted(e));
    for (unsigned i = 0; i < vector_count(e->ex); i++) {
        PartialAssignment* pa = vector_get(e->ex, i);
        partial_assignment_new_clause(pa, c);
        if (partial_assignment_is_conflicted(pa)) {
            e->conflicted_pa = pa;
            e->state = EXAMPLES_STATE_PROPAGATION_CONFLICT;
            return;
        }
    }
}

void examples_propagate(Examples* e) {
    if (examples_is_conflicted(e)) {
        return;
    }
    V3("Propagating %u example assignments.\n",vector_count(e->ex));
    for (unsigned i = 0; i < vector_count(e->ex); i++) {
        PartialAssignment* pa = vector_get(e->ex, i);
        partial_assignment_propagate(pa);
        if (partial_assignment_is_conflicted(pa)) {
            V1("Conflict in skolem example %u of %u (propagation)\n", i+1, vector_count(e->ex));
            e->conflicted_pa = pa;
            e->state = EXAMPLES_STATE_PROPAGATION_CONFLICT;
            return;
        }
    }
}
