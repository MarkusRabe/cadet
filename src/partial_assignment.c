//
//  partial_assignment.c
//  cadet
//
//  Created by Markus Rabe on 15/06/16.
//  Copyright © 2016 Saarland University. All rights reserved.
//

#include "partial_assignment.h"
#include "log.h"
#include "util.h"

#include <assert.h>
#include <stdint.h>

PartialAssignment* partial_assignment_init(QCNF* qcnf) {
    PartialAssignment* pa = malloc(sizeof(PartialAssignment));
    pa->qcnf = qcnf;
    pa->clauses_to_check = worklist_init(qcnf_compare_clauses_by_size);
    pa->assigned_variables = 0;
    pa->conflicted = 0;
    pa->conflicted_clause = NULL;
//    pa->recently_propagated_lits = int_vector_init();
    pa->stack = stack_init(partial_assignment_undo);
    pa->vals = vector_init();
#ifdef DEBUG_PARTIAL_ASSIGNMENT
    pa->vals_debug = vector_init();
#endif
    pa->causes = vector_init();
    
    pa->inner_address_length = sizeof(void*) == 8 ? 5 : sizeof(void*) == 4 ? 4 : 4;
    pa->inner_address_mask = (1 << pa->inner_address_length) - 1;
    
    pa->conflicts = 0;
    pa->propagations = 0;
    
    for (unsigned i = 0; i < vector_count(qcnf->clauses); i++) {
        Clause* c = vector_get(qcnf->clauses, i);
        if (c && c->size == 1) {
            worklist_push(pa->clauses_to_check, c);
        }
    }
    
    return pa;
}

void partial_assignment_free(PartialAssignment* pa) {
    worklist_free(pa->clauses_to_check);
    stack_free(pa->stack);
    vector_free(pa->vals);
#ifdef DEBUG_PARTIAL_ASSIGNMENT
    vector_free(pa->vals_debug);
#endif
    vector_free(pa->causes);
    free(pa);
}

void partial_assignment_pop(PartialAssignment* pa) {
    worklist_reset(pa->clauses_to_check);
    stack_pop(pa->stack, pa);
    assert(! partial_assignment_is_conflicted(pa));
}
void partial_assignment_push(PartialAssignment* pa) {
    stack_push(pa->stack);
}

unsigned partial_assignment_is_conflicted(PartialAssignment* pa) {
    assert((pa->conflicted_clause == NULL) == (pa->conflicted == 0));
    return pa->conflicted;
}

VAL partial_assignment_get_val(PartialAssignment* pa, unsigned var_id) {
    assert(var_id>=0);
    assert(sizeof(uint64_t) >= sizeof(void*));
    unsigned word_address = var_id >> pa->inner_address_length;
    while (word_address >= vector_count(pa->vals)) {
        vector_add(pa->vals, NULL);
    }
    uint64_t data = (uint64_t) vector_get(pa->vals, word_address);
    uint64_t inner_address =  var_id & pa->inner_address_mask;
    uint64_t twobitpattern =  (uint64_t)3 << (2 * inner_address);
    VAL val = (VAL)((data & twobitpattern) >> (2 * inner_address));
#ifdef DEBUG_PARTIAL_ASSIGNMENT
    while (var_id >= vector_count(pa->vals_debug)) {
        vector_add(pa->vals_debug, NULL);
    }
    VAL vd = (VAL) vector_get(pa->vals_debug, var_id);
    assert(vd == val);
#endif
    return val;
}

void partial_assignment_set_val(PartialAssignment* pa, unsigned var_id, VAL new) {
    assert(var_id >= 0);
    while (vector_count(pa->vals) <= (var_id >> pa->inner_address_length)) {
        vector_add(pa->vals, NULL); // value 0 is important here because we access it and interpret it as unknown.  
    }
    void* data = vector_get(pa->vals, var_id >> pa->inner_address_length);
    uint64_t inner_address =  var_id & pa->inner_address_mask;
    uint64_t twobitpattern =  (uint64_t)3 << (2 * inner_address);
    uint64_t new_data = (uint64_t)data & ~twobitpattern;
    new_data |= ((uint64_t) new) << (2 * inner_address);
    vector_set(pa->vals, var_id >> pa->inner_address_length, (void*)new_data);
    
#ifdef DEBUG_PARTIAL_ASSIGNMENT
    while (vector_count(pa->vals_debug) <= var_id) {
        vector_add(pa->vals_debug, 0); // value 0 is important here because we access it and interpret it as unknown.
    }
    vector_set(pa->vals_debug, var_id, (void*) new);
#endif
}

Lit partial_assignment_is_clause_satisfied(PartialAssignment* pa, Clause* c) {
    for (int i = 0; i < c->size; i++) {
        VAL v = partial_assignment_get_val(pa, lit_to_var(c->occs[i]));
        if (v == (c->occs[i] > 0 ? tt : ff)) {
            return c->occs[i];
        }
    }
    return 0;
}

void update_clause_worklist(PartialAssignment* pa, QCNF* qcnf, int unassigned_lit) {
    Var* v = var_vector_get(qcnf->vars, lit_to_var(unassigned_lit));
    vector* occs = unassigned_lit > 0 ? &v->neg_occs : &v->pos_occs;
    for (unsigned i = 0; i < vector_count(occs); i++) {
        worklist_push(pa->clauses_to_check, vector_get(occs, i));
    }
}

void partial_assignment_assign_value(PartialAssignment* pa, Lit lit) {
    V4("Partial assignment assign value %d.\n",lit);
    pa->assigned_variables++;
    update_clause_worklist(pa, pa->qcnf, lit);
    VAL new_val = lit > 0 ? tt : ff;
    partial_assignment_set_val(pa, lit_to_var(lit), new_val);
    stack_push_op(pa->stack, PA_OP_ASSIGN, (void*) (uint64_t) lit_to_var(lit));
}

void partial_assignment_propagate_clause(PartialAssignment* pa, Clause* c) {
    Lit unassigned_lit = 0;
    bool contains_universals = false;
    for (int i = 0; i < c->size; i++) {
        VAL v = partial_assignment_get_val(pa, lit_to_var(c->occs[i]));
        assert(v != bottom);
        
        if (v == (c->occs[i] > 0 ? tt : ff)) {
            // this literal satisfies the clause
            return;
        }
        if (v == top) {
            if (unassigned_lit != 0 || contains_universals) {
                // two unassigned existentials; clause cannot propagate
                return;
            }
            unassigned_lit = c->occs[i];
        }
    }
    
//    VAL new_val = top;
    if (unassigned_lit == 0) { // conflict
        
        pa->conflicted_clause = c;
        
        assert(pa->conflicted == 0);
        pa->conflicts++;
        pa->conflicted = lit_to_var(c->occs[c->size - 1]); // conflict is the last variable in the clause :/
        stack_push_op(pa->stack, PA_OP_CONFLICT, (void*) (int64_t) pa->conflicted);
        
        V3("Conflict in partial assignment domain for clause %u and var %u\n", pa->conflicted_clause->clause_id, pa->conflicted);
        
    } else { // assign value
        assert(! contains_universals);
//        V4("Propagating variable %d.\n",unassigned_lit);
        pa->propagations++;
        partial_assignment_assign_value(pa, unassigned_lit);
//        int_vector_add(pa->recently_propagated_lits, unassigned_lit);
        
        while (vector_count(pa->causes) <= lit_to_var(unassigned_lit)) {
            vector_add(pa->causes, NULL);
        }
        vector_set(pa->causes, lit_to_var(unassigned_lit), c);
    }
}

void partial_assignment_propagate(PartialAssignment* pa) {
    V4("Propagating partial assignments\n");
    while (worklist_count(pa->clauses_to_check) > 0) {
        Clause* c = worklist_pop(pa->clauses_to_check);
        partial_assignment_propagate_clause(pa, c);
        
        if (partial_assignment_is_conflicted(pa)) {
            worklist_free(pa->clauses_to_check);
            pa->clauses_to_check = worklist_init(qcnf_compare_clauses_by_size);
            return;
        }
    }
}

// INTERACTION WITH CONFLICT ANALYSIS
bool partial_assignment_is_legal_dependence(void* s, unsigned var_id, unsigned depending_on) {
    return true;
}
int partial_assignment_get_value_for_conflict_analysis(void* domain, Lit lit) {
    assert(lit != 0);
    VAL val = partial_assignment_get_val((PartialAssignment*) domain, lit_to_var(lit));
    assert(val != bottom);
    assert(val >= 0);
    assert(bottom == 3);
    assert(tt == 2);
    assert(ff == 1);
    assert(top == 0);
    assert((-3 % 3) == 0);
    int x = val == top ? 0 : ((2 * val) - 3);
    assert(val == ff && x == -1 || val == top && x == 0 || val == tt && x == 1);
    return lit > 0 ? x : -x;
}

bool partial_assignment_is_relevant_clause(void* domain, Clause* c, unsigned var_id) {
    PartialAssignment* pa = (PartialAssignment*) domain;
    bool res = false;
    if (var_id == pa->conflicted) {
        res = c == pa->conflicted_clause;
    }
    return res || (vector_count(pa->causes) > var_id && c == vector_get(pa->causes, var_id));
}

unsigned partial_assignment_get_decision_lvl(void* domain, unsigned var_id) {
    NOT_IMPLEMENTED();
}

// Register new clauses

void partial_assignment_new_clause(PartialAssignment* pa, Clause* c) {
    worklist_push(pa->clauses_to_check, c);
}


// PRINTING

void partial_assignment_print_statistics(PartialAssignment* pa) {
    V1("Partial assignment statistics:\n");
    V1("  Propagations: %zu\n",pa->propagations);
    V1("  Conflicts: %zu\n",pa->conflicts);
    V1("  Current assignments: %zu\n",pa->assigned_variables);
}

void pa_print_debug_info(PartialAssignment* pa) {
#ifdef DEBUG_PARTIAL_ASSIGNMENT
    V1("PA state: \n"
       "  is conflicted: %u\n  vals: ", pa->conflicted);
    unsigned j = 0;
    for (unsigned i = 0; i < vector_count(pa->vals_debug); i++) {
        VAL val = partial_assignment_get_val(pa, i);
        if (val) {
            V1("%u -> %d", i, partial_assignment_get_val(pa, i));
            if (i + 1 != vector_count(pa->vals_debug)) {
                V1(", ");
            }
            if (j % 8 == 7) {
                V1("\n  ");
            }
            j++;
        }
        if (i + 1 == vector_count(pa->vals_debug)) {
            V1("\n  ");
        }
            
    }
//    V1("Recently propagated: ");
//    for (unsigned i = 0; i < int_vector_count(pa->recently_propagated_lits); i++) {
//        V1("%d", int_vector_get(pa->recently_propagated_lits, i));
//        if (i + 1 != int_vector_count(pa->recently_propagated_lits)) {
//            V1(", ");
//        }
//        if (i % 8 == 7 || i + 1 == int_vector_count(pa->recently_propagated_lits)) {
//            V1("\n  ");
//        }
//    }
    V1("\n  Worklist count: %u\n", worklist_count(pa->clauses_to_check));
#endif
}

// PRIVATE FUNCTIONS

void partial_assignment_undo(void* parent, char type, void* obj) {
    PartialAssignment* pa = (PartialAssignment*) parent;
    switch ((PA_OPERATION) type) {
        case PA_OP_ASSIGN:
            assert(obj != NULL);
            unsigned var_id = (unsigned) obj;
            assert(partial_assignment_get_val(pa, var_id) == tt || partial_assignment_get_val(pa, var_id) == ff);
            partial_assignment_set_val(pa, var_id, top);
            if (vector_count(pa->causes) > var_id) { // could be decision var! so this is not always true
                vector_set(pa->causes, var_id, NULL);
            }
            pa->assigned_variables--;
            break;
            
        case PA_OP_CONFLICT:
            assert(pa->conflicted == (unsigned) obj);
//            assert((unsigned) obj <= 3); // i.e. is a VAL
//            VAL previous = (VAL) obj;
//            assert(partial_assignment_get_val(pa, pa->conflicted) == bottom);
//            partial_assignment_set_val(pa, pa->conflicted, previous);
            pa->conflicted = 0;
            assert(pa->conflicted_clause != NULL);
            pa->conflicted_clause = NULL;
            break;
            
        default:
            V0("Unknown undo operation in partial_assignment.c: %d\n",(int) type);
            NOT_IMPLEMENTED();
    }
}

void partial_assignment_print(PartialAssignment* pa) {
    NOT_IMPLEMENTED();
}
