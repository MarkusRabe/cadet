//
//  matrix_qbce.c
//  caqe
//
//  Created by Markus Rabe on 30/11/15.
//  Copyright © 2015 Saarland University. All rights reserved.
//

#include "matrix.h"
#include "assert.h"
#include "log.h"

#include "satsolver.h"

////////////////////////       QBCE      ///////////////////////////////

bool q_resolution(Occ* o1, Occ* o2) {
    assert(o1->var == o2->var);
    assert(o1->neg != o2->neg);
    assert(o1->var->value == 0);
    assert(o2->var->value == 0);
    MClause* c1 = o1->clause;
    MClause* c2 = o2->clause;
    
    Occ* left  = &c1->occs[0];
    Occ* right = &c2->occs[0];
    while (left <= &c1->occs[c1->size - 1] && right <= &c2->occs[c2->size - 1]) {
        
        if (left->var->value != 0) {
            left++;
            continue;
        }
        if (right->var->value != 0) {
            right++;
            continue;
        }
        
        int cmp = compare_occurrence_by_level_then_var_id(left, right);
        if (cmp == 0) { // found an equal pair!
            if (left == o1) {
                assert(right == o2);
                break;
            }
            if (left->neg != right->neg) {
                return true;
            }
            left++;
            right++;
        } else if (cmp > 0) {
            right++;
        } else { // cmp < 0
            left++;
        }
    }
    return false;
}

bool is_blocking_literal(Occ* o) {
    
    vector* opposite_occs = o->neg ? o->var->pos_occs : o->var->neg_occs;
    
    bool all_resovants_true = true;
    for (unsigned i = 0; i < vector_count(opposite_occs); i++) {
        Occ* other = vector_get(opposite_occs, i);
        if (is_clause_satisfied(other->clause) || other->clause->blocked) {
            continue;
        }
        
        if (! q_resolution(o, other)) {
            all_resovants_true = false;
            break;
        }
    }
    return all_resovants_true;
}


//      The following code is for checking QBCE based on a clause work list. May be slightly more efficient, but fits less well into the framework.

//void trigger_more_qbce_checks(MClause* c, heap* queue, map* is_queued) {
//    assert(c->blocked_lit != NULL);
//    for (int i = 0; i < c->size; i++) {
//        Occ* occ = &c->occs[i];
//        if (! is_active(occ)) {
//            continue;
//        }
//        vector* opposite_occs = occ->neg ? occ->var->pos_occs : occ->var->neg_occs;
//        for (unsigned j = 0; j < vector_count(opposite_occs); j++) {
//            Occ* o = vector_get(opposite_occs, j);
//            
//            assert(c != o->clause);
//            
//            if (o->clause->satisfied_by != NULL || o->clause->blocked_lit != NULL) {
//                continue;
//            }
//            
//            if (! map_contains(is_queued, o->clause->clause_id)) {
//                heap_push(queue, o->clause);
//                map_add(is_queued, o->clause->clause_id, NULL);
//            }
//        }
//    }
//}
//
//
//void matrix_qbce(Matrix* m) {
//    
//    heap* work_queue = heap_init(compare_clauses_by_size);
//    map* is_in_work_queue = map_init();
//    
//    for (unsigned i = 0; i < vector_count(m->clauses); i++) {
//        MClause* c = vector_get(m->clauses, i);
//        
//        if (c->blocked_lit != NULL || c->satisfied_by != NULL) {
//            continue;
//        }
//        
//        heap_push(work_queue, c);
//        map_add(is_in_work_queue, c->clause_id, NULL);
//    }
//    
//    while (heap_size(work_queue) > 0) {
//        
//        MClause* c = heap_pop(work_queue);
//        map_remove(is_in_work_queue, c->clause_id);
//        assert(c->blocked_lit == NULL);
//        
//        for (int j = 0; j < c->size; j++) {
//            Occ* o = &c->occs[j];
//            if (! is_active(o) || o->var->scope->qtype == QUANTIFIER_UNIVERSAL) {
//                continue;
//            }
//            
//            if (is_blocking_literal(o)) {
//                assert(o->clause->blocked_lit == NULL);
//                o->clause->blocked_lit = o;
//                
//                // Successful elimination of clause may trigger other eliminations
//                trigger_more_qbce_checks(o->clause, work_queue, is_in_work_queue);
//                
//                m->qbce_eliminated_clauses += 1;
//                
//                break; // continue with next clause
//            }
//        }
//    }
//}




void block_literal(Matrix* m, Occ* o) {
    
    assert(! o->clause->blocked);
    o->clause->blocked = true;
    m->qbce_eliminated_clauses += 1;
    
    // Successful elimination of clause may trigger other eliminations
    MClause* c = o->clause;
    for (int i = 0; i < c->size; i++) {
        Occ* occ = &c->occs[i];

        // TODO: for more efficiency during QBCE we could remember which polarity the variable is
        
        if (occ->var->value == 0 && ! occ->var->needs_qbce_check && occ->var->scope->qtype == QUANTIFIER_EXISTENTIAL) {
            heap_push(m->variables_to_check, occ->var);
            occ->var->needs_qbce_check = true;
        }
    }
}


// Checking variable for occurrences as blocking literal (for QBCE)
void check_var(Matrix* m, MVar* var) {
    assert(var->scope->qtype == QUANTIFIER_EXISTENTIAL);
    assert(var->needs_qbce_check == true);
    var->needs_qbce_check = false;
    
    bool pos_occs_empty = true;
    for (unsigned i = 0; i < vector_count(var->pos_occs); i++) {
        Occ* o = vector_get(var->pos_occs, i);
        MClause* c = o->clause;
        if (is_clause_satisfied(c) || c->blocked) {
            continue;
        }
        pos_occs_empty = false;
        if (is_blocking_literal(o)) {
            block_literal(m, o);
        }
    }

    bool neg_occs_empty = true;
    for (unsigned i = 0; i < vector_count(var->neg_occs); i++) {
        Occ* o = vector_get(var->neg_occs, i);
        MClause* c = o->clause;
        if (is_clause_satisfied(c) || c->blocked) {
            continue;
        }
        neg_occs_empty = false;
        if (is_blocking_literal(o)) {
            block_literal(m, o);
        }
    }
}

void matrix_qbce_vars(Matrix* m) {
    
    assert(heap_count(m->variables_to_check) == 0);
    
    for (unsigned i = 0; i < vector_count(m->scopes); i++) {
        MScope* s = vector_get(m->scopes, i);
        if (s->qtype == QUANTIFIER_UNIVERSAL) {
            continue;
        }
        for (unsigned j = 0; j < vector_count(s->vars); j++) {
            MVar* v = vector_get(s->vars, j);
            assert(v->scope->qtype == QUANTIFIER_EXISTENTIAL);
            if (v->value != 0 || v->dependence_level != NO_DEPENDENCE_LVL) {
                continue;
            }
            
            assert( ! v->needs_qbce_check);
            
            heap_push(m->variables_to_check, v);
            v->needs_qbce_check = true;
        }
    }
    
    while (heap_count(m->variables_to_check) > 0) {
        MVar* v = heap_pop(m->variables_to_check);
        check_var(m, v);
    }
    
    // mark variables that are completely eliminated by QBCE
    for (unsigned j = 0; j < vector_count(m->scopes); j++) {
        MScope* s = vector_get(m->scopes, j);
        for (unsigned i = 0; i < vector_count(s->vars); i++) {
            MVar* v = vector_get(s->vars, i);
            v->has_only_blocked_clauses = true;
            for (unsigned i = 0; i < vector_count(v->pos_occs) || i < vector_count(v->neg_occs); i++) {
                Occ* pos_occ = i < vector_count(v->pos_occs) ? vector_get(v->pos_occs, i) : NULL;
                Occ* neg_occ = i < vector_count(v->neg_occs) ? vector_get(v->neg_occs, i) : NULL;
                if ((pos_occ && ! pos_occ->clause->blocked) || (neg_occ && ! neg_occ->clause->blocked)) {
                    v->has_only_blocked_clauses = false;
                    break;
                }
            }
            if (v->has_only_blocked_clauses) {
                m->qbce_eliminated_vars++;
                V4("MVar %d is fully eliminated by QBCE.\n", v->var_id);
            }
        }
    }
}
