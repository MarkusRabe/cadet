//
//  matrix_validation.c
//  caqe
//
//  Created by Markus Rabe on 30/11/15.
//  Copyright © 2015 Saarland University. All rights reserved.
//

#include "assert.h"
#include "vector.h"
#include "matrix.h"
#include "log.h"

// The following code validates a number of invariants of the matrix data structure.
// It is particularly helpful to find NULL pointers and dangling references.

void matrix_validate_scope(Matrix* m, MScope* s) {
    assert( (s->level % 2 == 0) == (s->qtype == QUANTIFIER_EXISTENTIAL));
    assert( (s->qtype == QUANTIFIER_UNIVERSAL) || (s->qtype == QUANTIFIER_EXISTENTIAL));
    assert(  s->level >= 0);
    assert(  s->level < vector_count(m->scopes));
}

void matrix_validate_occ(Occ* o) {
    //    V4("(neg %d, var %d, active: %d)\n",o->neg, o->var->var_id, is_active(o));
    assert(o->neg ? o->var->value != -1 : o->var->value != 1);
    assert(o->var->value != (o->neg ? -1 : 1) || is_clause_satisfied(o->clause));
}

void matrix_validate_variable(Matrix* m, MVar* v) {
    
    assert(v->dependence_level <= v->scope->level || v->dependence_level == NO_DEPENDENCE_LVL);
    assert(v->dependence_level == v->scope->level || v->scope->qtype == QUANTIFIER_EXISTENTIAL);
    assert(v->value == 0 || v->dependence_level != NO_DEPENDENCE_LVL || v->scope->qtype == QUANTIFIER_UNIVERSAL);
    
    assert(v->dependence_level == NO_DEPENDENCE_LVL || v->scope->qtype == QUANTIFIER_UNIVERSAL || compute_dependence_lvl(m, v) == v->dependence_level);
    
    assert(v->value == -1 || v->value == 0 || v->value == 1);
    //    V4("MVar %d: value %d, level %zu, pos %zu:\n",v->var_id,v->value,v->scope->level, vector_count(v->pos_occs));
    
    for (unsigned i = 0; i < vector_count(v->pos_occs); i++) {
        Occ* o = vector_get(v->pos_occs, i);
        //        V4("   ");
        matrix_validate_occ(o);
        assert(v == o->var);
    }
    //    V4(" neg %zu: ", vector_count(v->neg_occs));
    for (unsigned i = 0; i < vector_count(v->neg_occs); i++) {
        Occ* o = vector_get(v->neg_occs, i);
        //        V4("   ");
        matrix_validate_occ(o);
        assert(v == o->var);
    }
    
    
}

void matrix_validate_clause(MClause* c) {
    //    V4("MClause %d: check %d, size %zu, max var %d, max level %zu, satisfied by %zu, occs:\n",c->clause_id, c->needs_check, c->orig_size,c->max_scope->var->var_id,c->max_scope->var->scope->level,(unsigned) c->satisfied_by);
    
    for (int i = 0; i < c->size; i++) {
        Occ* o = & c->occs[i];
        //        V4("   ");
        matrix_validate_occ(o);
        
        assert(o->clause == c);
        if ( ! is_clause_satisfied(c)) {
            assert(o->neg ? o->var->value != -1 : o->var->value != 1);
        }
        if (o->var->value == 0) {
            assert( ! is_clause_satisfied(c));
        }
    }
    
    for (Occ* o = &c->occs[c->size - 1]; o >= c->occs; o--) {
        assert(c == o->clause);
    }
}

// Validates the (some) invariants of the matrix (may assume sometimes that the matrix is properly simplified?)
void matrix_validate(Matrix* m) {
    
    assert(m->satisfied_clauses < m->clause_num || m->result == MATRIX_SATISFIABLE);
    assert(m->minimal_dependence_lvl % 2 == 0 && m->minimal_dependence_lvl >= 0 && m->minimal_dependence_lvl < vector_count(m->scopes)); // is the level of an existential quantifier
    
    for (unsigned i = 0; i < vector_count(m->scopes); i++) {
        MScope* s = vector_get(m->scopes, i);
        assert(s->level == i);
        for (unsigned j = 0; j < vector_count(s->vars); j++) {
            MVar* v = vector_get(s->vars, j);
            if (v->value == 0) {
                matrix_validate_variable(m, v);
            } else {
                matrix_validate_scope(m, v->scope);
            }
        }
    }
    
    for (MClause* c = m->first_clause; c != NULL; c = c->next) {
        if ( ! is_clause_satisfied(c)) {
            matrix_validate_clause(c);
        }
    }
}

