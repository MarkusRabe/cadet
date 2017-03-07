//
//  reencode.c
//  cadet
//
//  Created by Markus Rabe on 06/01/2017.
//  Copyright © 2017 UC Berkeley. All rights reserved.
//

#include "reencode.h"
#include "skolem.h"
#include "log.h"
#include "util.h"
#include "vector.h"

#include <assert.h>

void reencode_existentials(QCNF* qcnf, Options* o) {
    for (unsigned i = 0; i < vector_count(qcnf->scopes) - 1; i++) {
        // 1. propagate what inner existentials depend on outer existentials only
        Skolem* skolem_i = skolem_init(qcnf, o, i+1, i+1);
        skolem_i->mode = SKOLEM_MODE_RECORD_POTENTIAL_CONFLICTS;
        skolem_propagate(skolem_i);
        
        V0("Variables reassigned to level %u:",i);
        unsigned count = 0;
        unsigned constants = 0;
        for (unsigned j = 0; j < var_vector_count(qcnf->vars); j++) {
            if (qcnf_var_exists(qcnf, j) && skolem_is_deterministic(skolem_i, j)) {
                Var* v = var_vector_get(qcnf->vars, j);
                if (v->scope_id > i) {
                    count++;
                    bool is_constant = skolem_get_constant_value(skolem_i, (Lit) v->var_id) != 0;
                    if (is_constant) {
                        constants += 1;
                    }
                    V3(" %u %s",v->var_id, is_constant ? "(constant)" : "");
                    assert( ! v->is_universal);
                    v->scope_id = (unsigned short) i;
                }
            }
        }
        V0(" ... %u vars in total (%u constants)\n",count,constants);
        skolem_free(skolem_i);
    }
}

QCNF* threeqbf2twoqbf(QCNF* qcnf, Options* o) {
    
    abortif(vector_count(qcnf->scopes) > 2, "Need a 3QBF.");
    
    if (qcnf_contains_empty_clause(qcnf)) {
        return NULL;
    }
    
    // 1. propagate what inner existentials depend on outer existentials only
    Skolem* skolem0 = skolem_init(qcnf, o, 1, 1);
    skolem0->mode = SKOLEM_MODE_RECORD_POTENTIAL_CONFLICTS;
    skolem_propagate(skolem0);
    
    for (unsigned i = 0; i < var_vector_count(qcnf->vars); i++) {
        if (qcnf_var_exists(qcnf, i) && skolem_is_deterministic(skolem0, i)) {
            Var* v = var_vector_get(qcnf->vars, i);
            if (v->scope_id > i) {
                V0("Reassigning variable %u to level %u. %s\n",v->var_id, 0, skolem_get_constant_value(skolem0, (Lit) v->var_id) != 0 ? "(constant)" : "");
                assert( ! v->is_universal);
                v->scope_id = (unsigned short) 0;
                
                for (unsigned j = 0; j < vector_count(&v->pos_occs); j++) {
                    Clause* c = vector_get(&v->pos_occs, j);
                    if (lit_to_var(skolem_get_unique_consequence(skolem0, c)) == v->var_id) {
                        vector_add(qcnf->cubes, c);
                        vector_set(qcnf->clauses, c->clause_id, NULL);
                    }
                }
                for (unsigned j = 0; j < vector_count(&v->neg_occs); j++) {
                    Clause* c = vector_get(&v->neg_occs, j);
                    if (lit_to_var(skolem_get_unique_consequence(skolem0, c)) == v->var_id) {
                        vector_add(qcnf->cubes, c);
                        vector_set(qcnf->clauses, c->clause_id, NULL);
                    }
                }
            }
        }
    }
    skolem_free(skolem0);
    
    // 2. propagate what inner existentials depend on outer existentials and universals
    Skolem* skolem1 = skolem_init(qcnf, o, 2, 1);
    skolem1->mode = SKOLEM_MODE_RECORD_POTENTIAL_CONFLICTS;
    skolem_propagate(skolem1);
    
    // These should be all variables
    for (unsigned i = 0; i < var_vector_count(qcnf->vars); i++) {
        abortif(qcnf_var_exists(qcnf, i) && ! skolem_is_deterministic(skolem1, i), "This formula is not a 2QBF in disguise.");
    }
    
    // encode group 2 using delayed conflict formula
    // TODO: extract new clauses from the SAT solver representing the conflicts
    
    skolem_free(skolem1);
    NOT_IMPLEMENTED();
}

aiger* qbf2aiger(QCNF* qcnf, Options* o) {
    
    abortif(vector_count(qcnf->scopes) > 2, "Can only convert 3QBF to aiger right now.");
    
    // 1. propagate what inner existentials depend on outer existentials only
    Skolem* skolem0 = skolem_init(qcnf, o, 1, 1);
    skolem0->mode = SKOLEM_MODE_RECORD_POTENTIAL_CONFLICTS;
    skolem_propagate(skolem0);
    
    for (unsigned i = 0; i < var_vector_count(qcnf->vars); i++) {
        if (qcnf_var_exists(qcnf, i) && skolem_is_deterministic(skolem0, i)) {
            Var* v = var_vector_get(qcnf->vars, i);
            if (v->scope_id > i) {
                V0("Reassigning variable %u to level %u. %s\n",v->var_id, 0, skolem_get_constant_value(skolem0, (Lit) v->var_id) != 0 ? "(constant)" : "");
                assert( ! v->is_universal);
                v->scope_id = (unsigned short) 0;
            }
        }
    }
    skolem_free(skolem0);
    
    // 2. propagate what inner existentials depend on outer existentials and universals
    Skolem* skolem1 = skolem_init(qcnf, o, 2, 1);
    skolem1->mode = SKOLEM_MODE_RECORD_POTENTIAL_CONFLICTS;
    skolem_propagate(skolem1);
    
    // These should be all variables
    for (unsigned i = 0; i < var_vector_count(qcnf->vars); i++) {
        abortif(qcnf_var_exists(qcnf, i) && ! skolem_is_deterministic(skolem1, i), "This formula is not a 2QBF in disguise.");
    }
    
    // Create aiger
    aiger* a = aiger_init();
    
    // encode group 1 as constraints
    
    // encode group 2 as bads, using delayed conflict formula
    
    NOT_IMPLEMENTED();
}

