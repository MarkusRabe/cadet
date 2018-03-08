//
//  debug.c
//  cadet
//
//  Created by Markus Rabe on 21/09/16.
//  Copyright © 2016 Saarland University. All rights reserved.
//

#include "debug.h"
#include "log.h"
#include "statistics.h"
#include "mersenne_twister.h"

#include <assert.h>


// Generates random inputs to the skolem function and tests for
// satisfiability of the skolem solver. This makes sure that
// the skolem function is not too strong, which may cause the
// Function to
void debug_fuzz_for_incompleteness(C2* c2, unsigned num_trials) {
    
    assert(debug_verbosity >= VERBOSITY_NONE);
    V1("Fuzzing Skolem function for violations of totality with %u trials.\n", num_trials);
    
    vector* universals = vector_init();
    int_vector* assignment = int_vector_init();
    for (unsigned i = 0; i < var_vector_count(c2->qcnf->vars); i++) {
        Var* v = var_vector_get(c2->qcnf->vars, i);
        if (v->var_id != 0 && v->is_universal) {
            vector_add(universals, v);
            int_vector_add(assignment, 0);
        }
    }
    
    for (unsigned n = 0; n < num_trials; n++) {
        
        satsolver_push(c2->skolem->skolem);
        
        // take a random assignment
        for (unsigned i = 0; i < int_vector_count(assignment); i++) {
            Var* v = vector_get(universals, i);
            int val = genrand_int31()%2 ? 1 : -1;
//            int val = v->var_id == 5 ? -1 : 1;
            int_vector_set(assignment, i, val);
            Lit l = skolem_get_satsolver_lit(c2->skolem, val * (int)v->var_id);
            satsolver_add(c2->skolem->skolem, l);
            satsolver_clause_finished(c2->skolem->skolem);
//            V4("  asserting var %u, satlit %d\n", v->var_id, l);
        }
        
        sat_res res = satsolver_sat(c2->skolem->skolem);
        
        if (res != SATSOLVER_SAT) {
            printf("Fuzzing detected lack of totality for this assignment:\n");
            for (unsigned i = 0; i < vector_count(universals); i++) {
                Var* v = vector_get(universals, i);
                int val = int_vector_get(assignment, i);
                printf(" %d", val * (int) v->var_id);
            }
            printf("\n");
            abort();
        }
        
        satsolver_pop(c2->skolem->skolem);
    }
    
    vector_free(universals);
    int_vector_free(assignment);
}

// Prints the histogramm of the activity values of all variables up to specified decision level.
// Use c2->skolem->decision_lvl to get all variables.
void debug_print_histogram_of_activities(C2* c2, bool only_deterministic) {
    Stats* s = statistics_init(100000);
    float cur_max = -1;
    Var* v_max = NULL;
    for (unsigned i = 0; i < var_vector_count(c2->qcnf->vars); i++) {
        Var* v = var_vector_get(c2->qcnf->vars, i);
        if (v->var_id != 0 && (! only_deterministic || skolem_is_deterministic(c2->skolem, v->var_id)) ) {
            assert(v->var_id == i);
            float a = c2_get_activity(c2, v->var_id);
            assert(a >= 0.0);
            statistic_add_value(s, a);
            if (a > cur_max) {
                cur_max = a;
                v_max = v;
            }
        }
    }
    V1("Activity statistics:\n    ");
    if(v_max) {
        V1("Max activity var: %u\n", v_max->var_id);
    } else {
        V1("No deterministic var found.\n");
    }
    statistics_print(s);
    statistics_free(s);
}
