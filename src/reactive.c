
//
//  reactive.c
//  caqe
//
//  Created by Markus Rabe on 16/03/16.
//  Copyright © 2016 Saarland University. All rights reserved.
//

#include "reactive.h"
#include "aiger.h"
#include "aiger_utils.h"
#include "log.h"
#include "cadet.h"
#include "certification.h"

#include <stdio.h>
#include <string.h>

bool is_controllable(const char* str) {
    return strncmp("controllable_", str, 13) == 0;
}

void transition_relation_from_aiger(CADET* cadet, aiger* aig) {
    assert (aiger_check(aig) == NULL);
    assert(cadet->added_clauses == 0);
    assert(cadet->matrix->max_var_id == 0);
    
    cadet_new_universal_quantifier(cadet);
    
    // latches
    for (size_t i = 0; i < aig->num_latches; i++) {
        aiger_symbol l = aig->latches[i];
        cadet_create_var(cadet, aiger_lit2var(l.lit));
    }
    
    // uncontrollable inputs
    for (size_t i = 0; i < aig->num_inputs; i++) {
        aiger_symbol input = aig->inputs[i];
        if ( ! is_controllable(input.name)) {
            cadet_create_var(cadet, aiger_lit2var(input.lit));
        }
    }
    
    cadet_new_existential_quantifier(cadet);
    
    // controllable inputs
    for (size_t i = 0; i < aig->num_inputs; i++) {
        aiger_symbol input = aig->inputs[i];
        if (is_controllable(input.name)) {
            cadet_create_var(cadet, aiger_lit2var(input.lit));
        }
    }
    
    // next values for latches
    for (size_t i = 0; i < aig->num_latches; i++) {
        aiger_symbol l = aig->latches[i];
        if (l.next > 1 && ! cadet_variable_exists(cadet, aiger_lit2var(l.next))){
            cadet_create_var(cadet, aiger_lit2var(l.next));
        }
    }
    
    // outputs
    assert(aig->num_outputs > 0);
    if (aig->num_outputs > 1) {
        V1("Warning: multiple outputs defined. CADET uses their conjunction as the safety property.\n");
    }
    for (size_t i = 0; i < aig->num_outputs; i++) {
        aiger_symbol o = aig->outputs[i];
        if (o.lit > 1 && ! cadet_variable_exists(cadet, aiger_lit2var(o.lit))) {
            cadet_create_var(cadet, aiger_lit2var(o.lit));
        } // else ignore // we can ignore true and false signals.
    }
    
    for (size_t i = 0; i < aig->num_ands; i++) {
        aiger_and a = aig->ands[i];
        if (! cadet_variable_exists(cadet, aiger_lit2var(a.lhs))){
            cadet_create_var(cadet, aiger_lit2var(a.lhs));
        }
    }
    
    ////// now: CLAUSES //////
    
    // clauses
    for (size_t i = 0; i < aig->num_ands; i++) {
        aiger_and a = aig->ands[i];
        assert(a.lhs % 2 == 0);
        // make sure all three symbols exist, create if necessary
        assert(cadet_variable_exists(cadet, aiger_lit2var(a.lhs)));
        assert(a.rhs0 < 2 || cadet_variable_exists(cadet, aiger_lit2var(a.rhs0)));
        assert(a.rhs0 < 2 || cadet_variable_exists(cadet, aiger_lit2var(a.rhs1)));
        
        // create and gate with with three clauses
        if (a.rhs0 != 1) {
            cadet_add_lit(cadet, - aiger_lit2lit(a.lhs));
            if (a.rhs0 != 0) {
                cadet_add_lit(cadet, aiger_lit2lit(a.rhs0));
            } // else lit is literally false
            cadet_add_lit(cadet, 0);
        } // else lit is true and thus clause is satisfied.
        
        if (a.rhs1 != 1) {
            cadet_add_lit(cadet, - aiger_lit2lit(a.lhs));
            if (a.rhs1 != 0) {
                cadet_add_lit(cadet, aiger_lit2lit(a.rhs1));
            } // else lit is literally false
            cadet_add_lit(cadet, 0);
        } // else lit is true and thus clause is satisfied.

        if (a.rhs0 != 0 && a.rhs1 != 0) {
            cadet_add_lit(cadet, aiger_lit2lit(a.lhs));
            if (a.rhs0 != 1) { // lit is literally false
                cadet_add_lit(cadet, - aiger_lit2lit(a.rhs0));
            }
            if (a.rhs1 != 1) { // lit is literally false
                cadet_add_lit(cadet, - aiger_lit2lit(a.rhs1));
            }
            cadet_add_lit(cadet, 0);
        }
    }
}

void cube_refinement_incremental_interface(CADET *cadet, aiger *aig) {
    MVar* implication_var = cadet_fresh_var(cadet);
    V1("Implication var is %d\n",implication_var->var_id);
    // add the trivial overapproximation of safe states (with the implication literal).
    //    cadet_add_lit(cadet, implication_var->var_id);
    //    cadet_add_lit(cadet, 0);
    
    // if antecedent is true, output must be false
    for (size_t i = 0; i < aig->num_outputs; i++) {
        aiger_symbol o = aig->outputs[i];
        // this output may never be true!
        if (o.lit != 0) {
            if (o.lit != 1) {
                assert(cadet_variable_exists(cadet, aiger_lit2var(o.lit)));
                cadet_add_lit(cadet, - aiger_lit2lit(o.lit));
            }
            cadet_add_lit(cadet, - implication_var->var_id);
            cadet_add_lit(cadet, 0);
        }
    }
    
    vector* refinements = vector_init(); // not really needed, mere convenience for later inspection/output
    vector* conjunction_vars = vector_init();
    
    size_t iterations = 0;
    
    while (true) {
        iterations++;
        V1("Iteration %zu\n", iterations);
        
        if (debug_verbosity >= VERBOSITY_HIGH) {
            matrix_print_debug(cadet->matrix);
        }
        
        cadet_push(cadet);
        
        // add closing clause
        for (unsigned i = 0; i < vector_count(conjunction_vars); i++) {
            MVar* c_var = vector_get(conjunction_vars, i);
            cadet_add_lit(cadet, c_var->var_id);
        }
        cadet_add_lit(cadet, implication_var->var_id);
        cadet_add_lit(cadet, 0);
        
        if (debug_verbosity >= VERBOSITY_HIGH) {
            matrix_print_debug(cadet->matrix);
        }
        
        //        char filename[100];
        //        sprintf(filename, "/Users/markus/work/cadet/tmp%zu.qdimacs", iterations);
        //        FILE* f = fopen(filename, "w");
        //        if (f != NULL) {
        //            matrix_print_qdimacs_file(cadet->matrix, f);
        //            fflush(f);
        //            fclose(f);
        //        }
        
        cadet_solve(cadet);
        
        if (cadet->result == CADET_RESULT_SAT) {
            break;
        }
        
        int_vector* refuting_assignment = int_vector_copy(cadet->refuting_assignment);
        vector_add(refinements, refuting_assignment);
        
        V1("Refining with cube:");
        // Initial state contained?
        bool initial_state_contained = true;
        for (unsigned i = 0; i < int_vector_count(refuting_assignment); i++) {
            int val = int_vector_get(refuting_assignment, i);
            if (aiger_is_latch(aig, 2 * (unsigned) abs(val))) {
                V1(" %d", val);
                initial_state_contained = initial_state_contained && val < 0;
            }
        }
        V1("\n");
        if (initial_state_contained) {
            assert(cadet->result == CADET_RESULT_UNSAT);
            break;
        }
        
        cadet_pop(cadet);
        assert(cadet->matrix->push_count == 0);
        
        if (debug_verbosity >= VERBOSITY_HIGH) {
            matrix_print_debug(cadet->matrix);
        }
        
        // strengthen the right side of the implication
        bool clause_true = false;
        for (unsigned i = 0; i < int_vector_count(refuting_assignment); i++) {
            int lit = int_vector_get(refuting_assignment, i);
            aiger_symbol* latch = aiger_is_latch(aig, 2 * (unsigned) abs(lit));
            if (latch) {
                if (latch->next == 1) {
                    // add the dijunct FALSE, so do nothing
                } else if (latch->next == 0) {
                    // add the disjunct TRUE, so cancel the creation of this clause
                    abort(); // should not happen, otherwise we may not terminate
                    clause_true = true;
                    cadet_cancel_current_clause(cadet);
                } else {
                    cadet_add_lit(cadet, - (lit>0 ? 1 : -1) * aiger_lit2lit(latch->next));
                }
            }
        }
        if ( ! clause_true) {
            cadet_add_lit(cadet, - implication_var->var_id);
            cadet_add_lit(cadet, 0);
        }
        
        // create the conjunction by which we weaken the left side of the implication
        MVar* conjunction_var = cadet_fresh_var(cadet);
        vector_add(conjunction_vars, conjunction_var);
        for (unsigned i = 0; i < int_vector_count(refuting_assignment); i++) {
            int lit = int_vector_get(refuting_assignment, i);
            if (aiger_is_latch(aig, 2 * (unsigned) abs(lit))) {
                cadet_add_lit(cadet, lit);
                cadet_add_lit(cadet, - conjunction_var->var_id);
                cadet_add_lit(cadet, 0);
            }
        }
        for (unsigned i = 0; i < int_vector_count(refuting_assignment); i++) {
            int lit = int_vector_get(refuting_assignment, i);
            if (aiger_is_latch(aig, 2 * (unsigned) abs(lit))) {
                cadet_add_lit(cadet, - lit);
            }
        }
        cadet_add_lit(cadet, conjunction_var->var_id);
        cadet_add_lit(cadet, 0);
        
        
        if (debug_verbosity >= VERBOSITY_HIGH) {
            matrix_print_debug(cadet->matrix);
        }
        
        // the static part of the weakening
        cadet_add_lit(cadet, - conjunction_var->var_id);
        cadet_add_lit(cadet, - implication_var->var_id);
        cadet_add_lit(cadet, 0);
    }
    V0("Took %zu iterations\n", iterations);
}


void cube_refinement_direct(CADET *cadet, aiger *aig) {
    
    // Assert that the error output is false.
    // Just asserting the negated outputs can lead to an error, if the output is a latch (because it is universally quantified).
    // The helper var makes sure that universal variables in the clause are not eliminated by universal reduction.
    MVar* helper_var = cadet_fresh_var(cadet);
    V1("Helper var is %d\n",helper_var->var_id);
    cadet_add_lit(cadet, - helper_var->var_id);
    cadet_add_lit(cadet, 0);
    for (size_t i = 0; i < aig->num_outputs; i++) {
        aiger_symbol o = aig->outputs[i];
        // this output may never be true!
        if (o.lit != 0) {
            if (o.lit != 1) {
                assert(cadet_variable_exists(cadet, aiger_lit2var(o.lit)));
                cadet_add_lit(cadet, - aiger_lit2lit(o.lit));
            }
            cadet_add_lit(cadet, helper_var->var_id);
            cadet_add_lit(cadet, 0);
        }
    }
    
    vector* refinements = vector_init(); // not really needed, mere convenience for later inspection/output
    
    size_t iterations = 0;
    
    while (true) {
        iterations++;
        V1("Iteration %zu\n", iterations);
        
        if (debug_verbosity >= VERBOSITY_HIGH) {
            matrix_print_debug(cadet->matrix);
        }
        
        cadet_push(cadet);
        cadet_solve(cadet);
        
        if (cadet->result == CADET_RESULT_SAT) {
            break;
        }
        
        int_vector* refuting_assignment = int_vector_copy(cadet->refuting_assignment);
        vector_add(refinements, refuting_assignment);
        
        V1("Refining with cube:");
        // Initial state contained?
        bool initial_state_contained = true;
        for (unsigned i = 0; i < int_vector_count(refuting_assignment); i++) {
            int val = int_vector_get(refuting_assignment, i);
            if (aiger_is_latch(aig, 2 * (unsigned) abs(val))) {
                V1(" %d", val);
                initial_state_contained = initial_state_contained && val < 0;
            }
        }
        V1("\n");
        if (initial_state_contained) {
            assert(cadet->result == CADET_RESULT_UNSAT);
            break;
        }
        
        cadet_pop(cadet);
        
        // strengthen the right side of the implication
        bool clause_true = false;
        for (unsigned i = 0; i < int_vector_count(refuting_assignment); i++) {
            int lit = int_vector_get(refuting_assignment, i);
            satsolver_add(cadet->skolem, - lit);
            aiger_symbol* latch = aiger_is_latch(aig, 2 * (unsigned) abs(lit));
            if (latch) {
                if (latch->next == 1) {
                    // add the dijunct FALSE, so do nothing
                } else if (latch->next == 0) {
                    // add the disjunct TRUE, so cancel the creation of this clause
                    abort(); // should not happen, otherwise we may not terminate
                    clause_true = true;
                    cadet_cancel_current_clause(cadet);
                } else {
                    cadet_add_lit(cadet, - (lit>0 ? 1 : -1) * aiger_lit2lit(latch->next));
                }
            }
        }
        if ( ! clause_true) {
            cadet_add_lit(cadet, helper_var->var_id); // need of helper var explained above. Think of latches depending on other latches. 
            cadet_add_lit(cadet, 0);
            satsolver_add(cadet->skolem, 0);
        }
    }
    V0("Took %zu iterations\n", iterations);
}

int reactive(FILE* file, Options* options) {
    aiger* aig = aiger_init();
//    V0("Reading\n");
    const char* err = aiger_read_from_file(aig, file);
    if (err != NULL) {
        V0("Error occurred while reading AIGER file:\n%s\n", err);
        return 1;
    }
    
    assert(aig->num_bad == 0);
    assert(aig->num_constraints == 0);
    assert(aig->num_justice == 0);
    assert(aig->num_fairness == 0);
    
    CADET* cadet = cadet_init();
    free(cadet->options);
    cadet->options = options;
    transition_relation_from_aiger(cadet, aig);
    
//    cube_refinement_incremental_interface(cadet, aig);
    cube_refinement_direct(cadet, aig);
    
    V0("%s\n", cadet->result == CADET_RESULT_SAT ? "REALIZABLE" : (cadet->result == CADET_RESULT_UNSAT ? "UNREALIZABLE" : "UNKNOWN"));
    
    if (cadet->result == CADET_RESULT_SAT && cadet->options->certify_SAT) {
        aiger* certificate = synthesis_certificate(aig, cadet->matrix, options);
//        aiger* certificate = safety_game_implementation(aig, cadet->matrix, options);
        V0("Certificate has %u gates.\n", certificate->num_ands);
        FILE* certificate_file = fopen(options->certificate_file_name, "w");
        if (!certificate_file) {
            V0("Error: Cannot open file \"%s\" to write to.\n", options->certificate_file_name);
        } else {
            V0("Writing certificate to file \"%s\".\n", options->certificate_file_name);
            aiger_write_to_file(certificate, options->certificate_aiger_mode, certificate_file);
            fclose(certificate_file);
        }
        free(certificate); // TODO: cannot free the aiger-internal objects?!
    }
    
    return cadet->result;
}
