//
//  certify.c
//  cadet
//
//  Created by Markus Rabe on 21/09/16.
//  Copyright © 2016 Saarland University. All rights reserved.
//

#include "certify.h"
#include "c2_validate.h"
#include "aiger.h"
#include "aiger_utils.h"
#include "log.h"
#include "casesplits.h"
#include "satsolver.h"
#include "util.h"

#include <string.h>

#define AIGERLIT_UNDEFINED INT_MAX
#define QUANTIFIER_ELIMINATION_OUTPUT_STRING "There is an assignment to the existentials"

void cert_write_aiger(aiger* a, Options* o) {
    const char* filename = o->certificate_file_name;
    
    const char* err = aiger_check(a);
    abortif(err, "%s", err);
    
    int write_success = 0;
    if (!filename || strcmp(filename, "stdout") == 0) {
        write_success = aiger_write_to_file(a, aiger_ascii_mode, stdout);
    } else {
        write_success = aiger_open_and_write_to_file(a, filename);
        
    }
    abortif(!write_success, "Could not write to file for aiger certificate (file name '%s').", filename);
    V1("Wrote AIG certificate with %u gates to %s\n", a->num_ands, filename);
}

aiger* cert_setup_AIG(QCNF* qcnf) {
    aiger* a = aiger_init();
    
    // taking the logarithm of the maximum var_id
    int log_of_var_num = 0;
    unsigned var_num_copy = var_vector_count(qcnf->vars);
    while (var_num_copy >>= 1) log_of_var_num++;
    
    // Mark universal variables as inputs
    for (unsigned i = 0; i < var_vector_count(qcnf->vars); i++) {
        if (qcnf_var_exists(qcnf, i) && qcnf_is_original(qcnf, i)) {
            if (qcnf_is_universal(qcnf, i)) {
                char* name = malloc(sizeof(char) * (size_t) log_of_var_num + 2);
                sprintf(name, "%d", i);
                aiger_add_input(a, var2aigerlit(i), name);
                free(name);
            }
        }
    }
    return a;
}

unsigned lit2aigerlit(Lit lit) {
    assert(lit != 0);
    unsigned val = lit>0 ? 0 : 1;
    return (2*lit_to_var(lit)) + val;
}

void cert_propositional_AIG_certificate_SAT(QCNF* qcnf, Options* o, void* domain, int (*get_value)(void* domain, Lit lit)) {
    aiger* a = cert_setup_AIG(qcnf);
    for (unsigned var_id = 1; var_id < var_vector_count(qcnf->vars); var_id++) {
        if (qcnf_var_exists(qcnf, var_id)) {
            Var* v = var_vector_get(qcnf->vars, var_id);
            if (v->is_universal || ! v->original) {
                continue;
            }
            int val = get_value(domain, (Lit) var_id);
            if (val == 0) {val = 1;}
            unsigned aigerval = val > 0 ? 1 : 0; // true is 1,  false is 0
            aiger_add_and(a, var2aigerlit(var_id), aigerval, aigerval);
        }
    }
    cert_write_aiger(a, o);
    aiger_reset(a);
}

// aigerlits contains the CURRENT
unsigned mapped_lit2aigerlit(int_vector* aigerlits, Lit lit) {
    assert(lit != 0);
    unsigned var_id = lit_to_var(lit);
    unsigned aigerlit = (unsigned) int_vector_get(aigerlits, var_id);
    assert(aigerlit != AIGERLIT_UNDEFINED);
    if (lit < 0) {
        aigerlit = negate(aigerlit);
    }
    return aigerlit;
}


Lit cert_get_unique_consequence(int_vector* ucs, Clause* c) {
    if (int_vector_count(ucs) > c->clause_idx) {
        return int_vector_get(ucs, c->clause_idx);
    }
    return 0;
}


void cert_encode_unique_antecedents(QCNF* qcnf, aiger* a, int_vector* aigerlits, int_vector* unique_consequences, unsigned *max_sym, Lit lit) {
    assert(lit);
    unsigned var_id = lit_to_var(lit);
    
    // encode all the antecedents
    int_vector* antecedent_aigerlits = int_vector_init();
    vector* occs = qcnf_get_occs_of_lit(qcnf, lit);
    for (unsigned i = 0; i < vector_count(occs); i++) {
        Clause* c = vector_get(occs, i);
        if (c->is_cube) {
            continue;
        }
        if (cert_get_unique_consequence(unique_consequences, c) == lit) {
            // encode the antecedent
            unsigned antecedent = aiger_true; // empty conjunction is true
            for (unsigned j = 0; j < c->size; j++) {
                Lit clause_lit = c->occs[j];
                if (clause_lit != lit) { // != unique_consequence
                    unsigned clause_aigerlit = mapped_lit2aigerlit(aigerlits, clause_lit);
                    antecedent = aigeru_AND(a, max_sym, antecedent, negate(clause_aigerlit));
                }
            }
            int_vector_add(antecedent_aigerlits, (int) antecedent);
        }
    }
    assert(int_vector_get(aigerlits, var_id) == AIGERLIT_UNDEFINED);  // variable should not be defined twice; using 0 as the default
    unsigned aigerlit_for_lit = aigeru_multiOR(a, max_sym, antecedent_aigerlits);
    V3("Lit %d assigned aigerlit %u\n", lit, aigerlit_for_lit);
    if (lit < 0) {
        aigerlit_for_lit = negate(aigerlit_for_lit);
    }
    int_vector_set(aigerlits, var_id, (int) aigerlit_for_lit);
    int_vector_free(antecedent_aigerlits);
}


bool cert_is_dlvl_zero_var(Skolem* skolem, unsigned var_id) {
    return (skolem_is_deterministic(skolem, var_id) && skolem_get_decision_lvl(skolem, var_id) == 0);
}


// Returns an aiger lit that is true iff the cube is satisfied.
unsigned cert_encode_c2_cube(C2* c2, aiger* a, unsigned *max_sym, int_vector* aigerlits, int_vector* cube) {
    int_vector* cube_aigerlits = int_vector_init();
    for (unsigned i = 0; i < int_vector_count(cube); i++) {
        Lit l = int_vector_get(cube, i);
        assert(skolem_get_decision_lvl(c2->skolem, lit_to_var(l)) == 0); // Currently restricted to dlvl0 cubes
        int_vector_add(cube_aigerlits, (int) mapped_lit2aigerlit(aigerlits, l));
    }
    unsigned outputlit = inc(max_sym);
    aigeru_add_multiAND(a, max_sym, outputlit, cube_aigerlits);
    int_vector_free(cube_aigerlits);
    return outputlit;
}


unsigned cert_encode_CEGAR(Skolem* skolem, aiger* a, unsigned *max_sym, int_vector* aigerlits, Case* c) {
    assert(c->type == 0);  // encodes a function
    assert(c->universal_assumptions != NULL);
    
    // Certificate all remaining cases by writing out the unique consequences of the dlvl>0 variables
    for (unsigned i = 0; i < int_vector_count(c->determinization_order); i++) {
        Lit decision_lit = int_vector_get(c->determinization_order, i);
        assert(decision_lit != 0);
        unsigned var_id = lit_to_var(decision_lit);
        if (! qcnf_var_exists(skolem->qcnf, var_id)) {   //  || cert_is_dlvl_zero_var(c2, var_id) // not skipping dlvl0 variables as variables can move into dlvl0 after this case was finished
            //            assert(!int_vector_contains_sorted(c->potentially_conflicted_variables, (int) var_id));
            continue;
        }
        if (! cert_is_dlvl_zero_var(skolem, var_id)) {
            assert(!qcnf_is_universal(skolem->qcnf, var_id));
            int_vector_set(aigerlits, var_id, decision_lit > 0 ? aiger_true : aiger_false);
        }
    }
    
    unsigned case_is_valid = aiger_true;
    for (unsigned i = 0; i < int_vector_count(c->universal_assumptions); i++) {
        Lit assumption = int_vector_get(c->universal_assumptions, i);
        unsigned assumption_aigerlit = mapped_lit2aigerlit(aigerlits, assumption);
        case_is_valid = aigeru_AND(a, max_sym, case_is_valid, assumption_aigerlit);
    }
    return case_is_valid;
}

unsigned cert_encode_conflicts(Skolem* skolem, aiger* a, unsigned *max_sym, int_vector* aigerlits,
                               int_vector* decisions,
                               int_vector* potentially_conflicted_variables,
                               int_vector* unique_consequences) {
    
    unsigned conflict = aiger_false;
    
    int_vector_sort(potentially_conflicted_variables, compare_integers_natural_order); // to enable logarithmic lookup
    
    for (unsigned i = 0; i < int_vector_count(decisions); i++) {
        Lit decision_lit = int_vector_get(decisions, i);
        assert(decision_lit != 0);
        unsigned var_id = lit_to_var(decision_lit);
        if (int_vector_contains_sorted(potentially_conflicted_variables, (int) var_id)) {
            int polarity = decision_lit > 0 ? 1 : -1;
            assert(qcnf_var_exists(skolem->qcnf, var_id));
            
            // temporarily clear aigerlit to encode the other side
            unsigned aigerlit = (unsigned) int_vector_get(aigerlits, var_id);
            assert(aigerlit != AIGERLIT_UNDEFINED);
            int_vector_set(aigerlits, var_id, AIGERLIT_UNDEFINED);
            
            // encode other side
            cert_encode_unique_antecedents(skolem->qcnf, a, aigerlits, unique_consequences, max_sym, polarity * (Lit) var_id);
            
            // encode conflict
            unsigned anti_aigerlit = (unsigned) int_vector_get(aigerlits, var_id);
            unsigned conflict_aigerlit = aigeru_AND(a, max_sym,
                                                    polarity > 0 ? negate(aigerlit) : aigerlit,
                                                    polarity > 0 ? anti_aigerlit : negate(anti_aigerlit));
            conflict = aigeru_OR(a, max_sym, conflict, conflict_aigerlit);
            
            // reset the aigerlit to original value
            int_vector_set(aigerlits, var_id, (int) aigerlit);
        }
    }
    return conflict;
}

// Certify all vars with dlvl>0 by writing out the unique consequences in the correct order
void cert_encode_function_for_case(Skolem* skolem, aiger* a, unsigned *max_sym,
                                   int_vector* aigerlits,
                                   int_vector* decisions,
                                   int_vector* unique_consequences) {
    if (debug_verbosity >= VERBOSITY_MEDIUM) {V2("Decision order: "); int_vector_print(decisions); V2("\n");}
    for (unsigned i = 0; i < int_vector_count(decisions); i++) {
        Lit decision_lit = int_vector_get(decisions, i);
        assert(decision_lit != 0);
        unsigned var_id = lit_to_var(decision_lit);
        if (! qcnf_var_exists(skolem->qcnf, var_id)) {   //  || cert_is_dlvl_zero_var(c2, var_id) // not skipping dlvl0 variables as variables can move into dlvl0 after this case was finished
            continue;
        }
        if (int_vector_get(aigerlits, var_id) == AIGERLIT_UNDEFINED) {
            assert(!qcnf_is_universal(skolem->qcnf, var_id));
            cert_encode_unique_antecedents(skolem->qcnf, a, aigerlits, unique_consequences, max_sym, - decision_lit);
        }
    }
}


unsigned cert_dlvl0_definitions(aiger* a, int_vector* aigerlits, Skolem* skolem, unsigned* max_sym) {
    int_vector* decision_sequence = case_splits_determinization_order_with_polarities(skolem);
    cert_encode_function_for_case(skolem, a, max_sym, aigerlits, decision_sequence,
                                  skolem->unique_consequence);
    
    if (skolem->options->quantifier_elimination) {
        unsigned res = cert_encode_conflicts(skolem, a, max_sym, aigerlits, decision_sequence,
                                             skolem->potentially_conflicted_variables,
                                             skolem->unique_consequence);
        int_vector_free(decision_sequence);
        return res;
    } else {
        return aiger_false;
    }
}


static void cert_define_aiger_outputs(Skolem* skolem, aiger* a, int_vector* aigerlits) {
    for (unsigned i = 0; i < var_vector_count(skolem->qcnf->vars); i++) {
        if (qcnf_var_exists(skolem->qcnf, i)
            && qcnf_is_original(skolem->qcnf, i)
            && qcnf_is_existential(skolem->qcnf, i)) {
            
            char* output_name = NULL;
            unsigned name_size = 2; // for \0, one reserve
            if (skolem->options->certificate_type == QAIGER) {
                char* var_name = qcnf_get_variable_name(skolem->qcnf, i);
                if (var_name) {
                    name_size += strlen(var_name);
                    output_name = malloc(sizeof(char) * (size_t) name_size);
                    sprintf(output_name, "%s", var_name);
                    unsigned al = (unsigned) int_vector_get(aigerlits, i);
                    aiger_add_output(a, al, output_name);
                    free(output_name);
                }
            } else {
                name_size += discrete_logarithm(var_vector_count(skolem->qcnf->vars));
                output_name = malloc(sizeof(char) * (size_t) name_size);
                sprintf(output_name, "%u", i);
                unsigned al = (unsigned) int_vector_get(aigerlits, i);
                aiger_add_output(a, al, output_name);
                free(output_name);
            }
        }
    }
    
    // From the CAQECERT readme: "There is one additional output which must be the last output and it indicates whether the certificate is a Skolem or Herbrand certificate (value 1 and 0, respectively)."
    if (skolem->options->certificate_type == CAQECERT) {
        aiger_add_output(a, 1, "result");
    }
}


static void cert_define_aiger_inputs(aiger *a, int_vector *aigerlits, Skolem* skolem) {
    for (unsigned i = 0; i < var_vector_count(skolem->qcnf->vars); i++) {
        if (qcnf_var_exists(skolem->qcnf, i)
            && qcnf_is_original(skolem->qcnf, i)
            && qcnf_is_universal(skolem->qcnf, i)) {
            
            unsigned al = var2aigerlit(i);
            int_vector_set(aigerlits, i, (int) al);
            char* input_name = NULL;
            unsigned name_size = 2; // for \0, one reserve
            if (skolem->options->certificate_type == QAIGER) {
                char* var_name = qcnf_get_variable_name(skolem->qcnf, i);
                if (var_name) {
                    name_size += strlen(var_name);
                    input_name = malloc(sizeof(char) * (size_t) name_size);
                    sprintf(input_name, "%s", var_name);
                    aiger_add_input(a, al, input_name);
                    free(input_name);
                }
            } else {
                name_size += discrete_logarithm(var_vector_count(skolem->qcnf->vars));
                input_name = malloc(sizeof(char) * (size_t) name_size);
                sprintf(input_name, "%u", i);
                aiger_add_input(a, al, input_name);
                free(input_name);
            }
        }
    }
}


// Assumes c2 to be in SAT state and that dlvl 0 is fully propagated; and that dlvl is not propagated depending on restrictions to universals (i.e. after completed case_splits)
void c2_write_AIG_certificate(C2* c2) {
    abortif(c2->state != C2_SAT, "Can only generate certificate in SAT state.");
    abortif(int_vector_count(c2->skolem->universals_assumptions) > 0, "Current state of C2 must not depend on universal assumptions");
    
    Skolem* skolem_dlvl0 = skolem_init(c2->qcnf, c2->options);
    skolem_dlvl0->record_conflicts = true;
    skolem_propagate(skolem_dlvl0);
    
    aiger* a = aiger_init();
    
    // map from var_id to the current aiger_lit representing it
    int_vector* aigerlits = int_vector_init();
    for (unsigned i = 0 ; i < var_vector_count(c2->qcnf->vars); i++) {int_vector_add(aigerlits, AIGERLIT_UNDEFINED);}
    
    cert_define_aiger_inputs(a, aigerlits, skolem_dlvl0);
    
    if (skolem_is_conflicted(skolem_dlvl0)) { // constants conflicts on dlvl0 in functional synthesis mode ...
        assert(c2->options->functional_synthesis);
        assert(skolem_dlvl0->state == SKOLEM_STATE_CONSTANTS_CONLICT);
        if (c2->options->quantifier_elimination) {
            aiger_add_output(a, aiger_false, QUANTIFIER_ELIMINATION_OUTPUT_STRING);
        } else {
            for (unsigned i = 0 ; i < var_vector_count(c2->qcnf->vars); i++) {
                if (qcnf_var_exists(c2->qcnf, i)
                    && qcnf_is_original(c2->qcnf, i)
                    && qcnf_is_existential(c2->qcnf, i)) {
                    
                    int_vector_set(aigerlits, i, aiger_false);
                }
            }
            cert_define_aiger_outputs(skolem_dlvl0, a, aigerlits);
        }
        cert_write_aiger(a, c2->options);
        
        int_vector_free(aigerlits);
        skolem_free(skolem_dlvl0);
        aiger_reset(a);
        return;
    }
    
    unsigned max_sym = var2aigerlit(a->maxvar);
    assert(c2->options->certificate_type != QBFCERT || max_sym == var2aigerlit(a->maxvar + 1));
    
    // Certificate for the dlvl0 variables
    unsigned dlvl0_conflict_aigerlit = cert_dlvl0_definitions(a, aigerlits, skolem_dlvl0, &max_sym);
    
    // The following data structures remember all the aigerlits for all cases; dlvl0 vars are only remembered once
    vector* case_aigerlits = vector_init(); // stores for every variable an int_vector of aigerlits for the different cases
    for (unsigned i = 0 ; i < var_vector_count(c2->qcnf->vars); i++) {
        int_vector* var_aigerlits = int_vector_init();
        vector_add(case_aigerlits, var_aigerlits);
        if (qcnf_var_exists(c2->qcnf, i) && cert_is_dlvl_zero_var(skolem_dlvl0, i)) {
            unsigned curlit = (unsigned) int_vector_get(aigerlits, i);
            assert(curlit != AIGERLIT_UNDEFINED);
            int_vector_add(var_aigerlits, (int) curlit);
        }
    }
    int_vector* case_selectors = int_vector_init(); // aiger literals that indicate which cases apply
    
    // For every case, encode the function in a new set of symbols and connnect to the existing symbols with a MUX
    assert(vector_count(c2->cs->closed_cases) > 0);
    for (unsigned case_idx = 0; case_idx < vector_count(c2->cs->closed_cases); case_idx++) {
        unsigned case_applies = AIGERLIT_UNDEFINED;
        Case* c = vector_get(c2->cs->closed_cases, case_idx);
        if (c->type == 0) {  // CEGAR assignment
            case_applies = cert_encode_CEGAR(skolem_dlvl0, a, &max_sym, aigerlits, c);
        } else {  // certificate is an actual function, closed case split
            cert_encode_function_for_case(skolem_dlvl0, a, &max_sym, aigerlits,
                                          c->determinization_order, c->unique_consequences);
            case_applies = negate(cert_encode_conflicts(skolem_dlvl0, a, &max_sym, aigerlits,
                                                        c->determinization_order,
                                                        c->potentially_conflicted_variables,
                                                        c->unique_consequences));
        }
        abortif(!c2->options->functional_synthesis && ! c2->options->cegar && case_applies == aiger_false, "This case does not contribute.");
        
//        // Adding auxiliary outputs to the circuit to simplify debugging.
//        // These outputs violate output standards, so do not use otherwise.
//        char* s = malloc(sizeof(char) * 100);
//        sprintf(s, "case %u", case_idx + 1);
//        aiger_add_output(a, case_applies, s);
//
//        for (unsigned var_id = 0; var_id < int_vector_count(aigerlits); var_id++) {
//            if (qcnf_var_exists(c2->qcnf, var_id) && ! cert_is_dlvl_zero_var(c2, var_id)) {
//                unsigned l = (unsigned) int_vector_get(aigerlits, var_id);
//                char* s2 = malloc(sizeof(char) * 100);
//                sprintf(s2, "%u-%u", var_id, case_idx + 1);
//                aiger_add_output(a, l, s2);
//            }
//        }
        
        int_vector_add(case_selectors, (int) case_applies);
        for (unsigned var_id = 0; var_id < int_vector_count(aigerlits); var_id++) {
            if (qcnf_var_exists(c2->qcnf, var_id) && ! cert_is_dlvl_zero_var(skolem_dlvl0, var_id)) {
                unsigned aigerlit = (unsigned) int_vector_get(aigerlits, var_id);
                assert(aigerlit != AIGERLIT_UNDEFINED);
                int_vector* aigerlits_for_var = vector_get(case_aigerlits, var_id);
                int_vector_add(aigerlits_for_var, (int) aigerlit);
                int_vector_set(aigerlits, var_id, AIGERLIT_UNDEFINED);
            }
        }
    }
    
    bool valid = false;
    if (c2->options->quantifier_elimination) {
        // This is the quantifier elimination certificate.
        // There are three ways the resulting formula can evaluate to false:
        
        // (1) Conflict in dlvl0 variables
        // -- nothing to be done
        
        // (2) None of the cases applies
        unsigned some_case_applies = aiger_false;
        for (unsigned i = 0; i < int_vector_count(case_selectors); i++) {
            unsigned sel = (unsigned) int_vector_get(case_selectors, i);
            some_case_applies = aigeru_OR(a, &max_sym, some_case_applies, sel);
        }
        
        // (3) One of the clauses with only universal variables applies
        unsigned some_universal_violated = aiger_false;
        for (unsigned i = 0; i < int_vector_count(c2->qcnf->universal_clauses); i++) {
            unsigned universal_clause_idx = (unsigned) int_vector_get(c2->qcnf->universal_clauses, i);
            Clause* c = vector_get(c2->qcnf->all_clauses, universal_clause_idx);
            assert(c->universal_clause);
            unsigned clause_satisfied = aiger_false;
            for (unsigned j = 0; j < c->size; j++) {
                Lit l = c->occs[j];
                assert(qcnf_is_universal(c2->qcnf, lit_to_var(l)));
                unsigned al = mapped_lit2aigerlit(aigerlits, l); // universals have unique aigerlits throughout all cases
                clause_satisfied = aigeru_OR(a, &max_sym, clause_satisfied, al);
            }
            some_universal_violated = aigeru_OR(a, &max_sym, some_universal_violated, negate(clause_satisfied));
        }
        
        unsigned projection = aigeru_AND(a, &max_sym, some_case_applies, negate(some_universal_violated));
        projection = aigeru_AND(a, &max_sym, projection, negate(dlvl0_conflict_aigerlit));
        aiger_add_output(a, projection, QUANTIFIER_ELIMINATION_OUTPUT_STRING);
        
        if (c2->options->verify) {
            valid = cert_validate_quantifier_elimination(a, c2->qcnf, aigerlits, projection);
        } else {
            valid = true;
        }
    } else { // Create function
        int_vector* out_aigerlits = int_vector_copy(aigerlits);
        for (unsigned var_id = 0; var_id < vector_count(case_aigerlits); var_id++) {
            if (! qcnf_var_exists(c2->qcnf, var_id) || cert_is_dlvl_zero_var(skolem_dlvl0, var_id)) {
                continue;
            }
            int_vector* aigerlits_for_var = vector_get(case_aigerlits, var_id);
            unsigned num = int_vector_count(aigerlits_for_var);
            assert(num == 1 || num == int_vector_count(case_selectors));
            unsigned outlit_for_var = AIGERLIT_UNDEFINED;
            if (num == 1) {
                outlit_for_var = (unsigned) int_vector_get(aigerlits_for_var, 0);
            } else {
                outlit_for_var = aigeru_multiMUX(a, &max_sym, case_selectors, aigerlits_for_var);
            }
            int_vector_set(out_aigerlits, var_id, (int) outlit_for_var);
            int_vector_free(aigerlits_for_var);
            vector_set(case_aigerlits, var_id, NULL);
        }
        
        cert_define_aiger_outputs(skolem_dlvl0, a, out_aigerlits);
        
        if (!c2->options->verify) {
            valid = true;
        } else if (!c2->options->functional_synthesis) {
            valid = cert_validate_skolem_function(a, c2->qcnf, out_aigerlits, case_selectors);
        } else {
            valid = cert_validate_functional_synthesis(a, c2->qcnf, out_aigerlits, case_selectors);
        }
        
        int_vector_free(out_aigerlits);
    }
    cert_write_aiger(a, c2->options);
    
    abortif(!valid, "Validation of certificate invalid!");
    
    int_vector_free(aigerlits);
    vector_free(case_aigerlits);
    int_vector_free(case_selectors);
    skolem_free(skolem_dlvl0);
    aiger_reset(a);
}
