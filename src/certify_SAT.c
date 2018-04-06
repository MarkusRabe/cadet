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

void cert_write_aiger(aiger* a, Options* o) {
    const char* filename = o->certificate_file_name;
    // From the CAQECERT readme: "There is one additional output which must be the last output and it indicates whether the certificate is a Skolem or Herbrand certificate (value 1 and 0, respectively)."
    if (o->certificate_type == CAQECERT) {
        aiger_add_output(a, 1, "result");
    }
    
    const char* err = aiger_check(a);
    abortif(err, "%s", err);
    
    int write_success = 0;
    if (!filename || strcmp(filename, "stdout") == 0) {
        write_success = aiger_write_to_file(a, aiger_ascii_mode, stdout);
        
    } else {
        write_success = aiger_open_and_write_to_file(a, filename);
        
    }
    abortif(!write_success, "Could not write to file for aiger certificate (file name '%s').", filename);
    V1("Wrote AIG certificate to %s\n", filename);
}

aiger* cert_setup_AIG(QCNF* qcnf, Options* o) {
    aiger* a = aiger_init();
    
    // taking the logarithm of the maximum var_id
    int log_of_var_num = 0;
    unsigned var_num_copy = var_vector_count(qcnf->vars);
    while (var_num_copy >>= 1) log_of_var_num++;
    
    // Mark universal variables as inputs
    for (unsigned i = 0; i < var_vector_count(qcnf->vars); i++) {
        if (qcnf_var_exists(qcnf, i) && qcnf_is_original(qcnf, i)) {
            char* name = malloc(sizeof(char) * (size_t) log_of_var_num + 2);
            sprintf(name, "%d", i);
            if (qcnf_is_universal(qcnf, i)) {
                aiger_add_input(a, var2aigerlit(i), name);
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
    aiger* a = cert_setup_AIG(qcnf, o);
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


void cert_encode_unique_antecedents(C2* c2, aiger* a, int_vector* aigerlits, int_vector* unique_consequences, unsigned *max_sym, Lit lit) {
    assert(lit);
    unsigned var_id = lit_to_var(lit);
    
    // encode all the antecedents
    int_vector* antecedent_aigerlits = int_vector_init();
    vector* occs = qcnf_get_occs_of_lit(c2->qcnf, lit);
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
            
            // DEBUG
//            char* s = malloc(sizeof(char) * (size_t) 100);
//            sprintf(s, "clause %u", c->clause_idx);
//            aiger_add_output(a, antecedent, s);
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


bool cert_is_dlvl_zero_var(C2* c2, unsigned var_id) {
    return (skolem_is_deterministic(c2->skolem, var_id) && skolem_get_decision_lvl(c2->skolem, var_id) == 0);
}


//// Connect the copies of the signals for dlvl>0 variables with MUXs.
//// Variable case_selector is the condtition of the MUXs of this case.
//void cert_encode_new_aigerlits_for_case(C2* c2, aiger* a, unsigned* max_sym, unsigned case_selector, int_vector* aigerlits, int_vector* out_aigerlits) {
//    for (unsigned var_id = 0; var_id < var_vector_count(c2->qcnf->vars); var_id++) {
//        if (! qcnf_var_exists(c2->qcnf, var_id) || cert_is_dlvl_zero_var(c2, var_id)) {
//            continue;
//        }
//        unsigned aigerlit = (unsigned) int_vector_get(aigerlits, var_id);
//        unsigned old_aigerlit = (unsigned) int_vector_get(out_aigerlits, var_id);
//        unsigned new_aigerlit = aigeru_MUX(a, max_sym, case_selector, aigerlit, old_aigerlit);
//        int_vector_set(out_aigerlits, var_id, (int) new_aigerlit);
//    }
//}


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


unsigned cert_encode_CEGAR(C2* c2, aiger* a, unsigned *max_sym, int_vector* aigerlits, Case* c) {
    assert(c->type == 0);  // encodes a function
    assert(c->universal_assumptions != NULL);
    
    // Certificate all remaining cases by writing out the unique consequences of the dlvl>0 variables
    for (unsigned i = 0; i < int_vector_count(c->determinization_order); i++) {
        Lit decision_lit = int_vector_get(c->determinization_order, i);
        assert(decision_lit != 0);
        unsigned var_id = lit_to_var(decision_lit);
        if (! qcnf_var_exists(c2->qcnf, var_id)) {   //  || cert_is_dlvl_zero_var(c2, var_id) // not skipping dlvl0 variables as variables can move into dlvl0 after this case was finished
            //            assert(!int_vector_contains_sorted(c->potentially_conflicted_variables, (int) var_id));
            continue;
        }
        if (! cert_is_dlvl_zero_var(c2, var_id)) {
            assert(!qcnf_is_universal(c2->qcnf, var_id));
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


unsigned cert_encode_case(C2* c2, aiger* a, unsigned *max_sym, int_vector* aigerlits, Case* c) {
    assert(c->type == 1);  // encodes a function
    unsigned case_is_valid = aiger_true;
    int_vector_sort(c->potentially_conflicted_variables, compare_integers_natural_order); // for faster lookup
    
    if (debug_verbosity >= VERBOSITY_MEDIUM) {
        V2("Determinization order: ")
        int_vector_print(c->determinization_order);
        V2("\n");
    }
    
    // Certify all vars with dlvl>0 by writing out the unique consequences in the correct order
    for (unsigned i = 0; i < int_vector_count(c->determinization_order); i++) {
        Lit decision_lit = int_vector_get(c->determinization_order, i);
        assert(decision_lit != 0);
        unsigned var_id = lit_to_var(decision_lit);
        if (! qcnf_var_exists(c2->qcnf, var_id)) {   //  || cert_is_dlvl_zero_var(c2, var_id) // not skipping dlvl0 variables as variables can move into dlvl0 after this case was finished
//            assert(!int_vector_contains_sorted(c->potentially_conflicted_variables, (int) var_id));
            continue;
        }
        if (! cert_is_dlvl_zero_var(c2, var_id)) {
            assert(!qcnf_is_universal(c2->qcnf, var_id));
            cert_encode_unique_antecedents(c2, a, aigerlits, c->unique_consequences, max_sym, - decision_lit);
        }
        
        if (int_vector_contains_sorted(c->potentially_conflicted_variables, (int) var_id)) {
            // encode other side as well for conflicted variables
            unsigned aigerlit = (unsigned) int_vector_get(aigerlits, var_id);
            int_vector_set(aigerlits, var_id, AIGERLIT_UNDEFINED);
            // encode the other side of the decision lit
            cert_encode_unique_antecedents(c2, a, aigerlits, c->unique_consequences, max_sym,   decision_lit);
            unsigned anti_aigerlit = (unsigned) int_vector_get(aigerlits, var_id);
            unsigned conflict_aigerlit = aigeru_AND(a, max_sym,
                                                    decision_lit > 0 ? negate(aigerlit) : aigerlit,
                                                    decision_lit > 0 ? anti_aigerlit : negate(anti_aigerlit));
            case_is_valid = aigeru_AND(a, max_sym, case_is_valid, negate(conflict_aigerlit));
            
            // reset the aigerlit to actual
            int_vector_set(aigerlits, var_id, (int) aigerlit);
        }
    }
    return case_is_valid;
}


void cert_validate_print_assignment(aiger* a, QCNF* qcnf, SATSolver* checker, int_vector* aigerlits, Lit truelit) {
    V0("Violating assignment to universals:");
    for (unsigned i = 0; i < var_vector_count(qcnf->vars); i++) {
        if (qcnf_var_exists(qcnf, i) && qcnf_is_universal(qcnf, i)) {
            unsigned al = mapped_lit2aigerlit(aigerlits, (Lit) i);
            int val = satsolver_deref(checker, aiger_lit2lit(al, truelit));
            V0(" %d", val * (int) i);
        }
    }
    V0("\n");
    
    V0("Violating assignment to existentials:");
    for (unsigned i = 0; i < var_vector_count(qcnf->vars); i++) {
        if (qcnf_var_exists(qcnf, i) && qcnf_is_existential(qcnf, i)) {
            unsigned al = mapped_lit2aigerlit(aigerlits, (Lit) i);
            int val = satsolver_deref(checker, aiger_lit2lit(al, truelit));
            V0(" %d", val * (int) i);
        }
    }
    V0("\n");
}


bool cert_validate(aiger* a, QCNF* qcnf, int_vector* aigerlits, int_vector* case_selectors) {
    V1("Validating Skolem function with %u gates.\n", a->num_ands);
    Stats* timer = statistics_init(1000);  // 1 ms resolution
    statistics_start_timer(timer);
    bool ret = true;
    
    SATSolver* checker = satsolver_init();
    satsolver_set_max_var(checker, (int) a->maxvar);
    
    int truelit = satsolver_inc_max_var(checker);
    satsolver_add(checker, truelit);
    satsolver_clause_finished(checker);
    
    for (unsigned i = 0; i < a->num_ands; i++) {
        aiger_and and = a->ands[i];
        
        satsolver_add(checker,   aiger_lit2lit(and.rhs0, truelit));
        satsolver_add(checker, - aiger_lit2lit(and.lhs, truelit));
        satsolver_clause_finished(checker);
        
        satsolver_add(checker,   aiger_lit2lit(and.rhs1, truelit));
        satsolver_add(checker, - aiger_lit2lit(and.lhs, truelit));
        satsolver_clause_finished(checker);
        
        satsolver_add(checker, - aiger_lit2lit(and.rhs0, truelit));
        satsolver_add(checker, - aiger_lit2lit(and.rhs1, truelit));
        satsolver_add(checker,   aiger_lit2lit(and.lhs, truelit));
        satsolver_clause_finished(checker);
    }
    
    assert(satsolver_sat(checker) == SATSOLVER_SAT);
    

    satsolver_push(checker);
    for (unsigned i = 0; i < int_vector_count(case_selectors); i++) {
        unsigned sel = (unsigned) int_vector_get(case_selectors, i);
        satsolver_add(checker, - aiger_lit2lit(sel, truelit));
        satsolver_clause_finished(checker);
    }
    if (satsolver_sat(checker) == SATSOLVER_SAT) {
        LOG_ERROR("Case distinction in the certificate is incomplete.");
        cert_validate_print_assignment(a, qcnf, checker, aigerlits, truelit);
        ret = false;
    }
    satsolver_pop(checker);
    
    
    // Encode big disjunction over the violation of the clauses
    Lit some_clause_violated = - truelit;
    for (unsigned i = 0; i < vector_count(qcnf->all_clauses); i++) {
        Clause* c = vector_get(qcnf->all_clauses, i);
        if (qcnf_is_original_clause(qcnf, c->clause_idx)) {
            Lit this_clause_violated = satsolver_inc_max_var(checker);
            for (unsigned j = 0; j < c->size; j++) {
                Lit lit = c->occs[j];
                unsigned var_id = lit_to_var(lit);
                unsigned al = mapped_lit2aigerlit(aigerlits, - lit);
                assert(! qcnf_is_universal(qcnf, var_id) || aiger_is_input(a, aiger_strip(al)));
                satsolver_add(checker, aiger_lit2lit(al, truelit));
                satsolver_add(checker, - this_clause_violated);
                satsolver_clause_finished(checker);
            }
            
            Lit next_some_clause_violated = satsolver_inc_max_var(checker);
            satsolver_add(checker, some_clause_violated);
            satsolver_add(checker, this_clause_violated);
            satsolver_add(checker, - next_some_clause_violated);
            satsolver_clause_finished(checker);
            
            some_clause_violated = next_some_clause_violated;
        }
    }
    
    assert(satsolver_sat(checker) == SATSOLVER_SAT);
    
    satsolver_add(checker, some_clause_violated);
    satsolver_clause_finished(checker);
    
    sat_res res = satsolver_sat(checker);
    statistics_stop_and_record_timer(timer);
    V1("Validation took %f s\n", timer->accumulated_value);
    if (res != SATSOLVER_UNSAT) {
        LOG_ERROR("Validation failed!");
        cert_validate_print_assignment(a, qcnf, checker, aigerlits, truelit);
    }
    statistics_free(timer);
    satsolver_free(checker);
    ret = ret && (res == SATSOLVER_UNSAT);
    return ret;
}


//void case_encode_cegar() {
//    assert(c->decisions);
//    unsigned cube_lit = cert_encode_c2_cube(c2, a, &max_sym, aigerlits, c->universal_assumptions);
//
//    for (unsigned j = 0; j < int_vector_count(c->decisions); j++) {
//        Lit l = int_vector_get(c->decisions, j);
//        unsigned var_id = lit_to_var(l);
//        if (skolem_is_deterministic(c2->skolem, var_id)
//            && skolem_get_decision_lvl(c2->skolem, var_id) == 0) {
//            // can happen if clauses were learnt that made additional variables deterministic in the meantime.
//            // Instead we could make the split of the certificate at the interface stored in the domain.
//            continue;
//        }
//        assert(  !skolem_is_deterministic(c2->skolem, var_id)
//               || skolem_get_decision_lvl(c2->skolem, var_id) > 0);
//        assert(l != 0);
//        unsigned aiger_val = l > 0 ? aiger_true : aiger_false;
//        unsigned aiger_lit = (unsigned) int_vector_get(aigerlits, var_id);
//        assert(aiger_lit != aiger_false);
//        assert(aiger_lit <= max_sym);
//        unsigned new_aiger_lit = inc(&max_sym);
//        int_vector_set(aigerlits, var_id, (int) new_aiger_lit);
//        aigeru_add_multiplexer(a, &max_sym, aiger_lit, cube_lit, aiger_val, new_aiger_lit);
//    }
//}


static void cert_dlvl0_definitions(aiger *a, int_vector *aigerlits, C2 *c2, unsigned int *max_sym) {
    for (unsigned i = 0; i < int_vector_count(c2->skolem->determinization_order); i++) {
        unsigned var_id = (unsigned) int_vector_get(c2->skolem->determinization_order, i);
        if (! qcnf_var_exists(c2->qcnf, var_id) || ! cert_is_dlvl_zero_var(c2, var_id) || qcnf_is_universal(c2->qcnf, var_id)) {
            continue;
        }
        int val = skolem_get_constant_value(c2->skolem, (Lit) var_id);
        if (val != 0) {
            unsigned aiger_constant = val > 0 ? aiger_true : aiger_false;
            int_vector_set(aigerlits, var_id, (int) aiger_constant);
        } else {
            skolem_var sv = skolem_get_info(c2->skolem, var_id);
            c2_validate_var(c2, var_id);
            abortif(skolem_get_decision_val(c2->skolem, var_id) != 0, "dlvl0 variable is marked as decision variable");
            int polarity = 1;
            if (sv.pure_pos) {
                polarity = 1;
            } else if (sv.pure_neg) {
                polarity = -1;
            } else {
                Var* v = var_vector_get(c2->qcnf->vars, var_id);
                bool pos_occs_smaller = vector_count(&v->pos_occs) < vector_count(&v->neg_occs);
                polarity = pos_occs_smaller ? 1 : -1;
            }
            cert_encode_unique_antecedents(c2, a, aigerlits, c2->skolem->unique_consequence, max_sym, polarity * (Lit) var_id);
        }
    }
}

static void cert_define_aiger_outputs(C2* c2, aiger* a, int_vector* aigerlits) {
    int log_of_var_num = discrete_logarithm(var_vector_count(c2->qcnf->vars));
    for (unsigned i = 0; i < var_vector_count(c2->qcnf->vars); i++) {
        if (qcnf_var_exists(c2->qcnf, i)
            && qcnf_is_original(c2->qcnf, i)
            && qcnf_is_existential(c2->qcnf, i)) {
            
            unsigned al = (unsigned) int_vector_get(aigerlits, i);
            char* name = malloc(sizeof(char) * (size_t) log_of_var_num + 2);
            if (c2->options->certificate_type == QAIGER) {
                sprintf(name, "2 %d", i);
            } else {
                sprintf(name, "%d", i);
            }
            aiger_add_output(a, al, name);
            
        }
    }
}


static void cert_define_aiger_inputs(aiger *a, int_vector *aigerlits, C2 *c2) {
    int log_of_var_num = discrete_logarithm(var_vector_count(c2->qcnf->vars));
    for (unsigned i = 0; i < var_vector_count(c2->qcnf->vars); i++) {
        if (qcnf_var_exists(c2->qcnf, i) && qcnf_is_original(c2->qcnf, i) && qcnf_is_universal(c2->qcnf, i)) {
            unsigned al = var2aigerlit(i);
            int_vector_set(aigerlits, i, (int) al);
            char* name = malloc(sizeof(char) * (size_t) log_of_var_num + 2);
            if (c2->options->certificate_type == QAIGER) {
                sprintf(name, "1 %d", i);
            } else {
                sprintf(name, "%d", i);
            }
            aiger_add_input(a, al, name);
            
//            } else { // existential
//                int_vector_set(aigerlits, i, (int) al);
//                char* name = malloc(sizeof(char) * (size_t) log_of_var_num + 2);
//                sprintf(name, "%d", i);
//                aiger_add_output(a, al, name);
//            }
        }
    }
}


// Assumes c2 to be in SAT state and that dlvl 0 is fully propagated; and that dlvl is not propagated depending on restrictions to universals (i.e. after completed case_splits)
void c2_write_AIG_certificate(C2* c2) {
    abortif(c2->state != C2_SAT, "Can only generate certificate in SAT state.");
    abortif(int_vector_count(c2->skolem->universals_assumptions) > 0, "Current state of C2 must not depend on universal assumptions");
    
    aiger* a = aiger_init();
    
    int_vector* aigerlits = int_vector_init(); // maps var_id to the current aiger_lit representing it
    for (unsigned i = 0 ; i < var_vector_count(c2->qcnf->vars); i++) {int_vector_add(aigerlits, AIGERLIT_UNDEFINED);}
    
    cert_define_aiger_inputs(a, aigerlits, c2);
    
    unsigned max_sym = var2aigerlit(a->maxvar);
    assert(c2->options->certificate_type != QBFCERT || max_sym == var2aigerlit(a->maxvar + 1));
    
    // Certificate for the dlvl0 variables
    cert_dlvl0_definitions(a, aigerlits, c2, &max_sym);
    
    // The following data structures remember all the aigerlits for all cases; dlvl0 vars are only remembered once
    vector* case_aigerlits = vector_init(); // stores for every variable an int_vector of aigerlits for the different cases
    for (unsigned i = 0 ; i < var_vector_count(c2->qcnf->vars); i++) {
        int_vector* var_aigerlits = int_vector_init();
        vector_add(case_aigerlits, var_aigerlits);
        if (qcnf_var_exists(c2->qcnf, i) && cert_is_dlvl_zero_var(c2, i)) {
            unsigned curlit = (unsigned) int_vector_get(aigerlits, i);
            assert(curlit != AIGERLIT_UNDEFINED);
            int_vector_add(var_aigerlits, (int) curlit);
        }
    }
    int_vector* case_selectors = int_vector_init();
    
    // For every case, encode the function in a new set of symbols and connnect to the existing symbols with a MUX
    assert(vector_count(c2->cs->closed_cases) > 0);
    for (unsigned case_idx = 0; case_idx < vector_count(c2->cs->closed_cases); case_idx++) {
        unsigned case_applies = AIGERLIT_UNDEFINED;
        Case* c = vector_get(c2->cs->closed_cases, case_idx);
        if (c->type == 0) {  // CEGAR assignment
            case_applies = cert_encode_CEGAR(c2, a, &max_sym, aigerlits, c);
        } else {  // certificate is an actual function, closed case split
            case_applies = cert_encode_case(c2, a, &max_sym, aigerlits, c);
        }
        abortif(! c2->options->cegar && case_applies == aiger_false, "This case does not contribute.");
        
//#ifdef DEBUG
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
//#endif
        
        int_vector_add(case_selectors, (int) case_applies);
        for (unsigned var_id = 0; var_id < int_vector_count(aigerlits); var_id++) {
            if (qcnf_var_exists(c2->qcnf, var_id) && ! cert_is_dlvl_zero_var(c2, var_id)) {
                unsigned aigerlit = (unsigned) int_vector_get(aigerlits, var_id);
                assert(aigerlit != AIGERLIT_UNDEFINED);
                int_vector* aigerlits_for_var = vector_get(case_aigerlits, var_id);
                int_vector_add(aigerlits_for_var, (int) aigerlit);
                int_vector_set(aigerlits, var_id, AIGERLIT_UNDEFINED);
            }
        }
    }
    
    int_vector* out_aigerlits = int_vector_copy(aigerlits);
    for (unsigned var_id = 0; var_id < vector_count(case_aigerlits); var_id++) {
        if (! qcnf_var_exists(c2->qcnf, var_id) || cert_is_dlvl_zero_var(c2, var_id)) {
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
    
    cert_define_aiger_outputs(c2, a, out_aigerlits);
    
    bool valid = cert_validate(a, c2->qcnf, out_aigerlits, case_selectors);
    cert_write_aiger(a, c2->options);
    abortif(!valid, "Certificate invalid!");
    int_vector_free(aigerlits);
    int_vector_free(out_aigerlits);
    vector_free(case_aigerlits);
    int_vector_free(case_selectors);
    aiger_reset(a);
}
