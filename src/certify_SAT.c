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

#include <string.h>

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
    assert(aigerlit != 0);
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
    vector* occs = qcnf_get_occs_of_lit(c2->qcnf, lit);
    unsigned aigerlit = (unsigned) int_vector_get(aigerlits, var_id);
    
    unsigned disjunction = 0;
    if (lit < 0) {
        disjunction = aigerlit;
    } else {
        disjunction = inc(max_sym);
        aiger_add_and(a, aigerlit, disjunction + 1, disjunction + 1);
    }
    
    for (unsigned i = 0; i < vector_count(occs); i++) {
        Clause* c = vector_get(occs, i);
        if (cert_get_unique_consequence(unique_consequences, c) == lit) {
            unsigned conjunction = inc(max_sym);
            unsigned next_disjunction = inc(max_sym);
            aiger_add_and(a, disjunction, conjunction + 1, next_disjunction);
            disjunction = next_disjunction;
            
            // encode the antecedent
            for (unsigned j = 0; j < c->size; j++) {
                Lit clause_lit = c->occs[j];
                if (clause_lit != lit) { // != unique_consequence
                    unsigned clause_aigerlit = mapped_lit2aigerlit(aigerlits, clause_lit);
                    unsigned next_conjunction = inc(max_sym);
                    aiger_add_and(a, conjunction, negate(clause_aigerlit), next_conjunction);
                    conjunction = next_conjunction;
                }
            }
            
            aiger_add_and(a, conjunction, aiger_true, aiger_true); // define leftover conjunction symbol as true
        }
    }
    aiger_add_and(a, disjunction, aiger_true, aiger_true); // define leftover disjunction symbol as false
}


bool cert_is_dlvl_zero_var(C2* c2, unsigned var_id) {
    return (skolem_is_deterministic(c2->skolem, var_id) && skolem_get_decision_lvl(c2->skolem, var_id) == 0);
}


unsigned cert_encode_new_aigerlits_for_case(C2* c2, aiger* a, unsigned* max_sym, int_vector* aigerlits, int_vector* alt_aigerlits) {
    
    // Create a copy of all existentials with dlvl>0; connect them with a mux
    
    // Introduce signal that will be the condtition of the MUXs of this case
    unsigned case_selector = inc(max_sym);
    
    for (unsigned var_id = 0; var_id < var_vector_count(c2->qcnf->vars); var_id++) {
        if (! qcnf_var_exists(c2->qcnf, var_id) || cert_is_dlvl_zero_var(c2, var_id)) {
            continue;
        }
        unsigned new_aigerlit = inc(max_sym);
        unsigned alt_aigerlit = inc(max_sym);
        unsigned old_aigerlit = (unsigned) int_vector_get(aigerlits, var_id);
        
        aigeru_add_multiplexer(a, max_sym, old_aigerlit, case_selector, new_aigerlit, alt_aigerlit);
        
        int_vector_set(aigerlits, var_id, (int) new_aigerlit);
        int_vector_set(alt_aigerlits, var_id, (int) alt_aigerlit);
    }
    return case_selector;
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


void cert_move_alt_satlits_to_satlits(C2* c2, aiger* a, unsigned* max_sym, int_vector* aigerlits, int_vector* alt_aigerlits) {
    for (unsigned var_id = 0; var_id < var_vector_count(c2->qcnf->vars); var_id++) {
        if (! qcnf_var_exists(c2->qcnf, var_id) || cert_is_dlvl_zero_var(c2, var_id)) {
            continue;
        }
        int_vector_set(aigerlits, var_id, int_vector_get(alt_aigerlits, var_id));
    }
}


void cert_encode_case(C2* c2, aiger* a, unsigned *max_sym, int_vector* aigerlits, Case* c, unsigned case_selector) {
    assert(c->type == 1);  // encodes a function
    
    int_vector_sort(c->potentially_conflicted_variables, compare_integers_natural_order);
    int_vector* conflict_aigerlits = int_vector_init();
    
    // Certificate all remaining cases by writing out the unique consequences of the dlvl>0 variables
    for (unsigned i = 0; i < int_vector_count(c->decisions); i++) {
        Lit decision_lit = int_vector_get(c->decisions, i);
        assert(decision_lit != 0);
        unsigned var_id = lit_to_var(decision_lit);
        if (! qcnf_var_exists(c2->qcnf, var_id) || cert_is_dlvl_zero_var(c2, var_id)) {
            continue;
        }
        assert(!qcnf_is_universal(c2->qcnf, var_id));
        cert_encode_unique_antecedents(c2, a, aigerlits, c->unique_consequences, max_sym, - decision_lit);
        
        
        // encode other side as well for conflicted variables
        if (int_vector_contains_sorted(c->potentially_conflicted_variables, (int) var_id)) {
            unsigned aigerlit = (unsigned) int_vector_get(aigerlits, var_id);
            unsigned anti_aigerlit = inc(max_sym);
            int_vector_set(aigerlits, var_id, (int) anti_aigerlit);
            
            unsigned conflict_aigerlit = inc(max_sym);
            aiger_add_and(a, conflict_aigerlit, aigerlit, negate(anti_aigerlit));
            int_vector_add(conflict_aigerlits, (int) conflict_aigerlit);
            
            // encode the other side of the decision lit
            cert_encode_unique_antecedents(c2, a, aigerlits, c->unique_consequences, max_sym,   decision_lit);
            
            // reset the aigerlit to actual
            int_vector_set(aigerlits, var_id, (int) aigerlit);
        }
    }
    if (case_selector != aiger_true) {
        aigeru_add_multiOR(a, max_sym, negate(case_selector), conflict_aigerlits);
    }
    int_vector_free(conflict_aigerlits);
}

//void cert_validate(aiger* a, QCNF* qcnf, unsigned* max_sym, int_vector* aigerlits) {
//    unsigned some_clause_violated = aiger_false;
//    for (unsigned i = 0; i < vector_count(qcnf->all_clauses); i++) {
//        Clause* c = vector_get(qcnf->all_clauses, i);
//        if (qcnf_is_original_clause(qcnf, c->clause_idx)) {
//            int_vector* clause_aigerlits = int_vector_init();
//            for (unsigned j = 0; j < c->size; j++) {
//                int_vector_add(clause_aigerlits, (int) mapped_lit2aigerlit(aigerlits, - c->occs[j]));
//            }
//            unsigned this_clause_violated = aigeru_multiAND(a, max_sym, clause_aigerlits);
//            int_vector_free(clause_aigerlits);
//            some_clause_violated = aigeru_OR(a, max_sym, some_clause_violated, this_clause_violated);
//        }
//    }
//    aiger_add_bad(a, some_clause_violated, "some clause is violated");
//
//    SATSolver* checker = satsolver_init();
//    satsolver_set_max_var(checker, (int) a->maxvar);
//    int truelit = satsolver_inc_max_var(checker);
//    satsolver_add(checker, truelit);
//    satsolver_clause_finished(checker);
//    for (unsigned i = 0; i < a->num_ands; i++) {
//        aiger_and and = a->ands[i];
//
//        satsolver_add(checker,   aiger_lit2lit(and.rhs0, truelit));
//        satsolver_add(checker, - aiger_lit2lit(and.lhs, truelit));
//        satsolver_clause_finished(checker);
//
//        satsolver_add(checker,   aiger_lit2lit(and.rhs1, truelit));
//        satsolver_add(checker, - aiger_lit2lit(and.lhs, truelit));
//        satsolver_clause_finished(checker);
//
//        satsolver_add(checker, - aiger_lit2lit(and.rhs0, truelit));
//        satsolver_add(checker, - aiger_lit2lit(and.rhs1, truelit));
//        satsolver_add(checker,   aiger_lit2lit(and.lhs, truelit));
//        satsolver_clause_finished(checker);
//    }
//
//    satsolver_add(checker, aiger_lit2lit(some_clause_violated, truelit));
//    satsolver_clause_finished(checker);
//
//    sat_res res = satsolver_sat(checker);
//    abortif(res != SATSOLVER_UNSAT, "Certificate invalid");
//    V1("Certificate verified!\n");
//}

bool cert_validate(aiger* a, QCNF* qcnf) {
    
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
    
    // Encode big disjunction over the violation of the clauses
    Lit some_clause_violated = - truelit;
    for (unsigned i = 0; i < vector_count(qcnf->all_clauses); i++) {
        Clause* c = vector_get(qcnf->all_clauses, i);
        if (qcnf_is_original_clause(qcnf, c->clause_idx)) {
            Lit this_clause_violated = satsolver_inc_max_var(checker);
            for (unsigned j = 0; j < c->size; j++) {
                Lit lit = c->occs[j];
                unsigned var_id = lit_to_var(lit);
                assert(var_id <= a->maxvar);
                assert(! qcnf_is_universal(qcnf, var_id) || aiger_is_input(a, lit2aigerlit((int) var_id)));
                assert(! qcnf_is_existential(qcnf, var_id) || aiger_is_and(a, lit2aigerlit((int) var_id)));
                satsolver_add(checker, - lit);
                satsolver_add(checker, - this_clause_violated);
                satsolver_clause_finished(checker);
            }
//            for (unsigned j = 0; j < c->size; j++) {
//                unsigned aigerlit = mapped_lit2aigerlit(aigerlits, c->occs[j]);
//                Lit lit = aiger_lit2lit(aigerlit, truelit);
//                satsolver_add(checker,   lit);
//            }
//            satsolver_add(checker,   this_clause_violated);
//            satsolver_clause_finished(checker);
            
            Lit next_some_clause_violated = satsolver_inc_max_var(checker);
            satsolver_add(checker, some_clause_violated);
            satsolver_add(checker, this_clause_violated);
            satsolver_add(checker, - next_some_clause_violated);
            satsolver_clause_finished(checker);
            
            some_clause_violated = next_some_clause_violated;
        }
    }
    
    satsolver_add(checker, some_clause_violated);
    satsolver_clause_finished(checker);
    
    sat_res res = satsolver_sat(checker);
    if (res != SATSOLVER_UNSAT) {
        LOG_ERROR("Certificate invalid!");
        V1("Violating assignment to universals:");
        for (unsigned i = 0; i < var_vector_count(qcnf->vars); i++) {
            if (qcnf_var_exists(qcnf, i) && qcnf_is_universal(qcnf, i)) {
                int val = satsolver_deref(checker, (int) i);
                V0(" %d", val * (int) i);
            }
        }
        V0("\n");
        
        V0("Violating assignment to existentials:");
        for (unsigned i = 0; i < var_vector_count(qcnf->vars); i++) {
            if (qcnf_var_exists(qcnf, i) && qcnf_is_existential(qcnf, i)) {
                int val = satsolver_deref(checker, (int) i);
                V0(" %d", val * (int) i);
            }
        }
        V0("\n");
//        aiger_write_to_file(a, aiger_ascii_mode, stdout);
    } else {
        V1("Certificate verified!\n");
    }
    satsolver_free(checker);
    return res == SATSOLVER_UNSAT;
}


// Assumes c2 to be in SAT state and that dlvl 0 is fully propagated; and that dlvl is not propagated depending on restrictions to universals (i.e. after completed case_splits)
void c2_write_AIG_certificate(C2* c2) {
    abortif(c2->state != C2_SAT, "Can only generate certificate in SAT state.");
    abortif(int_vector_count(c2->skolem->universals_assumptions) > 0, "Current state of C2 must not depend on universal assumptions");
    
    aiger* a = aiger_init();
    
    int_vector* aigerlits = int_vector_init(); // maps var_id to the current aiger_lit representing it
    for (unsigned i = 0 ; i < var_vector_count(c2->qcnf->vars); i++) {int_vector_add(aigerlits, 0);}
    
    // taking the logarithm of the maximum var_id
    int log_of_var_num = 0;
    unsigned var_num_copy = var_vector_count(c2->qcnf->vars);
    while (var_num_copy >>= 1) log_of_var_num++;
    
    // Reserve aigerlits for the original variables; needed for QBFCERT compatibility
    for (unsigned i = 0; i < var_vector_count(c2->qcnf->vars); i++) {
        if (qcnf_var_exists(c2->qcnf, i) && qcnf_is_original(c2->qcnf, i)) {
            unsigned al = var2aigerlit(i);
            int_vector_set(aigerlits, i, (int) al);
            
            char* name = malloc(sizeof(char) * (size_t) log_of_var_num + 2);
            sprintf(name, "%d", i); // TODO: use QAIGER compatible names
            if (qcnf_is_universal(c2->qcnf, i)) {
                aiger_add_input(a, al, name);
            } else {
                aiger_add_output(a, al, name);
            }
        }
    }
    
    unsigned max_sym = var2aigerlit(var_vector_count(c2->qcnf->vars));
    assert(max_sym == var2aigerlit(a->maxvar + 1));
    
    // Certificate for the dlvl0 variables
    for (unsigned i = 0; i < var_vector_count(c2->qcnf->vars); i++) {
        if (! qcnf_var_exists(c2->qcnf, i) || ! cert_is_dlvl_zero_var(c2, i) || qcnf_is_universal(c2->qcnf, i)) {
            continue;
        }
        if (skolem_get_constant_value(c2->skolem, (Lit) i) != 0) {
            unsigned aiger_constant = skolem_get_constant_value(c2->skolem, (Lit) i) > 0 ? 1 : 0;
            aiger_add_and(a, mapped_lit2aigerlit(aigerlits, (Lit) i), aiger_constant, aiger_constant);
        } else {
            skolem_var sv = skolem_get_info(c2->skolem, i);
            c2_validate_var(c2, i);
            
            abortif(skolem_get_decision_val(c2->skolem, i) != 0, "dlvl0 variable is marked as decision variable");
            
            int polarity = 1;
            if (sv.pure_pos) {
                polarity = 1;
            } else if (sv.pure_neg) {
                polarity = -1;
            } else {
                Var* v = var_vector_get(c2->qcnf->vars, i);
                bool pos_occs_smaller = vector_count(&v->pos_occs) < vector_count(&v->neg_occs);
                polarity = pos_occs_smaller ? 1 : -1;
            }
            cert_encode_unique_antecedents(c2, a, aigerlits, c2->skolem->unique_consequence, &max_sym, polarity * (Lit) i);
        }
    }
    
    int_vector* alt_aigerlits = int_vector_copy(aigerlits);
    
    // For every case, encode the function in a new set of symbols and connnect to the existing symbols with a MUX
    for (unsigned i = 0; i < vector_count(c2->cs->closed_cases); i++) {
        unsigned case_selector = aiger_true;
        if (i + 1 < vector_count(c2->cs->closed_cases)) { // i.e. this is not the last case
            case_selector = cert_encode_new_aigerlits_for_case(c2, a, &max_sym, aigerlits, alt_aigerlits);
        }
        
        Case* c = vector_get(c2->cs->closed_cases, i);
        if (c->type == 0) {  // CEGAR assignment
            NOT_IMPLEMENTED();
            assert(c->decisions);
            unsigned cube_lit = cert_encode_c2_cube(c2, a, &max_sym, aigerlits, c->universal_assumptions);
            
            for (unsigned j = 0; j < int_vector_count(c->decisions); j++) {
                Lit l = int_vector_get(c->decisions, j);
                unsigned var_id = lit_to_var(l);
                if (skolem_is_deterministic(c2->skolem, var_id)
                    && skolem_get_decision_lvl(c2->skolem, var_id) == 0) {
                    // can happen if clauses were learnt that made additional variables deterministic in the meantime.
                    // Instead we could make the split of the certificate at the interface stored in the domain.
                    continue;
                }
                assert(  !skolem_is_deterministic(c2->skolem, var_id)
                       || skolem_get_decision_lvl(c2->skolem, var_id) > 0);
                assert(l != 0);
                unsigned aiger_val = l > 0 ? aiger_true : aiger_false;
                unsigned aiger_lit = (unsigned) int_vector_get(aigerlits, var_id);
                assert(aiger_lit != aiger_false);
                assert(aiger_lit <= max_sym);
                unsigned new_aiger_lit = inc(&max_sym);
                int_vector_set(aigerlits, var_id, (int) new_aiger_lit);
                aigeru_add_multiplexer(a, &max_sym, aiger_lit, cube_lit, aiger_val, new_aiger_lit);
            }
        } else {  // certificate is an actual function, closed case split
            cert_encode_case(c2, a, &max_sym, aigerlits, c, case_selector);
        }
        
        cert_move_alt_satlits_to_satlits(c2, a, &max_sym, aigerlits, alt_aigerlits);
    }
    
    bool valid = cert_validate(a, c2->qcnf);
    cert_write_aiger(a, c2->options);
    abortif(!valid, "Certificate invalid!");
    int_vector_free(aigerlits);
    aiger_reset(a);
}
