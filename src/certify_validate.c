//
//  certify_validate.c
//  cadet
//
//  Created by Markus Rabe on 07.04.18.
//  Copyright © 2018 UC Berkeley. All rights reserved.
//

#include "certify.h"
#include "aiger.h"
#include "aiger_utils.h"
#include "log.h"
#include "satsolver.h"
#include "util.h"

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
    
//    V0("Violating assignment to existentials:");
//    for (unsigned i = 0; i < var_vector_count(qcnf->vars); i++) {
//        if (qcnf_var_exists(qcnf, i) && qcnf_is_existential(qcnf, i)) {
//            unsigned al = mapped_lit2aigerlit(aigerlits, (Lit) i);
//            int val = satsolver_deref(checker, aiger_lit2lit(al, truelit));
//            V0(" %d", val * (int) i);
//        }
//    }
//    V0("\n");
}

void cert_validate_encode_aiger(aiger* a, SATSolver* checker, int truelit) {
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
}


Lit cert_validate_encode_violation_of_some_clause(aiger* a, QCNF* qcnf, int_vector* aigerlits, SATSolver* checker, int truelit) {
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
    return some_clause_violated;
}


bool cert_validate_skolem_function(aiger* a, QCNF* qcnf, int_vector* aigerlits, int_vector* case_selectors) {
#ifndef DEBUG
    return true;
#endif
    V1("Validating Skolem function with %u gates.\n", a->num_ands);
    Stats* timer = statistics_init(1000);  // 1 ms resolution
    statistics_start_timer(timer);
    bool ret = true;
    
    SATSolver* checker = satsolver_init();
    satsolver_set_max_var(checker, (int) a->maxvar);
    
    int truelit = satsolver_inc_max_var(checker);
    satsolver_add(checker, truelit);
    satsolver_clause_finished(checker);
    
    cert_validate_encode_aiger(a, checker, truelit);
    
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
    V1("Case distinction in certificate is complete.\n");
    
    // Encode big disjunction over the violation of the clauses
    Lit some_clause_violated = cert_validate_encode_violation_of_some_clause(a, qcnf, aigerlits, checker, truelit);
    
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


// Check one side of the correcntess of the function
// If there is a satisfying assignment, then the function should produce a satisfying assignment, too.
bool cert_validate_functional_synthesis(aiger* a, QCNF* qcnf, int_vector* aigerlits, int_vector* case_selectors) {
#ifndef DEBUG
    return true;
#endif
    V1("Validating functional synthesis certificate with %u gates.\n", a->num_ands);
    Stats* timer = statistics_init(1000);  // 1 ms resolution
    statistics_start_timer(timer);
    
    SATSolver* checker = satsolver_init();
    satsolver_set_max_var(checker, (int) a->maxvar);
    
    int truelit = satsolver_inc_max_var(checker);
    satsolver_add(checker, truelit);
    satsolver_clause_finished(checker);
    
    cert_validate_encode_aiger(a, checker, truelit);
    
    Lit some_clause_violated = cert_validate_encode_violation_of_some_clause(a, qcnf, aigerlits, checker, truelit);
    
    int_vector* qcnfvar2satlit = int_vector_init();
    for (unsigned i = 0; i < var_vector_count(qcnf->vars); i++) {
        int satlit = satsolver_inc_max_var(checker);
        int_vector_add(qcnfvar2satlit, satlit);
    }
    // encode that universal variables of the aiger encoding and the qcnf encoding are equal
    for (unsigned i = 0; i < var_vector_count(qcnf->vars); i++) {
        if (qcnf_var_exists(qcnf, i) && qcnf_is_universal(qcnf, i)) {
            unsigned al = mapped_lit2aigerlit(aigerlits, (Lit) i);
            assert(aiger_is_input(a, al));
                   
            satsolver_add(checker,   int_vector_get(qcnfvar2satlit, i));
            satsolver_add(checker, - aiger_lit2lit(al, truelit));
            
            satsolver_clause_finished(checker);
            
            satsolver_add(checker, - int_vector_get(qcnfvar2satlit, i));
            satsolver_add(checker,   aiger_lit2lit(al, truelit));
            satsolver_clause_finished(checker);
        }
    }
    // encode the qcnf in the satlits in qcnfvar2satlit
    for (unsigned i = 0; i < vector_count(qcnf->all_clauses); i++) {
        Clause* c = vector_get(qcnf->all_clauses, i);
        if (c->original) {
            for (unsigned j = 0; j < c->size; j++) {
                Lit l = c->occs[j];
                unsigned var_id = lit_to_var(l);
                int polarity = l > 0 ? 1 : -1;
                int satlit = int_vector_get(qcnfvar2satlit, var_id);
                satsolver_add(checker, satlit * polarity);
            }
            satsolver_clause_finished(checker);
        }
    }
    //    assert(satsolver_sat(checker) == SATSOLVER_SAT); // not the case for empty clause!
    
    satsolver_add(checker, some_clause_violated); // is violated even though there must be an assignment to the existentials
    satsolver_clause_finished(checker);
    
    sat_res res = satsolver_sat(checker);
    statistics_stop_and_record_timer(timer);
    V1("Validation took %f s\n", timer->accumulated_value);
    if (res != SATSOLVER_UNSAT) {
        LOG_ERROR("Validation failed!");
        cert_validate_print_assignment(a, qcnf, checker, aigerlits, truelit);
    }
    
    int_vector_free(qcnfvar2satlit);
    statistics_free(timer);
    satsolver_free(checker);
    return res == SATSOLVER_UNSAT;
}

// Check one side of the correcntess of the projection:
// If the projection is 'false', then there should not be a satisfying assignment.
bool cert_validate_quantifier_elimination(aiger* a, QCNF* qcnf, int_vector* aigerlits, unsigned projection_lit) {
#ifndef DEBUG
    return true;
#endif
    V1("Validating quantifier elimination with %u gates.\n", a->num_ands);
    Stats* timer = statistics_init(1000);  // 1 ms resolution
    statistics_start_timer(timer);
    
    SATSolver* checker = satsolver_init();
    satsolver_set_max_var(checker, (int) a->maxvar);
    
    int truelit = satsolver_inc_max_var(checker);
    satsolver_add(checker, truelit);
    satsolver_clause_finished(checker);
    
    cert_validate_encode_aiger(a, checker, truelit);
    
    int_vector* qcnfvar2satlit = int_vector_init();
    for (unsigned i = 0; i < var_vector_count(qcnf->vars); i++) {
        int satlit = satsolver_inc_max_var(checker);
        int_vector_add(qcnfvar2satlit, satlit);
    }
    // encode that universal variables of the aiger encoding and the qcnf encoding are equal
    for (unsigned i = 0; i < var_vector_count(qcnf->vars); i++) {
        if (qcnf_var_exists(qcnf, i) && qcnf_is_universal(qcnf, i)) {
            unsigned al = mapped_lit2aigerlit(aigerlits, (Lit) i);
            assert(aiger_is_input(a, al));
            
            satsolver_add(checker,   int_vector_get(qcnfvar2satlit, i));
            satsolver_add(checker, - aiger_lit2lit(al, truelit));
            
            satsolver_clause_finished(checker);
            
            satsolver_add(checker, - int_vector_get(qcnfvar2satlit, i));
            satsolver_add(checker,   aiger_lit2lit(al, truelit));
            satsolver_clause_finished(checker);
        }
    }
    // encode the qcnf in the satlits in qcnfvar2satlit
    for (unsigned i = 0; i < vector_count(qcnf->all_clauses); i++) {
        Clause* c = vector_get(qcnf->all_clauses, i);
        if (c->original) {
            for (unsigned j = 0; j < c->size; j++) {
                Lit l = c->occs[j];
                unsigned var_id = lit_to_var(l);
                int polarity = l > 0 ? 1 : -1;
                int satlit = int_vector_get(qcnfvar2satlit, var_id);
                satsolver_add(checker, satlit * polarity);
            }
            satsolver_clause_finished(checker);
        }
    }
    //    assert(satsolver_sat(checker) == SATSOLVER_SAT); // not the case for empty clause!
    
    int projection_satlit = aiger_lit2lit(projection_lit, truelit);
    satsolver_add(checker, - projection_satlit); // is violated even though there must be an assignment to the existentials
    satsolver_clause_finished(checker);
    
    sat_res res = satsolver_sat(checker);
    statistics_stop_and_record_timer(timer);
    V1("Validation took %f s\n", timer->accumulated_value);
    if (res != SATSOLVER_UNSAT) {
        LOG_ERROR("Validation failed!");
        cert_validate_print_assignment(a, qcnf, checker, aigerlits, truelit);
    }
    
    int_vector_free(qcnfvar2satlit);
    statistics_free(timer);
    satsolver_free(checker);
    return res == SATSOLVER_UNSAT;
}
