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
#ifdef DEBUG
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
    V1("Case distinction in certificate is complete.\n");
    
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

