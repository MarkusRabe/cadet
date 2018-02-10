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
#include "domain.h"

#include <string.h>


void c2_print_qdimacs_certificate(C2* c2, void* domain, int (*get_value)(void* domain, Lit lit)) {
    printf("V");
    for (unsigned i = 1; i < var_vector_count(c2->qcnf->vars); i++) {
        Var* v = var_vector_get(c2->qcnf->vars, i);
        if (v && v->var_id != 0 && v->is_universal) {
            if (get_value(domain, (Lit) v->var_id) != 0) {
                printf(" %d", get_value(domain, (Lit) v->var_id) * (Lit) v->var_id);
            }
        }
    }
    printf("\n");
}

bool cert_check_UNSAT(QCNF* qcnf, void* domain, int (*get_value)(void* domain, Lit lit)) {
    
    SATSolver* checker = satsolver_init();
    satsolver_set_max_var(checker, (int) var_vector_count(qcnf->vars));
    
    for (unsigned i = 0; i < vector_count(qcnf->clauses); i++) {
        Clause* c = vector_get(qcnf->clauses, i);
        if (c && c->original) {
            for (unsigned j = 0; j < c->size; j++) {
                satsolver_add(checker, c->occs[j]);
            }
            satsolver_clause_finished(checker);
        }
    }
    
    for (unsigned i = 0; i < var_vector_count(qcnf->vars); i++) {
        Var* v = var_vector_get(qcnf->vars, i);
        abortif(!v, "What!?");
        if (v->var_id != 0 && v->is_universal && v->original) {
            int val = get_value(domain, (Lit) v->var_id);
            abortif(val < -1 || val > 1, "Inconsistent value");
            if (val == 0) {
                val = 1;
            }
            satsolver_assume(checker, val * (Lit) v->var_id);
        }
    }
    
    sat_res res = satsolver_sat(checker);
    
    satsolver_free(checker);
    
    return res == SATSOLVER_UNSATISFIABLE;
}

unsigned lit2aigerlit(int_vector* aigerlits, Lit lit) {
    assert(lit != 0);
    unsigned var_id = lit_to_var(lit);
    unsigned aigerlit = (unsigned) int_vector_get(aigerlits, var_id);
    assert(aigerlit != 0);
    if (lit < 0) {
        aigerlit = negate(aigerlit);
    }
    return aigerlit;
}

void cert_encode_unique_antecedents(C2* c2, aiger* a, int_vector* aigerlits, unsigned *max_sym, Lit lit) {
    assert(lit);
    
    unsigned var_id = lit_to_var(lit);
    Var* v = var_vector_get(c2->qcnf->vars, var_id);
    vector* occs = lit > 0 ? &v->pos_occs : &v->neg_occs;
    
    unsigned aigerlit = (unsigned) int_vector_get(aigerlits, v->var_id);
    
    unsigned disjunction;
    if (lit < 0) {
        disjunction = aigerlit;
    } else {
        disjunction = inc(max_sym);
        aiger_add_and(a, aigerlit, disjunction + 1, disjunction + 1);
    }
    
    for (unsigned i = 0; i < vector_count(occs); i++) {
        Clause* c = vector_get(occs, i);
        if (skolem_get_unique_consequence(c2->skolem, c) == lit && ! skolem_clause_satisfied(c2->skolem, c)) {
            unsigned conjunction = inc(max_sym);
            unsigned next_disjunction = inc(max_sym);
            aiger_add_and(a, disjunction, conjunction + 1, next_disjunction);
            disjunction = next_disjunction;
            
            // encode the antecedent
            for (unsigned j = 0; j < c->size; j++) {
                Lit clause_lit = c->occs[j];
                if (clause_lit != lit) { // != unique_consequence
                    unsigned clause_aigerlit = lit2aigerlit(aigerlits, clause_lit);
                    unsigned next_conjunction = inc(max_sym);
                    aiger_add_and(a, conjunction, negate(clause_aigerlit), next_conjunction);
                    conjunction = next_conjunction;
                }
            }
            
            aiger_add_and(a, conjunction, 1, 1); // define leftover conjunction symbol as true
        }
    }
    aiger_add_and(a, disjunction, 1, 1); // define leftover disjunction symbol as false
}

// Returns an aiger lit that is true iff the cube is satisfied.
unsigned cert_encode_cube(C2* c2, aiger* a, unsigned *max_sym, int_vector* aigerlits, int_vector* cube) {
    unsigned outputlit = 1; // define empty conjunction as true
    for (unsigned i = 0; i < int_vector_count(cube); i++) {
        Lit l = int_vector_get(cube, i);
        assert(skolem_get_decision_lvl(c2->skolem, lit_to_var(l)) == 0); // Currently restricted to dlvl0 cubes
        unsigned next_outputlit = inc(max_sym);
        aiger_add_and(a, next_outputlit, outputlit, lit2aigerlit(aigerlits, l));
        outputlit = next_outputlit;
    }
    return outputlit;
}

void cert_encode_multiplexer(aiger* a, unsigned *max_sym, unsigned output, unsigned selector, unsigned if_signal, unsigned else_signal) {
    unsigned if_component = inc(max_sym);
    aiger_add_and(a, if_component, selector, if_signal);
    unsigned else_component = inc(max_sym);
    aiger_add_and(a, else_component, negate(selector), else_signal);
    unsigned negation_of_output = inc(max_sym); // need extra symbol as we cannot define left side of the final and as negated signal.
    aiger_add_and(a, negation_of_output, negate(if_component), negate(else_component));
    aiger_add_and(a, output, negate(negation_of_output), negate(negation_of_output));
}

void cert_AIG_certificate(C2* c2) {
    
    aiger* a = aiger_init();
    
    // taking the logarithm of the maximum var_id
    int log_of_var_num = 0;
    unsigned var_num_copy = var_vector_count(c2->qcnf->vars);
    while (var_num_copy >>= 1) log_of_var_num++;
    
    int_vector* aigerlits = int_vector_init(); // maps var_id to aiger_lit
    
    // create inputs and outputs
    for (unsigned i = 0; i < var_vector_count(c2->qcnf->vars); i++) {
        Var* v = var_vector_get(c2->qcnf->vars, i);
        int_vector_add(aigerlits, (int) var2aigerlit(v->var_id)); // sets it to 0(=true), if variable does not exist
        if (v->var_id != 0) {
            if (v->original) {
                char* name = malloc(sizeof(char) * (size_t) log_of_var_num + 2);
                sprintf(name, "%d", v->var_id);
                if (!v->is_universal) {
                    aiger_add_output(a, var2aigerlit(v->var_id), name);
                } else {
                    aiger_add_input(a, var2aigerlit(v->var_id), name);
                }
            }
        }
    }
    
    unsigned max_sym = var2aigerlit(var_vector_count(c2->qcnf->vars));
    
    // From the CAQECERT readme: "There is one additional output which must be the last output and it indicates whether the certificate is a Skolem or Herbrand certificate (value 1 and 0, respectively)."
    if (c2->options->certificate_type == CAQECERT) {
        aiger_add_output(a, 1, "result");
    }
    
    // Certificate for the dlvl0 variables
    for (unsigned i = 1; i < var_vector_count(c2->qcnf->vars); i++) {
        Var* v = var_vector_get(c2->qcnf->vars, i);
        if (v->var_id == 0 || v->is_universal) {
            continue;
        }
        if (skolem_is_deterministic(c2->skolem, i) && skolem_get_decision_lvl(c2->skolem, i) == 0 && v->var_id != 0 && ! v->is_universal) {
            if (skolem_lit_satisfied(c2->skolem, (Lit) v->var_id) || skolem_lit_satisfied(c2->skolem, - (Lit) v->var_id)) {
                unsigned c = skolem_lit_satisfied(c2->skolem, (Lit) v->var_id) ? 1 : 0;
                aiger_add_and(a, lit2aigerlit(aigerlits, (Lit) v->var_id), c, c);
            } else {
                skolem_var sv = skolem_get_info(c2->skolem, v->var_id);
                c2_validate_var(c2,v->var_id);
                
                if (sv.pure_pos) {
                    cert_encode_unique_antecedents(c2, a, aigerlits, &max_sym,   (Lit) v->var_id);
                } else if (sv.pure_neg) {
                    cert_encode_unique_antecedents(c2, a, aigerlits, &max_sym, - (Lit) v->var_id);
                } else {
                    int val = c2_get_decision_val(c2, v->var_id);
                    abortif(val < -1 || val > 1, "");
                    if (val == 1) {
                        cert_encode_unique_antecedents(c2, a, aigerlits, &max_sym, - (Lit) v->var_id);
                    } else if (val == -1) {
                        cert_encode_unique_antecedents(c2, a, aigerlits, &max_sym,   (Lit) v->var_id);
                    } else {
                        bool pos_occs_smaller = vector_count(&v->pos_occs) < vector_count(&v->neg_occs);
                        cert_encode_unique_antecedents(c2, a, aigerlits, &max_sym, (pos_occs_smaller ? 1 : -1) * (Lit) v->var_id);
                    }
                }
            }
        }
    }
    
    for (unsigned i = 0; i < vector_count(c2->skolem->domain->solved_cases); i++) {
        PartialFunction* pf = vector_get(c2->skolem->domain->solved_cases, i);
        if (pf->cube) {
            assert(pf->assignment);
            unsigned cube_lit = cert_encode_cube(c2, a, &max_sym, aigerlits, pf->cube);
            
            for (unsigned j = 0; j < int_vector_count(pf->assignment); j++) {
                Lit l = int_vector_get(pf->assignment, j);
                unsigned var_id = lit_to_var(l);
                assert(!skolem_is_deterministic(c2->skolem, var_id) || skolem_get_decision_lvl(c2->skolem, var_id) > 0);
                assert(l != 0);
                unsigned aiger_val = l > 0 ? 1 : 0;
                unsigned aiger_lit = (unsigned) int_vector_get(aigerlits, var_id);
                assert(aiger_lit != 0);
                assert(aiger_lit <= max_sym);
                unsigned new_aiger_lit = inc(&max_sym);
                int_vector_set(aigerlits, var_id, (int) new_aiger_lit);
                cert_encode_multiplexer(a, &max_sym, aiger_lit, cube_lit, aiger_val, new_aiger_lit);
            }
        } else {
            NOT_IMPLEMENTED();
        }
        // TODO: For each case, define output and leave ITE-else-case open as new symbol. the other variables should be defined in the last domain-case.
    }
    
    // Certificate all remaining cases by writing out the unique consequences of the dlvl>0 variables
    for (unsigned i = 0; i < var_vector_count(c2->qcnf->vars); i++) {
        Var* v = var_vector_get(c2->qcnf->vars, i);
        if (v->var_id == 0 || v->is_universal) {
            continue;
        }
        assert(skolem_is_deterministic(c2->skolem, i));
        if (skolem_is_deterministic(c2->skolem, i) && skolem_get_decision_lvl(c2->skolem, i) > 0) {
            if (skolem_lit_satisfied(c2->skolem, (Lit) v->var_id) || skolem_lit_satisfied(c2->skolem, - (Lit) v->var_id)) {
                unsigned c = skolem_lit_satisfied(c2->skolem, (Lit) v->var_id) ? 1 : 0;
                aiger_add_and(a, lit2aigerlit(aigerlits, (Lit) v->var_id), c, c);
            } else {
                skolem_var sv = skolem_get_info(c2->skolem, v->var_id);
                c2_validate_var(c2,v->var_id);
                
                if (sv.pure_pos) {
                    cert_encode_unique_antecedents(c2, a, aigerlits, &max_sym,   (Lit) v->var_id);
                } else if (sv.pure_neg) {
                    cert_encode_unique_antecedents(c2, a, aigerlits, &max_sym, - (Lit) v->var_id);
                } else {
                    int val = c2_get_decision_val(c2, v->var_id);
                    abortif(val < -1 || val > 1, "");
                    if (val == 1) {
                        cert_encode_unique_antecedents(c2, a, aigerlits, &max_sym, - (Lit) v->var_id);
                    } else if (val == -1) {
                        cert_encode_unique_antecedents(c2, a, aigerlits, &max_sym,   (Lit) v->var_id);
                    } else {
                        bool pos_occs_smaller = vector_count(&v->pos_occs) < vector_count(&v->neg_occs);
                        cert_encode_unique_antecedents(c2, a, aigerlits, &max_sym, (pos_occs_smaller ? 1 : -1) * (Lit) v->var_id);
                    }
                }
            }
        }
    }
    
    // TODO: implement "Close" rule, i.e. record the certificate for the dlvl>0 vars. Do we need to remember unique antecedents? Do we need to remember decisions and pure variables?
    
    const char* err = aiger_check(a);
    abortif(err, "%s", err);
    
    if (strcmp(c2->options->certificate_file_name, "stdout") == 0) {
        assert(c2->options->certificate_aiger_mode == aiger_ascii_mode);
        aiger_write_to_file(a, aiger_ascii_mode, stdout);
    } else {
        int write_success = aiger_open_and_write_to_file(a, c2->options->certificate_file_name);
        abortif(!write_success, "Could not write to file for aiger certificate (file name '%s').",c2->options->certificate_file_name);
    }
    int_vector_free(aigerlits);
    aiger_reset(a);
}

bool cert_check_SAT(C2* c2) {
    NOT_IMPLEMENTED();
    return false;
}
