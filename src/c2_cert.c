//
//  c2_cert.c
//  cadet
//
//  Created by Markus Rabe on 21/09/16.
//  Copyright © 2016 Saarland University. All rights reserved.
//

#include "c2_cert.h"
#include "c2_validate.h"
#include "aiger.h"
#include "aiger_utils.h"
#include "log.h"

bool c2_cert_check_UNSAT(QCNF* qcnf, void* domain, int (*get_value)(void* domain, Lit lit)) {
    
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
        if (v->is_universal && v->original) {
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

unsigned lit2aigerlit(Lit lit) {
    return (lit < 0 ? 1 : 0) + var2aigerlit(lit_to_var(lit));
}

unsigned c2_cert_encode_unique_antecedents(C2* c2, aiger* a, unsigned max_sym, Lit lit) {
    assert(lit);
    
    unsigned var_id = lit_to_var(lit);
    Var* v = var_vector_get(c2->qcnf->vars, var_id);
    vector* occs = lit > 0 ? &v->pos_occs : &v->neg_occs;
    
    unsigned disjunction;
    if (lit < 0) {
        disjunction = (unsigned) var2aigerlit(v->var_id);
    } else {
        disjunction = inc(&max_sym);
        aiger_add_and(a, (unsigned) v->var_id * 2, disjunction + 1, disjunction + 1);
    }
    
    for (unsigned i = 0; i < vector_count(occs); i++) {
        Clause* c = vector_get(occs, i);
        if (skolem_get_unique_consequence(c2->skolem, c) == lit && ! skolem_clause_satisfied(c2->skolem, c)) {
            unsigned conjunction = inc(&max_sym);
            unsigned next_disjunction = inc(&max_sym);
            aiger_add_and(a, disjunction, conjunction + 1, next_disjunction);
            disjunction = next_disjunction;
            
            // encode the antecedent
            for (unsigned j = 0; j < c->size; j++) {
                Lit clause_lit = c->occs[j];
                if (clause_lit != lit) { // != unique_consequence
                    unsigned next_conjunction = inc(&max_sym);
                    unsigned neg_aigerlit = lit2aigerlit(-clause_lit);
                    aiger_add_and(a, conjunction, neg_aigerlit, next_conjunction);
                    conjunction = next_conjunction;
                }
            }
            
            aiger_add_and(a, conjunction, 1, 1); // define leftover conjunction symbol as true
        }
    }
    
    aiger_add_and(a, disjunction, 1, 1); // define leftover disjunction symbol as false

    return max_sym;
}


void c2_cert_AIG_certificate(C2* c2) {
    
    aiger* a = aiger_init();
    
    // taking the logarithm of the maximum var_id
    int log_of_var_num = 0;
    unsigned var_num_copy = var_vector_count(c2->qcnf->vars);
    while (var_num_copy >>= 1) log_of_var_num++;
    
    // create inputs and outputs
    for (unsigned i = 0; i < var_vector_count(c2->qcnf->vars); i++) {
        Var* v = var_vector_get(c2->qcnf->vars, i);
        
        if (v->var_id != 0 && v->original) {
            char* name = malloc(sizeof(char) * (size_t) log_of_var_num + 2);
            sprintf(name, "%d", v->var_id);
            
            if (!v->is_universal) {
                aiger_add_output(a, var2aigerlit(v->var_id), name);
            } else {
                aiger_add_input(a, var2aigerlit(v->var_id), name);
            }
        }
    }
    
    // From the CAQECERT readme: "There is one additional output which must be the last output and it indicates whether the certificate is a Skolem or Herbrand certificate (value 1 and 0, respectively)."
    if (c2->options->certificate_type == CAQECERT) {
        aiger_add_output(a, 1, "result");
    }
    
    unsigned max_sym = var2aigerlit(var_vector_count(c2->qcnf->vars));
    
    for (unsigned i = 0; i < var_vector_count(c2->qcnf->vars); i++) {
        Var* v = var_vector_get(c2->qcnf->vars, i);
        if (v->var_id != 0 && ! v->is_universal) {
            
            if (skolem_lit_satisfied(c2->skolem, (Lit) v->var_id) || skolem_lit_satisfied(c2->skolem, - (Lit) v->var_id)) {
                unsigned c = skolem_lit_satisfied(c2->skolem, (Lit) v->var_id) ? 1 : 0;
                aiger_add_and(a, 2 * (unsigned) v->var_id, c, c);
            } else {
                skolem_var sv = skolem_get_info(c2->skolem, v->var_id);
                c2_validate_var(c2,v->var_id);
                
                if (sv.pure_pos) {
                    max_sym = c2_cert_encode_unique_antecedents(c2, a, max_sym,   (Lit) v->var_id);
                } else if (sv.pure_neg) {
                    max_sym = c2_cert_encode_unique_antecedents(c2, a, max_sym, - (Lit) v->var_id);
                } else {
                    int val = c2_get_decision_val(c2, v->var_id);
                    abortif(val < -1 || val > 1, "");
                    if (val == 1) {
                        max_sym = c2_cert_encode_unique_antecedents(c2, a, max_sym, - (Lit) v->var_id);
                    } else if (val == -1) {
                        max_sym = c2_cert_encode_unique_antecedents(c2, a, max_sym,   (Lit) v->var_id);
                    } else {
                        bool pos_occs_smaller = vector_count(&v->pos_occs) < vector_count(&v->neg_occs);
                        max_sym = c2_cert_encode_unique_antecedents(c2, a, max_sym, (pos_occs_smaller ? 1 : -1) * (Lit) v->var_id);
                    }
                }
            }
        }
    }
    
    const char* err = aiger_check(a);
    abortif(err, "%s", err);
    
    if (strcmp(c2->options->certificate_file_name, "stdout") == 0) {
        assert(c2->options->certificate_aiger_mode == aiger_ascii_mode);
        aiger_write_to_file(a, aiger_ascii_mode, stdout);
    } else {
        int write_success = aiger_open_and_write_to_file(a, c2->options->certificate_file_name);
        abortif(!write_success, "Could not write to file for aiger certificate (file name '%s').",c2->options->certificate_file_name);
    }
}
