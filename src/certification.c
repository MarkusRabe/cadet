//
//  certification.c
//  caqe
//
//  File created by Markus Rabe on 17/02/2016.
//  Copyright (c) 2016. All rights reserved.
//

#include "certification.h"
#include "aiger.h"
#include "aiger_utils.h"
#include "log.h"
#include "util.h"
#include "reactive.h"

#include <string.h>
#include <assert.h>

unsigned occ2aigerlit(Occ* o) {
    return (o->neg ? 1 : 0) + var2aigerlit((unsigned) o->var->var_id);
}

unsigned encode_unique_antecedents(unsigned max_sym, MVar* v, vector* occs, aiger* a, bool negated) {
    
    unsigned disjunction;
    if (negated) {
        disjunction =(unsigned) v->var_id * 2;
    } else {
        disjunction = inc(&max_sym);
        aiger_add_and(a, (unsigned) v->var_id * 2, disjunction + 1, disjunction + 1);
    }
    
    for (unsigned k = 0; k < vector_count(occs); k++) {
        Occ* o = vector_get(occs, k);
        MClause* c = o->clause;
        if (c->unique_consequence_occ == o && ! is_clause_satisfied(c)) {
            unsigned conjunction = inc(&max_sym);
            unsigned next_disjunction = inc(&max_sym);
            aiger_add_and(a, disjunction, conjunction + 1, next_disjunction);
            disjunction = next_disjunction;
            
            // encode the antecedent
            for (unsigned i = 0; i < c->size; i++) {
                Occ* clause_occ = &c->occs[i];
                if (clause_occ != o) {
                    unsigned next_conjunction = inc(&max_sym);
                    unsigned occ_sig = occ2aigerlit(clause_occ);
                    aiger_add_and(a, conjunction, negate(occ_sig), next_conjunction);
                    conjunction = next_conjunction;
                }
            }
            
            aiger_add_and(a, conjunction, 1, 1); // define leftover conjunction symbol as true
        }
    }
    
    aiger_add_and(a, disjunction, 1, 1); // define leftover disjunction symbol as false
    
    return max_sym;
}

aiger* qbf_Skolem_certificate(Matrix* m, Options* options) {
    
    aiger* a = aiger_init();
    
    // taking the logarithm of the max_var_id
    int log_of_var_num = 0;
    unsigned var_num_copy = (unsigned) m->max_var_id;
    while (var_num_copy >>= 1) log_of_var_num++;
    
    // create inputs and outputs
    for (unsigned i = 0; i < vector_count(m->scopes); i++) {
        MScope* s = vector_get(m->scopes, i);
        for (unsigned j = 0; j < vector_count(s->vars); j++) {
            MVar* v = vector_get(s->vars, j);
            
            char* name = malloc(sizeof(char) * (size_t) log_of_var_num + 2);
            sprintf(name, "%d", v->var_id);
            assert(v->var_id <= m->max_var_id);
            
            if (s->qtype == QUANTIFIER_EXISTENTIAL) {
                if (! v->is_helper) {
                    aiger_add_output(a, 2 * (unsigned) v->var_id, name);
                }
            } else {
                assert(s->qtype == QUANTIFIER_UNIVERSAL);
                assert(!v->is_helper);
                aiger_add_input(a, 2 * (unsigned) v->var_id, name);
            }
        }
    }
    
    // From the CAQECERT readme: "There is one additional output which must be the last output and it indicates whether the certificate is a Skolem or Herbrand certificate (value 1 and 0, respectively)."
    if (options->certificate_type == CAQECERT) {
        aiger_add_output(a, 1, "result");
    }
    
    
    unsigned max_sym = (unsigned) m->max_var_id * 2;
    
    for (unsigned i = 0; i < vector_count(m->scopes); i++) {
        MScope* s = vector_get(m->scopes, i);
        if (s->qtype == QUANTIFIER_EXISTENTIAL) {
            for (unsigned j = 0; j < vector_count(s->vars); j++) {
                MVar* v = vector_get(s->vars, j);
                
                if (v->value != 0) {
                    unsigned c = v->value == 1 ? 1 : 0;
                    aiger_add_and(a, 2 * (unsigned) v->var_id, c, c);
                } else {
                    bool use_negated_occs = vector_count(v->pos_occs) < vector_count(v->neg_occs);
                    vector* shorter_occs = use_negated_occs ? v->neg_occs : v->pos_occs;
                    max_sym = encode_unique_antecedents(max_sym, v, shorter_occs, a, use_negated_occs);
                }
            }
        }
    }
    const char* err = aiger_check(a);
    if (err) {
        printf("%s\n", err);
    }
    
    return a;
}

aiger* synthesis_implementation(aiger* problem, Matrix* m, Options* options) {
    if (debug_verbosity >= VERBOSITY_HIGH) {
        matrix_print_debug(m);
    }
    aiger* a = aiger_init();
    
    // uncontrollable inputs
    for (unsigned i = 0; i < problem->num_inputs; i++) {
        aiger_symbol input = problem->inputs[i];
        if ( ! is_controllable(input.name)) {
            aiger_add_input(a, input.lit, input.name);
        }
    }
    // outputs: the controllables
    for (unsigned i = 0; i < problem->num_inputs; i++) {
        aiger_symbol input = problem->inputs[i];
        if (is_controllable(input.name)) {
            aiger_add_output(a, input.lit, input.name);
        }
    }
    
    ////////// Define everything that the controllables depend on
    
    heap* variables_to_define = heap_init(compare_variables_by_occ_num); // queue of variables for which we need the definitions
    map* defined = map_init();
    
    for (unsigned i = 0; i < problem->num_inputs; i++) {
        aiger_symbol input = problem->inputs[i];
        if (is_controllable(input.name)) {
            MVar* v = map_get(m->var_lookup, aiger_lit2lit(input.lit));
            assert(v);
            V4("Adding var %d to definition queue (controllable).\n", v->var_id);
            heap_push(variables_to_define, v);
            map_add(defined, v->var_id, NULL);
        }
    }
    
    unsigned max_sym = (unsigned) m->max_var_id * 2;
    
    while (heap_count(variables_to_define) > 0) {
        MVar* v = heap_pop(variables_to_define);
        if (v->scope->qtype == QUANTIFIER_UNIVERSAL) {
            aiger_symbol* latch = aiger_is_latch(a, var2aigerlit((unsigned)v->var_id));
            if (latch) {
                aiger_add_input(a, latch->lit, latch->name);
            }
            continue;
        }
        
        unsigned aigerlit = var2aigerlit((unsigned) v->var_id);
        if (aigerlit > 2 * problem->maxvar || (aiger_is_and(a, aigerlit) == NULL && aiger_is_input(a, aigerlit) == NULL && aiger_is_latch(a, aigerlit) == NULL))  {
            
            if (v->value != 0) {
                unsigned c = v->value == 1 ? 1 : 0;
                aiger_add_and(a, 2 * (unsigned) v->var_id, c, c);
            } else {
                bool use_negated_occs = vector_count(v->pos_occs) > vector_count(v->neg_occs);
                vector* shorter_occs = use_negated_occs ? v->neg_occs : v->pos_occs;
                max_sym = encode_unique_antecedents(max_sym, v, shorter_occs, a, use_negated_occs);
                
                for (unsigned i = 0; i < vector_count(shorter_occs); i++) {
                    Occ* o = vector_get(shorter_occs, i);
                    for (unsigned j = 0; j < o->clause->size; j++) {
                        Occ* clause_occ = &o->clause->occs[j];
                        if ( ! map_contains(defined, clause_occ->var->var_id)) {
                            V4("Adding var %d to definition queue.\n", clause_occ->var->var_id);
                            heap_push(variables_to_define, clause_occ->var);
                            map_add(defined, clause_occ->var->var_id, NULL);
                        }
                    }
                }
            }
        }
    }
    
    heap_free(variables_to_define);
    map_free(defined);
    
    const char* err = aiger_check(a);
    if (err) {
        LOG_ERROR("AIGER library reports an error: \n%s", err);
    }
    
    return a;
}



aiger* synthesis_certificate(aiger* problem, Matrix* m, Options* options) {
    if (debug_verbosity >= VERBOSITY_HIGH) {
        matrix_print_debug(m);
    }
    aiger* certificate = aiger_init(); // need a copy, because the controllable inputs are now and gates.
    
    // latches
    for (size_t i = 0; i < problem->num_latches; i++) {
        aiger_symbol l = problem->latches[i];
        aiger_add_latch(certificate, l.lit, l.next, l.name);
    }
    // uncontrollable inputs
    for (size_t i = 0; i < problem->num_inputs; i++) {
        aiger_symbol input = problem->inputs[i];
        if ( ! is_controllable(input.name)) {
            aiger_add_input(certificate, input.lit, input.name);
        }
    }
    // outputs
    assert(problem->num_outputs > 0);
    for (size_t i = 0; i < problem->num_outputs; i++) {
        aiger_symbol o = problem->outputs[i];
        aiger_add_output(certificate, o.lit, o.name);
    }
    // and gates
    for (size_t i = 0; i < problem->num_ands; i++) {
        aiger_and and = problem->ands[i];
        aiger_add_and(certificate, and.lhs, and.rhs0, and.rhs1);
    }
    // also copy the comments
    certificate->comments = problem->comments;
    
    ////////// Define the controllables
    
    aiger* implementation = synthesis_implementation(problem, m, options);
    
    //// Merge the implementation into the certificate.
    
    map* translation_table = map_init();
    unsigned maxvar =  2 * certificate->maxvar;
    V0("Debug: check maxvar for consistency: maxvar is %u\n", maxvar);
    
    map_add(translation_table, 0, 0);
    
    // certificate uses the inputs of the problem
    for (size_t i = 0; i < problem->num_inputs; i++) {
        aiger_symbol input = problem->inputs[i];
        map_add(translation_table, (int) input.lit, (void*) (unsigned long) input.lit);
    }
    // ... and also the latches of the problem
    for (size_t i = 0; i < problem->num_latches; i++) {
        aiger_symbol l = problem->latches[i];
        map_add(translation_table, (int) l.lit, (void*) (unsigned long) l.lit);
    }
    
    for (size_t i = 0; i < implementation->num_ands; i++) {
        aiger_and and = implementation->ands[i];
        if (!map_contains(translation_table, (int) and.lhs)) {
            map_add(translation_table, (int) and.lhs, (void*) (unsigned long) inc(&maxvar));
        }
        if (!map_contains(translation_table, (int) aiger_strip(and.rhs0))) {
            map_add(translation_table, (int) aiger_strip(and.rhs0), (void*) (unsigned long) inc(&maxvar));
        }
        if (!map_contains(translation_table, (int) aiger_strip(and.rhs1))) {
            map_add(translation_table, (int) aiger_strip(and.rhs1), (void*) (unsigned long) inc(&maxvar));
        }
        
        unsigned new_rhs0 = (unsigned) map_get(translation_table, (int) aiger_strip(and.rhs0)) + aiger_sign(and.rhs0);
        unsigned new_rhs1 = (unsigned) map_get(translation_table, (int) aiger_strip(and.rhs1)) + aiger_sign(and.rhs1);
        V4("From %u %u %u  to  %u %u %u\n", and.lhs, and.rhs0, and.rhs1, (unsigned) map_get(translation_table, (int) and.lhs), new_rhs0, new_rhs1);
        
        aiger_add_and(certificate, (unsigned) map_get(translation_table, (int) and.lhs), new_rhs0, new_rhs1);
    }
    
    const char* err = aiger_check(certificate);
    if (err) {
        LOG_ERROR("AIGER library reports an error: \n%s", err);
    }
    
    return certificate;
}
