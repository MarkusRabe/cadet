//
//  parse.c
//  caqe
//
//  Copyright (c) 2015, Leander Tentrup, Saarland University
//                2015, Markus Rabe, University of California, Berkeley
//
//  Permission is hereby granted, free of charge, to any person obtaining
//  a copy of this software and associated documentation files (the
//  "Software"), to deal in the Software without restriction, including
//  without limitation the rights to use, copy, modify, merge, publish,
//  distribute, sublicense, and/or sell copies of the Software, and to
//  permit persons to whom the Software is furnished to do so, subject to
//  the following conditions:
//
//  The above copyright notice and this permission notice shall be
//  included in all copies or substantial portions of the Software.
//
//  THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
//  EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
//  MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT.
//  IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY
//  CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT,
//  TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION WITH THE
//  SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
//

#include "cadet_internal.h"

#include "util.h"
#include "log.h"
#include "qcnf.h"
#include "aiger.h"
#include "aiger_utils.h"
#include "c2_rl.h"

#include <string.h>
#include <assert.h>
#include <stdio.h>

inline static void skip_space(char* buffer, size_t* pos) {
    while (buffer[*pos] == ' ') {
        (*pos)++;
    }
}

static inline int create_lit(int var, bool negated) { return negated ? -var : var; }

inline static int get_next_lit(char* buffer, size_t* pos, int line_num) {
    if (!(buffer[*pos] == '-' || (buffer[*pos] >= '0' && buffer[*pos] <= '9'))) {
        V1("Unexpected character: %c (ascii: %d) in line %d char %zu\n",buffer[*pos],buffer[*pos],line_num,*pos);
        assert(false);
    }
    bool negated = (buffer[*pos] == '-');
    if (negated) {
        (*pos)++;
    }
    int var = 0;
    if (!(buffer[*pos] >= '0' && buffer[*pos] <= '9')) {
        V1("Unexpected digit: %c (ascii: %d) in line %d char %zu\n",buffer[*pos],buffer[*pos],line_num,*pos);
        abort();
    }
    while (buffer[*pos] >= '0' && buffer[*pos] <= '9') {
        var = (var * 10) + (buffer[*pos] - '0');
        (*pos)++;
    }
    return create_lit(var, negated);
}

// Has to be called with line being the header from the QDIMACS file.
C2* c2_from_qdimacs_and_header(Options* options, FILE* file, char* header, int line_num) {
    assert(header != NULL);
    C2* c2 = c2_init(options);
    
    // Parse number of variables and number of clauses.
    size_t var_num;
    size_t clause_num;
    sscanf(header, "p cnf %zd %zd", &var_num, &clause_num);
    int log_of_var_num = 0;
    size_t var_num_copy = var_num;
    while (var_num_copy >>= 1) log_of_var_num++;
    int len = 10 + (log_of_var_num + 2) * (int)var_num; // assuming that literals don't repeat too often within a clause
    assert(len >= 0);
    char* line = malloc((size_t)len);
    
    V3("File indicates %zu variables and %zu clauses.\n", var_num, clause_num);
    
    var_vector_resize(c2->qcnf->vars, (unsigned) (2 * var_num + 1)); // should usually prevent resizing of the var vector
    assert(var_vector_count(c2->qcnf->vars) == 1); // nullvar
//    memset(qcnf->vars.data, 0, sizeof(Var) * (var_num + var_num/2));
    // We parse dependency quantifiers after all regular quantifiers are parsed. So the following two vectors store their variables and dependency sets.
    vector* dependency_sets = vector_init();
    int_vector* dependency_variables = int_vector_init();
    
    // Parse the quantifier part
    unsigned qlvl = 0;
    while (fgets(line, len, file)) {
        line_num++;
        size_t pos = 0;
        bool is_dependency_quantifier = false;
        
        switch (line[0]) {
            case 'e':
                if (qlvl%2 == 1) {
                    qlvl++;
                } else if (qlvl != 0) {
                    V0("Warning: Consecutive quantifiers of the same type are not allowed in the DIMACS/QDIMACS/DQDIMACS standard (line %d)\n", line_num);
                }
                assert(qlvl%2 == 0);
                pos++;
                break;
            case 'a':
                if (qlvl%2 == 0) {
                    qlvl++;
                } else {
                    V0("Warning: Consecutive quantifiers of the same type are not allowed in the DIMACS/QDIMACS/DQDIMACS standard (line %d).\n", line_num);
                }
                pos++;
                break;
            case 'd':
                // qlvl++; or should we?
                pos++;
                is_dependency_quantifier = true;
                break;
            case 'c':
                V0("Comment in line %d is not conform in the DIMACS/QDIMACS/DQDIMACS standard.\n", line_num);
                continue;
                break;
            default:
                break;
        }
        if (pos == 0) {
            // reached end of quantification
            break;
        }
        
        bool num_vars_parsed_this_line = 0;
        if (is_dependency_quantifier) {
            vector_add(dependency_sets, int_vector_init());
        }
        
        while (line[pos] != '\n' && line[pos] != '\r' && line[pos] != '\0') {
            skip_space(line, &pos);
            int next_lit = get_next_lit(line, &pos, line_num);
            if (next_lit == 0) {
                break;
            }
            if (next_lit < 0) {
                V0("Error: Quantifier introduces negative number as a variable name (line %d). Abort.\n", line_num);
                abort();
            }
            
            if (is_dependency_quantifier) {
                if (num_vars_parsed_this_line == 0) {
                    int_vector_add(dependency_variables, next_lit);
                } else {
                    if (!qcnf_var_exists(c2->qcnf, (unsigned) next_lit)) {
                        V0("Error: Variable %d in line %d must be introduced as universal variable before it occurs in the scope of a dependency quantifier.\n",next_lit,line_num);
                        abort();
                    }
                    int_vector_add(vector_get(dependency_sets, vector_count(dependency_sets) - 1), next_lit);
                }
            } else {
                bool is_universal = qlvl % 2 == 1;
                
                if (qcnf_var_exists(c2->qcnf, (unsigned) next_lit)) {
                    V0("Error: line %d contains duplicate variable %d.\n", line_num, next_lit);
                    abort();
                }
                c2_new_variable(c2, is_universal, qlvl / 2 + (is_universal ? 1 : 0), (unsigned) next_lit);
            }
            num_vars_parsed_this_line += 1;
            skip_space(line, &pos);
        }
    }
    
    if (qlvl % 2 == 1) {
        LOG_WARNING("Quantifier hierarchy ended with a universal quantifier.");
        if (qlvl == 1) {
            LOG_WARNING("Removing last quantifier. Will obtain a propositional problem. This is a bit hacky, so beware.");
            vector_reduce_count(c2->qcnf->scopes, 1);
            c2->qcnf->problem_type = QCNF_PROPOSITIONAL;
            for (unsigned i = 0; i < var_vector_count(c2->qcnf->vars); i++) {
                Var* v = var_vector_get(c2->qcnf->vars, i);
                if (v->var_id && v->is_universal) {
                    abortif(vector_count(&v->pos_occs) || vector_count(&v->neg_occs), "Universal variables shouldn't have any occurrences in a propositional problem.");
                    v->var_id = 0;
                    v->is_universal = 0;
                    free(v->pos_occs.data);
                    free(v->neg_occs.data);
                }
            }
        }
    }
    
    // TODO: the following is a bit out of date; moved this function from qcnf to c2 at some point
    if (int_vector_count(dependency_variables) != 0) {
        assert(vector_count(dependency_sets) == int_vector_count(dependency_variables));
        assert(! qcnf_is_DQBF(c2->qcnf));
        qcnf_convert_to_DQBF(c2->qcnf);
        
        for (unsigned i = 0; i < vector_count(dependency_sets); i++) {
            unsigned dep_var_id = (unsigned) int_vector_get(dependency_variables, i);
            int_vector* dep_set = vector_get(dependency_sets, i);
            
            int_vector_sort(dep_set, compare_integers_natural_order);
            unsigned dependency_scope_id = qcnf_scope_init(c2->qcnf, dep_set);
            c2_new_variable(c2, false, dependency_scope_id, dep_var_id);
        }
    }

    if (debug_verbosity >= VERBOSITY_ALL) {
        V4("Detected the following quantifier hierarchy:\n");
        qcnf_print_qdimacs_quantifiers(c2->qcnf, stdout);
    }
    if (feof(file)) {
        free(line);
        return c2;
    }
    
    // Parse the matrix
    do {
        //printf("%s", line);
        size_t pos = 0;
        line_num++;
        if (line[0] == 'c') {
            continue;
        }
        while (line[pos] != '\n' && line[pos] != '\r' && line[pos] != '\0') {
            skip_space(line, &pos);
            int next_lit = get_next_lit(line, &pos, line_num);
            abortif(pos >= (size_t)len, "Clause was way too long. Cannot parse.\n");
            if (next_lit != 0 && !qcnf_var_exists(c2->qcnf, lit_to_var(next_lit))) {
                c2_new_variable(c2, 0, 0, lit_to_var(next_lit));
            }
            c2_add_lit(c2, next_lit);
            skip_space(line, &pos);
        }
    } while (fgets(line, len, file));
    abortif(int_vector_count(c2->qcnf->new_clause) != 0, "Last clause was not closed by 0.");
    free(line);
    return c2;
}


bool is_controllable_input(const char* str, Options* options) {
    return strlen(str) >= strlen(options->aiger_controllable_inputs)
        && strncmp(options->aiger_controllable_inputs, str, strlen(options->aiger_controllable_inputs)) == 0;
}

unsigned aiger_quantification_levels(unsigned depends_on_input_group) {
    return (depends_on_input_group + 1) / 2; // because we joined quantification levels in CADET2
}

//C2* c2_from_aiger(aiger* aig, Options* o) {
//    assert (aiger_check(aig) == NULL);
//    abortif(aig->num_bad == 0 && aig->num_constraints == 0, "No bad outputs and no constraints detected.");
//    if (aig->num_bad > 1) {
//        LOG_WARNING("Multiple bad outputs defined. CADET uses their conjunction as the bad property.");
//    }
//    abortif(aig->num_latches > 0, "CADET only supports reading combinatorial AIGs for QBF input. What should a latch mean in the context of a QBF?");
//    if (o->aiger_negated_encoding) {
//        LOG_WARNING("The negated encoding so far only creates 3QBF, according to the informal standard that Baruch and Markus agreed on. Shall be extended to Leander's QBF interpretation of AIGs later on.");
//    }
//
//    C2* c2 = c2_init(o);
//
//    unsigned input_group = o->aiger_negated_encoding ? 0 : 1;
//
//    // uncontrollable inputs
//    for (size_t i = 0; i < aig->num_inputs; i++) {
//        aiger_symbol input = aig->inputs[i];
//        if ( ! is_controllable_input(input.name,o)) {
//            c2_new_variable(c2, aiger_quantification_polarity(input_group, true), aiger_quantification_levels(input_group), aiger_lit2var(input.lit));
//            if (o->print_name_mapping)
//                V0("%s not controllable; var %d\n", input.name, aiger_lit2var(input.lit));
//            options_set_variable_name(o, aiger_lit2var(input.lit), input.name);
//        }
//    }
//
//    input_group += 1;
//
//    // controllable inputs
//    for (size_t i = 0; i < aig->num_inputs; i++) {
//        aiger_symbol input = aig->inputs[i];
//        if (is_controllable_input(input.name, o)) {
//            c2_new_variable(c2, aiger_quantification_polarity(input_group, true), aiger_quantification_levels(input_group), aiger_lit2var(input.lit));
//            if (o->print_name_mapping)
//                V0("%s is controllable; var %d\n", input.name, aiger_lit2var(input.lit));
//            options_set_variable_name(o, aiger_lit2var(input.lit), input.name);
//        }
//    }
//
////    // next values for latches
////    for (size_t i = 0; i < aig->num_latches; i++) {
////        aiger_symbol l = aig->latches[i];
////        if (l.next > 1 && ! qcnf_var_exists(qcnf, aiger_lit2var(l.next))) {
////            c2_new_variable(c2, true, 1, aiger_lit2var(l.next));
////        }
////    }
//
//    // remember the names of outputs
//    for (size_t i = 0; i < aig->num_outputs; i++) {
//        aiger_symbol out = aig->outputs [i];
//        options_set_variable_name(o, aiger_lit2var(out.lit), out.name);
//    }
//
//    // outputs
//    for (size_t i = 0; i < aig->num_bad; i++) {
//        aiger_symbol b = aig->bad[i];
//        if (b.lit > 1 && ! qcnf_var_exists(c2->qcnf, aiger_lit2var(b.lit))) {
//            c2_new_variable(c2, aiger_quantification_polarity(input_group, false), aiger_quantification_levels(input_group), aiger_lit2var(b.lit));
//        } // else ignore // we can ignore true and false signals.
//        options_set_variable_name(o, aiger_lit2var(b.lit), b.name);
//    }
//
//    for (size_t i = 0; i < aig->num_constraints; i++) {
//        aiger_symbol c = aig->constraints[i];
//        if (c.lit > 1 && ! qcnf_var_exists(c2->qcnf, aiger_lit2var(c.lit))) {
//            c2_new_variable(c2, aiger_quantification_polarity(o->aiger_negated_encoding ? 0 : 1, false), aiger_quantification_levels(o->aiger_negated_encoding ? 0 : 1), aiger_lit2var(c.lit));
//        } // else ignore // we can ignore true and false signals.
//        options_set_variable_name(o, aiger_lit2var(c.lit), c.name);
//    }
//    unsigned circuit_depth = 0;
//    while (true) {
//        bool new_gate = false;
//        for (size_t i = 0; i < aig->num_ands; i++) {
//            aiger_and a = aig->ands[i];
//            if (! qcnf_var_exists(c2->qcnf, aiger_lit2var(a.lhs)) && qcnf_var_exists(c2->qcnf, aiger_lit2var(a.rhs0)) && qcnf_var_exists(c2->qcnf, aiger_lit2var(a.rhs1))) {
//                new_gate = true;
//                Var* rhs0 = var_vector_get(c2->qcnf->vars, aiger_lit2var(a.rhs0));
//                Var* rhs1 = var_vector_get(c2->qcnf->vars, aiger_lit2var(a.rhs1));
//                unsigned gate_dependency = rhs0->scope_id > rhs1->scope_id ? rhs0->scope_id : rhs1->scope_id;
//                c2_new_variable(c2, aiger_quantification_polarity(gate_dependency, false), aiger_quantification_levels(gate_dependency), aiger_lit2var(a.lhs));
//            }
//        }
//        if (!new_gate) {
//            break;
//        }
//        circuit_depth += 1;
//    }
//    V1("Circuit has depth %u\n", circuit_depth);
//
//    ////// CLAUSES //////
//
//    // bads
//    unsigned bads_qcnf_var = (unsigned) aiger_lit2lit( 2 * (aig->maxvar + 1) );
//    options_set_variable_name(o, bads_qcnf_var, "BADS");
//
//    c2_new_variable(c2, aiger_quantification_polarity(input_group, false), aiger_quantification_levels(input_group), bads_qcnf_var);
//    if (o->print_name_mapping) {
//        V0("bads summary variable %d\n", bads_qcnf_var);
//    }
//
//    for (size_t i = 0; i < aig->num_bad; i++) {
//        aiger_symbol b = aig->bad[i];
//        c2_add_lit(c2, - aiger_lit2lit(b.lit));
//        c2_add_lit(c2, (Lit) bads_qcnf_var);
//        c2_add_lit(c2, 0);
//
//        if (o->print_name_mapping) {
//            V0("bad %d\n", aiger_lit2lit(b.lit));
//        }
//    }
//    for (size_t i = 0; i < aig->num_bad; i++) {
//        aiger_symbol b = aig->bad[i];
//        c2_add_lit(c2, aiger_lit2lit(b.lit));
//    }
//    c2_add_lit(c2, - (Lit) bads_qcnf_var);
//    c2_add_lit(c2, 0);
//
//    // constraints
//    unsigned constraints_qcnf_var = (unsigned) aiger_lit2lit( 2 * (aig->maxvar + 2) );
//    int_vector_add(c2->qcnf->universals_constraints, (int) constraints_qcnf_var);
//    options_set_variable_name(o, constraints_qcnf_var, "CONSTRAINTS");
//
//    c2_new_variable(c2, aiger_quantification_polarity(o->aiger_negated_encoding ? 0 : 1, false), aiger_quantification_levels(o->aiger_negated_encoding ? 0 : 1), constraints_qcnf_var);
//    if (o->print_name_mapping) {
//        V0("constraints summary variable %d\n", constraints_qcnf_var);
//    }
//
//    for (size_t i = 0; i < aig->num_constraints; i++) {
//        aiger_symbol c = aig->constraints[i];
//        c2_add_lit(c2, aiger_lit2lit(c.lit));
//        c2_add_lit(c2, - (Lit) constraints_qcnf_var);
//        c2_add_lit(c2, 0);
//        if (o->print_name_mapping)
//            V0("constraint %d\n", aiger_lit2lit(c.lit));
//    }
//    for (size_t i = 0; i < aig->num_constraints; i++) {
//        aiger_symbol c = aig->constraints[i];
//        c2_add_lit(c2, - aiger_lit2lit(c.lit));
//    }
//    c2_add_lit(c2, (Lit) constraints_qcnf_var);
//    c2_add_lit(c2, 0);
//
//    if (o->aiger_negated_encoding) {
//        LOG_WARNING("Double-check polarity of bad signals and constraints in negated AIGER encoding.\n");
//        c2_add_lit(c2, (Lit) - bads_qcnf_var);
//        c2_add_lit(c2, 0);
//        c2_add_lit(c2, (Lit) constraints_qcnf_var);
//        c2_add_lit(c2, 0);
//
//    } else {
//        // putting constraints and bads together: if the constraints hold, then the bads should be false.
//        c2_add_lit(c2, (Lit) - constraints_qcnf_var);
//        c2_add_lit(c2, (Lit) - bads_qcnf_var);
//        c2_add_lit(c2, 0);
//    }
//
//    // circuit definition
//    for (size_t i = 0; i < aig->num_ands; i++) {
//        aiger_and a = aig->ands[i];
//        assert(a.lhs % 2 == 0);
//        // make sure all three symbols exist, create if necessary
//        assert(qcnf_var_exists(c2->qcnf, aiger_lit2var(a.lhs)));
//        assert(a.rhs0 < 2 || qcnf_var_exists(c2->qcnf, aiger_lit2var(a.rhs0)));
//        assert(a.rhs0 < 2 || qcnf_var_exists(c2->qcnf, aiger_lit2var(a.rhs1)));
//
//        // create and gate with with three clauses
//        if (a.rhs0 != 1) {
//            c2_add_lit(c2, - aiger_lit2lit(a.lhs));
//            if (a.rhs0 != 0) {
//                c2_add_lit(c2, aiger_lit2lit(a.rhs0));
//            } // else lit is literally false
//            c2_add_lit(c2, 0);
//        } // else lit is true and thus clause is satisfied.
//
//        if (a.rhs1 != 1) {
//            c2_add_lit(c2,  - aiger_lit2lit(a.lhs));
//            if (a.rhs1 != 0) {
//                c2_add_lit(c2,  aiger_lit2lit(a.rhs1));
//            } // else lit is literally false
//            c2_add_lit(c2, 0);
//        } // else lit is true and thus clause is satisfied.
//
//        if (a.rhs0 != 0 && a.rhs1 != 0) {
//            c2_add_lit(c2, aiger_lit2lit(a.lhs));
//            if (a.rhs0 != 1) { // lit is literally false
//                c2_add_lit(c2,  - aiger_lit2lit(a.rhs0));
//            }
//            if (a.rhs1 != 1) { // lit is literally false
//                c2_add_lit(c2,  - aiger_lit2lit(a.rhs1));
//            }
//            c2_add_lit(c2, 0);
//        }
//    }
//    return c2;
//}

unsigned qaiger_quantifier_level(char* name) {
    if (strncmp("0 ", name, 2) == 0) {
        return 0;
    }
    if (strncmp("1 ", name, 2) == 0) {
        return 1;
    }
    if (strncmp("2 ", name, 2) == 0) {
        return 2;
    }
    abortif(true, "Only 2 QBF is supported");
}

C2* c2_from_qaiger(aiger* aig, Options* options) {
    if (!options) {options = default_options();}
    assert (aiger_check(aig) == NULL);
    if (aig->num_bad > 0) {
        LOG_WARNING("QAIGER does not support bad outputs; conjoining them with outputs.");
    }
    if (aig->num_outputs > 1) {
        LOG_WARNING("QAIGER requires a single output but given %u; conjoining outputs.", aig->num_outputs);
    }
    if (aig->num_constraints != 0) {
        LOG_WARNING("QAIGER does not support constraints.");
    }
    if (aig->num_bad > 1) {
        LOG_WARNING("Multiple bad outputs defined. CADET uses their conjunction as the bad property.");
    }
    abortif(aig->num_latches > 0, "CADET only supports reading combinatorial AIGs for QBF input.");
    
    C2* c2 = c2_init(options);
    
    // uncontrollable inputs
    for (size_t i = 0; i < aig->num_inputs; i++) {
        aiger_symbol input = aig->inputs[i];
        unsigned qaiger_quantifier_lvl = qaiger_quantifier_level(input.name);
        c2_new_variable(c2, qaiger_quantifier_lvl % 2, aiger_quantification_levels(qaiger_quantifier_lvl), aiger_lit2var(input.lit));
        
        if (options->print_name_mapping) {
            V0("%s %s controllable; var %d\n",
               input.name,
               qaiger_quantifier_lvl == 1 ? "not" : "is",
               aiger_lit2var(input.lit));
        }
        options_set_variable_name(options, aiger_lit2var(input.lit), input.name);
    }
    
    // remember the names of outputs, but don't do more
    for (size_t i = 0; i < aig->num_outputs; i++) {
        aiger_symbol out = aig->outputs [i];
        options_set_variable_name(options, aiger_lit2var(out.lit), out.name);
    }
    
    // outputs
    for (size_t i = 0; i < aig->num_bad; i++) {
        aiger_symbol b = aig->bad[i];
        if (b.lit > 1 && ! qcnf_var_exists(c2->qcnf, aiger_lit2var(b.lit))) {
            c2_new_variable(c2, false, qaiger_quantifier_level(b.name), aiger_lit2var(b.lit));
        } // else ignore // we can ignore true and false signals.
        options_set_variable_name(options, aiger_lit2var(b.lit), b.name);
    }
    
    for (size_t i = 0; i < aig->num_constraints; i++) {
        aiger_symbol c = aig->constraints[i];
        if (c.lit > 1 && ! qcnf_var_exists(c2->qcnf, aiger_lit2var(c.lit))) {
            c2_new_variable(c2, false, 1, aiger_lit2var(c.lit));
        } // else ignore // we can ignore true and false signals.
        options_set_variable_name(options, aiger_lit2var(c.lit), c.name);
    }
    unsigned circuit_depth = 0;
    while (true) {
        bool new_gate = false;
        for (size_t i = 0; i < aig->num_ands; i++) {
            aiger_and a = aig->ands[i];
            if (! qcnf_var_exists(c2->qcnf, aiger_lit2var(a.lhs)) && qcnf_var_exists(c2->qcnf, aiger_lit2var(a.rhs0)) && qcnf_var_exists(c2->qcnf, aiger_lit2var(a.rhs1))) {
                new_gate = true;
                Var* rhs0 = var_vector_get(c2->qcnf->vars, aiger_lit2var(a.rhs0));
                Var* rhs1 = var_vector_get(c2->qcnf->vars, aiger_lit2var(a.rhs1));
                unsigned gate_dependency = rhs0->scope_id > rhs1->scope_id ? rhs0->scope_id : rhs1->scope_id;
                c2_new_variable(c2, false, aiger_quantification_levels(gate_dependency), aiger_lit2var(a.lhs));
            }
        }
        if (!new_gate) {
            break;
        }
        circuit_depth += 1;
    }
    V1("Circuit has depth %u\n", circuit_depth);
    
    ////// CLAUSES //////
    
    // bads
    unsigned bads_qcnf_var = (unsigned) aiger_lit2lit( 2 * (aig->maxvar + 1) );
    options_set_variable_name(options, bads_qcnf_var, "BADS");
    
    c2_new_variable(c2, false, 1, bads_qcnf_var);
    if (options->print_name_mapping) {
        V0("bads summary variable %d\n", bads_qcnf_var);
    }
    
    for (size_t i = 0; i < aig->num_outputs; i++) {
        aiger_symbol o = aig->outputs[i];
        c2_add_lit(c2, - aiger_lit2lit(o.lit));
        c2_add_lit(c2, (Lit) bads_qcnf_var);
        c2_add_lit(c2, 0);
        
        if (options->print_name_mapping) {
            V0("bad %d\n", aiger_lit2lit(o.lit));
        }
    }
    for (size_t i = 0; i < aig->num_bad; i++) {
        aiger_symbol b = aig->bad[i];
        c2_add_lit(c2, - aiger_lit2lit(b.lit));
        c2_add_lit(c2, (Lit) bads_qcnf_var);
        c2_add_lit(c2, 0);
        
        if (options->print_name_mapping) {
            V0("bad %d\n", aiger_lit2lit(b.lit));
        }
    }
    for (size_t i = 0; i < aig->num_outputs; i++) {
        aiger_symbol o = aig->outputs[i];
        c2_add_lit(c2, aiger_lit2lit(o.lit));
    }
    for (size_t i = 0; i < aig->num_bad; i++) {
        aiger_symbol b = aig->bad[i];
        c2_add_lit(c2, aiger_lit2lit(b.lit));
    }
    c2_add_lit(c2, - (Lit) bads_qcnf_var);
    c2_add_lit(c2, 0);
    
    // constraints
    unsigned constraints_qcnf_var = (unsigned) aiger_lit2lit( 2 * (aig->maxvar + 2) );
//    int_vector_add(c2->qcnf->universals_constraints, (int) constraints_qcnf_var);
    options_set_variable_name(options, constraints_qcnf_var, "CONSTRAINTS");
    
    c2_new_variable(c2, false, 1, constraints_qcnf_var);
    if (options->print_name_mapping) {
        V0("constraints summary variable %d\n", constraints_qcnf_var);
    }
    
    for (size_t i = 0; i < aig->num_constraints; i++) {
        aiger_symbol c = aig->constraints[i];
        c2_add_lit(c2, aiger_lit2lit(c.lit));
        c2_add_lit(c2, - (Lit) constraints_qcnf_var);
        c2_add_lit(c2, 0);
        if (options->print_name_mapping)
            V0("constraint %d\n", aiger_lit2lit(c.lit));
    }
    for (size_t i = 0; i < aig->num_constraints; i++) {
        aiger_symbol c = aig->constraints[i];
        c2_add_lit(c2, - aiger_lit2lit(c.lit));
    }
    c2_add_lit(c2, (Lit) constraints_qcnf_var);
    c2_add_lit(c2, 0);
    
    // putting constraints and bads together: if the constraints hold, then the bads should be false.
    c2_add_lit(c2, (Lit) - constraints_qcnf_var);
    c2_add_lit(c2, (Lit) - bads_qcnf_var);
    c2_add_lit(c2, 0);
    
    // circuit definition
    for (size_t i = 0; i < aig->num_ands; i++) {
        aiger_and a = aig->ands[i];
        assert(a.lhs % 2 == 0);
        // make sure all three symbols exist, create if necessary
        assert(qcnf_var_exists(c2->qcnf, aiger_lit2var(a.lhs)));
        assert(a.rhs0 < 2 || qcnf_var_exists(c2->qcnf, aiger_lit2var(a.rhs0)));
        assert(a.rhs0 < 2 || qcnf_var_exists(c2->qcnf, aiger_lit2var(a.rhs1)));
        
        // create and gate with with three clauses
        if (a.rhs0 != 1) {
            c2_add_lit(c2, - aiger_lit2lit(a.lhs));
            if (a.rhs0 != 0) {
                c2_add_lit(c2, aiger_lit2lit(a.rhs0));
            } // else lit is literally false
            c2_add_lit(c2, 0);
        } // else lit is true and thus clause is satisfied.
        
        if (a.rhs1 != 1) {
            c2_add_lit(c2,  - aiger_lit2lit(a.lhs));
            if (a.rhs1 != 0) {
                c2_add_lit(c2,  aiger_lit2lit(a.rhs1));
            } // else lit is literally false
            c2_add_lit(c2, 0);
        } // else lit is true and thus clause is satisfied.
        
        if (a.rhs0 != 0 && a.rhs1 != 0) {
            c2_add_lit(c2, aiger_lit2lit(a.lhs));
            if (a.rhs0 != 1) { // lit is literally false
                c2_add_lit(c2,  - aiger_lit2lit(a.rhs0));
            }
            if (a.rhs1 != 1) { // lit is literally false
                c2_add_lit(c2,  - aiger_lit2lit(a.rhs1));
            }
            c2_add_lit(c2, 0);
        }
    }
    return c2;
}

C2* c2_from_file(FILE* file, Options* options) {
    if (!options) {options = default_options();}
    int len = 1000; // max 1kb for the first line
    char *line = malloc((size_t)len);
    
    abortif(!cautious_readline(line, len, file), "Could not read first line");
    
    int line_num = 1;
    
    // Skip comment lines
    while (line[0] == 'c') {
        line_num++;
        abortif(!cautious_readline(line, len, file), "Expected header after comments ending in line %d", line_num);
    }
    
    char* qcnf_header_start = "p cnf ";
    char* aiger_header_start = "aig ";
    char* aiger_ascii_header_start = "aag ";
    C2* solver = NULL;
    if (strncmp(qcnf_header_start, line, strlen(qcnf_header_start)) == 0) {
        solver = c2_from_qdimacs_and_header(options, file, line, line_num);
    } else if (   strncmp(aiger_header_start, line, strlen(aiger_header_start)) == 0
               || strncmp(aiger_ascii_header_start, line, strlen(aiger_ascii_header_start)) == 0) {
        
        aiger* aig = aiger_init();
        abortif(file == stdin, "AIGER input currently coes not work from stdin.");
        fseek(file, 0, SEEK_SET);
        const char* err = aiger_read_from_file(aig, file);
        
        abortif(err, "Error while reading aiger file:\n %s", err);
        
        solver = c2_from_qaiger(aig, options);
    } else {
        abortif(true, "Cannot identify header of the file. Wrong file format? Some line must start with 'p cnf', 'aig', or 'aag'.");
    }
    
    free(line);
    return solver;
}
