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

#include "parse.h"

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
QCNF* create_qcnf_from_qdimacs(Options* options, FILE* file, char* header, int line_num) {
    assert(header != NULL);
    
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
    
    QCNF* qcnf = qcnf_init();
    var_vector_resize(qcnf->vars, (unsigned) (2 * var_num + 1)); // should usually prevent resizing of the var vector
    assert(var_vector_count(qcnf->vars) == 1); // nullvar
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
                    if (!qcnf_var_exists(qcnf, (unsigned) next_lit)) {
                        V0("Error: Variable %d in line %d must be introduced as universal variable before it occurs in the scope of a dependency quantifier.\n",next_lit,line_num);
                        abort();
                    }
                    int_vector_add(vector_get(dependency_sets, vector_count(dependency_sets) - 1), next_lit);
                }
            } else {
                bool is_universal = qlvl % 2 == 1;
                
                if (qcnf_var_exists(qcnf, (unsigned) next_lit)) {
                    V0("Error: line %d contains duplicate variable %d.\n", line_num, next_lit);
                    abort();
                }
                qcnf_new_var(qcnf, is_universal, qlvl / 2 + (is_universal ? 1 : 0), (unsigned) next_lit);
            }
            num_vars_parsed_this_line += 1;
            skip_space(line, &pos);
        }
    }
    
    if (qlvl % 2 == 1) {
        LOG_WARNING("Quantifier hierarchy ended with a universal quantifier.");
        if (qlvl == 1) {
            LOG_WARNING("Removing last quantifier. Will obtain a propositional problem. This is a bit hacky, so beware.");
            vector_reduce_count(qcnf->scopes, 1);
            qcnf->problem_type = QCNF_PROPOSITIONAL;
            for (unsigned i = 0; i < var_vector_count(qcnf->vars); i++) {
                Var* v = var_vector_get(qcnf->vars, i);
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
    
    if (int_vector_count(dependency_variables) != 0) {
        assert(vector_count(dependency_sets) == int_vector_count(dependency_variables));
        assert(! qcnf_is_DQBF(qcnf));
        qcnf_convert_to_DQBF(qcnf);
        
        for (unsigned i = 0; i < vector_count(dependency_sets); i++) {
            unsigned dep_var_id = (unsigned) int_vector_get(dependency_variables, i);
            int_vector* dep_set = vector_get(dependency_sets, i);
            
            int_vector_sort(dep_set, compare_integers_natural_order);
            unsigned dependency_scope_id = qcnf_scope_init(qcnf, dep_set);
            qcnf_new_var(qcnf, false, dependency_scope_id, dep_var_id);
        }
    }

    if (debug_verbosity >= VERBOSITY_ALL) {
        V4("Detected the following quantifier hierarchy:\n");
        qcnf_print_qdimacs_quantifiers(qcnf, stdout);
    }
    if (feof(file)) {
        free(line);
        return qcnf;
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
            if (pos >= (size_t)len) {
                printf("Clause was way too long. Cannot parse.\n");
                goto error;
            }
            if (next_lit == 0) {
                Clause* c = qcnf_close_clause(qcnf);
                if (c) {c2_rl_new_clause(options, c);}
            } else {
                qcnf_add_lit(qcnf, next_lit);
            }
            skip_space(line, &pos);
        }
    } while (fgets(line, len, file));
    
    // reduce dead memory (could be significant)
    if (int_vector_count(qcnf->new_clause) != 0) {
        V0("Last clause was not closed by 0.");
        goto error;
    }
    free(line);
    int_vector_free(qcnf->new_clause);
    qcnf->new_clause = int_vector_init();
    
    return qcnf;
    
error:
    free(line);
    return NULL;
}


bool is_controllable_input(const char* str, Options* options) {
    return strlen(str) >= strlen(options->aiger_controllable_inputs)
        && strncmp(options->aiger_controllable_inputs, str, strlen(options->aiger_controllable_inputs)) == 0;
}

unsigned aiger_quantification_levels(unsigned depends_on_input_group) {
    return (depends_on_input_group + 1) / 2; // because we joined quantification levels in CADET2
}
// true for universal, false for existential
bool aiger_quantification_polarity(unsigned depends_on_input_group, bool is_input) {
    return depends_on_input_group % 2 == 1 && is_input;
}

QCNF* create_qcnf_from_aiger(aiger* aig, Options* o) {
    
    QCNF* qcnf = qcnf_init();

    assert (aiger_check(aig) == NULL);
    abortif(aig->num_bad == 0 && aig->num_constraints == 0, "No bad outputs and no constraints detected.");
    if (aig->num_bad > 1) {
        LOG_WARNING("Multiple bad outputs defined. CADET uses their conjunction as the bad property.");
    }
    abortif(aig->num_latches > 0, "CADET only supports reading combinatorial AIGs for QBF input. What should a latch mean in the context of a QBF?");
    if (o->aiger_negated_encoding) {
        LOG_WARNING("The negated encoding so far only creates 3QBF, according to the informal standard that Baruch and Markus agreed on. Shall be extended to Leander's QBF interpretation of AIGs later on.");
    }
    
    // latches
//    for (size_t i = 0; i < aig->num_latches; i++) {
//        aiger_symbol l = aig->latches[i];
//        qcnf_new_var(qcnf, true, 1, aiger_lit2var(l.lit));
//        options_set_variable_name(options, aiger_lit2var(l.lit), l.name);
//    }
    
    unsigned input_group = o->aiger_negated_encoding ? 0 : 1;
    
    // uncontrollable inputs
    for (size_t i = 0; i < aig->num_inputs; i++) {
        aiger_symbol input = aig->inputs[i];
        if ( ! is_controllable_input(input.name,o)) {
            qcnf_new_var(qcnf, aiger_quantification_polarity(input_group, true), aiger_quantification_levels(input_group), aiger_lit2var(input.lit));
            if (o->print_name_mapping)
                V0("%s not controllable; var %d\n", input.name, aiger_lit2var(input.lit));
            options_set_variable_name(o, aiger_lit2var(input.lit), input.name);
        }
    }
    
    input_group += 1;
    
    // controllable inputs
    for (size_t i = 0; i < aig->num_inputs; i++) {
        aiger_symbol input = aig->inputs[i];
        if (is_controllable_input(input.name, o)) {
            qcnf_new_var(qcnf, aiger_quantification_polarity(input_group, true), aiger_quantification_levels(input_group), aiger_lit2var(input.lit));
            if (o->print_name_mapping)
                V0("%s is controllable; var %d\n", input.name, aiger_lit2var(input.lit));
            options_set_variable_name(o, aiger_lit2var(input.lit), input.name);
        }
    }
    
//    // next values for latches
//    for (size_t i = 0; i < aig->num_latches; i++) {
//        aiger_symbol l = aig->latches[i];
//        if (l.next > 1 && ! qcnf_var_exists(qcnf, aiger_lit2var(l.next))) {
//            qcnf_new_var(qcnf, true, 1, aiger_lit2var(l.next));
//        }
//    }
    
    // remember the names of outputs
    for (size_t i = 0; i < aig->num_outputs; i++) {
        aiger_symbol out = aig->outputs [i];
        options_set_variable_name(o, aiger_lit2var(out.lit), out.name);
    }
    
    // outputs
    for (size_t i = 0; i < aig->num_bad; i++) {
        aiger_symbol b = aig->bad[i];
        if (b.lit > 1 && ! qcnf_var_exists(qcnf, aiger_lit2var(b.lit))) {
            qcnf_new_var(qcnf, aiger_quantification_polarity(input_group, false), aiger_quantification_levels(input_group), aiger_lit2var(b.lit));
        } // else ignore // we can ignore true and false signals.
        options_set_variable_name(o, aiger_lit2var(b.lit), b.name);
    }
    
    for (size_t i = 0; i < aig->num_constraints; i++) {
        aiger_symbol c = aig->constraints[i];
        if (c.lit > 1 && ! qcnf_var_exists(qcnf, aiger_lit2var(c.lit))) {
            qcnf_new_var(qcnf, aiger_quantification_polarity(o->aiger_negated_encoding ? 0 : 1, false), aiger_quantification_levels(o->aiger_negated_encoding ? 0 : 1), aiger_lit2var(c.lit));
        } // else ignore // we can ignore true and false signals.
        options_set_variable_name(o, aiger_lit2var(c.lit), c.name);
    }
    unsigned circuit_depth = 0;
    while (true) {
        bool new_gate = false;
        for (size_t i = 0; i < aig->num_ands; i++) {
            aiger_and a = aig->ands[i];
            if (! qcnf_var_exists(qcnf, aiger_lit2var(a.lhs)) && qcnf_var_exists(qcnf, aiger_lit2var(a.rhs0)) && qcnf_var_exists(qcnf, aiger_lit2var(a.rhs1))) {
                new_gate = true;
                Var* rhs0 = var_vector_get(qcnf->vars, aiger_lit2var(a.rhs0));
                Var* rhs1 = var_vector_get(qcnf->vars, aiger_lit2var(a.rhs1));
                unsigned gate_dependency = rhs0->scope_id > rhs1->scope_id ? rhs0->scope_id : rhs1->scope_id;
                qcnf_new_var(qcnf, aiger_quantification_polarity(gate_dependency, false), aiger_quantification_levels(gate_dependency), aiger_lit2var(a.lhs));
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
    options_set_variable_name(o, bads_qcnf_var, "BADS");
    
    qcnf_new_var(qcnf, aiger_quantification_polarity(input_group, false), aiger_quantification_levels(input_group), bads_qcnf_var);
    if (o->print_name_mapping) {
        V0("bads summary variable %d\n", bads_qcnf_var);
    }
    
    for (size_t i = 0; i < aig->num_bad; i++) {
        aiger_symbol b = aig->bad[i];
        qcnf_add_lit(qcnf, - aiger_lit2lit(b.lit));
        qcnf_add_lit(qcnf, (Lit) bads_qcnf_var);
        qcnf_close_clause(qcnf);
        
        if (o->print_name_mapping) {
            V0("bad %d\n", aiger_lit2lit(b.lit));
        }
    }
    for (size_t i = 0; i < aig->num_bad; i++) {
        aiger_symbol b = aig->bad[i];
        qcnf_add_lit(qcnf, aiger_lit2lit(b.lit));
    }
    qcnf_add_lit(qcnf, - (Lit) bads_qcnf_var);
    qcnf_close_clause(qcnf);
    
    // constraints
    unsigned constraints_qcnf_var = (unsigned) aiger_lit2lit( 2 * (aig->maxvar + 2) );
    int_vector_add(qcnf->universals_constraints, (int) constraints_qcnf_var);
    options_set_variable_name(o, constraints_qcnf_var, "CONSTRAINTS");
    
    qcnf_new_var(qcnf, aiger_quantification_polarity(o->aiger_negated_encoding ? 0 : 1, false), aiger_quantification_levels(o->aiger_negated_encoding ? 0 : 1), constraints_qcnf_var);
    if (o->print_name_mapping) {
        V0("constraints summary variable %d\n", constraints_qcnf_var);
    }
    
    for (size_t i = 0; i < aig->num_constraints; i++) {
        aiger_symbol c = aig->constraints[i];
        qcnf_add_lit(qcnf, aiger_lit2lit(c.lit));
        qcnf_add_lit(qcnf, - (Lit) constraints_qcnf_var);
        qcnf_close_clause(qcnf);
        if (o->print_name_mapping)
            V0("constraint %d\n", aiger_lit2lit(c.lit));
    }
    for (size_t i = 0; i < aig->num_constraints; i++) {
        aiger_symbol c = aig->constraints[i];
        qcnf_add_lit(qcnf, - aiger_lit2lit(c.lit));
    }
    qcnf_add_lit(qcnf, (Lit) constraints_qcnf_var);
    qcnf_close_clause(qcnf);
    
    if (o->aiger_negated_encoding) {
        LOG_WARNING("Double-check polarity of bad signals and constraints in negated AIGER encoding.\n");
        qcnf_add_lit(qcnf, (Lit) - bads_qcnf_var);
        qcnf_close_clause(qcnf);
        qcnf_add_lit(qcnf, (Lit) constraints_qcnf_var);
        qcnf_close_clause(qcnf);
        
    } else {
        // putting constraints and bads together: if the constraints hold, then the bads should be false.
        qcnf_add_lit(qcnf, (Lit) - constraints_qcnf_var);
        qcnf_add_lit(qcnf, (Lit) - bads_qcnf_var);
        qcnf_close_clause(qcnf);
    }
    
    // circuit definition
    for (size_t i = 0; i < aig->num_ands; i++) {
        aiger_and a = aig->ands[i];
        assert(a.lhs % 2 == 0);
        // make sure all three symbols exist, create if necessary
        assert(qcnf_var_exists(qcnf, aiger_lit2var(a.lhs)));
        assert(a.rhs0 < 2 || qcnf_var_exists(qcnf, aiger_lit2var(a.rhs0)));
        assert(a.rhs0 < 2 || qcnf_var_exists(qcnf, aiger_lit2var(a.rhs1)));
        
        // create and gate with with three clauses
        if (a.rhs0 != 1) {
            qcnf_add_lit(qcnf, - aiger_lit2lit(a.lhs));
            if (a.rhs0 != 0) {
                qcnf_add_lit(qcnf, aiger_lit2lit(a.rhs0));
            } // else lit is literally false
            qcnf_close_clause(qcnf);
        } // else lit is true and thus clause is satisfied.
        
        if (a.rhs1 != 1) {
            qcnf_add_lit(qcnf,  - aiger_lit2lit(a.lhs));
            if (a.rhs1 != 0) {
                qcnf_add_lit(qcnf,  aiger_lit2lit(a.rhs1));
            } // else lit is literally false
            qcnf_close_clause(qcnf);
        } // else lit is true and thus clause is satisfied.
        
        if (a.rhs0 != 0 && a.rhs1 != 0) {
            qcnf_add_lit(qcnf, aiger_lit2lit(a.lhs));
            if (a.rhs0 != 1) { // lit is literally false
                qcnf_add_lit(qcnf,  - aiger_lit2lit(a.rhs0));
            }
            if (a.rhs1 != 1) { // lit is literally false
                qcnf_add_lit(qcnf,  - aiger_lit2lit(a.rhs1));
            }
            qcnf_close_clause(qcnf);
        }
    }
    
    return qcnf;
}


QCNF* create_qcnf_from_file(FILE* file, Options* options) {
    int len = 1000; // max 1kb for the first line
    char *line = malloc((size_t)len);
    
    // Read first line
    if (!fgets(line, len, file)) {
        goto error;
    }
    
    int line_num = 1;
    
    // Skip comment lines
    while (line[0] == 'c') {
        line_num++;
        if (!fgets(line, len, file)) {
            goto error;
        }
    }
    
    QCNF* qcnf = NULL;
    
    char* qcnf_header_start = "p cnf ";
    char* aiger_header_start = "aig ";
    char* aiger_ascii_header_start = "aag ";
    if (strncmp(qcnf_header_start, line, strlen(qcnf_header_start)) == 0) {
        qcnf = create_qcnf_from_qdimacs(options, file, line, line_num);
    } else if (   strncmp(aiger_header_start, line, strlen(aiger_header_start)) == 0
               || strncmp(aiger_ascii_header_start, line, strlen(aiger_ascii_header_start)) == 0) {
        
        aiger* aig = aiger_init();
        abortif(file == stdin, "AIGER input currently coes not work from stdin.");
        fseek(file, 0, SEEK_SET);
        const char* err = aiger_read_from_file(aig, file);
        
        abortif(err, "Error while reading aiger file:\n %s", err);
        
        qcnf = create_qcnf_from_aiger(aig, options);
    } else {
        abortif(true, "Cannot identify header of the file. Wrong file format? Some line must start with 'p cnf', 'aig', or 'aag'.");
    }
    
    free(line);
    return qcnf;
    
error:
    free(line);
    return NULL;
}
