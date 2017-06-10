//
//  options.c
//  caqe
//
//  Created by Markus Rabe on 29/03/16.
//  Copyright © 2016 Saarland University. All rights reserved.
//

#include "options.h"
#include "log.h"

Options* default_options() {
    Options* o = malloc(sizeof(Options));
    
    o->easy_debugging_mode_c2 = false;

    // Computational enginges
    o->cegar = true;
    o->cegar_only = false;
    o->use_qbf_engine_also_for_propositional_problems = false;
    o->functional_synthesis = false;
    o->decisions_consistent_with_quantification_hierarchy = true;
    
    // Examples domain
    o->examples_max_num = 0; // 0 corresponds to not doing examples at all
    o->initial_examples = 0;
    
    // Aiger interpretations
    o->aiger_controllable_inputs = "pi_"; // "controllable_";
    o->aiger_negated_encoding = false;
    
    // Certificates
    o->certify_internally_UNSAT = true;
    o->certify_UNSAT = false;
    o->certify_SAT = false;
    o->certificate_file_name = NULL;
    o->certificate_type = CAQECERT;
    o->certificate_aiger_mode = aiger_ascii_mode;
    
    // Case splits
    o->case_splits = false;
    o->case_splits_only_at_decision_level_0 = true;
    
    // Optimizations
    o->miniscoping = false;
    o->find_smallest_reason = true;
    o->minimize_conflicts = false;
    o->preprocess = false;
    o->delete_clauses_on_restarts = false;
    o->propagate_pure_literals = true;
    o->enhanced_pure_literals = false;
    
    // Printing
    o->print_detailed_miniscoping_stats = false;
    o->print_name_mapping = true;
    o->print_statistics = true;
    o->print_qdimacs = false;
    o->variable_names = NULL;
    
    o->trace_learnt_clauses = false;
    o->trace_for_visualization = false;
    
    return o;
}

void options_print_literal_name(Options* o, char* color, int lit) {
    assert(lit != 0);
    unsigned var_id = (unsigned) (lit < 0 ? - lit : lit);
    if (o->variable_names && var_id < vector_count(o->variable_names) && vector_get(o->variable_names, var_id) != NULL) {
        if (lit > 0) {
            LOG_COLOR(color, " %s", (char*) vector_get(o->variable_names, var_id));
        } else {
            LOG_COLOR(color, " -%s", (char*) vector_get(o->variable_names, var_id));
        }
    } else {
        LOG_COLOR(color, " %d", lit);
    }
}

void options_set_variable_name(Options* o, unsigned var_id, char* name) {
    if (o->variable_names && name) {
        while (vector_count(o->variable_names) <= var_id) {
            vector_add(o->variable_names, NULL);
        }
        vector_set(o->variable_names, var_id, name);
    }
}
