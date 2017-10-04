//
//  options.h
//  caqe
//
//  Created by Markus Rabe on 29/03/16.
//  Copyright © 2016 Saarland University. All rights reserved.
//

#ifndef options_h
#define options_h

#include "aiger.h"
#include "vector.h"

#include <stdbool.h>

typedef enum {
    QBFCERT,
    CAQECERT
} certificate_type;

typedef struct {
    
    // Use a configuration of CADET 2 that is easier to debug than the performance-oriented configuration
    bool easy_debugging_mode_c2;
    
    // Computational enginge
    bool cegar;
    bool cegar_only;
    bool delay_conflict_checks;
    bool use_qbf_engine_also_for_propositional_problems;
    unsigned examples_max_num;
    unsigned initial_examples;
    bool functional_synthesis;
    
    // Aiger interpretations
    const char* aiger_controllable_inputs;
    bool aiger_negated_encoding; // creates 3QBF out of 2QBF, for example
    
    // Certificates
    bool certify_internally_UNSAT;
    bool certify_UNSAT;
    bool certify_SAT;
    const char* certificate_file_name;
    certificate_type certificate_type;
    aiger_mode certificate_aiger_mode;
    
    // Case splits
    bool case_splits;
    
    // Optimizations
    bool plaisted_greenbaum_completion;
    bool miniscoping;
    bool find_smallest_reason;
    bool minimize_conflicts;
    bool preprocess;
    bool delete_clauses_on_restarts;
    bool pure_literals;
    bool enhanced_pure_literals;
    bool failed_literals;
    
    // Output options
    bool print_qdimacs;
    bool print_name_mapping;
    bool print_statistics;
    bool print_detailed_miniscoping_stats;
    vector* variable_names;
    
    // Traces
    bool trace_learnt_clauses;
    bool trace_for_visualization;
    bool trace_for_profiling;
    
} Options;

Options* default_options();
void options_print_literal_name(Options*, char* color, int lit);
void options_set_variable_name(Options*, unsigned var_id, char* name);

#endif /* options_h */
