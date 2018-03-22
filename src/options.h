//
//  options.h
//  caqe
//
//  Created by Markus Rabe on 29/03/16.
//  Copyright © 2016 Saarland University. All rights reserved.
//

#ifndef options_h
#define options_h

#include "vector.h"

#include <stdbool.h>

typedef enum {
    QBFCERT,
    CAQECERT
} certificate_type;

typedef struct {
    
    unsigned long seed; // for the random number generator
    bool reinforcement_learning; // take decisions through stdin; trace state
    bool rl_advanced_rewards;
    bool reinforcement_learning_mock; // for testing reinforcement learning code
    bool cegar_soft_conflict_limit; // switches cegar on after 1000 conflicts to also solve hard problems.
    
    // Use a configuration of CADET 2 that is easier to debug than the performance-oriented configuration
    bool easy_debugging;
    
    // Computational enginge
    bool cegar;
    bool cegar_only;
    bool use_qbf_engine_also_for_propositional_problems;
    unsigned examples_max_num;
    bool functional_synthesis;
    
    // Aiger interpretations
    const char* aiger_controllable_inputs;
    
    // Certificates
    bool certify_internally_UNSAT;
    bool certify_SAT;
    const char* certificate_file_name;
    certificate_type certificate_type;
    
    // Case splits
    bool casesplits;
    bool casesplits_cubes; // old case split code
    
    // Optimizations
    bool plaisted_greenbaum_completion;
    bool qbce;
    bool miniscoping;
    bool find_smallest_reason;
    bool minimize_learnt_clauses;
    bool preprocess;
    bool delete_clauses_on_restarts;
    bool pure_literals;
    bool enhanced_pure_literals;
    bool failed_literals;
    
    // Output options
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
char* options_get_help();

#endif /* options_h */
