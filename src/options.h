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
    CAQECERT,
    QAIGER
} function_output_format;

typedef struct {
    float completion_reward;
    float reward_per_decision;
    float vsids_similarity_reward_factor;
    float total_reward_for_necessary_conflicts;
    float self_reward_factor;
} Rewards;
Rewards* default_rewards();

typedef struct {
    Rewards* rewards;
    unsigned long seed; // for the random number generator
    bool fresh_random_seed;
    bool reinforcement_learning; // take decisions through stdin; trace state
    bool rl_advanced_rewards;
    bool rl_vsids_rewards;
    bool rl_slim_state;
    bool reinforcement_learning_mock; // for testing reinforcement learning code
    unsigned hard_decision_limit;
    bool verify;
    
    // Use a configuration of CADET 2 that is easier to debug than the
    // performance-oriented configuration
    bool easy_debugging;
    
    // Computational enginge
    bool cegar;
    bool cegar_only;
    bool use_qbf_engine_also_for_propositional_problems;
    unsigned examples_max_num;
    bool random_decisions;
    
    // Aiger interpretations
    const char* aiger_controllable_input_prefix;
    
    // Certificates
    bool functional_synthesis;
    bool quantifier_elimination;
    bool certify_internally_UNSAT;
    bool certify_SAT;
    const char* certificate_file_name;
    function_output_format certificate_type;
    
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
    bool print_variable_names;
    
    // Traces
    bool trace_learnt_clauses;
    bool trace_for_visualization;
    bool trace_for_profiling;
} Options;

Options* default_options();
void options_print(Options* o);
void options_free(Options* o);
char* options_get_help();

#endif /* options_h */
