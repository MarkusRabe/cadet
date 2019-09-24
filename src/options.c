//
//  options.c
//  caqe
//
//  Created by Markus Rabe on 29/03/16.
//  Copyright © 2016 Saarland University. All rights reserved.
//

#include "options.h"
#include "log.h"
#include "util.h"

#include <string.h>

Rewards* default_rewards() {
    Rewards* r = malloc(sizeof(Rewards));
    r->completion_reward = 1.0f;
    r->reward_per_decision = -0.0001f;
    r->vsids_similarity_reward_factor = 0.5f;
    r->total_reward_for_necessary_conflicts = 0.5f;
    r->self_reward_factor = 0.5f;
    return r;
}

Options* default_options() {
    Options* o = malloc(sizeof(Options));

    o->rewards = default_rewards();
    
    o->seed = 0;

    o->easy_debugging = false;
    o->fresh_random_seed = false;
    
    // Computational enginges
    o->cegar = true;
    o->cegar_only = false;
    o->use_qbf_engine_also_for_propositional_problems = false;
    o->casesplits = false;
    o->casesplits_cubes = false;
    o->random_decisions = false;

    // Examples domain
    o->examples_max_num = 0; // 0 corresponds to not doing examples at all

    // Aiger interpretations
    o->aiger_controllable_input_prefix = "2 "; // "controllable_";

    // Certificates
    o->functional_synthesis = false;
    o->quantifier_elimination = false;
    o->certify_internally_UNSAT = true;
    o->certify_SAT = false;
    o->certificate_file_name = NULL;
    o->certificate_type = CAQECERT;

    // Optimizations
    o->plaisted_greenbaum_completion = false; // pure literal detection is better
    o->qbce = false;
    o->miniscoping = false;
    o->find_smallest_reason = true;
    o->minimize_learnt_clauses = true;
    o->delete_clauses_on_restarts = false;
    o->pure_literals = true;
    o->enhanced_pure_literals = false;

    // Printing
    o->print_detailed_miniscoping_stats = false;
    o->print_name_mapping = true;
    o->print_statistics = true;
    o->print_variable_names = true;

    o->trace_learnt_clauses = false;
    o->trace_for_visualization = false;
    o->trace_for_profiling = false;
    o->reinforcement_learning = false;
    o->rl_advanced_rewards = false;
    o->rl_vsids_rewards = false;
    o->rl_slim_state = false;
    o->reinforcement_learning_mock = false;
    o->hard_decision_limit = 0;  // 0 means no limit
    o->verify = 1;
    return o;
}


char* options_get_help() {
    Options* o = default_options();
    char* options_string = malloc(sizeof(char) * 10000);
    
    sprintf(options_string,
    "  General options:\n"
    "\t-v [0-4]\t\tSet the verbosity [default %d]\n"
    "\t-s [num]\t\tSet the seed for the random number generator\n"
    "\t--no_colors \t\tSuppress colors in output.\n"
    "\t-c [file]\t\tProduce Skolem function.\n\t\t\t\tFile ending (aag/aig) determines output type.\n"
    "\t-e [file]\t\tEliminate existential quantifier.\n\t\t\t\tFile ending (aag/aig) determines output type.\n"
    "\t-f [file]\t\tProduce funcitonal synthesis certificate.\n\t\t\t\tFile ending (aag/aig) determines output type. ()\n"
    "\t--qbfcert\t\tWrite certificate in qbfcert-readable format.\n\t\t\t\tOnly compatible with aag file ending.\n"
    "\t--caqecert\t\tWrite certificate in caqecert format (default)\n"
    "\t--qaiger\t\tWrite certificate in qaiger format\n"
    "\n  Options for the QBF engine\n"
    "\t--debugging \t\tEasy debugging configuration (default %d)\n"
    "\t--cegar\t\t\tUse CEGAR refinements in addition to clause learning\n\t\t\t\t(default %d)\n"
    "\t--cegar_only\t\tUse CEGAR strategy exclusively (default %d)\n"
    "\t--case_splits \t\tCase distinctions (default %d) \n"
    "\t--sat_by_qbf\t\tUse QBF engine also for propositional problems\n\t\t\t\t(default %d)\n"
    "\t--miniscoping \t\tEnables miniscoping (default %d)\n"
    "\t--minimize \t\tConflict minimization (default %d) \n"
    "\t--pure_literals\t\tUse pure literal detection (default %d)\n"
    "\t--fresh_seed\t\tUse a fresh random seed for every initialization of\n\t\t\t\tthe solver (default false)\n"
    "\t-l [N]\t\t\tStop after N decisions; return UNKNONW (30).\n"
//    "\t--enhanced_pure_literals\tUse enhanced pure literal detection (default %d)\n"
//    "\t--qbce\t\t\tBlocked clause elimination (default %d)\n"
//    "\t--pg\t\t\tPlaisted Greenbaum completion (default %d).\n"
    "\n  Output options\n"
    "\t--qdimacs_out\t\tOutput compliant with QDIMACS standard\n"
    "\t--miniscoping_info \tPrint additional info on miniscoping (default %d)\n"
    "\t--trace_learnt_clauses\tPrint (colored) learnt clauses.\n"
    "\t--trace_for_vis\t\tPrint trace of solver states at every conflict point.\n"
    "\t--trace_for_profiling\tPrint trace of learnt clauses with timestamps\n\t\t\t\tand SAT solver time consumption.\n"
    "\t--print_variable_names\tReplace variable numbers by names where available\n\t\t\t\t(default %d)\n"
    "\t--dontverify\t\tDo not verify results.\n"
    "\n  Aiger options\n"
    "\t--aiger_controllable_inputs [string]\tSet prefix of controllable inputs in QAIGER\n\t\t\t\t(default '%s')\n"
    "  Reinforcement Learning\n"
    "\t--rl\t\t\tReinforcement learning mode: print state-action pairs,\n\t\t\t\tread decisions (default %d).\n"
    "\t--rl_advanced_rewards\tReward necessary actions (default %d)\n"
    "\t--rl_vsids_rewards\tReward actions that are similar to VSIDS (default %d)\n"
    "\t--rl_slim_state\t\tPrint rl state without statistics (default %d)\n"
    "\t--rl_completion_reward \t\t(default %f)\n"
    "\t--rl_reward_per_decision \t\t(default %f)\n"
    "\t--rl_vsids_similarity_reward_factor \t\t(default %f)\n"
    "\t--rl_total_reward_for_necessary_conflicts \t\t(default %f)\n"
    "\t--rl_self_reward_factor \t\t(default %f)\n"
    "\n",
    debug_verbosity,
    o->easy_debugging,
    o->cegar,
    o->cegar_only,
    o->casesplits,
    o->use_qbf_engine_also_for_propositional_problems,
    o->miniscoping,
    o->minimize_learnt_clauses,
    o->pure_literals,
//    o->enhanced_pure_literals,
//    o->qbce,
//    o->plaisted_greenbaum_completion,
    o->print_detailed_miniscoping_stats,
    o->print_variable_names,
    o->aiger_controllable_input_prefix,
    o->reinforcement_learning,
    o->rl_advanced_rewards,
    o->rl_vsids_rewards,
    o->rl_slim_state,
    o->rewards->completion_reward,
    o->rewards->reward_per_decision,
    o->rewards->vsids_similarity_reward_factor,
    o->rewards->total_reward_for_necessary_conflicts,
    o->rewards->self_reward_factor
    );
    
    return options_string;
}

void options_print(Options* o) {
    V1("Decision limit: %u\n", o->hard_decision_limit);
}

void options_free(Options* o) {
    free(o);
}
