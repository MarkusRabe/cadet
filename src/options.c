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
    o->delay_conflict_checks = false;
    o->use_qbf_engine_also_for_propositional_problems = false;
    o->functional_synthesis = false;

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

    // Optimizations
    o->miniscoping = false;
    o->find_smallest_reason = true;
    o->minimize_conflicts = true;
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
    o->trace_for_profiling = false;
    o->trace_for_reinforcement_learning = false;
    
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

char* options_get_help() {
    Options* o = default_options();
    char* options_string = malloc(sizeof(char) * 10000);
    
    sprintf(options_string,
    "  General options:\n"
    "\t-v [0-4]\t\tSet the verbosity [default %d]\n"
    "\t-s [num]\t\tSet the seed for the random number generator\n"
    "\t--print \t\tPrint the qdimacs file as read.\n"
    "\t--no_colors \t\tSuppress colors in output.\n"
    "\t-c [file]\t\tWrite certificate to specified file. File ending defines Aiger formag aag/aig.\n"
    "\t--qbfcert\t\tWrite certificate in qbfcert-readable format. Only compatible with aag file ending.\n"
    "\n  Options for the QBF engine\n"
    "\t--debugging \t\tEasy debugging configuration (default %d)\n"
    "\t--cegar\t\t\tUse CEGAR refinements in addition to clause learning (default %d)\n"
    "\t--cegar_only\t\tUse CEGAR strategy exclusively (default %d)\n"
    "\t--case_splits \t\tCase distinctions (default %d) \n"
    "\t--functional-synthesis\tFunctional synthesis (default %d)\n"
    "\t--sat_by_qbf\t\tUse QBF engine also for propositional problems (default %d)\n"
    "\t--miniscoping \t\tEnables miniscoping (default %d)\n"
    "\t--minimize_conflicts \tConflict minimization (default %d) \n"
    "\n  Output options\n"
    "\t--qdimacs_out\t\tOutput compliant with QDIMACS standard\n"
    "\t--miniscoping_info \tPrint additional info on miniscoping (default %d)\n"
    "\t--trace_learnt_clauses\tPrint (colored) learnt clauses; independent of verbosity.\n"
    "\t--trace_for_visualization\tPrint trace of solver states at every conflict point.\n"
    "\t--trace_for_profiling\tPrint trace of learnt clauses with timestamps and SAT solver time consumption.\n"
    "\t--trace_rl\t\t\t Trace reinforcement learning state-action pairs\n"
    "\t--print_variable_names\tReplace variable numbers by names where available\n"
    "\n  Aiger options\n"
    "\t--aiger_negated\t\tNegate encoding of aiger files. Can be combined with --print.\n"
    "\t--aiger_controllable_inputs [string] Set prefix of controllable inputs of AIGER files (default 'pi_')\n"
    "\n",
    debug_verbosity,
    o->easy_debugging_mode_c2,
    o->cegar,
    o->cegar_only,
    o->case_splits,
    o->functional_synthesis,
    o->use_qbf_engine_also_for_propositional_problems,
    o->miniscoping,
    o->minimize_conflicts,
    o->print_detailed_miniscoping_stats
    );
    
    return options_string;
}
