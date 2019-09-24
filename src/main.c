
#include "log.h"
#include "certify.h"
#include "options.h"
#include "util.h"
#include "cadet_internal.h"
#include "heap.h"
#include "c2_rl.h"
#include "mersenne_twister.h"
#include "tests.h"

#include <stdio.h>
#include <stdbool.h>
#include <assert.h>
#include <string.h>

void print_usage(const char* name) {
    printf("Usage: %s [options] file\n\n  The file can be in QDIMACS or AIGER format. Files can be compressed with gzip\n  (ending in .gz or .gzip). \n\n%s\n", name, options_get_help());
}

static void certificate_filename(const char* filename, Options *options) {
    options->certificate_file_name = filename;
    
    if (strcmp(options->certificate_file_name, "stdout") == 0) {
        log_silent = true;
    } else {
        const char* ext = get_filename_ext(options->certificate_file_name);
        if (! ext || strlen(ext) != 3) {
            LOG_ERROR("Must give file extension aig or aag for certificates.\n");
            abort();
        }
        if (strcmp(ext, "aig") != 0 && strcmp(ext, "aag") != 0) {
            LOG_ERROR("File extension of certificate must be aig or aag.\n");
            abort();
        }
    }
}

int main(int argc, const char* argv[]) {

    // default
    Options* options = default_options();
    char *file_name = NULL;
    
    // scan for file name and flags
    for (int i = 1; i < argc; i++) {
        if (strlen(argv[i]) < 2) {
            LOG_ERROR("Argument '%s' is too short", argv[i]);
        }
        
        if (argv[i][0] == '-') {
            switch (argv[i][1]) {
                case 'e':
                    abortif(options->quantifier_elimination || options->certify_SAT,
                            "Can only set one of the options -e, -f, -c; and each one only once.");
                    options->quantifier_elimination = true;
                    // WARNING: CASE CONTINUES TO NEXT ONE
                case 'f':
                    abortif(options->functional_synthesis || options->certify_SAT,
                            "Can only set one of the options -e, -f, -c; and each one only once.");
                    options->functional_synthesis = true;
                    // WARNING: CASE CONTINUES TO NEXT ONE
                case 'c': // certification flag
//                    abortif(options->quantifier_elimination || options->functional_synthesis,
//                            "Can only set one of the options -e, -f, -c.");
                    options->certify_SAT = true;
                    
                    if (i + 1 >= argc) {
                        LOG_ERROR("File name for certificate missing.\n");
                        print_usage(argv[0]);
                        return 1;
                    }
                    
                    certificate_filename(argv[i+1], options);
                    i++;
                    break;
                    
                case 'h':
                    print_usage(argv[0]);
                    return 0;
                
                case 'v':
                    // verbosity flag
                    if (i + 1 >= argc) {
                        printf("Error: Verbosity number missing\n");
                        print_usage(argv[0]);
                        return 1;
                    }
                    debug_verbosity = (int) strtol(argv[i+1], NULL, 0);
                    abortif(debug_verbosity < 0 || debug_verbosity > 4, "Verbosity must be in [0,4]. Argument was: %s", argv[i+1]);
                    i++;
                    
                    break;
                    
                case 's':
                    if (i + 1 >= argc) {
                        LOG_ERROR("Missing seed number\n");
                        print_usage(argv[0]);
                        return 1;
                    }
                    options->seed = (unsigned long) strtol(argv[i+1], NULL, 0);
                    i++;
                    break;
                
                case 'l':
                    if (i + 1 >= argc) {
                        LOG_ERROR("Missing number for decision limit\n");
                        print_usage(argv[0]);
                        return 1;
                    }
                    options->hard_decision_limit = (unsigned) strtol(argv[i+1], NULL, 0);
                    assert(options->hard_decision_limit < 10000000);
                    i++;
                    break;
                    
                case '-': // long argument (--...)
                    if (strcmp(argv[i], "--stats") == 0) {
                        V0("Enabled printing statistics\n");
                        options->print_statistics = true;
                    } else if (strcmp(argv[i], "--caqecert") == 0) {
                        options->certificate_type = CAQECERT;
                    } else if (strcmp(argv[i], "--qbfcert") == 0) {
                        options->certificate_type = QBFCERT;
                    } else if (strcmp(argv[i], "--qaiger") == 0) {
                        options->certificate_type = QAIGER;
                    } else if (strcmp(argv[i], "--qdimacs_out") == 0) {
                        log_qdimacs_compliant = !log_qdimacs_compliant;
                        log_colors = false;
                    } else if (strcmp(argv[i], "--no_colors") == 0) {
                        log_colors = false;
                    } else if (strcmp(argv[i], "--debugging") == 0) {
                        options->easy_debugging = !options->easy_debugging;
                    } else if (strcmp(argv[i], "--aiger_controllable_inputs") == 0) {
                        if (i + 1 >= argc) {
                            LOG_ERROR("Missing string for argument --aiger_controllable_inputs\n");
                            print_usage(argv[0]);
                            return 1;
                        }
                        options->aiger_controllable_input_prefix = argv[i+1];
                        i++;
                    } else if (strcmp(argv[i], "--case_splits") == 0) {
                        options->casesplits = ! options->casesplits;
                    } else if (strcmp(argv[i], "--fresh_seed") == 0) {
                        options->fresh_random_seed = true;
                    } else if (strcmp(argv[i], "--random_decisions") == 0) {
                        options->random_decisions = true;
                    } else if (strcmp(argv[i], "--minimize") == 0) {
                        options->minimize_learnt_clauses = ! options->minimize_learnt_clauses;
                    } else if (strcmp(argv[i], "--miniscoping") == 0) {
                        options->miniscoping = ! options->miniscoping;
                    } else if (strcmp(argv[i], "--miniscoping_info") == 0) {
                        options->print_detailed_miniscoping_stats = ! options->print_detailed_miniscoping_stats;
                    } else if (strcmp(argv[i], "--trace_learnt_clauses") == 0) {
                        options->trace_learnt_clauses = ! options->trace_learnt_clauses;
                    } else if (strcmp(argv[i], "--trace_for_vis") == 0) {
                        options->trace_for_visualization = true;
                        options->trace_learnt_clauses = true;
                        log_colors = false;
                    } else if (strcmp(argv[i], "--rl") == 0) {
                        options->reinforcement_learning = true;
                        log_colors = false;
                    } else if (strcmp(argv[i], "--rl_advanced_rewards") == 0) {
                        options->rl_advanced_rewards = ! options->rl_advanced_rewards;
                    } else if (strcmp(argv[i], "--rl_vsids_rewards") == 0) {
                        options->rl_vsids_rewards = ! options->rl_vsids_rewards;
                    } else if (strcmp(argv[i], "--rl_slim_state") == 0) {
                        options->rl_slim_state = ! options->rl_slim_state;
                    } else if (strcmp(argv[i], "--rl_mock") == 0) {
                        options->reinforcement_learning = true;
                        log_colors = false;
                        options->reinforcement_learning_mock = true;
                    } else if (strcmp(argv[i], "--rl_completion_reward") == 0) {
                        if (i + 1 >= argc) {
                            LOG_ERROR("Missing float for rl_completion_reward\n");
                            print_usage(argv[0]);
                            return 1;
                        }
                        options->rewards->completion_reward = strtof(argv[i+1], NULL);
                        LOG_WARNING("--rl_completion_reward set to %f\n",
                                    options->rewards->completion_reward);
                        i++;
                    } else if (strcmp(argv[i], "--rl_reward_per_decision") == 0) {
                        if (i + 1 >= argc) {
                            LOG_ERROR("Missing float for rl_reward_per_decision\n");
                            print_usage(argv[0]);
                            return 1;
                        }
                        options->rewards->reward_per_decision = strtof(argv[i+1], NULL);
                        LOG_WARNING("--rl_reward_per_decision set to %f\n",
                                    options->rewards->reward_per_decision);
                        i++;
                    } else if (strcmp(argv[i], "--rl_vsids_similarity_reward_factor") == 0) {
                        if (i + 1 >= argc) {
                            LOG_ERROR("Missing float for rl_vsids_similarity_reward_factor\n");
                            print_usage(argv[0]);
                            return 1;
                        }
                        options->rewards->vsids_similarity_reward_factor = strtof(argv[i+1], NULL);
                        LOG_WARNING("--rl_vsids_similarity_reward_factor set to %f\n",
                                    options->rewards->vsids_similarity_reward_factor);
                        i++;
                    } else if (strcmp(argv[i], "--rl_total_reward_for_necessary_conflicts") == 0) {
                        if (i + 1 >= argc) {
                            LOG_ERROR("Missing float for rl_total_reward_for_necessary_conflicts\n");
                            print_usage(argv[0]);
                            return 1;
                        }
                        options->rewards->total_reward_for_necessary_conflicts = strtof(argv[i+1], NULL);
                        LOG_WARNING("--rl_total_reward_for_necessary_conflicts set to %f\n",
                                 options->rewards->total_reward_for_necessary_conflicts);
                        i++;
                    } else if (strcmp(argv[i], "--rl_self_reward_factor") == 0) {
                        if (i + 1 >= argc) {
                            LOG_ERROR("Missing float for rl_self_reward_factor\n");
                            print_usage(argv[0]);
                            return 1;
                        }
                        options->rewards->self_reward_factor = strtof(argv[i+1], NULL);
                        LOG_WARNING("--rl_self_reward_factor set to %f\n",
                                 options->rewards->self_reward_factor);
                        i++;
                    } else if (strcmp(argv[i], "--trace_for_profiling") == 0) {
                        options->trace_for_profiling = true;
                    } else if (strcmp(argv[i], "--print_variable_names") == 0) {
                        options->print_variable_names = true;
                    } else if (strcmp(argv[i], "--selftest") == 0) {
                        test_all();
                        exit(0);
                    } else if (strcmp(argv[i], "--cegar") == 0) {
                        options->cegar = ! options->cegar;
                    } else if (strcmp(argv[i], "--cegar_only") == 0) {
                        options->cegar_only = ! options->cegar_only;
                    } else if (strcmp(argv[i], "--sat_by_qbf") == 0) {
                        options->use_qbf_engine_also_for_propositional_problems = ! options->use_qbf_engine_also_for_propositional_problems;
                    } else if (strcmp(argv[i], "--pg") == 0) {
                        options->plaisted_greenbaum_completion = ! options->plaisted_greenbaum_completion;
                    } else if (strcmp(argv[i], "--pure_literals") == 0) {
                        options->pure_literals = ! options->pure_literals;
                    } else if (strcmp(argv[i], "--enhanced_pure_literals") == 0) {
                        assert(options->pure_literals);
                        LOG_WARNING("Enhanced pure literals still buggy: conflict analysis cannot detect cases in which enhanced pure literals caused the assignment.");
                        options->enhanced_pure_literals = ! options->enhanced_pure_literals;
                    } else if (strcmp(argv[i], "--qbce") == 0) {
                        options->qbce = ! options->qbce;
                    } else if (strcmp(argv[i], "--dontverify") == 0) {
                        options->verify = 0;
                    } else {
                        LOG_ERROR("Unknown long argument '%s'", argv[i]);
                        print_usage(argv[0]);
                        return 1;
                    }
                    break;
                
                default:
                    LOG_ERROR("Unknown argument '%s'", argv[i]);
                    print_usage(argv[0]);
                    return 1;
            }
        } else {
            // expect file name as last argument
            file_name = malloc(strlen(argv[i]) + 1);
            strcpy(file_name, argv[i]);
            break;
        }
    }
    
    if (log_qdimacs_compliant && debug_verbosity > VERBOSITY_LOW) {
        LOG_WARNING("Verbosity is medium or higher and comment prefix is set. May result in cluttered log.");
    }
    
    V0("CADET %s\n", VERSION);
    
    options_print(options);
    
//    void* solver = create_solver_from_qdimacs(file);
//    int res = qipasir_solve(solver);
//    return res == 0 ? 30 : res; // unknown result according to ipasir is not the same as unknown result otherwise.
    
    if (!options->reinforcement_learning) {
        cadet_res res = c2_solve_qdimacs(file_name, options);
        return res;
    } else {
        if (options->cegar) {
            LOG_WARNING("Switching off CEGAR for reinforcement learning.\n");
            options->cegar = false;
        }
        if (options->casesplits) {
            LOG_WARNING("Switching off casesplits for reinforcement learning.\n");
            options->casesplits = false;
        }
//        if (options->minimize_learnt_clauses) {
//            LOG_WARNING("Switching off clause minimization for reinforcement learning.\n");
//            options->minimize_learnt_clauses = false;
//        }
        if (options->reinforcement_learning_mock) {
            rl_mock_file(file_name);
        }
        return c2_rl_run_c2(options);
    }
}
