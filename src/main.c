
#include "log.h"
#include "certify.h"
#include "options.h"
#include "util.h"
#include "cadet2.h"
#include "heap.h"
#include "c2_rl.h"
//#include "qipasir.h"
//#include "qipasir_parser.h"

#include <stdio.h>
#include <stdbool.h>
#include <assert.h>
#include <string.h>

void print_usage(const char* name) {
    printf("Usage: %s [options] file\n\n  The file can be in QDIMACS or AIGER format. Files can be compressed with gzip\n  (ending in .gz or .gzip). \n\n%s\n", name, options_get_help());
}

int main(int argc, const char* argv[]) {

    // default
    Options* options = default_options();
    const char *file_name = NULL;
    long seed = SEED;
    FILE* file;
    
    // scan for file name and flags
    for (int i = 1; i < argc; i++) {
        if (strlen(argv[i]) < 2) {
            LOG_ERROR("Argument '%s' is too short", argv[i]);
        }
        
        if (argv[i][0] == '-') {
            switch (argv[i][1]) {
                    
                case 'c': // certification flag
                    if (i + 1 >= argc) {
                        LOG_ERROR("File name for certificate missing.\n");
                        print_usage(argv[0]);
                        return 1;
                    }
                    
                    options->certify_SAT = true;
//                    options->certify_UNSAT = true;
                    options->certify_internally_UNSAT = false;
                    
                    options->certificate_file_name = argv[i+1];
                    
                    if (strcmp(options->certificate_file_name, "stdout") != 0) {
                        const char* ext = get_filename_ext(options->certificate_file_name);
                        if (! ext || strlen(ext) != 3) {
                            LOG_ERROR("Must give file extension aig or aag for certificates.\n");
                            print_usage(argv[0]);
                            return 0;
                        }
                        if (strcmp(ext, "aig") == 0) {
                            options->certificate_aiger_mode = aiger_binary_mode;
                        } else if (strcmp(ext, "aag") == 0) {
                            options->certificate_aiger_mode = aiger_ascii_mode;
                        } else {
                            LOG_ERROR("File extension of certificate must be aig or aag.\n");
                            print_usage(argv[0]);
                            return 0;
                        }
                    } else {
                        options->certificate_aiger_mode = aiger_ascii_mode;
                        log_silent = true;
                    }
                    
                    if (options->casesplits) {
                        LOG_WARNING("Case splits not compatible with certificates right now. Deactivating case splits.");
                        options->casesplits = false;
                    }
//                    if (options->cegar) {
//                        LOG_WARNING("CEGAR is not compatible with certificates right now. Deactivating CEGAR.");
//                        options->cegar = false;
//                    }
                    
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
                    seed = strtol(argv[i+1], NULL, 0);
                    i++;
                    break;
                
                case '-': // long argument (--...)
                    if (strcmp(argv[i], "--stats") == 0) {
                        V0("Enabled printing statistics\n");
                        options->print_statistics = true;
                    } else if (strcmp(argv[i], "--qbfcert") == 0) {
                        options->certificate_type = QBFCERT;
                    } else if (strcmp(argv[i], "--qdimacs_out") == 0) {
                        log_qdimacs_compliant = !log_qdimacs_compliant;
                        log_colors = false;
                    } else if (strcmp(argv[i], "--no_colors") == 0) {
                        log_colors = false;
                    } else if (strcmp(argv[i], "--aiger_negated") == 0) {
                        options->aiger_negated_encoding = true;
                    } else if (strcmp(argv[i], "--debugging") == 0) {
                        options->easy_debugging = !options->easy_debugging;
                    } else if (strcmp(argv[i], "--aiger_controllable_inputs") == 0) {
                        if (i + 1 >= argc) {
                            LOG_ERROR("Missing string for argument --aiger_ci\n");
                            print_usage(argv[0]);
                            return 1;
                        }
                        options->aiger_controllable_inputs = argv[i+1];
                        i++;
                    } else if (strcmp(argv[i], "--case_splits") == 0) {
                        options->casesplits = ! options->casesplits;
                    } else if (strcmp(argv[i], "--functional-synthesis") == 0) {
                        assert(!options->functional_synthesis);
                        options->functional_synthesis = true;
                        if (options->cegar) {
                            V0("Functional synthesis currently incompatible with CEGAR. Deactivating CEGAR.\n");
                            options->cegar = false;
                        }
                        if (options->casesplits) {
                            V0("Functional synthesis currently incompatible with case splits. Deactivating case splits.\n");
                            options->casesplits = false;
                        }
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
                    } else if (strcmp(argv[i], "--rl_mock") == 0) {
                        options->reinforcement_learning_mock = true;
                    } else if (strcmp(argv[i], "--cegar_soft_conflict_limit") == 0) {
                        options->cegar_soft_conflict_limit = true;
                    } else if (strcmp(argv[i], "--trace_for_profiling") == 0) {
                        options->trace_for_profiling = true;
                    } else if (strcmp(argv[i], "--print_variable_names") == 0) {
                        options->variable_names = vector_init();
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
            file_name = argv[i];
            break;
        }
    }
    
    srand((unsigned int)seed);
    
    if (options->certificate_aiger_mode == aiger_binary_mode && options->certificate_type == QBFCERT) {
        LOG_WARNING("QBFCERT cannot read aiger files in binary mode. Use .aag file extension for certificate file.\n");
    }
    if (log_qdimacs_compliant && debug_verbosity > VERBOSITY_LOW) {
        LOG_WARNING("Verbosity is medium or higher and comment prefix is set. May result in cluttered log.");
    }
    
    if (file_name == NULL) {
        V0("Reading from stdin\n");
        file = stdin;
    } else {
        V0("Processing file \"%s\".\n", file_name);
        file = open_possibly_zipped_file(file_name);
    }
    
    V0("CADET %s\n", VERSION);
    
//    void* solver = create_solver_from_qdimacs(file);
//    int res = qipasir_solve(solver);
//    return res == 0 ? 30 : res; // unknown result according to ipasir is not the same as unknown result otherwise.
    
    if (!options->reinforcement_learning) {
        return c2_solve_qdimacs(file,options);
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
        rl_mock_file(file);
        return c2_rl_run_c2(options);
    }
}
