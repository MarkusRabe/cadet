
#include "log.h"
#include "parse.h"
#include "certify.h"
#include "options.h"
#include "util.h"
#include "cadet2.h"
#include "heap.h"
//#include "qipasir.h"
//#include "qipasir_parser.h"

#include <stdio.h>
#include <stdbool.h>
#include <assert.h>
#include <string.h>

void print_usage(const char* name) {
    const char* options_string =
                                "  General options:\n"
                                    "\t-v [0-4]\t\tSet the verbosity [default 0]\n"
                                    "\t-s [num]\t\tSet the seed for the random number generator\n"
                                    "\t--print \t\tPrint the qdimacs file as read.\n"
                                    "\t--no_colors \t\tSuppress colors in output.\n"
                                    "\t-c [file]\t\tWrite certificate to specified file. File ending defines Aiger formag aag/aig.\n"
                                    "\t--qbfcert\t\tWrite certificate in qbfcert-readable format. Only compatible with aag file ending.\n"
                                    "\t--qdimacs_out\t\tOutput compliant with QDIMACS standard\n"
                                    "\n"
                                "  Options for the QBF engine\n"
                                    "\t--debugging \t\tEasy debugging configuration (default off)\n"
                                    "\t--cegar\t\t\tUse CEGAR strategy in addition to incremental determinization (default off).\n"
                                    "\t--cegar_only\t\tUse CEGAR strategy exclusively.\n"
                                    "\t--case_splits \t\tCase distinctions (default off) \n"
                                    "\t--functional-synthesis\tFunctional synthesis. I.e. compute skolem functions for UNSAT instances.\n"
                                    "\t--pg\t\t\tPlaisted Greenbaum completion (default on).\n"
                                    "\t--sat_by_qbf\t\tUse QBF engine also for propositional problems. Uses SAT solver by default.\n"
                                    "\t--miniscoping \t\tEnables miniscoping \n"
                                    "\t--miniscoping_info \tPrint additional info on miniscoping (default off)\n"
                                    "\t--minimize_conflicts \tConflict minimization (default off) \n"
                                    "\t--delay_conflicts\tDelay conflict checks and instead check conflicted variables in bulk.\n"
                                "  Visualization options\n"
                                    "\t--trace_learnt_clauses\tPrint (colored) learnt clauses; independent of verbosity.\n"
                                    "\t--trace_for_visualization\tPrint trace of solver states at every conflict point.\n"
                                    "\t--trace_for_profiling\tPrint trace of learnt clauses with timestamps and SAT solver time consumption.\n"
                                    "\t--print_variable_names\tReplace variable numbers by names where available\n"
                                "  Aiger options\n"
                                    "\t--aiger_negated\t\tNegate encoding of aiger files. Can be combined with --print.\n"
                                    "\t--aiger_controllable_inputs [string] Set prefix of controllable inputs of AIGER files (default 'pi_')\n"
                                    "\n"
                                    ;
  printf("Usage: %s [options] file\n\n  The file can be in QDIMACS or AIGER format. Files can be compressed with gzip (ending in .gz or .gzip). \n\n%s\n", name, options_string);
}

int main(int argc, const char* argv[]) {

    // default
    Options* options = default_options();
    const char *file_name = NULL;
    long verbosity = 0;
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
                    options->certify_UNSAT = true;
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
                    
                    if (options->case_splits) {
                        LOG_WARNING("Case splits not compatible with certificates right now. Deactivating case splits.");
                        options->case_splits = false;
                    }
                    if (options->cegar) {
                        LOG_WARNING("CEGAR is not compatible with certificates right now. Deactivating CEGAR.");
                        options->cegar = false;
                    }
                    
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
                    verbosity = strtol(argv[i+1], NULL, 0);
                    switch (verbosity) {
                        case 0:
                            debug_verbosity = VERBOSITY_NONE;
                            break;
                        case 1:
                            debug_verbosity = VERBOSITY_LOW;
                            break;
                        case 2:
                            debug_verbosity = VERBOSITY_MEDIUM;
                            break;
                        case 3:
                            debug_verbosity = VERBOSITY_HIGH;
                            break;
                        case 4:
                            debug_verbosity = VERBOSITY_ALL;
                            break;
                            
                        default:
                            printf("Error: illegal verbosity number %ld\n", verbosity);
                            print_usage(argv[0]);
                            return 1;
                    }
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
                    } else if (strcmp(argv[i], "--disable-preprocessing") == 0) {
                        V0("Disable preprocessing\n");
                        options->preprocess = false;
                    } else if (strcmp(argv[i], "--qbfcert") == 0) {
                        options->certificate_type = QBFCERT;
                    } else if (strcmp(argv[i], "--qdimacs_out") == 0) {
                        log_qdimacs_compliant = true;
                        log_colors = false;
                    } else if (strcmp(argv[i], "--print") == 0) {
                        options->preprocess = false;
                        options->print_qdimacs = true;
                        log_qdimacs_compliant = true;
                        log_colors = false;
                    } else if (strcmp(argv[i], "--no_colors") == 0) {
                        log_colors = false;
                    } else if (strcmp(argv[i], "--aiger_negated") == 0) {
                        options->aiger_negated_encoding = true;
                    } else if (strcmp(argv[i], "--debugging") == 0) {
                        options->easy_debugging_mode_c2 = true;
                    } else if (strcmp(argv[i], "--aiger_controllable_inputs") == 0) {
                        if (i + 1 >= argc) {
                            LOG_ERROR("Missing string for argument --aiger_controllable_inputs\n");
                            print_usage(argv[0]);
                            return 1;
                        }
                        options->aiger_controllable_inputs = argv[i+1];
                        i++;
                    } else if (strcmp(argv[i], "--case_splits") == 0) {
                        options->case_splits = ! options->case_splits;
                    } else if (strcmp(argv[i], "--functional-synthesis") == 0) {
                        options->functional_synthesis = true;
                        if (options->cegar) {
                            V0("Functional synthesis currently incompatible with CEGAR. Deactivating CEGAR.\n");
                            options->cegar = false;
                        }
                    } else if (strcmp(argv[i], "--minimize") == 0) {
                        options->minimize_conflicts = ! options->minimize_conflicts;
                    } else if (strcmp(argv[i], "--enhanced_pure_literals") == 0) {
                        options->enhanced_pure_literals = true;
                    } else if (strcmp(argv[i], "--miniscoping") == 0) {
                        options->miniscoping = ! options->miniscoping;
                    } else if (strcmp(argv[i], "--miniscoping_info") == 0) {
                        options->print_detailed_miniscoping_stats = ! options->print_detailed_miniscoping_stats;
                    } else if (strcmp(argv[i], "--trace_learnt_clauses") == 0) {
                        options->trace_learnt_clauses = ! options->trace_learnt_clauses;
                    } else if (strcmp(argv[i], "--trace_for_visualization") == 0) {
                        options->trace_for_visualization = true;
                        options->trace_learnt_clauses = true;
                        log_colors = false;
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
                    } else if (strcmp(argv[i], "--delay_conflicts") == 0) {
                        options->delay_conflict_checks = ! options->delay_conflict_checks;
                    } else if (strcmp(argv[i], "--pg") == 0) {
                        options->plaisted_greenbaum_completion = ! options->plaisted_greenbaum_completion;
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
        const char* ext = get_filename_ext(file_name);
        size_t extlen = strlen(ext);
        V4("Detected file name extension %s\n", ext);
        if ( (extlen == 2 && strcmp("gz", ext) == 0) || (extlen == 4 && strcmp("gzip", ext) == 0) ) {
#ifdef __APPLE__
            char* unzip_tool_name = "gzcat ";
#endif
#ifdef __linux__
            char* unzip_tool_name = "zcat ";
#endif
#ifdef _WIN32
            abort(); // please use a proper operating system
#endif
            
            char* cmd = malloc(strlen(unzip_tool_name) + strlen(file_name) + 5);
            sprintf(cmd, "%s '%s'", unzip_tool_name, file_name);
            file = popen(cmd, "r");
            free(cmd);
            if (!file) {
                LOG_ERROR("Cannot open gzipped file with zcat via popen. File may not exist.\n");
                return 1;
            }
        } else {
            file = fopen(file_name, "r");
            if (!file) {
                LOG_ERROR("Cannot open file \"%s\", does not exist?\n", file_name);
                return 1;
            }
        }
    }
    
    V0("CADET %s\n", VERSION);
    
//    void* solver = create_solver_from_qdimacs(file);
//    int res = qipasir_solve(solver);
//    return res == 0 ? 30 : res; // unknown result according to ipasir is not the same as unknown result otherwise.

    return c2_solve_qdimacs(file,options);
}
