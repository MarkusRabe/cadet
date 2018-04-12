//
//  c2_outputs.c
//  cadet
//
//  Created by Markus Rabe on 25/01/2017.
//  Copyright © 2017 UC Berkeley. All rights reserved.
//

#include "log.h"
#include "c2_traces.h"
#include "casesplits.h"

#include <sys/time.h>

void c2_print_variable_states(C2* c2) {
    if (!c2->options->trace_for_visualization) {
        return;
    }
    V0("Activities");
    for (unsigned i = 1; i < var_vector_count(c2->qcnf->vars); i++) {
        if (qcnf_var_exists(c2->qcnf, i)) {
            Var* v = var_vector_get(c2->qcnf->vars, i);
            if (!v->original) {
                continue;
            }
        }
        V0(",%f",c2_get_activity(c2, i));
    }
    V0("\nDecision levels");
    for (unsigned i = 1; i < var_vector_count(c2->qcnf->vars); i++) {
        if (qcnf_var_exists(c2->qcnf, i)) {
            Var* v = var_vector_get(c2->qcnf->vars, i);
            if (!v->original) {
                continue;
            }
        }
        if (skolem_is_deterministic(c2->skolem, i)) {
            V0(",%d",skolem_get_decision_lvl(c2->skolem, i));
        } else {
            V0(",");
        }
    }
    V0("\nDecision variables");
    for (unsigned i = 1; i < var_vector_count(c2->qcnf->vars); i++) {
        if (qcnf_var_exists(c2->qcnf, i)) {
            Var* v = var_vector_get(c2->qcnf->vars, i);
            if (!v->original) {
                continue;
            }
        }
        V0(",%d",skolem_get_decision_val(c2->skolem, i));
    }
    V0("\nConstants");
    for (unsigned i = 1; i < var_vector_count(c2->qcnf->vars); i++) {
        if (qcnf_var_exists(c2->qcnf, i)) {
            Var* v = var_vector_get(c2->qcnf->vars, i);
            if (!v->original) {
                continue;
            }
        }
        V0(",%d",skolem_get_constant_value(c2->skolem, (Lit) i));
    }
    V0("\n");
}

char* c2_literal_color(C2* c2, Clause* c, Lit lit) {
    unsigned var_id = lit_to_var(lit);
    Var* v = var_vector_get(c2->qcnf->vars, var_id);
    if (v->is_universal) {
        if (skolem_get_constant_value(c2->skolem, lit) != 0) {
            return KRED_BOLD;
        } else {
            return KRED;
        }
    } else if (c && skolem_get_unique_consequence(c2->skolem, c) == lit) {
        return KMAG;
    } else if (skolem_is_decision_var(c2->skolem, var_id)) {
        if (skolem_get_constant_value(c2->skolem, lit) != 0) {
            return KGRN_BOLD;
        } else {
            return KGRN;
        }
    } else if (skolem_is_deterministic(c2->skolem, var_id)) {
        if (skolem_get_constant_value(c2->skolem, lit) != 0) {
            if (skolem_get_decision_lvl(c2->skolem, var_id) == 0) {
                return KORANGE_BOLD;
            } else {
                return KYEL_BOLD;
            }
        } else {
            if (skolem_get_decision_lvl(c2->skolem, var_id) == 0) {
                return KORANGE;
            } else {
                return KYEL;
            }
        }
    } else {
        return KNRM;
    }
}

// WARNING: Calling this function may change the state of the sat solver!
void c2_print_universals_assignment(C2* c2) {
    V1("Assignment to the universals: ");
    for (unsigned i = 0; i < var_vector_count(c2->qcnf->vars); i++) {
        Var* v = var_vector_get(c2->qcnf->vars, i);
        if (v->var_id != 0 && v->is_universal) {
            int val;
            if (c2->state == C2_SKOLEM_CONFLICT) {
                val = skolem_get_value_for_conflict_analysis(c2->skolem, (Lit) v->var_id);
            } else if (c2->state == C2_EXAMPLES_CONFLICT) {
                val = examples_get_value_for_conflict_analysis(c2->examples, (Lit) v->var_id);
            } else {
                NOT_IMPLEMENTED();
            }
            assert(val >= -1 && val <= 1);
            V1("%d ", val * (int) v->var_id);
        }
    }
    V1("\n");
}

void c2_print_debug_info(C2* c2) {
    V1("C2 state: \n"
       "  decision lvl: %u\n  dlvls per variable: ", c2->skolem->decision_lvl);
    for (unsigned i = 0; i < skolem_var_vector_count(c2->skolem->infos); i++) {
        skolem_var* sv = skolem_var_vector_get(c2->skolem->infos, i);
        unsigned dlvl = sv->decision_lvl;
        if (dlvl) {
            V1("%u -> %u", i, dlvl);
            if (i + 1 != skolem_var_vector_count(c2->skolem->infos)) {
                V1(", ");
            }
            if (i % 8 == 7 || i + 1 == skolem_var_vector_count(c2->skolem->infos)) {
                V1("\n  ");
            }
        }
    }
    V1("\n");
    
    skolem_print_debug_info(c2->skolem);
}

// Watch out, this is an O(|phi|) operation
void c2_print_statistics(C2* c2) {
    
    unsigned unique_consequence_clauses = 0;
    unsigned non_satisfied_clause_count = 0;
    
    Clause_Iterator ci = qcnf_get_clause_iterator(c2->qcnf); Clause* c = NULL;
    while ((c = qcnf_next_clause(&ci)) != NULL) {
        if (skolem_has_unique_consequence(c2->skolem, c)) {
            unique_consequence_clauses++;
        }
        if (skolem_clause_satisfied(c2->skolem, c)) {
            non_satisfied_clause_count++;
        }
    }
    
    qcnf_print_statistics(c2->qcnf);
    skolem_print_statistics(c2->skolem);
    casesplits_print_statistics(c2->cs);
    if (c2->options->examples_max_num > 0) {
        examples_print_statistics(c2->examples);
    }
    V0("CADET statistics:\n")
    V0("  Decisions: %zu\n", c2->statistics.decisions);
    V0("  Conflicts: %zu\n", c2->statistics.conflicts);
    V0("  Added clauses: %zu\n", c2->statistics.added_clauses);
    V0("  Levels backtracked: %zu\n", c2->statistics.lvls_backtracked);
    V0("  Restarts:  %zu\n", c2->restarts);
    V0("  Major restarts:  %zu\n", c2->major_restarts);
    V0("  Cases explored:  %zu\n", c2->statistics.cases_closed);
    V0("  Literals eliminated:  %zu / %zu\n", c2->statistics.successful_conflict_clause_minimizations, c2->statistics.learnt_clauses_total_length);
    V0("  Time spent minimizing: %f\n", c2->statistics.minimization_stats->accumulated_value)
    V0("  Failed Literals Conflicts:  %zu\n", c2->statistics.failed_literals_conflicts);
    statistics_print(c2->statistics.failed_literals_stats);
}

bool c2_printed_color_legend = false;

void c2_print_learnt_clause_color_legend() {
    if (log_colors && !c2_printed_color_legend) {
        c2_printed_color_legend = true;
        V0("\n"); // prints a new line, but can be prefixed by 'c ' if in qdimacs printout mode.
        V0("Legend for the colored learnt clauses:\n");
        LOG_COLOR(KRED,"Red: "); V0("Universal variables\n");
        LOG_COLOR(KMAG,"Magenta: "); V0("Unique consequence\n");
        LOG_COLOR(KGRN,"Green: "); V0("Decision var\n");
        LOG_COLOR(KORANGE,"Orange: "); V0("Decision lvl 0\n");
        LOG_COLOR(KYEL,"Yellow: "); V0("Decision lvl >0\n");
        LOG_COLOR(KNRM,"Normal: "); V0("everything else\n");
        V0("Bold numbers represent constants.\n");
        V0("\n"); // prints a new line, but can be prefixed by 'c ' if in qdimacs printout mode.
    }
}

void c2_log_clause(C2* c2, Clause* c) {
    if (debug_verbosity >= VERBOSITY_MEDIUM || c2->options->trace_learnt_clauses) {
        c2_print_learnt_clause_color_legend();
        
        for (unsigned i = 0; i < c->size; i++) {
            c2_print_colored_literal_name(c2, c2_literal_color(c2, c, c->occs[i]), c->occs[i]);
        }
        LOG_COLOR(KNRM, "\n");
    }
}

void c2_trace_for_profiling_initialize(Options* o, SATSolver* s) {
    if (!o->trace_for_profiling) {
        return;
    }
    satsolver_measure_all_calls(s);
}

double last_time_stamp = 0.0;
double last_satsolver_seconds = 0.0;

void c2_trace_for_profiling(C2* c2) {
    if (!c2->options->trace_for_profiling) {
        return;
    }
    double total_time_passed = get_seconds() - c2->statistics.start_time;
    V0("Timestamp: %f\n", total_time_passed);
    double time_passed_since_last = total_time_passed - last_time_stamp;
    
    double satsolver = satsolver_seconds(c2->skolem->skolem);
    double satsolver_took_since_last = satsolver - last_satsolver_seconds;
    
    V0("SATSolver current portion: %f\n", satsolver_took_since_last / time_passed_since_last);
    
    last_time_stamp = total_time_passed;
    last_satsolver_seconds = satsolver;
}
