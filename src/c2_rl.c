//
//  c2_rl.c
//  cadet
//
//  Created by Markus Rabe on 24.01.18.
//  Copyright © 2018 UC Berkeley. All rights reserved.
//

#include "c2_rl.h"
#include "log.h"

#include <stdio.h>

void c2_rl_print_activity(Options* o, unsigned var_id, float activity) {
    if (o->trace_for_reinforcement_learning && activity > 0.5) {
        LOG_PRINTF("a %u,%f\n", var_id, activity);
    }
}

void c2_rl_update_D(Options* o, unsigned var_id, bool deterministic) {
    if (!o->trace_for_reinforcement_learning) {
        return;
    }
    LOG_PRINTF("u%c %u\n", deterministic?'+':'-',var_id);
}

void c2_rl_learnt_clause(Options* o, Clause* c) {
    if (!o->trace_for_reinforcement_learning) {
        return;
    }
    LOG_PRINTF("c");
    for (unsigned i = 0; i < c->size; i++) {
        LOG_PRINTF(" %d",c->occs[i]);
    }
    LOG_PRINTF("\n");
}

void c2_rl_print_state(C2* c2, unsigned conflicts_until_next_restart) {
    if (!c2->options->trace_for_reinforcement_learning) {
        return;
    }
    
    assert(qcnf_is_2QBF(c2->qcnf));
    
    unsigned var_num = var_vector_count(c2->qcnf->vars);
    unsigned uvar_num = int_vector_count(vector_get(c2->qcnf->scopes, 1));
    float var_ratio = (float) uvar_num / (float) (var_num + 1);
    
    // Solver state
    LOG_PRINTF("s %u,%u,%zu,%f,%zu,%zu,%u,",
               c2->restart_base_decision_lvl,
               c2->skolem->decision_lvl,
               c2->skolem->deterministic_variables,
               (float) c2->skolem->deterministic_variables / (float) (var_num + 1),
               c2->restarts,
               c2->restarts_since_last_major,
               conflicts_until_next_restart
               );
    
    // Formula statistics
    LOG_PRINTF("%u,%u,%f,",
               var_num,
               vector_count(c2->qcnf->clauses),
               var_ratio);
    
    // Solver statistics
    LOG_PRINTF("%zu,%zu,%f,%f,%zu,%f,%zu,%f,%zu,%f,%zu,%f,%zu,%f,%zu,%zu,%f,%f,%zu,%f,%zu,%f,%zu,%f,%zu\n",
               c2->statistics.decisions,
               c2->statistics.conflicts,
               (float) c2->statistics.decisions / (float) (c2->statistics.conflicts + 1),
               (float) c2->statistics.decisions / (float) (c2->restarts + 1),
               c2->skolem->statistics.propagations,
               (float) c2->skolem->statistics.propagations / (float) (c2->statistics.decisions + 1),
               c2->skolem->statistics.explicit_propagations,
               (float) c2->skolem->statistics.explicit_propagations / (float) (c2->skolem->statistics.propagations + 1),
               c2->skolem->statistics.pure_vars,
               (float) c2->skolem->statistics.pure_vars / (float) (c2->skolem->statistics.propagations + 1),
               c2->skolem->statistics.pure_constants,
               (float) c2->skolem->statistics.pure_constants / (float) (c2->skolem->statistics.pure_vars + 1),
               c2->skolem->statistics.local_determinicity_checks,
               (float) c2->skolem->statistics.local_determinicity_checks / (float) (c2->skolem->statistics.propagations + 1),
               c2->skolem->statistics.local_conflict_checks,
               c2->skolem->statistics.global_conflict_checks,
               (float) c2->skolem->statistics.global_conflict_checks / (float) (c2->skolem->statistics.local_conflict_checks + 1),
               (float) c2->statistics.conflicts / (float) (c2->skolem->statistics.global_conflict_checks + 1),
               c2->skolem->statistics.explicit_propagation_conflicts,
               (float) c2->skolem->statistics.explicit_propagation_conflicts / (float) (c2->statistics.conflicts + 1),
               c2->statistics.learnt_clauses_total_length,
               (float) c2->statistics.learnt_clauses_total_length / (float) (c2->statistics.conflicts + 1),
               c2->statistics.successful_conflict_clause_minimizations,
               (float) c2->statistics.successful_conflict_clause_minimizations / (float) (c2->statistics.learnt_clauses_total_length + 1),
               c2->statistics.cases_explored
               );
    
}

void c2_rl_print_decision(Options* o, unsigned decision_var_id, int phase) {
    LOG_PRINTF("d %u,%d\n", decision_var_id, phase);
}


char *buffer = NULL;

int c2_rl_get_decision() {
    size_t bufsize = 32;
    
    if (buffer == NULL) {
        buffer = (char *)malloc(bufsize * sizeof(char));
        if( buffer == NULL) {
            perror("Unable to allocate input buffer for reinforcement learning");
            exit(1);
        }
    }
    ssize_t characters = getline(&buffer, &bufsize, stdin);
    abortif(characters == 0, "Could not read number from stdin");
    
    char *s = buffer;
    char *end;
    long ret = LONG_MIN;
    ret = strtol(s, &end, 10);
//    LOG_PRINTF("The number(unsigned long integer) is %ld\n", ret);
    abortif(*s == '\0', "String could not be read.");
    abortif(*end != '\0' && *end != '\n', "String not terminated by \\0 or \\n");
    assert(ret != LONG_MIN);
    assert(ret <= INT_MAX);
    assert(ret >= INT_MIN);
    return (int) ret;
}

