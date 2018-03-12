//
//  c2_rl.c
//  cadet
//
//  Created by Markus Rabe on 24.01.18.
//  Copyright © 2018 UC Berkeley. All rights reserved.
//

#include "c2_rl.h"
#include "log.h"
#include "statistics.h"
#include "float_vector.h"

#include <stdio.h>
#include <math.h>

float reward_cost_per_second = (float) 0.1;
float total_reward_for_necessary_conflicts = (float) 0.1;

typedef struct {
    Stats* stats;
    // Record relevant information about the run to give rewards later
    map* conflicts_in_reward_vector; // maps learnt clauses to an index in the reward vector. Used for rewarding "necessary" conflicts.
    
    // reward vector etc
    float_vector* rewards;
    float_vector* runtimes;
} RL;

RL* rl = NULL;

void rl_init() {
    assert(rl == NULL);
    rl = malloc(sizeof(RL));
    rl->stats = statistics_init(10000);
    rl->rewards = float_vector_init();
    rl->runtimes = float_vector_init();
    rl->conflicts_in_reward_vector = map_init();
}

void rl_add_reward(unsigned dec_idx, float value) { // for current decision
    abortif(dec_idx >= float_vector_count(rl->rewards), "Array out of bounds.");
    float_vector_set(rl->rewards, dec_idx, float_vector_get(rl->rewards, dec_idx) + value);
}

void rl_free() {
    statistics_free(rl->stats);
    float_vector_free(rl->rewards);
    float_vector_free(rl->runtimes);
    map_free(rl->conflicts_in_reward_vector);
    free(rl);
    rl = NULL;
}

void c2_rl_print_activity(Options* o, unsigned var_id, float activity) {
    if (o->reinforcement_learning && activity > 0.5) {
        LOG_PRINTF("a %u,%f\n", var_id, activity);
    }
}

void c2_rl_conflict(Options* o, unsigned var_id) {
    if (!o->reinforcement_learning) {
        return;
    }
    LOG_PRINTF("conflict %u\n", var_id);
}

void c2_rl_update_constant_value(Options* o, unsigned var_id, int val) {
    if (!o->reinforcement_learning) {
        return;
    }
    LOG_PRINTF("v %u %d\n", var_id, val);
}

void c2_rl_update_unique_consequence(Options* o, unsigned clause_idx, Lit lit) {
    if (!o->reinforcement_learning) {
        return;
    }
    LOG_PRINTF("uc %u %d\n", clause_idx, lit);
}

void c2_rl_update_D(Options* o, unsigned var_id, bool deterministic) {
    if (!o->reinforcement_learning) {
        return;
    }
    LOG_PRINTF("u%c %u\n", deterministic?'+':'-',var_id);
}

void c2_rl_new_clause(Options* o, Clause* c) {
    if (!o->reinforcement_learning) {
        return;
    }
    if (!c->original && c->consistent_with_originals) {
        map_add(rl->conflicts_in_reward_vector, (int) c->clause_idx, (void*) (size_t) (float_vector_count(rl->rewards) - 1));
    }
    LOG_PRINTF("clause %u %u lits", c->clause_idx, !c->original);
    for (unsigned i = 0; i < c->size; i++) {
        LOG_PRINTF(" %d",c->occs[i]);
    }
    LOG_PRINTF("\n");
}

void c2_rl_print_state(C2* c2, unsigned conflicts_until_next_restart) {
    if (!c2->options->reinforcement_learning) {
        return;
    }
    
    assert(qcnf_is_2QBF(c2->qcnf));
    
    unsigned var_num = var_vector_count(c2->qcnf->vars);
    Scope* s = vector_get(c2->qcnf->scopes, 1);
    unsigned uvar_num = int_vector_count(s->vars);
    float var_ratio = (float) uvar_num / (float) (var_num + 1);
    
    // Solver state
    LOG_PRINTF("s %u,%u,%u,%f,%zu,%zu,%u,",
               c2->restart_base_decision_lvl,
               c2->skolem->decision_lvl,
               int_vector_count(c2->skolem->determinization_order),
               (float) int_vector_count(c2->skolem->determinization_order) / (float) (var_num + 1),
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
               c2->statistics.cases_closed
               );
}

void c2_rl_print_decision(Options* o, unsigned decision_var_id, int phase) {
    LOG_PRINTF("d %u,%d\n", decision_var_id, phase);
}


char *buffer = NULL;
size_t bufsize = 32;

char* c2_rl_readline() {
    fflush(stdout); // flush stdout to make sure listening processes get the full state before printing a decision
    if (buffer == NULL) {
        buffer = (char *)malloc(bufsize * sizeof(char));
        abortif(buffer == NULL, "Unable to allocate input buffer for reinforcement learning.");
    }
    long characters = getline(&buffer, &bufsize, stdin);
    abortif(characters == 0, "Could not read number from stdin");
    return buffer;
}

int c2_rl_get_decision() {
    double seconds_since_last_decision = 0.0;
    if (statistics_timer_is_running(rl->stats)) {
        seconds_since_last_decision = statistics_stop_and_record_timer(rl->stats);
        float seconds_since_last_decision_float = (float) seconds_since_last_decision;
        assert(!isnan(seconds_since_last_decision_float));
        float_vector_set(rl->runtimes, float_vector_count(rl->runtimes) - 1, seconds_since_last_decision_float);
    }
    
    char *s = c2_rl_readline();
    
    char *end = NULL;
    long ret = LONG_MIN;
    ret = strtol(s, &end, 10); // convert to an integer, base 10, end pointer indicates last character read.
//    LOG_PRINTF("The number(unsigned long integer) is %ld\n", ret);
    abortif(*s == '\0', "String could not be read.");
    abortif(*end != '\0' && *end != '\n', "String not terminated by \\0 or \\n");
    assert(ret != LONG_MIN);
    assert(ret <= INT_MAX);
    assert(ret >= INT_MIN);
    
    if (ret != 0) {
        statistics_start_timer(rl->stats);
        float_vector_add(rl->rewards, 0.0);
        float_vector_add(rl->runtimes, 0.0);
    }
    assert(float_vector_count(rl->rewards) == float_vector_count(rl->runtimes));
    
    return (int) ret;
}

void c2_rl_print_rewards() {
    LOG_PRINTF("rewards");
    for (unsigned i = 0; i < float_vector_count(rl->rewards); i++) {
        LOG_PRINTF(" %f", float_vector_get(rl->rewards, i));
    }
    LOG_PRINTF("\n");
}


int_vector* c2_rl_test_assumptions(Skolem* s, int_vector* universal_assumptions) {
    V1("Testing assumption of closed case\n");
    for (unsigned i = 0; i < int_vector_count(universal_assumptions); i++) {
        Lit lit = int_vector_get(universal_assumptions, i);
        assert(qcnf_is_universal(s->qcnf, lit_to_var(lit)));
        assert(skolem_is_deterministic(s, lit_to_var(lit)));
        int satlit = skolem_get_satsolver_lit(s, lit);
        assert(satlit != - s->satlit_true);
        assert(satlit != s->satlit_true);
        satsolver_assume(s->skolem, satlit);
    }
    
    sat_res res = satsolver_sat(s->skolem);
    if (res == SATSOLVER_UNSAT) {
        int_vector* failed_as = int_vector_init();
        for (unsigned i = 0; i < int_vector_count(universal_assumptions); i++) {
            Lit lit = int_vector_get(universal_assumptions, i);
            int satlit = skolem_get_satsolver_lit(s, lit);
            if (satsolver_failed_assumption(s->skolem, satlit)) {
                int_vector_add(failed_as, lit);
            }
        }
        return failed_as;
    } else {
        return NULL;
    }
}

char *debug_file_name;

int_vector* c2_rl_necessary_learnt_clauses(C2 *solver, Options *o) {
    assert(c2_result(solver) == CADET_RESULT_SAT);
    map* lc_vars = map_init(); // mapping universal variable IDs to learnt clause idxs
    int_vector* universal_assumptions = int_vector_init();
    
    QCNF* qcnf_copy = qcnf_init();
    for (unsigned i = 0; i < var_vector_count(solver->qcnf->vars); i++) {
        if (qcnf_var_exists(solver->qcnf, i)) {
            Var* v = var_vector_get(solver->qcnf->vars, i);
            qcnf_new_var(qcnf_copy, v->is_universal, v->scope_id, v->var_id);
        }
    }
    for (unsigned i = 0; i < vector_count(solver->qcnf->clauses); i++) {
        Clause* c = (Clause*) vector_get(solver->qcnf->clauses, i);
        if (c && !c->is_cube) {
            assert(c->clause_idx == i);
//            assert(!c->minimized); // other clauses may contribute to the SAT proof indirectly by helping to minimize clauses
            Clause* new = NULL;
            for (unsigned j = 0; j < c->size; j++) {
                qcnf_add_lit(qcnf_copy, c->occs[j]);
            }
            if (!c->original && c->consistent_with_originals) {
                // this is a learnt clause!
                unsigned universal = qcnf_fresh_universal(qcnf_copy);
                qcnf_add_lit(qcnf_copy, - (Lit) universal);
                new = qcnf_close_clause(qcnf_copy);
                map_add(lc_vars, (int) universal, (void*)(size_t) new->clause_idx); // clause_idxs of new and c may differ
                int_vector_add(universal_assumptions, (int) universal);
            } else {
                new = qcnf_close_clause(qcnf_copy);
            }
            new->original = c->original;
            new->blocked = c->blocked;
            new->consistent_with_originals = c->consistent_with_originals;
            new->is_cube = c->is_cube;
            new->minimized = c->minimized;
        }
    }
    
    // Step 2: Replay skolem domain to build the SAT formula
    Skolem* replay = skolem_init(qcnf_copy, o);

    Case* last_case = vector_get(solver->cs->closed_cases, vector_count(solver->cs->closed_cases) - 1);
    casesplits_record_conflicts(replay, last_case->decisions);
    int_vector* necessary_assumptions = c2_rl_test_assumptions(replay, universal_assumptions);
    abortif(!necessary_assumptions, "Formula was not solved correctly in RL mode. Generation of early rewards failed.");
    V1("%d out of %d learnt clauses were necessary.\n",
       int_vector_count(necessary_assumptions),
       int_vector_count(universal_assumptions));
    int_vector* necessary_clause_idxs = int_vector_init();
    for (unsigned i = 0; i < int_vector_count(necessary_assumptions); i++) {
        Lit lit = int_vector_get(necessary_assumptions, i);
        assert(lit > 0);
        unsigned var_id = lit_to_var(lit);
        unsigned clause_idx = (unsigned) map_get(lc_vars, (int) var_id);
        int_vector_add(necessary_clause_idxs, (int) clause_idx);
        Clause* c = vector_get(qcnf_copy->clauses, clause_idx);
        assert(c && ! c->original && c->consistent_with_originals);
        if (debug_verbosity >= 1) {
            V1("  ");
            qcnf_print_clause(c, stdout);
        }
    }
    int_vector_free(necessary_assumptions);
    return necessary_clause_idxs;
}

cadet_res c2_rl_run_c2(Options* o) {
    while (true) {
        rl_init();
        char *file_name = c2_rl_readline();
        // scan for end, should be terminated with newline
        char *end = file_name;
        int i = 0; int maxlen = 1000;
        while (i < maxlen) {
            if (*end == '\n') *end = '\0';
            if (*end == '\0') break;
            end += 1;
            i += 1;
        }
        abortif(i >= maxlen, "File name too long.");
        
        LOG_PRINTF("\n");
        FILE* file = open_possibly_zipped_file(file_name);
        C2* solver = c2_from_file(file, o);
        cadet_res res = c2_sat(solver);
        
        if (res == CADET_RESULT_SAT || res == CADET_RESULT_UNSAT) {
            rl_add_reward(float_vector_count(rl->rewards) - 1, 1.0);
        }
        
        if (res == CADET_RESULT_UNSAT) {
            // Determine which parts of the formula/decisions were important to figure out the counterexample.
            // Could predict the UNSAT core (but there could be multiple ... have to compute a covering of all possible UNSAT cores?)
            // Could predict the refuting assignment ... but there may be many! We would need to check if the networks prediction was correct.
            
//            int_vector* refutation = c2_refuting_assignment(solver);
            rl_add_reward(float_vector_count(rl->rewards) - 1, total_reward_for_necessary_conflicts);
        }
        if (res == CADET_RESULT_SAT) {
            // Determine which learnt clauses were needed for the solution
            
            // Step 1: Add one fresh universal variable per learnt clause
            int_vector* necessary_clause_idxs = c2_rl_necessary_learnt_clauses(solver, o);
            for (unsigned i = 0; i < int_vector_count(necessary_clause_idxs); i++) {
                unsigned cidx = (unsigned) int_vector_get(necessary_clause_idxs, i);
                unsigned reward_idx = (unsigned) map_get(rl->conflicts_in_reward_vector, (int) cidx);
                float reward = total_reward_for_necessary_conflicts
                               / (float) int_vector_count(necessary_clause_idxs);
                rl_add_reward(reward_idx, reward);
            }
            // If no conflicts were necessary, add the reward to the end; to avoid penalizing direct solutions.
            if (int_vector_count(necessary_clause_idxs) == 0) {
                rl_add_reward(float_vector_count(rl->rewards) - 1, total_reward_for_necessary_conflicts);
            }
        }
        
        for (unsigned i = 0; i < float_vector_count(rl->rewards); i++) {
            float seconds_since_last_decision = float_vector_get(rl->runtimes, i);
            assert(!isnan(seconds_since_last_decision)); // Time array contains NaN
            if (!isnan(seconds_since_last_decision)) {
                rl_add_reward(i, - seconds_since_last_decision * reward_cost_per_second);
            }
        }
        
        c2_rl_print_rewards();
        rl_free();
    }
    return CADET_RESULT_UNKNOWN;
}
