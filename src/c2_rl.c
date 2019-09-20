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

typedef struct {
    Stats* stats;
    // Record relevant information about the run to give rewards later
    map* conflicts_in_reward_vector; // maps learnt clauses to an index in the reward vector. Used for rewarding "necessary" conflicts.
    
    // reward vector etc
    float_vector* rewards;
    bool mute;
} RL;

RL* rl = NULL;
char* mock_file = NULL;

void rl_init() {
    assert(rl == NULL);
    rl = malloc(sizeof(RL));
    rl->stats = statistics_init(10000);
    rl->rewards = float_vector_init();
    rl->conflicts_in_reward_vector = map_init();
    rl->mute = false;
}


void rl_mute() {
    if (rl) {
        assert(!rl->mute);
        rl->mute = true;
    }
}
void rl_unmute() {
    if (rl) {
        assert(rl->mute);
        rl->mute = false;
    }
}

void rl_add_reward(unsigned dec_idx, float value) { // for current decision
    abortif(dec_idx >= float_vector_count(rl->rewards), "Array out of bounds.");
    float_vector_set(rl->rewards, dec_idx, float_vector_get(rl->rewards, dec_idx) + value);
}

void rl_free() {
    statistics_free(rl->stats);
    float_vector_free(rl->rewards);
    map_free(rl->conflicts_in_reward_vector);
    free(rl);
    rl = NULL;
}

void c2_rl_print_activity(unsigned var_id, float activity) {
    if (rl && !rl->mute && activity > 0.5) {
        LOG_PRINTF("a %u,%f\n", var_id, activity);
    }
}

void c2_rl_conflict(unsigned var_id) {
    if (rl && !rl->mute) {
        LOG_PRINTF("conflict %u\n", var_id);
    }
}

void c2_rl_update_constant_value(unsigned var_id, int val) {
    if (rl && !rl->mute) {
        LOG_PRINTF("v %u %d\n", var_id, val);
    }
}

void c2_rl_update_unique_consequence(unsigned clause_idx, Lit lit) {
    if (rl && !rl->mute) {
        LOG_PRINTF("uc %u %d\n", clause_idx, lit);
    }
}

void c2_rl_update_D(unsigned var_id, bool deterministic) {
    if (rl && !rl->mute) {
        LOG_PRINTF("u%c %u\n", deterministic?'+':'-',var_id);
    }
}

void c2_rl_new_clause(Clause* c) {
    if (rl && !rl->mute) {
        if (!c->original) {
            map_add(rl->conflicts_in_reward_vector, (int) c->clause_idx, (void*) (size_t) (float_vector_count(rl->rewards) - 1));
        }
        LOG_PRINTF("clause %u %u lits", c->clause_idx, !c->original);
        for (unsigned i = 0; i < c->size; i++) {
            LOG_PRINTF(" %d",c->occs[i]);
        }
        LOG_PRINTF("\n");
    }
}

void c2_rl_delete_clause(Clause* c) {
    if (rl && !rl->mute) {
        LOG_PRINTF("delete_clause %u\n", c->clause_idx);
    }
}

void c2_rl_print_slim_state(C2* c2, unsigned conflicts_until_next_restart) {
    if (!rl || rl->mute) {
        return;
    }
    unsigned var_num = var_vector_count(c2->qcnf->vars);
    LOG_PRINTF("s %u,%f,%zu,%zu,%u\n",
               c2->skolem->decision_lvl,
               (float) int_vector_count(c2->skolem->determinization_order) / (float) (var_num + 1),
               c2->restarts,
               c2->restarts_since_last_major,
               conflicts_until_next_restart);
}

void c2_rl_print_state(C2* c2, unsigned conflicts_until_next_restart, float max_activity) {
    if (!rl || rl->mute) {
        return;
    }
    
    // this makes sure that very large values are mapped to -1, which helps us avoid normalization ...
    int conflicts_until_next_restart_int = (int) conflicts_until_next_restart;
    if (conflicts_until_next_restart > UINT_MAX / 2) {
        conflicts_until_next_restart_int = -1;
    }
    
    unsigned var_num = var_vector_count(c2->qcnf->vars);
    unsigned uvar_num = 0;
    if (!qcnf_is_propositional(c2->qcnf)) {
        Scope* s = vector_get(c2->qcnf->scopes, 1);
        uvar_num = int_vector_count(s->vars);
    }
    float var_ratio = (float) uvar_num / (float) (var_num + 1);
    if (c2->options->rl_slim_state) {
        LOG_PRINTF("s %u,%u,%f,%zu,%zu,%d,%f\n",
                   c2->restart_base_decision_lvl,
                   c2->skolem->decision_lvl,
                   (float) int_vector_count(c2->skolem->determinization_order) / (float) (var_num + 1),
                   c2->restarts,
                   c2->restarts_since_last_major,
                   conflicts_until_next_restart_int,
                   max_activity
                   );
    } else {
        // Solver state
        LOG_PRINTF("s %u,%u,%u,%f,%zu,%zu,%d,",
                   c2->restart_base_decision_lvl,
                   c2->skolem->decision_lvl,
                   int_vector_count(c2->skolem->determinization_order),
                   (float) int_vector_count(c2->skolem->determinization_order) / (float) (var_num + 1),
                   c2->restarts,
                   c2->restarts_since_last_major,
                   conflicts_until_next_restart_int
                   );
        
        // Formula statistics
        LOG_PRINTF("%u,%u,%f,",
                   var_num,
                   vector_count(c2->qcnf->active_clauses),
                   var_ratio);
        
        // Solver statistics
        LOG_PRINTF("%zu,%zu,%f,%f,%zu,%f,%zu,%f,%zu,%f,%zu,%f,%zu,%f,%zu,%zu,%f,%f,%zu,%f,%zu,%f,%zu,%f,%zu,%f\n",
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
                   c2->statistics.cases_closed,
                   max_activity
                   );
    }
}

void c2_rl_print_decision(unsigned decision_var_id, int phase) {
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


// decision var is the default, returns its ID if user does not pick a variable
int c2_rl_get_decision(C2* solver, unsigned default_decision, float max_activity) {
    Rewards* r = solver->options->rewards;
    long ret = 0;
    bool pick_by_std_heuristic = false;
    bool restart = false;
    bool ask_on_terminal_for_line = !solver->options->reinforcement_learning_mock;
    if (ask_on_terminal_for_line) {
        char *s = c2_rl_readline();
        if (s != NULL && s[0] == '?') {
            pick_by_std_heuristic = true;
        } else if (s != NULL && s[0] == 'r') {
            assert(ret == 0);
            restart = true;
        } else {
            char *end = NULL;
            ret = LONG_MIN;
            ret = strtol(s, &end, 10); // convert to an integer, base 10, end pointer indicates last character read.
            //    LOG_PRINTF("The number(unsigned long integer) is %ld\n", ret);
            abortif(*s == '\0', "String could not be read.");
            abortif(*end != '\0' && *end != '\n', "String not terminated by \\0 or \\n");
        }
    }
    assert(!restart || ! pick_by_std_heuristic);
    
    if (pick_by_std_heuristic || solver->options->reinforcement_learning_mock) {
        ret = default_decision;
    }
    
    assert(ret != LONG_MIN);
    assert(ret > INT_MIN);
    assert(ret <= INT_MAX);
    
    if (ret != 0) {
        assert(!restart);
        unsigned var_id = lit_to_var((int) ret);
        
        float activity_ratio = 0.0f;
        if (max_activity > 0.0) {
            float decision_activity = c2_get_activity(solver, var_id);
            activity_ratio = decision_activity / max_activity;
            assert(activity_ratio <= 1.0f);
            assert(activity_ratio >= 0.0f);
        }
        
        float aux = 0.0f;
        if (solver->options->rl_vsids_rewards) {
            aux = - r->vsids_similarity_reward_factor * r->reward_per_decision * activity_ratio;
            abortif(aux < 0.0f, "Illegal value for VSIDS aux reward: %f\n", aux);
        }
        float_vector_add(rl->rewards, r->reward_per_decision + aux);
    }
    
    if (restart) {
        float_vector_add(rl->rewards, r->reward_per_decision * 10);
        ret = INT_MIN; // is a hack; indicates a restart
    }
    
    return (int) ret;
}

void c2_rl_print_rewards() {
    float total = 0.0f;
    unsigned positive_reward_num = 0;
    LOG_PRINTF("rewards");
    for (unsigned i = 0; i < float_vector_count(rl->rewards); i++) {
        float r = float_vector_get(rl->rewards, i);
        LOG_PRINTF(" %f", r);
        total += r;
        if (r > 0.0) {positive_reward_num += 1;}
    }
    LOG_PRINTF("\n");
    V1("Total reward %f over %u decisions; %u of which are positive.\n", total, float_vector_count(rl->rewards), positive_reward_num);
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

int_vector* c2_rl_necessary_learnt_clauses(C2* solver) {
    rl_mute();
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
    Clause_Iterator ci = qcnf_get_clause_iterator(solver->qcnf); Clause* c = NULL;
    while ((c = qcnf_next_clause(&ci)) != NULL) {
        assert(c->active);
        if (c->is_cube) {
            // Even without casesplits, CADET generates an empty cube as the last step
            assert(c->size == 0);
            continue;
        }
        assert(!c->universal_clause);
        for (unsigned j = 0; j < c->size; j++) {
            qcnf_add_lit(qcnf_copy, c->occs[j]);
        }
        if (!c->original) {
            // this is a learnt clause or a minimized clause
            unsigned universal = qcnf_fresh_universal(qcnf_copy);
            map_add(lc_vars, (int) universal, (void*)(size_t) c->clause_idx); // clause_idxs of new and c may differ
            int_vector_add(universal_assumptions, (int) universal);
            
            qcnf_add_lit(qcnf_copy, - (Lit) universal);
        }
        Clause* new = qcnf_close_clause(qcnf_copy);
        new->original = c->original;
        new->blocked = c->blocked;
        new->consistent_with_originals = c->consistent_with_originals;
        new->is_cube = c->is_cube;
        new->minimized = c->minimized;
        new->universal_clause = c->universal_clause;
    }
    
    // Step 2: Replay skolem domain to build the SAT formula
    Skolem* replay = skolem_init(qcnf_copy, solver->options);

    Case* last_case = vector_get(solver->cs->closed_cases, vector_count(solver->cs->closed_cases) - 1);
    casesplits_record_conflicts(replay, last_case->determinization_order);
    skolem_encode_global_conflict_check(replay);
    int_vector* necessary_assumptions = c2_rl_test_assumptions(replay, universal_assumptions);
    abortif(!necessary_assumptions, "Formula was not solved correctly in RL mode. Generation of early rewards failed."); // can now fail because we change the determinization order of the case for storage TODO
#ifdef DEBUG
    for (unsigned i = 0; i < int_vector_count(necessary_assumptions); i++) {
        assert(int_vector_contains(universal_assumptions, int_vector_get(necessary_assumptions, i)));
    }
#endif
    V1("%d out of %d learnt clauses were necessary.\n",
       int_vector_count(necessary_assumptions),
       int_vector_count(universal_assumptions));
    int_vector* necessary_clause_idxs = int_vector_init();
    for (unsigned i = 0; i < int_vector_count(necessary_assumptions); i++) {
        Lit lit = int_vector_get(necessary_assumptions, i);
        assert(lit > 0);
        unsigned var_id = lit_to_var(lit);
        unsigned clause_idx = (unsigned) map_get(lc_vars, (int) var_id);
        assert(qcnf_is_active(solver->qcnf, clause_idx));
        int_vector_add(necessary_clause_idxs, (int) clause_idx);
    }
    int_vector_free(necessary_assumptions);
    rl_unmute();
    return necessary_clause_idxs;
}

// Gives half the reward to the clause itself and, recursively, the other half
// of the reward to the clauses it was derived from.
void rl_reward_clause(C2* solver, unsigned idx, float total_reward) {
    Rewards* r = solver->options->rewards;
    int_vector* clauses_to_reward = int_vector_init();
    int_vector_add(clauses_to_reward, (int) idx);
    float_vector* clause_rewards_to_distribute = float_vector_init();
    float_vector_add(clause_rewards_to_distribute, total_reward);
    while (int_vector_count(clauses_to_reward)) {
        assert(int_vector_count(clauses_to_reward) == float_vector_count(clause_rewards_to_distribute));
        unsigned idx = (unsigned) int_vector_pop(clauses_to_reward);
        assert(!qcnf_is_original_clause(solver->qcnf, idx));
        assert(map_contains(rl->conflicts_in_reward_vector, (int) idx));
        
        float reward = float_vector_pop(clause_rewards_to_distribute);
        unsigned reward_idx = (unsigned) map_get(rl->conflicts_in_reward_vector, (int) idx);
        
        float self_reward = reward * r->self_reward_factor;
        float remaining_reward = reward - self_reward;
        rl_add_reward(reward_idx, self_reward);
        V1("Rewarding clause %u at pos %u with %f\n", idx, reward_idx, self_reward);
        
        // Count how many of the operands were learnt clauses, then distribute the remaining reward evenly
        unsigned learnt_clause_operands = 0;
        int_vector* resolution_operands = NULL;
        if (map_contains(solver->ca->resolution_graph, (int) idx)) {
            resolution_operands = map_get(solver->ca->resolution_graph, (int) idx);
            for (unsigned i = 0; i < int_vector_count(resolution_operands); i++) {
                unsigned operand_clause_idx = (unsigned) int_vector_get(resolution_operands, i);
                if (!qcnf_is_original_clause(solver->qcnf, operand_clause_idx)) {
                    learnt_clause_operands += 1;
                }
            }
        }
        if (learnt_clause_operands > 0) {
            assert(resolution_operands);
            float reward_per_operand = remaining_reward / (float) learnt_clause_operands;
            for (unsigned i = 0; i < int_vector_count(resolution_operands); i++) {
                unsigned operand_clause_idx = (unsigned) int_vector_get(resolution_operands, i);
                if (!qcnf_is_original_clause(solver->qcnf, operand_clause_idx)) {
                    unsigned operand_reward_idx = (unsigned) map_get(rl->conflicts_in_reward_vector, (int) operand_clause_idx);
                    assert(operand_reward_idx <= reward_idx);
                    int_vector_add(clauses_to_reward, (int) operand_clause_idx);
                    float_vector_add(clause_rewards_to_distribute, reward_per_operand);
                }
            }
        } else {
            rl_add_reward(reward_idx, remaining_reward);
            V1("Rewarding REMAINING for clause %u at pos %u with %f\n", idx, reward_idx, remaining_reward);
        }
    }
    int_vector_free(clauses_to_reward);
    clauses_to_reward = NULL;
}

void rl_mock_file(char* file_name) {
    mock_file = file_name;
}

void rl_advanced_action_rewards(C2* solver) {
    Rewards* r = solver->options->rewards;
    if (!solver->options->rl_advanced_rewards) {
        return;
    }
    cadet_res res = c2_result(solver);
    if (res == CADET_RESULT_UNSAT) {
        // Determine which parts of the formula/decisions were important to figure out the counterexample.
        // Could predict the UNSAT core (but there could be multiple ... have to compute a covering of all possible UNSAT cores?)
        // Could predict the refuting assignment ... but there may be many! We would need to check if the networks prediction was correct.
        assert(solver->state == C2_UNSAT);
        if (vector_count(solver->qcnf->all_clauses) > 0) {
            unsigned last_clause_idx = (unsigned) vector_count(solver->qcnf->all_clauses) - 1;
            assert(solver->statistics.decisions == 0 || qcnf_is_active(solver->qcnf, last_clause_idx));
            if (!qcnf_is_original_clause(solver->qcnf, last_clause_idx)) {
                rl_reward_clause(solver, last_clause_idx, r->total_reward_for_necessary_conflicts);
            }
        }
        //            int_vector* refutation = c2_refuting_assignment(solver);
    }
    if (res == CADET_RESULT_SAT) {
        // Determine which learnt clauses were needed for the solution
        
        // Step 1: Add one fresh universal variable per learnt clause
        // If no conflicts were necessary, add the reward to the end; to avoid penalizing direct solutions.
        int_vector* necessary_clause_idxs = c2_rl_necessary_learnt_clauses(solver);
        if (int_vector_count(necessary_clause_idxs) == 0) {
            if (float_vector_count(rl->rewards) > 0) {
                rl_add_reward(float_vector_count(rl->rewards) - 1, r->total_reward_for_necessary_conflicts);
            }
        } else {
            float reward_per_necessary_conflict = r->total_reward_for_necessary_conflicts / (float) int_vector_count(necessary_clause_idxs);
            for (unsigned i = 0; i < int_vector_count(necessary_clause_idxs); i++) {
                unsigned cidx = (unsigned) int_vector_get(necessary_clause_idxs, i);
                assert(qcnf_is_active(solver->qcnf, cidx));
                rl_reward_clause(solver, cidx, reward_per_necessary_conflict);
            }
        }
    }
}

cadet_res c2_rl_run_c2(Options* o) {
    while (true) {
        rl_init();
        
        char *file_name = NULL;
        if (mock_file) {
            file_name = mock_file;
        } else {
            LOG_PRINTF("Enter new filename:\n");
            fflush(stdout);
            file_name = c2_rl_readline();
            LOG_PRINTF("\n");
        }
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
        FILE* file = open_possibly_zipped_file(file_name);
        C2* solver = c2_from_file(file, o);
        close_possibly_zipped_file(file_name, file);
        
        cadet_res res = c2_sat(solver);
        
        if (res == CADET_RESULT_SAT) {
            V0("SAT\n");
        }
        if (res == CADET_RESULT_UNSAT) {
            V0("UNSAT\n");
        }
        
        if (res == CADET_RESULT_SAT || res == CADET_RESULT_UNSAT) {
            if (float_vector_count(rl->rewards) > 0) {
                rl_add_reward(float_vector_count(rl->rewards) - 1, o->rewards->completion_reward);
            }
        }
        
        rl_advanced_action_rewards(solver);
        
        c2_rl_print_rewards();
        
        fflush(stdout);
        
        rl_free();
        c2_free(solver);
        if (mock_file) {
            return res;
        }
    }
    return CADET_RESULT_UNKNOWN;
}
