//
//  decision_tree.c
//  cadet
//
//  Created by Markus Rabe on 6/29/20.
//  Copyright © 2020 UC Berkeley. All rights reserved.
//

#include "skolem.h"
#include "skolem_var.h"
#include "skolem_dependencies.h"
#include "log.h"
#include "util.h"
#include "c2_traces.h"
#include "casesplits.h"
#include "c2_rl.h"
#include "set.h"

#include <math.h>
#include <assert.h>
#include <stdint.h>
#include <sys/time.h>


unsigned MAX_DECISION_DEPTH = 4;
unsigned RELEVANT_CLAUSE_MAX_DISTANCE = 1;


void skolem_dt_relevant_clauses(Skolem* s, Lit lit,
                                vector* lit_clauses, float_vector* values,
                                set* split_candidates,
                                unsigned depth) {
    // Initialize lit_clauses and lit_values for the decision tree algorithm
//    assert(vector_count(lit_clauses) == 0);
//    assert(float_vector_count(values) == 0);
    if (depth == 0) {
        return;  // depth indicates how many hops away the clauses can be
    }
    
    vector* lit_occs = qcnf_get_occs_of_lit(s->qcnf, lit);
    for (unsigned i = 0; i < vector_count(lit_occs); i++) {
        Clause* c = vector_get(lit_occs, i);
        assert( - lit != skolem_get_unique_consequence(s, c));
//        if (lit == skolem_get_unique_consequence(s, c)) {
//            continue;
//        }
        // All clauses that are not satisfied are fair game
        if (skolem_clause_satisfied(s, c)) {
            continue;
        }
        vector_add(lit_clauses, c);
        float value = ((float) depth) / ((float) c->size * (float) c->size);  // quadratic size weighting
        if (value < 0.0f) {value = 0.0f;}
        float_vector_add(values, value);  // c->size cannot be zero as it must contain lit
        
        for (unsigned j = 0; j < c->size; j++) {
            Lit l = c->occs[j];
            if (l == lit) {
                continue;
            }
            unsigned var_id = lit_to_var(l);
            void* var_id_as_ptr = (void*) (unsigned long) var_id;
            if (skolem_is_deterministic(s, var_id) && ! set_contains(split_candidates, var_id_as_ptr)) {
                set_add(split_candidates, var_id_as_ptr);
                
                skolem_dt_relevant_clauses(s, l, lit_clauses, values, split_candidates, depth - 1);
//                // Now also add all clauses that imply the literal (with low weight)
//                Var* split_candidate = var_vector_get(s->qcnf->vars, var_id);
//                vector* occs = NULL;
//                if (l > 0) {
//                    occs = &split_candidate->pos_occs;
//                } else {
//                    occs = &split_candidate->neg_occs;
//                }
//                for (unsigned k = 0; k < vector_count(occs); k ++) {
//                    Clause* other_clause = vector_get(occs, k);
//                    vector_add(lit_clauses, other_clause);
//                    float value = 0.25f;  // base weight for second degree clauses
//                    value = value / ((float) other_clause->size * (float) other_clause->size);  // quadratic size weighting
//                    float_vector_add(values, value / other_clause->size);
//                }
            }
        }
    }
}

float skolem_dt_upper_entropy_bound(float p_pos, float p_neg, float p_unknown) {
    p_pos = p_pos + p_unknown;
    p_neg = p_neg + p_unknown;
    return p_pos * log2f(p_pos) + p_neg * log2f(p_neg);
}

float skolem_dt_candidate_information_gain(
        Skolem* s, Lit decision_lit, unsigned split_candidate_var_id,
        vector* pos_clauses, float_vector* pos_values,
        vector* neg_clauses, float_vector* neg_values) {
    float true_pos = 0.0f;  // candidate is true and decision lit is true
    float false_pos = 0.0f;  // candidate is false and decision lit is true
    float none_pos = 0.0f;  // candidate is not in clause and decision lit is true
    float all_pos = 0.0f;
    Var* candidate_var = var_vector_get(s->qcnf->vars, split_candidate_var_id);
    for (unsigned i = 0; i < vector_count(pos_clauses); i++) {
        Clause* c = vector_get(pos_clauses, i);
        float clause_value = float_vector_get(pos_values, i);
        int candidate_lit = qcnf_contains_variable(c, candidate_var);
        all_pos += clause_value;
        if (candidate_lit > 0) {
            true_pos += clause_value;
        } else if (candidate_lit < 0) {
            false_pos += clause_value;
        } else { /* candidate_lit == 0 */
            none_pos += clause_value;
        }
    }
    float true_neg = 0.0f;  // candidate is true and decision lit is false
    float false_neg = 0.0f;  // candidate is false and decision lit is false
    float none_neg = 0.0f;  // candidate is not in clause and decision lit is false
    float all_neg = 0.0f;
    for (unsigned i = 0; i < vector_count(neg_clauses); i++) {
        Clause* c = vector_get(neg_clauses, i);
        float clause_value = float_vector_get(neg_values, i);
        int candidate_lit = qcnf_contains_variable(c, candidate_var);
        all_neg += clause_value;
        if (candidate_lit > 0) {
            true_neg += clause_value;
        } else if (candidate_lit < 0) {
            false_neg += clause_value;
        } else { /* candidate_lit == 0 */
            none_neg += clause_value;
        }
    }
    float entropy_entire_set = skolem_dt_upper_entropy_bound(all_pos, all_neg, 0.0f);
    float entropy_true_split = skolem_dt_upper_entropy_bound(true_pos, true_neg, none_pos + none_neg);
    float entropy_false_split = skolem_dt_upper_entropy_bound(false_pos, false_neg, none_pos + none_neg);
    
    float total_size = all_pos + all_neg;
    if (total_size < 0.0001f) {
        V1("Total size of clause set is close to zero: %f\n", total_size);
        total_size = 0.0001f;
    }
    float size_true_split = true_pos + none_pos + none_neg + true_neg;
    float prob_true_split = size_true_split / total_size;
    float size_false_split = false_pos + none_pos + none_neg + false_neg;
    float prob_false_split = size_false_split / total_size;
    
    return entropy_entire_set - prob_true_split * entropy_true_split - prob_false_split * entropy_false_split;
}

void skolem_dt_clauses_not_containing_lit(vector* clauses, float_vector* values,
                                             vector* split_clauses, float_vector* split_values,
                                             Lit lit) {
    // Split off the clauses and values of clauses that do not contain lit. Populates vectors split_*.
    assert(vector_count(split_clauses) == 0);
    assert(float_vector_count(split_values) == 0);
    for (unsigned i = 0; i < vector_count(clauses); i++) {
        Clause* c = vector_get(clauses, i);
        if (! qcnf_contains_literal(c, lit)) {
            vector_add(split_clauses, c);
            float_vector_add(split_values, float_vector_get(values, i));
        }
    }
}

void skolem_dt_recursive_splits(Skolem* s, Lit decision_lit, int decision_tree_sat_lit,
                                vector* pos_clauses, float_vector* pos_values,
                                vector* neg_clauses, float_vector* neg_values,
                                int_vector* split_candidates, unsigned max_decision_depth,
                                int_vector* collected_literals) {
    // Recursive function
    // 1. For each potential split variable, determine how much it would split clauses.
    // 2. Pick variable with highest (lower bound of) entropy. Remove split variable from split_candidates.
    // 3. Split clause list according to dt variable picked
    // 4. Split and extend collected_literals and recurse.
    
    // TODO: catch special cases, such as empty clause lists.
    
    bool allocated_collected_literals = false;
    if (collected_literals == NULL) {
        collected_literals = int_vector_init();
        allocated_collected_literals = true;
    }
    
    bool close_case = max_decision_depth <= 0;
    if (vector_count(pos_clauses) == 0) {
        V3("DT: no pos clauses.\n");
        close_case = true;
    }
    if (vector_count(neg_clauses) == 0) {
        V3("DT: no neg clauses.\n");
        close_case = true;
    }
    
    int best_split_candidate_idx = -1;
    float best_split_candidate_ig = 0.0f;
    for (unsigned i = 0; i < int_vector_count(split_candidates); i++) {
        if (close_case) {break;}
        unsigned split_candidate_var_id = (unsigned) int_vector_get(split_candidates, i);
        float ig = skolem_dt_candidate_information_gain(s, decision_lit, split_candidate_var_id,
                                                        pos_clauses, pos_values, neg_clauses, neg_values);
        if (best_split_candidate_idx == -1 || ig > best_split_candidate_ig) {
            best_split_candidate_ig = ig;
            best_split_candidate_idx = (int) i;
        }
    }
    
    if (best_split_candidate_idx == -1) {
        V2("Did not find a split candidate.\n");
        close_case = true;
    }
    
    if (close_case) {
        V2("Decision clause:");
        for (unsigned i = 0; i < int_vector_count(collected_literals); i ++) {
            int lit = int_vector_get(collected_literals, i);
            satsolver_add(s->skolem, skolem_get_satsolver_lit(s, - lit));
            V2(" %d", - lit);
        }
        float pos_weight = 0.0f;
        float neg_weight = 0.0f;
        for (unsigned j = 0; j < float_vector_count(pos_values); j++) {
            pos_weight += float_vector_get(pos_values, j);
        }
        for (unsigned j = 0; j < float_vector_count(neg_values); j++) {
            neg_weight += float_vector_get(neg_values, j);
        }
        if (pos_weight > neg_weight) {
            satsolver_add(s->skolem, decision_tree_sat_lit);
            V2(" %d", decision_lit);
        } else {
            satsolver_add(s->skolem, - decision_tree_sat_lit);
            V2(" %d", - decision_lit);
        }
        satsolver_clause_finished(s->skolem);
        V2("\n");  // end of decision clause logging
    } else {
        Lit best_split_candidate_lit = int_vector_get(split_candidates, (unsigned) best_split_candidate_idx);
        V2("Recurse on split candidate: %d (pos %d/neg %d)\n", best_split_candidate_lit, vector_count(pos_clauses), vector_count(neg_clauses));
        // Recursive call for positive split
        int_vector* split_candidates_pos = int_vector_copy(split_candidates);
        int_vector_remove_index(split_candidates_pos, (unsigned) best_split_candidate_idx);
        int_vector* collected_literals_pos = int_vector_copy(collected_literals);
        int_vector_add(collected_literals_pos, best_split_candidate_lit);
        
        vector* true_pos_clauses = vector_init();
        float_vector* true_pos_values = float_vector_init();
        vector* true_neg_clauses = vector_init();
        float_vector* true_neg_values = float_vector_init();
        skolem_dt_clauses_not_containing_lit(pos_clauses, pos_values, true_pos_clauses, true_pos_values, best_split_candidate_lit);
        skolem_dt_clauses_not_containing_lit(neg_clauses, neg_values, true_neg_clauses, true_neg_values, best_split_candidate_lit);
        
        skolem_dt_recursive_splits(s, decision_lit, decision_tree_sat_lit, true_pos_clauses, true_pos_values, true_neg_clauses, true_neg_values, split_candidates_pos, max_decision_depth - 1, collected_literals_pos);
        
        vector_free(true_pos_clauses);
        float_vector_free(true_pos_values);
        vector_free(true_neg_clauses);
        float_vector_free(true_neg_values);
        int_vector_free(split_candidates_pos);
        int_vector_free(collected_literals_pos);
            
        // Recursive call for negative split
        int_vector* split_candidates_neg = int_vector_copy(split_candidates);
        int_vector_remove_index(split_candidates_neg, (unsigned) best_split_candidate_idx);
        int_vector* collected_literals_neg = int_vector_copy(collected_literals);
        int_vector_add(collected_literals_neg, - best_split_candidate_lit);
        
        vector* false_pos_clauses = vector_init();
        float_vector* false_pos_values = float_vector_init();
        vector* false_neg_clauses = vector_init();
        float_vector* false_neg_values = float_vector_init();
        skolem_dt_clauses_not_containing_lit(pos_clauses, pos_values, false_pos_clauses, false_pos_values, - best_split_candidate_lit);
        skolem_dt_clauses_not_containing_lit(neg_clauses, neg_values, false_neg_clauses, false_neg_values, - best_split_candidate_lit);
        
        assert(vector_count(false_pos_clauses) == float_vector_count(false_pos_values));
        assert(vector_count(false_neg_clauses) == float_vector_count(false_neg_values));
        
        skolem_dt_recursive_splits(s, decision_lit, decision_tree_sat_lit, false_pos_clauses, false_pos_values, false_neg_clauses, false_neg_values, split_candidates_neg, max_decision_depth - 1, collected_literals_neg);
        
        vector_free(false_pos_clauses);
        float_vector_free(false_pos_values);
        vector_free(false_neg_clauses);
        float_vector_free(false_neg_values);
        int_vector_free(split_candidates_neg);
        int_vector_free(collected_literals_neg);
    }

    if (allocated_collected_literals) {
        int_vector_free(collected_literals);
    }
}

void skolem_learn_decision_tree(Skolem* s, Lit decision_lit, int decision_tree_sat_lit) {
    double time_stamp_start = get_seconds();
    
    // 1. Determine list of decision-tree variables: the list of determined variables.
    // 2. Determine list of clauses: all clauses the decision variable occurs in.
    //     Weigh clauses by size (1/2^size or 1/size?) and weigh it higher if it contains a determined variable.
    // 3. Recursively split set of clauses by selecting split variables.
    
    // var_ids of variables we can use as split variables in the decision tree
    set* split_candidate_set = set_init();
    
    vector* pos_clauses = vector_init();
    float_vector* pos_values = float_vector_init();
    vector* neg_clauses = vector_init();
    float_vector* neg_values = float_vector_init();
    
    skolem_dt_relevant_clauses(s, decision_lit, pos_clauses, pos_values, split_candidate_set, RELEVANT_CLAUSE_MAX_DISTANCE);
    skolem_dt_relevant_clauses(s, -decision_lit, neg_clauses, neg_values, split_candidate_set, RELEVANT_CLAUSE_MAX_DISTANCE);
    
    vector* split_candidates_raw = set_items(split_candidate_set);  // convert set to vector for easy iteration
    int_vector* split_candidates = int_vector_init();
    for (unsigned i = 0; i < vector_count(split_candidates_raw); i++) {
        unsigned var_id = (unsigned) vector_get(split_candidates_raw, i);
        int_vector_add(split_candidates, (int) var_id);
    }

    skolem_dt_recursive_splits(s, decision_lit, decision_tree_sat_lit,
                               pos_clauses, pos_values, neg_clauses, neg_values,
                               split_candidates, MAX_DECISION_DEPTH, NULL);
    
    V2("Decision tree learned.\n");
    
    set_free(split_candidate_set);
    vector_free(split_candidates_raw);
    int_vector_free(split_candidates);
    vector_free(pos_clauses);
    vector_free(neg_clauses);
    float_vector_free(pos_values);
    float_vector_free(neg_values);
    
    double time_stamp_end = get_seconds();
    statistic_add_value(s->statistics.decision_tree, time_stamp_end - time_stamp_start);
}
