//
//  c2_analysis.c
//  cadet
//
//  Created by Markus Rabe on 17/12/2016.
//  Copyright © 2016 UC Berkeley. All rights reserved.
//

#include "cadet_internal.h"
#include "log.h"
#include <assert.h>

unsigned c2_analysis_follow_partition_numbers(int_vector* partition_numbers, unsigned pn, unsigned minimal_pn_to_follow) {
    assert(pn < int_vector_count(partition_numbers));
    pn = (unsigned) int_vector_get(partition_numbers, pn);
    while ((unsigned) int_vector_get(partition_numbers, pn) != pn && pn >= minimal_pn_to_follow) {
        abortif(pn >= int_vector_count(partition_numbers), "Illegal partition number.");
        abortif(pn < (unsigned) int_vector_get(partition_numbers, pn), "Partition pointer points in wrong direction.");
        pn = (unsigned) int_vector_get(partition_numbers, pn);
    }
    abortif(pn == 0, "Partition number points to illegal element");
    return pn;
}

void c2_analysis_determine_number_of_partitions(C2* c2) {
    int_vector* partition_numbers = int_vector_init();
    for (unsigned i = 0; i < var_vector_count(c2->qcnf->vars); i++) {
        if (i > 0 && ! skolem_is_deterministic(c2->skolem, i)) {
            int_vector_add(partition_numbers, (int) i);
        } else {
            int_vector_add(partition_numbers, (int) 0);
        }
        assert(int_vector_get(partition_numbers, i) == (int) i || int_vector_get(partition_numbers, i) == 0);
    }
    
    // Connect all vars to the minimal pn in each clause.
    for (unsigned i = 0; i < vector_count(c2->qcnf->all_clauses); i++) {
        Clause* c = vector_get(c2->qcnf->all_clauses, i);
        if (c->original) {
            unsigned minimal_pn = UINT_MAX;
            for (unsigned j = 0; j < c->size; j++) {
                unsigned var_id = lit_to_var(c->occs[j]);
                unsigned pn = (unsigned) int_vector_get(partition_numbers, var_id);
                if (pn != 0 && pn < minimal_pn) {
                    minimal_pn = pn;
                }
            }
            
            // set pn for all literals in the clause (all that are not excluded)
            if (minimal_pn != UINT_MAX) {
                // follow minimal_pn to minimize further, not strictly required
                minimal_pn = c2_analysis_follow_partition_numbers(partition_numbers,minimal_pn,0);
                
                for (unsigned j = 0; j < c->size; j++) {
                    unsigned var_id = lit_to_var(c->occs[j]);
                    unsigned pn = (unsigned) int_vector_get(partition_numbers, var_id);
                    if (pn != 0) {
                        assert(! skolem_is_deterministic(c2->skolem, var_id));
                        // connect partition of var_id to minimal_pn
                        int_vector_set(partition_numbers, pn, (int) minimal_pn);
                        // optional, but also set partition of var_id explicitly to minimal_pn (was pointing to pn)
                        int_vector_set(partition_numbers, var_id, (int) minimal_pn);
                    }
                }
            }
        }
    }
    // now we have a tree of partition pointers
    
    // Contract the tree of partition pointers and number the partitions incrementally
    unsigned number_of_partitions = 0;
    int_vector* partition_sizes = int_vector_init();
    for (unsigned i = 0; i < var_vector_count(c2->qcnf->vars); i++) {
        unsigned pn = (unsigned) int_vector_get(partition_numbers, i);
        if (pn != 0 && qcnf_var_exists(c2->qcnf, i)) {
            if (pn == i) {
                number_of_partitions++;
                int_vector_set(partition_numbers, i, (int) number_of_partitions);
                int_vector_add(partition_sizes, 1);
            } else {
                unsigned new_pn = c2_analysis_follow_partition_numbers(partition_numbers, pn, number_of_partitions+1);
                assert(new_pn != 0);
                assert(new_pn <= number_of_partitions);
                int_vector_set(partition_numbers, i, (int) new_pn);
                int_vector_set(partition_sizes, new_pn - 1, int_vector_get(partition_sizes, new_pn - 1) + 1);
            }
        }
    }
    
#ifdef DEBUG
    for (unsigned i = 0; i < vector_count(c2->qcnf->all_clauses); i++) {
        Clause* c = vector_get(c2->qcnf->all_clauses, i);
        if (c->original) {
            unsigned clause_pn = 0;
            for (unsigned j = 0; j < c->size; j++) {
                unsigned var_id = lit_to_var(c->occs[j]);
                unsigned pn = (unsigned) int_vector_get(partition_numbers, var_id);
                if (clause_pn == 0) {
                    clause_pn = pn;
                }
                if (pn != 0) {
                    assert(pn == clause_pn);
                }
            }
        }
    }
#endif
    
    int_vector* clauses_per_partition = int_vector_init();
    int_vector* interface_clauses_per_partition = int_vector_init();
    vector* interface_vars_per_partition = vector_init();
    for (unsigned i = 0; i < int_vector_count(partition_sizes); i++) {
        int_vector_add(clauses_per_partition, 0);
        int_vector_add(interface_clauses_per_partition, 0);
        vector_add(interface_vars_per_partition, int_vector_init());
    }
    for (unsigned i = 0; i < vector_count(c2->qcnf->all_clauses); i++) {
        Clause* c = vector_get(c2->qcnf->all_clauses, i);
        if (c->original) {
            bool contains_deterministic = false;
            unsigned clause_partition_number = 0;
            for (unsigned j = 0; j < c->size; j++) {
                unsigned var_id = lit_to_var(c->occs[j]);
                unsigned pn = (unsigned) int_vector_get(partition_numbers, var_id);
                if (clause_partition_number == 0) {
                    clause_partition_number = pn;
                } else {
                    assert(pn == 0 || pn == clause_partition_number);
                }
                if (!contains_deterministic && skolem_is_deterministic(c2->skolem, var_id)) {
                    contains_deterministic = true;
                }
            }
            
            if (clause_partition_number != 0) {
                int old_num = int_vector_get(clauses_per_partition, clause_partition_number - 1);
                int_vector_set(clauses_per_partition, clause_partition_number - 1, old_num + 1);
                if (contains_deterministic) {
                    for (unsigned j = 0; j < c->size; j++) {
                        unsigned var_id = lit_to_var(c->occs[j]);
                        if (skolem_is_deterministic(c2->skolem, var_id)) {
                            int_vector_add((int_vector*) vector_get(interface_vars_per_partition, clause_partition_number - 1), (int) var_id);
                        }
                    }
                    
                    int old_num2 = int_vector_get(interface_clauses_per_partition, clause_partition_number - 1);
                    int_vector_set(interface_clauses_per_partition, clause_partition_number - 1, old_num2 + 1);
                }
            }
        }
    }
    for (unsigned i = 0; i < vector_count(interface_vars_per_partition); i++) {
        int_vector_sort(vector_get(interface_vars_per_partition, i), compare_integers_natural_order);
        int_vector_remove_duplicates(vector_get(interface_vars_per_partition, i));
    }
    
    V0("Partitioning statistics:\n");
    V0("  Found %u partitions! Variables per partition:", number_of_partitions);
    int_vector_print(partition_sizes);
    if (c2->options->print_detailed_miniscoping_stats) {
        for (unsigned i = 0; i < number_of_partitions; i++) {
            printf("  Partition %u:", i);
            for (unsigned j = 0; j < int_vector_count(partition_numbers); j++) {
                unsigned pn = (unsigned) int_vector_get(partition_numbers, j);
                if (pn == i + 1) {
                    printf(" %u", j);
                }
            }
            printf("\n");
        }
    }
    V0("  Clauses per partition: ");
    int_vector_print(clauses_per_partition);
    V0("  Interface clauses per partition:");
    int_vector_print(interface_clauses_per_partition);
    V0("  Interface vars per partition:");
    for (unsigned i = 0; i < vector_count(interface_vars_per_partition); i++) {
        V0(" %u",int_vector_count(vector_get(interface_vars_per_partition, i)));
    }
    V0("\n");
    
    int_vector_free(partition_sizes);
    int_vector_free(clauses_per_partition);
    int_vector_free(interface_clauses_per_partition);
    for (unsigned i = 0; i < vector_count(interface_vars_per_partition); i++) {
        int_vector_free(vector_get(interface_vars_per_partition, i));
    }
    vector_free(interface_vars_per_partition);
    int_vector_free(partition_numbers);
}
