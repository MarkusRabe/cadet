//
//  satsolver_picosat_assumptions.c
//  cadet
//
//  This is a variant of the picosat interface, building on assumptions only.
//
//  Created by Markus Rabe on 13/01/2017.
//  Copyright © 2017 UC Berkeley. All rights reserved.
//

#include "satsolver.h"

#if (USE_SOLVER == SOLVER_LINGELING_ASSUMPTIONS)

#include "lingeling/lglib.h"
#include "lingeling/lglconst.h"
#include "log.h"
#include "map.h"

#include <assert.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdlib.h>

// Sanity check, make sure the return values are correct
#if (LGL_SATISFIABLE != SATSOLVER_SAT_CONST) || (LGL_UNSATISFIABLE != SATSOLVER_UNSAT_CONST) || (LGL_UNKNOWN != SATSOLVER_UNKNOWN_CONST)
    #error "Return values of SAT solver and the generic SAT solver interface mismatch"
#endif

struct SATSolver {
    LGL* lgl;
    map* var_mapping;
    int max_var;
    int_vector* max_var_stack; // for undo
    int_vector* assumptions;
    bool assumptions_used_in_sat_call;
    int_vector* context_literals;
    
    sat_res res; // last result of sat call, initially unknown
    
    map* reverse_var_mapping;
    bool maintain_reverse_mapping;
    
#ifdef SATSOLVER_TRACE
    bool trace_solver_commands;
#endif
};

static inline int lit_from_int(SATSolver* solver, int lit) {
    bool neg = lit < 0;
    int var = neg ? -lit : lit;
    
    if (lit == 0) {
        return 0;
    } else {
        abortif(solver->max_var < var, "Called lit_from_int on lit %d that is unknown to the SATSolver (with max_var %d).\n", lit, solver->max_var);
    }
    
    // lookup variable
    int nvar;
    if (!map_contains(solver->var_mapping, var)) {
        nvar = lglincvar(solver->lgl);
        lglfreeze(solver->lgl, nvar);
#ifdef SATSOLVER_TRACE
        if (solver->trace_solver_commands) {
            LOG_PRINTF("assert(lglincvar(s) == %d); lglfreeze(s, %d);\n", nvar, nvar);
        }
#endif
        map_add(solver->var_mapping, var, (void *)(intptr_t)nvar);
        if (solver->maintain_reverse_mapping) {
            map_add(solver->reverse_var_mapping, nvar, (void *)(intptr_t)var);
        }
    } else {
        nvar = (int) map_get(solver->var_mapping, var);
    }
    return neg ? -nvar : nvar;
}

SATSolver* satsolver_init() {
    SATSolver* solver = malloc(sizeof(SATSolver));
    solver->lgl = lglinit();
    solver->var_mapping = map_init();
    solver->max_var = 0;
    solver->max_var_stack = int_vector_init();
    solver->assumptions = int_vector_init();
    solver->assumptions_used_in_sat_call = false;
    solver->context_literals = int_vector_init();
    
    solver->maintain_reverse_mapping = false;
    solver->reverse_var_mapping = NULL;
    if (solver->maintain_reverse_mapping) {
        solver->reverse_var_mapping = map_init();
    }
    
    solver->res = SATSOLVER_UNKNOWN;
    
#ifdef SATSOLVER_TRACE
    solver->trace_solver_commands = false;
#endif
    return solver;
}

void satsolver_free(SATSolver* solver) {
#ifdef SATSOLVER_TRACE
    if (solver->trace_solver_commands) {
        LOG_PRINTF("lglrelease(s);\n");
    }
#endif
    
    lglrelease(solver->lgl);
    map_free(solver->var_mapping);
    int_vector_free(solver->assumptions);
    int_vector_free(solver->context_literals);
    
    if (solver->maintain_reverse_mapping) {
        map_free(solver->reverse_var_mapping);
    }
    free(solver);
}

void satsolver_adjust(SATSolver* solver, int variables) {
    // is supposed to raise the maximal variable index in advance, but is not important
    
    // not implemented, but OK
}

void satsolver_save_original_clauses(SATSolver* solver) {
    abort(); // not implemented
}

sat_res satsolver_state(SATSolver* solver) {
    return solver->res;
}

int satsolver_inc_max_var(SATSolver* solver) {
    return ++solver->max_var;
}

int satsolver_get_max_var(SATSolver* solver) {
    return solver->max_var;
}

void satsolver_set_max_var(SATSolver* solver, int new_max) {
    assert(new_max >= solver->max_var);
    solver->max_var = new_max;
}

void satsolver_add(SATSolver* solver, int lit) {
    assert(lit != 0);
    if (solver->assumptions_used_in_sat_call) {
        solver->assumptions_used_in_sat_call = false;
        int_vector_reset(solver->assumptions);
    }
    
    int pico_lit = lit_from_int(solver, lit);
    lgladd(solver->lgl, pico_lit);
    
#ifdef SATSOLVER_TRACE
    if (solver->trace_solver_commands) {
        LOG_PRINTF("lgladd(s,%d);\n",pico_lit);
    }
#endif
}

void satsolver_clause_finished(SATSolver* solver) {
    satsolver_clause_finished_for_context(solver, int_vector_count(solver->context_literals)); // used as proxy for push_count
}

void satsolver_clause_finished_for_context(SATSolver* solver, unsigned context_index) {
    assert(int_vector_count(solver->max_var_stack) == int_vector_count(solver->context_literals));
    assert(context_index <= int_vector_count(solver->context_literals));
    
    if (solver->assumptions_used_in_sat_call) {
        solver->assumptions_used_in_sat_call = false;
        int_vector_reset(solver->assumptions);
    }
    
    if (context_index != 0) {
        int context_lit = int_vector_get(solver->context_literals, context_index - 1);
        lgladd(solver->lgl, context_lit);
#ifdef SATSOLVER_TRACE
        if (solver->trace_solver_commands) {
            LOG_PRINTF("lgladd(s,%d); // context var %u\n", context_lit, context_index);
        }
#endif
    }
    
    lgladd(solver->lgl, 0);
#ifdef SATSOLVER_TRACE
    if (solver->trace_solver_commands) {
        LOG_PRINTF("lgladd(s,0);\n");
    }
#endif
}

void satsolver_assume(SATSolver* solver, int lit) {
    abortif(lit == 0, "Tried to assume literal 0.");
    
    if (solver->assumptions_used_in_sat_call) {
        solver->assumptions_used_in_sat_call = false;
        int_vector_reset(solver->assumptions);
    }
    int_vector_add(solver->assumptions, lit);
}

void satsolver_clear_assumptions(SATSolver* solver) {
    solver->assumptions_used_in_sat_call = false;
    int_vector_reset(solver->assumptions);
}

bool satsolver_inconsistent(SATSolver* solver) {
    bool res = lglinconsistent(solver->lgl);
    
#ifdef SATSOLVER_TRACE
    if (solver->trace_solver_commands) {
        LOG_PRINTF("lglinconsistent(s);\n");
    }
#endif
    return res;
}

sat_res satsolver_sat(SATSolver* solver) {
    if (solver->assumptions_used_in_sat_call) {
        solver->assumptions_used_in_sat_call = false;
        int_vector_reset(solver->assumptions);
    }
    for (unsigned i = 0; i < int_vector_count(solver->assumptions); i++) {
        int assumption_lit = int_vector_get(solver->assumptions, i);
        int pico_lit = lit_from_int(solver, assumption_lit);
        lglassume(solver->lgl, pico_lit);
#ifdef SATSOLVER_TRACE
        if (solver->trace_solver_commands) {
            LOG_PRINTF("picosat_assume(s,%d);\n",pico_lit);
        }
#endif
    }
    
    for (unsigned i = 0; i < int_vector_count(solver->context_literals); i++) {
        int context_lit = int_vector_get(solver->context_literals, i);
        lglassume(solver->lgl, - context_lit);
#ifdef SATSOLVER_TRACE
        if (solver->trace_solver_commands) {
            LOG_PRINTF("lglassume(s,%d);\n", - context_lit);
        }
#endif
    }
    
    V4("  ... calling picosat\n");
    solver->res = (sat_res) lglsat(solver->lgl);
    solver->assumptions_used_in_sat_call = true;
    
#ifdef SATSOLVER_TRACE
    if (solver->trace_solver_commands) {
        LOG_PRINTF("assert(lglsat(s) == %d);\n", solver->res);
    }
#endif
    return solver->res;
}

int satsolver_deref(SATSolver* solver, int lit) {
    int pico_lit = lit_from_int(solver, lit);
    assert( ! int_vector_contains(solver->context_literals, abs(pico_lit)));
    int res = lglderef(solver->lgl, pico_lit);
    
#ifdef SATSOLVER_TRACE
    if (solver->trace_solver_commands) {
        LOG_PRINTF("assert(lglderef(s,%d) == %d);\n",pico_lit, res);
    }
#endif
    return res;
}

// Same as satsolver_deref, but with void * instead of SATSolver *
int satsolver_deref_generic(void* solver, int lit) {
    return satsolver_deref((SATSolver*) solver, lit);
}

int satsolver_deref_partial(SATSolver* solver, int lit) {
    abort(); // not implemented
}

int satsolver_deref_toplevel(SATSolver* solver, int lit) {
    int pico_lit = lit_from_int(solver, lit);
    int res = lglfixed(solver->lgl, pico_lit);
    
#ifdef SATSOLVER_TRACE
    if (solver->trace_solver_commands) {
        LOG_PRINTF("assert(lglfixed(s,%d) == %d);\n",pico_lit, res);
    }
#endif
    return res;
}

bool satsolver_failed_assumption(SATSolver* solver, int lit) {
    assert(int_vector_contains(solver->assumptions, lit));
    int pico_lit = lit_from_int(solver, lit);
#ifdef SATSOLVER_TRACE
    if (solver->trace_solver_commands) {
        LOG_PRINTF("picosat_failed_assumption(s,%d);\n", pico_lit);
    }
#endif
    return lglfailed(solver->lgl, pico_lit);
}

void satsolver_failed_assumptions(SATSolver* solver, int_vector* failed_assumptions) {
    abortif(int_vector_count(failed_assumptions) != 0, "failed assumption vector needs to be empty");
    abortif( ! solver->assumptions_used_in_sat_call, "Assumptions have not been used at all.");
    
    for (unsigned i = 0; i < int_vector_count(solver->assumptions); i++) {
        int assumption = int_vector_get(solver->assumptions, i);
        int pico_lit = lit_from_int(solver, assumption);
        if (lglfailed(solver->lgl, pico_lit)) {
            int_vector_add(failed_assumptions, assumption);
        }
#ifdef SATSOLVER_TRACE
        if (solver->trace_solver_commands) {
            LOG_PRINTF("picosat_failed_assumption(s,%d);\n", pico_lit);
        }
#endif
    }
}

double satsolver_seconds(SATSolver* solver) {
    double res = lglsec(solver->lgl);
    
#ifdef SATSOLVER_TRACE
    if (solver->trace_solver_commands) {
        LOG_PRINTF("lglsec(s);\n");
    }
#endif
    return res;
}

void satsolver_set_global_default_phase(SATSolver* solver, int phase) {
    abort(); // not implemented
}

void satsolver_set_default_phase_lit(SATSolver* solver, int lit, int phase) {
    assert(phase >= -1 && phase <= 1);
    int pico_lit = lit_from_int(solver, lit);
    lglsetphase(solver->lgl, pico_lit * phase);
    
#ifdef SATSOLVER_TRACE
    if (solver->trace_solver_commands) {
        LOG_PRINTF("lglsetphase(s, %d);\n", pico_lit * phase);
    }
#endif
}

void satsolver_print_translation_table(SATSolver* solver) {
    V3("Translation table (outer -> inner):\n");
    for (int i = 1; i <= solver->max_var; i++) {
        if (map_contains(solver->var_mapping, i)) {
            int a = (int)map_get(solver->var_mapping, i);
            V3("%d -> %d\n", i, a);
        }
    }
}

void satsolver_print(SATSolver* solver) {
    lglprint(solver->lgl, stdout);
}

void satsolver_push(SATSolver* solver) {
    int_vector_add(solver->max_var_stack, solver->max_var);
    int new_context_lit = lglincvar(solver->lgl);
    lglfreeze(solver->lgl, new_context_lit);
    int_vector_add(solver->context_literals,new_context_lit);
#ifdef SATSOLVER_TRACE
    if (solver->trace_solver_commands) {
        LOG_PRINTF("assert(picosat_inc_max_var(s) == %d); lglfreeze(s, %d);// push context %d\n", new_context_lit, new_context_lit, int_vector_count(solver->context_literals));
    }
#endif
}

void satsolver_pop(SATSolver* solver) {
    if (solver->assumptions_used_in_sat_call) {
        solver->assumptions_used_in_sat_call = false;
        int_vector_reset(solver->assumptions);
    }
    
    abortif(int_vector_count(solver->max_var_stack) == 0, "Trying to pop from a satsolver without contexts.");
    solver->max_var = int_vector_pop(solver->max_var_stack);
    
    int context_var = int_vector_pop(solver->context_literals);
    lgladd(solver->lgl, context_var);
    lgladd(solver->lgl, 0);
    
#ifdef SATSOLVER_TRACE
    if (solver->trace_solver_commands) {
        LOG_PRINTF("lgladd(s,%d); // context %u\n", context_var, int_vector_count(solver->context_literals) + 1);
        LOG_PRINTF("lgladd(s,0);\n");
    }
#endif
}

void satsolver_set_more_important_lit (SATSolver* solver, int lit) {
    assert(lit>0);
    int pico_lit = lit_from_int(solver, lit);
    lglsetimportant(solver->lgl, pico_lit);
    
#ifdef SATSOLVER_TRACE
    if (solver->trace_solver_commands) {
        LOG_PRINTF("lglsetimportant(s,%d);\n",pico_lit);
    }
#endif
}

#ifdef SATSOLVER_TRACE
void satsolver_trace_commands(SATSolver* solver) {
    solver->trace_solver_commands = true;
    LOG_PRINTF("#include <stdio.h>\n"
"#include <assert.h>\n"
"#include \"lglib.h\"\n"
"int main() {\n"
"    LGL* s = lglinit();\n");
}
#endif

void satsolver_print_statistics(SATSolver* solver) {
    V0("Skolem SAT solver:\n");
    V0("  SATSolver maxvar: %u\n", satsolver_get_max_var(solver));
    V0("  PicoSAT maxvar: %u\n", lglmaxvar(solver->lgl));
#ifdef SATSOLVER_TRACE
    if (solver->trace_solver_commands) {
        abortif(true,"Not logging satsolver_print_statistics, implement me.");
    }
#endif
}

void satsolver_measure_all_calls(SATSolver* solver) {
    abort(); // not implemented
}

#endif
