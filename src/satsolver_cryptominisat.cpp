//
//  satsolver_cryptominisat.cpp
//  cadet
//
//  Created by Markus Rabe on 20/05/16.
//  Copyright © 2016 Saarland University. All rights reserved.
//

extern "C" {
#include "satsolver.h"
}

#if (USE_SOLVER == SOLVER_CRYPTOMINISAT)

#include <assert.h>
#include <stdbool.h>
#include "log.h"
#include "cryptominisat/cryptominisat.h"
#include "cryptominisat/Vec.h"
#include <map>

using namespace CMSat;
using namespace std;

struct SATSolver {
    Solver* instance;
    vec<Lit> clause;
    vec<Lit> assumptions;
    //    int_vector* failed_assumptions;
    map<int,Var> var_mapping;
    map<Var,int> var_reverse_mapping;
    int max_var;
};

Var var_from_int(SATSolver* solver, int var) {
    assert(var > 0);
    
    // lookup variable
    Var nvar;
    map<int,Var>::iterator elem = solver->var_mapping.find(var);
    if (elem == solver->var_mapping.end()) {
        // setting u_pol to l_False seems to favor negative assignments
        nvar = solver->instance->newVar(l_False);
        solver->var_mapping[var] = nvar;
        solver->var_reverse_mapping[nvar] = var;
    } else {
        nvar = elem->second;
    }
    
    if (solver->max_var < var) {
        solver->max_var = var;
    }
    
    return nvar;
}

Lit lit_from_int(SATSolver* solver, int lit) {
    bool neg = lit < 0;
    int var = neg ? -lit : lit;
    
    return mkLit(var_from_int(solver, var), neg);
}

int lit_to_int(SATSolver* solver, Lit lit) {
    bool neg = sign(lit);
    int v = var(lit);
    return neg ? -solver->var_reverse_mapping[v] : solver->var_reverse_mapping[v];
}

SATSolver* satsolver_init() {
    SATSolver* solver = new SATSolver;
    solver->instance = new Solver();
    solver->max_var = 0;
    
    return solver;
}

void satsolver_free(SATSolver* solver) {
    delete solver->instance;
    delete solver;
}

void satsolver_adjust(SATSolver* solver, int variables) {
    NOT_IMPLEMENTED();
}

void satsolver_save_original_clauses(SATSolver* solver) {
    NOT_IMPLEMENTED();
}

int satsolver_inc_max_var(SATSolver* solver) {
    solver->max_var += 1;
    return solver->max_var;
}

void satsolver_add(SATSolver* solver, int lit) {
    if (lit == 0) {
        if (solver->assumptions.size() > 0) {
            solver->clause.push( ~ solver->assumptions.last() ); // to enable "popping it later"
        }
        solver->instance->addClause(solver->clause);
        solver->clause.clear();
    } else {
        Lit l = lit_from_int(solver, lit);
        solver->clause.push(l);
    }
}

// Currently doesn't work together with push-pop semantics
void satsolver_assume(SATSolver* solver, int lit) {
    NOT_IMPLEMENTED();
    //    if (solver->last_sat_call) {
    //        solver->assumptions.clear();
    //        solver->last_sat_call = false;
    //    }
    //    solver->assumptions.push(lit_from_int(solver, lit));
}

sat_res satsolver_sat(SATSolver* solver) {
    sat_res res = solver->instance->solve(solver->assumptions) ? SATSOLVER_RESULT_SAT : SATSOLVER_RESULT_UNSAT;
    return res;
}

int satsolver_deref(SATSolver* solver, int lit) {
    int var = lit < 0 ? -lit : lit;
    map<int,Var>::iterator elem = solver->var_mapping.find(var);
    if (elem == solver->var_mapping.end()) {
        abort(); // returning a 0 is too scary
        return 0;
    }
    
    lbool res = solver->instance->modelValue(lit_from_int(solver, lit));
    if (res == l_True) {
        return 1;
    } else if (res == l_False) {
        return -1;
    } else if (res == l_Undef) {
        abort(); // returning a 0 is too scary
        return 0;
    }
    assert(false);
    return 0;
}

int satsolver_deref_partial(SATSolver* solver, int lit) {
    NOT_IMPLEMENTED();
    //    return satsolver_deref(solver, lit);
}

void satsolver_set_global_default_phase(SATSolver* solver, int phase) {
    NOT_IMPLEMENTED();
}

void satsolver_set_default_phase_lit (SATSolver* solver, int lit, int phase) {
    NOT_IMPLEMENTED();
    /*lbool lphase = l_False;
     if (phase > 0) {
     lphase = l_True;
     }
     solver->instance->setPolarity(var_from_int(solver, lit), lphase);
     return; // TODO*/
}

void satsolver_print(SATSolver*) {
    NOT_IMPLEMENTED();
}

void satsolver_push(SATSolver* solver) {
    assert(solver->clause.size() == 0); // doesn't hurt if violated, but what exactly should the semantics be? Currently the clause is then assumed to be in the new frame.
    Var var = solver->instance->newVar(l_False);
    Lit l = mkLit(var, false);
    solver->assumptions.push(l);
}

void satsolver_pop(SATSolver* solver) {
    solver->assumptions.pop();
}

void satsolver_set_max_var(SATSolver* solver, int new_max) {
    assert(new_max > solver->max_var);
    solver->max_var = new_max;
}

int satsolver_get_max_var(SATSolver* solver) {
    return solver->max_var;
}

//void satsolver_failed_negative_assumptions(SATSolver* solver, int* failed_assumptions, size_t failed_assumptions_size) {
//    LSet& conflict = solver->instance->conflict;
//    assert(conflict.size() < failed_assumptions_size);
//
//    int i = 0;
//    for (int j = 0; j < solver->assumptions.size(); j++) {
//        Lit elem = solver->assumptions[j];
//        Lit pure = ~elem;
//        if (conflict.has(pure)) {
//            int l = lit_to_int(solver, elem);
//            if (l<0) {
//                failed_assumptions[i++] = j;
//            }
//        }
//    }
//
//    assert(i == conflict.size());
//    failed_assumptions[i] = 0;
//}


//void satsolver_failed_assumptions(SATSolver* solver, int* failed_assumptions, size_t failed_assumptions_size) {
////const int* satsolver_failed_assumptions(SATSolver* solver) {
//    LSet& conflict = solver->instance->conflict;
//    assert(conflict.size() < failed_assumptions_size);
////    solver->failed_assumptions = (int *)malloc(sizeof(int) * (conflict.size() + 1));
//
//    int i = 0;
//    for (int j = 0; j < solver->assumptions.size(); j++) {
//        Lit elem = solver->assumptions[j];
//        Lit pure = ~elem;
//        if (conflict.has(pure)) {
//            failed_assumptions[i++] = lit_to_int(solver, elem);
//        }
//    }
//
//    /*for (i = 0; i < conflict.size(); i++) {
//        Lit failed = conflict[i];
//        //solver->failed_assumptions[i] = lit_to_int(solver, failed);
//    }*/
//
//    assert(i == conflict.size());
//    failed_assumptions[i] = 0;
//}

#endif
