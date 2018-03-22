//
//  qipasir.h
//
// QIPASIR v1.0
//
// A generic API for incremental QBF, derived from the API ipasir for SAT.
//

#ifndef qipasir_h
#define qipasir_h

/**
 * Return the name and the version of the incremental QBF
 * solving library.
 */
const char * qipasir_signature ();

/**
 * Construct a new solver and return a pointer to it.
 * Use the returned pointer as the first parameter in each
 * of the following functions.
 *
 * Required state: N/A
 * State after: INPUT
 */
void * qipasir_init ();

/**
 * Release the solver, i.e., all its resoruces and
 * allocated memory (destructor). The solver pointer
 * cannot be used for any purposes after this call.
 *
 * Required state: INPUT or SAT or UNSAT
 * State after: undefined
 */
void qipasir_release (void * solver);

/**
 * Introduce a new variable with the name 'lit', which must be
 * strictly greater than 0. 'quantifier' indicates on which quantifier
 * level the variable is introduced.
 *
 * Even quantifier levels are existential, odd quantifier levels are
 * universal. Variables on quantifier level n can depend on all variables
 * with smaller quantifier level.
 *
 * 'quantifier' must be greater or equal 0. Level 0 thus contains the
 * outermost existential variables.
 *
 * Required state: INPUT or SAT or UNSAT
 * State after: INPUT
 *
 */
void qipasir_new_variable(void * solver, int lit, int quantifier);

/**
 * Add the given literal into the currently added clause
 * or finalize the clause with a 0.  Clauses added this way
 * cannot be removed. The addition of removable clauses
 * can be simulated using activation literals and assumptions.
 *
 * If the variable corresponding to the literal is not defined
 * it is considered to be a top-level existential variable. The 
 * function then shows the same behavior as if we first called 
 * qipasir_new_variable(solver, abs(lit_or_zero), 0).
 * This ensures backward compatibility to ipasir.
 *
 * Warning: This may introduce a new quantifier level!
 *
 * Literals are encoded as (non-zero) integers as in the
 * QDIMACS format.  They have to be smaller or equal to
 * INT_MAX and strictly larger than INT_MIN (to avoid
 * negation overflow).  This applies to all the literal
 * arguments in API functions.
 *
 * Required state: INPUT or SAT or UNSAT
 * State after: INPUT
 *
 */
void qipasir_add (void * solver, int lit_or_zero);

/**
 * Add an assumption for the next call to qipasir_solve. After calling
 * qipasir_solve all the previously added assumptions are cleared.
 *
 * Required state: INPUT or SAT or UNSAT
 * State after: INPUT
 */
void qipasir_assume (void * solver, int lit);

/**
 * Solve the formula under the specified assumptions (if any).
 * If the formula is satisfiable the function returns 10 and the state of the solver is changed to SAT.
 * If the formula is unsatisfiable the function returns 20 and the state of the solver is changed to UNSAT.
 * If the search is interrupted (see ipasir_set_terminate) the function returns 0 and the state of the solver remains INPUT.
 *
 * Required state: INPUT or SAT or UNSAT
 * State after: INPUT or SAT or UNSAT
 */
int qipasir_solve (void * solver);

/**
 * Get the truth value of the given top-level literal. Return 'lit' if True, '-lit' if False, 
 * and 0 if not relevant in the current assignment.
 *
 * Top-level variables are the variables on quantifier level 0 or, if quantifier level 0 is empty, 
 * the variables on level 1.
 *
 * Required state: SAT if top-level quantifier is existential, UNSAT if it is universal
 * State after: SAT if top-level quantifier is existential, UNSAT if it is universal
 */
int qipasir_val (void * solver, int lit);

/**
 * Check if the given assumption literal was used to prove the
 * unsatisfiability of the formula under the assumptions
 * used for the last call to qipasir_solve. Return 1 if so, 0 otherwise.
 *
 * Required state: UNSAT
 * State after: UNSAT
 */
int qipasir_failed (void * solver, int lit);

/**
 * Set a callback function used to indicate a termination requirement to the
 * solver. The solver will periodically call this function and check its return
 * value during the search. The qipasir_set_terminate function can be called in any
 * state of the solver, the state remains unchanged after the call.
 * The callback function is of the form "int terminate(void * state)"
 *   - it returns a non-zero value if the solver should terminate.
 *   - the solver calls the callback function with the parameter "state"
 *     having the value passed in the ipasir_set_terminate function (2nd parameter).
 *
 * Required state: INPUT or SAT or UNSAT
 * State after: INPUT or SAT or UNSAT
 */
void qipasir_set_terminate (void * solver, void * state, int (*terminate)(void * state));

#endif /* qipasir_h */
