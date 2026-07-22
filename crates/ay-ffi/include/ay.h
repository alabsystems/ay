// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

/**
 * AY SMT Solver - C FFI Header
 *
 * This header provides C-compatible bindings for the AY SMT solver.
 * Link against libay_ffi.a (static) or libay_ffi.so/dylib (dynamic).
 *
 * Thread Safety:
 * - AYSolver handles are NOT thread-safe
 * - Use separate solver instances for concurrent access
 *
 * Memory Management:
 * - ay_solver_new() returns handles that must be freed with ay_solver_free()
 * - String returns (ay_get_model, ay_get_error, ay_get_statistics, ay_version)
 *   must be freed with ay_string_free()
 *
 * Author: Andrew Yates <andrewyates.name@gmail.com>
 */

#ifndef AY_H
#define AY_H

#include <stdint.h>

#ifdef __cplusplus
extern "C" {
#endif

/* Result codes */
#define AY_SAT      1    /* Satisfiable - a model exists */
#define AY_UNSAT    0    /* Unsatisfiable - no model exists */
#define AY_UNKNOWN  (-1) /* Unknown - solver could not determine */
#define AY_ERROR    (-2) /* Error - invalid input or internal error */

/* Opaque solver handle */
typedef struct AYSolver AYSolver;

/* ============================================================================
 * Core Functions
 * ============================================================================ */

/**
 * Create a new solver instance.
 *
 * @return Non-null pointer on success, null on failure (out of memory)
 */
AYSolver* ay_solver_new(void);

/**
 * Destroy a solver instance and free associated memory.
 *
 * @param solver Solver handle (safe to call with null)
 */
void ay_solver_free(AYSolver* solver);

/**
 * Solve SMT-LIB input.
 *
 * Parses and executes the given SMT-LIB commands, returning the result
 * of the last (check-sat) command.
 *
 * @param solver Solver handle
 * @param smtlib Null-terminated SMT-LIB string
 * @return AY_SAT, AY_UNSAT, AY_UNKNOWN, or AY_ERROR
 */
int ay_solve_smtlib(AYSolver* solver, const char* smtlib);

/**
 * Get the model from the last SAT result.
 *
 * @param solver Solver handle
 * @return Model string (caller must free with ay_string_free), or null
 */
char* ay_get_model(AYSolver* solver);

/**
 * Get the last error message.
 *
 * @param solver Solver handle
 * @return Error string (caller must free with ay_string_free), or null
 */
char* ay_get_error(AYSolver* solver);

/**
 * Set the per-check timeout for this solver.
 *
 * A value of 0 disables the timeout. Non-zero values are milliseconds.
 *
 * @param solver Solver handle (safe to call with null)
 * @param timeout_ms Timeout in milliseconds, or 0 for no timeout
 */
void ay_set_timeout(AYSolver* solver, uint64_t timeout_ms);

/**
 * Get the per-check timeout for this solver.
 *
 * @param solver Solver handle
 * @return Timeout in milliseconds, or 0 when disabled/null
 */
uint64_t ay_get_timeout(AYSolver* solver);

/**
 * Get statistics from the last check-sat call.
 *
 * @param solver Solver handle
 * @return Statistics string (caller must free with ay_string_free), or null
 */
char* ay_get_statistics(AYSolver* solver);

/**
 * Free a string returned by ay functions.
 *
 * @param s String to free (safe to call with null)
 */
void ay_string_free(char* s);

/**
 * Reset the solver state.
 *
 * Clears all assertions and declarations.
 *
 * @param solver Solver handle
 */
void ay_reset(AYSolver* solver);

/* ============================================================================
 * Incremental Solving Functions
 * ============================================================================ */

/**
 * Push an assertion scope.
 *
 * Saves the current assertion state. Assertions added after push
 * can be removed by calling ay_pop. Enables incremental solving mode.
 *
 * @param solver Solver handle
 */
void ay_push(AYSolver* solver);

/**
 * Pop assertion scopes.
 *
 * Removes `levels` assertion scopes, restoring the solver state
 * to before the corresponding ay_push calls.
 *
 * @param solver Solver handle
 * @param levels Number of scopes to pop (must be > 0)
 * @return 0 on success, AY_ERROR on failure (underflow, invalid levels)
 */
int ay_pop(AYSolver* solver, int levels);

/**
 * Assert a formula.
 *
 * Parses the SMT-LIB term and adds it as an assertion. The formula
 * should be a term, not a command -- e.g., "(> x 0)" not "(assert (> x 0))".
 *
 * @param solver Solver handle
 * @param formula Null-terminated SMT-LIB term string
 * @return 0 on success, AY_ERROR on parse error or invalid input
 */
int ay_assert(AYSolver* solver, const char* formula);

/**
 * Check satisfiability of current assertions.
 *
 * @param solver Solver handle
 * @return AY_SAT, AY_UNSAT, AY_UNKNOWN, or AY_ERROR
 */
int ay_check_sat(AYSolver* solver);

/**
 * Check satisfiability under additional assumptions.
 *
 * The assumptions are temporary and do not persist after this call.
 * Each assumption is an SMT-LIB literal (e.g., "p" or "(not p)").
 *
 * @param solver Solver handle
 * @param assumptions Array of null-terminated assumption strings
 * @param count Number of assumptions (0 for none)
 * @return AY_SAT, AY_UNSAT, AY_UNKNOWN, or AY_ERROR
 */
int ay_check_sat_assuming(AYSolver* solver, const char** assumptions, int count);

/**
 * Get the unsat core from the last UNSAT check-sat-assuming result.
 *
 * Returns the unsat assumptions as an SMT-LIB formatted string.
 * Only valid after a check-sat-assuming that returned UNSAT.
 *
 * @param solver Solver handle
 * @return Unsat core string (caller must free with ay_string_free), or null
 */
char* ay_get_unsat_core(AYSolver* solver);

/* ============================================================================
 * Quick Solve Functions (One-shot, no handle management)
 * ============================================================================ */

/**
 * Quick SMT solve (one-shot).
 *
 * Creates a temporary solver, runs the input, returns result.
 *
 * @param smtlib Null-terminated SMT-LIB string
 * @return AY_SAT, AY_UNSAT, AY_UNKNOWN, or AY_ERROR
 */
int ay_quick_solve(const char* smtlib);

/**
 * Quick LIA solve.
 *
 * Convenience for QF_LIA problems (automatically adds logic declaration).
 *
 * @param formula SMT-LIB formula without logic declaration
 * @return AY_SAT, AY_UNSAT, AY_UNKNOWN, or AY_ERROR
 */
int ay_solve_lia(const char* formula);

/**
 * Quick SAT solve.
 *
 * Convenience for propositional problems.
 *
 * @param formula SMT-LIB formula with Bool declarations
 * @return AY_SAT, AY_UNSAT, AY_UNKNOWN, or AY_ERROR
 */
int ay_solve_sat(const char* formula);

/**
 * Quick BV solve.
 *
 * Convenience for QF_BV problems.
 *
 * @param formula SMT-LIB formula with BitVec declarations
 * @return AY_SAT, AY_UNSAT, AY_UNKNOWN, or AY_ERROR
 */
int ay_solve_bv(const char* formula);

/* ============================================================================
 * Version Info
 * ============================================================================ */

/**
 * Get AY version string.
 *
 * @return Heap-allocated version string (caller must free with ay_string_free)
 */
char* ay_version(void);

#ifdef __cplusplus
}
#endif

#endif /* AY_H */
