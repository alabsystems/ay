// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// ay-dpll panicking convenience methods are deprecated in favor of try_* variants.
// This FFI layer uses catch_unwind guards; migration to try_* tracked in ay#6183.
#![allow(deprecated)]
#![deny(clippy::unwrap_used)]

//! ay-ffi: C FFI bindings for AY SMT solver
//!
//! This crate provides C-compatible FFI bindings for AY, enabling integration
//! with Lean 4, other language runtimes, and external tools.
//!
//! # Thread Safety
//!
//! AYSolver handles are NOT thread-safe. Each solver instance should be used
//! from a single thread. For concurrent use, create separate solver instances.
//!
//! # Memory Management
//!
//! - Solver handles must be freed with `ay_solver_free`
//! - String results must be freed with `ay_string_free`
//! - Failure to free memory will cause leaks
//!
//! # Example (C)
//!
//! ```c
//! AYSolver* solver = ay_solver_new();
//! const char* smtlib = "(set-logic QF_LIA)(declare-const x Int)(assert (> x 0))(check-sat)";
//! int result = ay_solve_smtlib(solver, smtlib);
//! if (result == AY_SAT) {
//!     char* model = ay_get_model(solver);
//!     printf("Model: %s\n", model);
//!     ay_string_free(model);
//! }
//! ay_solver_free(solver);
//! ```
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com>

#[allow(non_camel_case_types, non_snake_case)]
pub mod z3_compat;

use ay_core::time::Instant;
use std::ffi::{c_char, c_int, CStr, CString};
use std::panic::{catch_unwind, AssertUnwindSafe};
use std::time::Duration;

use ay_dpll::Executor;
use ay_frontend::{parse, Command};

const BUILD_STAMP: &str = env!("AY_BUILD_STAMP");

// ============================================================================
// Result Codes
// ============================================================================

/// Satisfiable - a model exists
pub const AY_SAT: c_int = 1;
/// Unsatisfiable - no model exists
pub const AY_UNSAT: c_int = 0;
/// Unknown - solver could not determine satisfiability
pub const AY_UNKNOWN: c_int = -1;
/// Error - invalid input or internal error
pub const AY_ERROR: c_int = -2;

// ============================================================================
// Solver Handle
// ============================================================================

/// Opaque solver handle for FFI
///
/// This wraps the internal AY executor and maintains state between calls.
pub struct AYSolver {
    executor: Executor,
    last_error: Option<String>,
    timeout: Option<Duration>,
}

impl AYSolver {
    fn new() -> Self {
        Self {
            executor: Executor::new(),
            last_error: None,
            timeout: None,
        }
    }

    fn set_error(&mut self, msg: String) {
        self.last_error = Some(msg);
    }

    fn clear_error(&mut self) {
        self.last_error = None;
    }

    fn deadline_from_timeout(&self) -> Option<Instant> {
        // On wasm there are no background threads to enforce a wall-clock
        // deadline (see `check_sat.rs` / `bv/mod.rs`), so we never install one.
        // The solve still terminates via the inline deadline polls when a
        // deadline is present, but the default FFI path installs none.
        #[cfg(target_arch = "wasm32")]
        {
            None
        }
        #[cfg(not(target_arch = "wasm32"))]
        {
            self.timeout
                .and_then(|timeout| Instant::now().checked_add(timeout))
        }
    }

    fn execute_with_timeout(&mut self, cmd: &Command) -> ay_dpll::ExecutorResult<Option<String>> {
        match cmd {
            Command::CheckSat | Command::CheckSatAssuming(_) => {
                self.executor.set_deadline(self.deadline_from_timeout());
                let result = self.executor.execute(cmd);
                self.executor.set_deadline(None);
                result
            }
            _ => self.executor.execute(cmd),
        }
    }
}

// ============================================================================
// Core FFI Functions
// ============================================================================

/// Create a new solver instance
///
/// # Returns
/// - Non-null pointer to solver handle on success
/// - Null pointer on failure (out of memory)
///
/// # Safety
/// The returned pointer must be freed with `ay_solver_free`.
#[no_mangle]
pub extern "C" fn ay_solver_new() -> *mut AYSolver {
    match catch_unwind(AYSolver::new) {
        Ok(solver) => Box::into_raw(Box::new(solver)),
        Err(_) => std::ptr::null_mut(),
    }
}

/// Destroy a solver instance and free associated memory
///
/// # Safety
/// - `solver` must be a valid pointer returned by `ay_solver_new`
/// - `solver` must not be used after this call
/// - Safe to call with null pointer (no-op)
#[no_mangle]
pub unsafe extern "C" fn ay_solver_free(solver: *mut AYSolver) {
    if solver.is_null() {
        return;
    }
    // Drop could panic (e.g., Executor cleanup); catch to prevent UB across FFI.
    // SAFETY: `solver` was null-checked above and, per this function's `# Safety`
    // contract, was produced by `ay_solver_new` via `Box::into_raw`. This
    // `Box::from_raw` consumes the pointer exactly once, so double-free is
    // impossible. The caller must not use the pointer after this call.
    let _ = catch_unwind(AssertUnwindSafe(|| unsafe {
        let _ = Box::from_raw(solver);
    }));
}

/// Solve SMT-LIB input and return result
///
/// Parses and executes the given SMT-LIB commands, returning the result
/// of the last `(check-sat)` command.
///
/// # Arguments
/// - `solver` - Solver handle from `ay_solver_new`
/// - `smtlib` - Null-terminated UTF-8 string containing SMT-LIB commands
///
/// # Returns
/// - `AY_SAT` (1) if satisfiable
/// - `AY_UNSAT` (0) if unsatisfiable
/// - `AY_UNKNOWN` (-1) if solver could not determine
/// - `AY_ERROR` (-2) if parse error or invalid input
///
/// # Safety
/// - `solver` must be a valid pointer from `ay_solver_new`
/// - `smtlib` must be a valid null-terminated UTF-8 string
#[no_mangle]
pub unsafe extern "C" fn ay_solve_smtlib(solver: *mut AYSolver, smtlib: *const c_char) -> c_int {
    // Validate pointers before entering catch_unwind
    if solver.is_null() || smtlib.is_null() {
        return AY_ERROR;
    }

    // SAFETY: The caller's `# Safety` contract requires the C string pointer to be non-null
    // and to point to a valid, null-terminated sequence of bytes owned by the caller for the
    // duration of this call. The pointer was null-checked before entering this block.
    let result = catch_unwind(AssertUnwindSafe(|| unsafe {
        let solver = &mut *solver;
        solver.clear_error();

        // Parse input string
        let smtlib_str = match CStr::from_ptr(smtlib).to_str() {
            Ok(s) => s,
            Err(_) => {
                solver.set_error("Input is not valid UTF-8".to_string());
                return AY_ERROR;
            }
        };

        // Parse SMT-LIB commands
        let commands = match parse(smtlib_str) {
            Ok(cmds) => cmds,
            Err(e) => {
                solver.set_error(format!("Parse error: {e}"));
                return AY_ERROR;
            }
        };

        // Execute commands and track last check-sat result
        let mut last_result = AY_UNKNOWN;

        for cmd in &commands {
            match solver.execute_with_timeout(cmd) {
                Ok(Some(output)) => {
                    // Check if this is a check-sat result
                    match output.as_str() {
                        "sat" => last_result = AY_SAT,
                        "unsat" => last_result = AY_UNSAT,
                        "unknown" => last_result = AY_UNKNOWN,
                        _ => {} // Other outputs (e.g., get-model) don't change result
                    }
                }
                Ok(None) => {}
                Err(e) => {
                    solver.set_error(format!("Execution error: {e}"));
                    return AY_ERROR;
                }
            }
        }

        last_result
    }));

    match result {
        Ok(val) => val,
        // SAFETY: All raw pointers used inside this block were validated (null-checked and/or
        // bounds-checked) above, and the caller's `# Safety` contract on this extern "C"
        // function guarantees they remain valid for the duration of the call.
        Err(panic) => unsafe {
            let solver = &mut *solver;
            solver.set_error(format!(
                "panic in ay_solve_smtlib: {}",
                z3_compat::panic_payload_to_string(&*panic)
            ));
            AY_ERROR
        },
    }
}

/// Get the model from the last SAT result
///
/// Returns the model as an SMT-LIB formatted string. Only valid after
/// a `check-sat` that returned SAT.
///
/// # Returns
/// - Pointer to null-terminated string on success (caller must free with `ay_string_free`)
/// - Null pointer if no model available or error
///
/// # Safety
/// - `solver` must be a valid pointer from `ay_solver_new`
/// - Returned string must be freed with `ay_string_free`
#[no_mangle]
pub unsafe extern "C" fn ay_get_model(solver: *mut AYSolver) -> *mut c_char {
    if solver.is_null() {
        return std::ptr::null_mut();
    }

    // SAFETY: All raw pointers used inside this block were validated (null-checked and/or
    // bounds-checked) above, and the caller's `# Safety` contract on this extern "C" function
    // guarantees they remain valid for the duration of the call.
    match catch_unwind(AssertUnwindSafe(|| unsafe {
        let solver = &mut *solver;

        // Execute get-model command
        let cmd = Command::GetModel;
        match solver.executor.execute(&cmd) {
            Ok(Some(model)) => match CString::new(model) {
                Ok(s) => s.into_raw(),
                Err(_) => std::ptr::null_mut(),
            },
            _ => std::ptr::null_mut(),
        }
    })) {
        Ok(val) => val,
        Err(_) => std::ptr::null_mut(),
    }
}

/// Get the last error message
///
/// # Returns
/// - Pointer to null-terminated error message (caller must free with `ay_string_free`)
/// - Null pointer if no error
///
/// # Safety
/// - `solver` must be a valid pointer from `ay_solver_new`
#[no_mangle]
pub unsafe extern "C" fn ay_get_error(solver: *mut AYSolver) -> *mut c_char {
    if solver.is_null() {
        return std::ptr::null_mut();
    }

    // SAFETY: All raw pointers used inside this block were validated (null-checked and/or
    // bounds-checked) above, and the caller's `# Safety` contract on this extern "C" function
    // guarantees they remain valid for the duration of the call.
    match catch_unwind(AssertUnwindSafe(|| unsafe {
        let solver = &*solver;

        match &solver.last_error {
            Some(msg) => match CString::new(msg.as_str()) {
                Ok(s) => s.into_raw(),
                Err(_) => std::ptr::null_mut(),
            },
            None => std::ptr::null_mut(),
        }
    })) {
        Ok(val) => val,
        Err(_) => std::ptr::null_mut(),
    }
}

/// Set the per-check timeout for this solver.
///
/// A value of 0 disables the timeout. Non-zero values are interpreted as
/// milliseconds and apply to subsequent `check-sat` operations.
///
/// # Safety
/// - `solver` must be a valid pointer from `ay_solver_new`
/// - Safe to call with null pointer (no-op)
#[no_mangle]
pub unsafe extern "C" fn ay_set_timeout(solver: *mut AYSolver, timeout_ms: u64) {
    if solver.is_null() {
        return;
    }

    // SAFETY: `solver` was null-checked above and the caller's `# Safety`
    // contract requires it to point to a valid `AYSolver`.
    let _ = catch_unwind(AssertUnwindSafe(|| unsafe {
        let solver = &mut *solver;
        solver.timeout = if timeout_ms == 0 {
            None
        } else {
            Some(Duration::from_millis(timeout_ms))
        };
        solver.clear_error();
    }));
}

/// Get the per-check timeout for this solver, in milliseconds.
///
/// Returns 0 when no timeout is configured or when `solver` is null.
///
/// # Safety
/// - `solver` must be a valid pointer from `ay_solver_new`
#[no_mangle]
pub unsafe extern "C" fn ay_get_timeout(solver: *mut AYSolver) -> u64 {
    if solver.is_null() {
        return 0;
    }

    // SAFETY: `solver` was null-checked above and the caller's `# Safety`
    // contract requires it to point to a valid `AYSolver`.
    let timeout_ms: u64 = catch_unwind(AssertUnwindSafe(|| unsafe {
        let solver = &*solver;
        solver.timeout.map_or(0, |timeout| {
            u64::try_from(timeout.as_millis()).unwrap_or(u64::MAX)
        })
    }))
    .unwrap_or_default();
    timeout_ms
}

/// Get statistics from the last `check-sat` call.
///
/// Returns an SMT-LIB formatted statistics string. The caller must free the
/// returned string with `ay_string_free`.
///
/// # Safety
/// - `solver` must be a valid pointer from `ay_solver_new`
#[no_mangle]
pub unsafe extern "C" fn ay_get_statistics(solver: *mut AYSolver) -> *mut c_char {
    if solver.is_null() {
        return std::ptr::null_mut();
    }

    // SAFETY: `solver` was null-checked above and the caller's `# Safety`
    // contract requires it to point to a valid `AYSolver`.
    match catch_unwind(AssertUnwindSafe(|| unsafe {
        let solver = &mut *solver;

        match solver
            .executor
            .execute(&Command::GetInfo("all-statistics".to_string()))
        {
            Ok(Some(stats)) => match CString::new(stats) {
                Ok(s) => s.into_raw(),
                Err(_) => std::ptr::null_mut(),
            },
            _ => std::ptr::null_mut(),
        }
    })) {
        Ok(val) => val,
        Err(_) => std::ptr::null_mut(),
    }
}

/// Free a string returned by ay functions
///
/// # Safety
/// - `s` must be a pointer returned by ay string functions
/// - `s` must not be used after this call
/// - Safe to call with null pointer (no-op)
#[no_mangle]
pub unsafe extern "C" fn ay_string_free(s: *mut c_char) {
    // SAFETY: The pointer arguments were validated above and are required to be valid by the
    // enclosing extern "C" function's `# Safety` contract.
    unsafe {
        if !s.is_null() {
            let _ = CString::from_raw(s);
        }
    }
}

/// Reset the solver state
///
/// Clears all assertions and declarations, returning the solver to
/// its initial state. Equivalent to creating a new solver.
///
/// # Safety
/// - `solver` must be a valid pointer from `ay_solver_new`
#[no_mangle]
pub unsafe extern "C" fn ay_reset(solver: *mut AYSolver) {
    if solver.is_null() {
        return;
    }

    // SAFETY: All raw pointers used inside this block were validated (null-checked and/or
    // bounds-checked) above, and the caller's `# Safety` contract on this extern "C" function
    // guarantees they remain valid for the duration of the call.
    let _ = catch_unwind(AssertUnwindSafe(|| unsafe {
        let solver = &mut *solver;
        solver.executor = Executor::new();
        solver.clear_error();
    }));
}

// ============================================================================
// Incremental Solving Functions
// ============================================================================

/// Helper: map an executor output string to a result code.
fn output_to_result_code(output: &str) -> c_int {
    match output {
        "sat" => AY_SAT,
        "unsat" => AY_UNSAT,
        _ => AY_UNKNOWN,
    }
}

/// Push an assertion scope
///
/// Saves the current assertion state. Assertions added after push
/// can be removed by calling `ay_pop`. Enables incremental solving mode.
///
/// # Safety
/// - `solver` must be a valid pointer from `ay_solver_new`
#[no_mangle]
pub unsafe extern "C" fn ay_push(solver: *mut AYSolver) {
    if solver.is_null() {
        return;
    }

    // SAFETY: All raw pointers used inside this block were validated (null-checked and/or
    // bounds-checked) above, and the caller's `# Safety` contract on this extern "C" function
    // guarantees they remain valid for the duration of the call.
    let _ = catch_unwind(AssertUnwindSafe(|| unsafe {
        let solver = &mut *solver;
        solver.clear_error();
        if let Err(e) = solver.executor.execute(&Command::Push(1)) {
            solver.set_error(format!("Push error: {e}"));
        }
    }));
}

/// Pop assertion scopes
///
/// Removes `levels` assertion scopes, restoring the solver state
/// to before the corresponding `ay_push` calls.
///
/// # Arguments
/// - `solver` - Solver handle from `ay_solver_new`
/// - `levels` - Number of scopes to pop (must be > 0)
///
/// # Returns
/// - 0 on success
/// - `AY_ERROR` (-2) if levels <= 0, null pointer, or scope underflow
///
/// # Safety
/// - `solver` must be a valid pointer from `ay_solver_new`
#[no_mangle]
pub unsafe extern "C" fn ay_pop(solver: *mut AYSolver, levels: c_int) -> c_int {
    if solver.is_null() {
        return AY_ERROR;
    }
    if levels <= 0 {
        return AY_ERROR;
    }

    // SAFETY: All raw pointers used inside this block were validated (null-checked and/or
    // bounds-checked) above, and the caller's `# Safety` contract on this extern "C" function
    // guarantees they remain valid for the duration of the call.
    let result = catch_unwind(AssertUnwindSafe(|| unsafe {
        let solver = &mut *solver;
        solver.clear_error();

        #[allow(clippy::cast_sign_loss)]
        match solver.executor.execute(&Command::Pop(levels as u32)) {
            Ok(_) => 0,
            Err(e) => {
                solver.set_error(format!("Pop error: {e}"));
                AY_ERROR
            }
        }
    }));

    match result {
        Ok(val) => val,
        // SAFETY: All raw pointers used inside this block were validated (null-checked and/or
        // bounds-checked) above, and the caller's `# Safety` contract on this extern "C"
        // function guarantees they remain valid for the duration of the call.
        Err(panic) => unsafe {
            let solver = &mut *solver;
            solver.set_error(format!(
                "panic in ay_pop: {}",
                z3_compat::panic_payload_to_string(&*panic)
            ));
            AY_ERROR
        },
    }
}

/// Assert a formula
///
/// Parses the SMT-LIB term and adds it as an assertion to the solver.
/// The formula should be a term, not a full command -- e.g., `"(> x 0)"`
/// not `"(assert (> x 0))"`.
///
/// # Arguments
/// - `solver` - Solver handle from `ay_solver_new`
/// - `formula` - Null-terminated UTF-8 string containing an SMT-LIB term
///
/// # Returns
/// - 0 on success
/// - `AY_ERROR` (-2) on parse error, invalid input, or null pointer
///
/// # Safety
/// - `solver` must be a valid pointer from `ay_solver_new`
/// - `formula` must be a valid null-terminated UTF-8 string
#[no_mangle]
pub unsafe extern "C" fn ay_assert(solver: *mut AYSolver, formula: *const c_char) -> c_int {
    if solver.is_null() || formula.is_null() {
        return AY_ERROR;
    }

    // SAFETY: The caller's `# Safety` contract requires the C string pointer to be non-null
    // and to point to a valid, null-terminated sequence of bytes owned by the caller for the
    // duration of this call. The pointer was null-checked before entering this block.
    let result = catch_unwind(AssertUnwindSafe(|| unsafe {
        let solver = &mut *solver;
        solver.clear_error();

        let formula_str = match CStr::from_ptr(formula).to_str() {
            Ok(s) => s,
            Err(_) => {
                solver.set_error("Input is not valid UTF-8".to_string());
                return AY_ERROR;
            }
        };

        // Wrap the term as an (assert ...) command and parse it
        let wrapped = format!("(assert {formula_str})");
        let commands = match parse(&wrapped) {
            Ok(cmds) => cmds,
            Err(e) => {
                solver.set_error(format!("Parse error: {e}"));
                return AY_ERROR;
            }
        };

        // Execute the parsed assert command
        for cmd in &commands {
            if let Err(e) = solver.executor.execute(cmd) {
                solver.set_error(format!("Execution error: {e}"));
                return AY_ERROR;
            }
        }

        0
    }));

    match result {
        Ok(val) => val,
        // SAFETY: All raw pointers used inside this block were validated (null-checked and/or
        // bounds-checked) above, and the caller's `# Safety` contract on this extern "C"
        // function guarantees they remain valid for the duration of the call.
        Err(panic) => unsafe {
            let solver = &mut *solver;
            solver.set_error(format!(
                "panic in ay_assert: {}",
                z3_compat::panic_payload_to_string(&*panic)
            ));
            AY_ERROR
        },
    }
}

/// Check satisfiability of current assertions
///
/// Executes a `(check-sat)` command on the current set of assertions.
///
/// # Returns
/// - `AY_SAT` (1) if satisfiable
/// - `AY_UNSAT` (0) if unsatisfiable
/// - `AY_UNKNOWN` (-1) if solver could not determine
/// - `AY_ERROR` (-2) on error or null pointer
///
/// # Safety
/// - `solver` must be a valid pointer from `ay_solver_new`
#[no_mangle]
pub unsafe extern "C" fn ay_check_sat(solver: *mut AYSolver) -> c_int {
    if solver.is_null() {
        return AY_ERROR;
    }

    // SAFETY: All raw pointers used inside this block were validated (null-checked and/or
    // bounds-checked) above, and the caller's `# Safety` contract on this extern "C" function
    // guarantees they remain valid for the duration of the call.
    let result = catch_unwind(AssertUnwindSafe(|| unsafe {
        let solver = &mut *solver;
        solver.clear_error();

        match solver.execute_with_timeout(&Command::CheckSat) {
            Ok(Some(output)) => output_to_result_code(&output),
            Ok(None) => AY_UNKNOWN,
            Err(e) => {
                solver.set_error(format!("Execution error: {e}"));
                AY_ERROR
            }
        }
    }));

    match result {
        Ok(val) => val,
        // SAFETY: All raw pointers used inside this block were validated (null-checked and/or
        // bounds-checked) above, and the caller's `# Safety` contract on this extern "C"
        // function guarantees they remain valid for the duration of the call.
        Err(panic) => unsafe {
            let solver = &mut *solver;
            solver.set_error(format!(
                "panic in ay_check_sat: {}",
                z3_compat::panic_payload_to_string(&*panic)
            ));
            AY_ERROR
        },
    }
}

/// Check satisfiability under additional assumptions
///
/// The assumptions are temporary and do not persist after this call.
/// Each assumption is an SMT-LIB literal -- either a symbol like `"p"`
/// or a negated symbol like `"(not p)"`.
///
/// # Arguments
/// - `solver` - Solver handle from `ay_solver_new`
/// - `assumptions` - Array of null-terminated UTF-8 strings, each an SMT-LIB literal
/// - `count` - Number of assumptions (must be >= 0)
///
/// # Returns
/// - `AY_SAT` (1) if satisfiable
/// - `AY_UNSAT` (0) if unsatisfiable
/// - `AY_UNKNOWN` (-1) if solver could not determine
/// - `AY_ERROR` (-2) on error or null pointer
///
/// # Safety
/// - `solver` must be a valid pointer from `ay_solver_new`
/// - `assumptions` must be a valid pointer to `count` null-terminated C strings,
///   or null if `count` is 0
/// - `count` must be >= 0
#[no_mangle]
pub unsafe extern "C" fn ay_check_sat_assuming(
    solver: *mut AYSolver,
    assumptions: *const *const c_char,
    count: c_int,
) -> c_int {
    if solver.is_null() {
        return AY_ERROR;
    }
    if count < 0 {
        return AY_ERROR;
    }
    if count > 0 && assumptions.is_null() {
        return AY_ERROR;
    }

    // SAFETY: The caller's `# Safety` contract requires the C string pointer to be non-null
    // and to point to a valid, null-terminated sequence of bytes owned by the caller for the
    // duration of this call. The pointer was null-checked before entering this block.
    let result = catch_unwind(AssertUnwindSafe(|| unsafe {
        let solver = &mut *solver;
        solver.clear_error();

        // Build the literal list for check-sat-assuming
        let mut lit_strs = Vec::new();
        #[allow(clippy::cast_sign_loss)]
        for i in 0..(count as usize) {
            let ptr = *assumptions.add(i);
            if ptr.is_null() {
                solver.set_error(format!("Null assumption at index {i}"));
                return AY_ERROR;
            }
            match CStr::from_ptr(ptr).to_str() {
                Ok(s) => lit_strs.push(s.to_string()),
                Err(_) => {
                    solver.set_error(format!("Assumption at index {i} is not valid UTF-8"));
                    return AY_ERROR;
                }
            }
        }

        // Construct a (check-sat-assuming (<lit1> <lit2> ...)) command string and parse it
        let lits_joined = lit_strs.join(" ");
        let cmd_str = format!("(check-sat-assuming ({lits_joined}))");

        let commands = match parse(&cmd_str) {
            Ok(cmds) => cmds,
            Err(e) => {
                solver.set_error(format!("Parse error: {e}"));
                return AY_ERROR;
            }
        };

        // Execute the parsed check-sat-assuming command
        for cmd in &commands {
            match solver.execute_with_timeout(cmd) {
                Ok(Some(output)) => return output_to_result_code(&output),
                Ok(None) => {}
                Err(e) => {
                    solver.set_error(format!("Execution error: {e}"));
                    return AY_ERROR;
                }
            }
        }

        AY_UNKNOWN
    }));

    match result {
        Ok(val) => val,
        // SAFETY: All raw pointers used inside this block were validated (null-checked and/or
        // bounds-checked) above, and the caller's `# Safety` contract on this extern "C"
        // function guarantees they remain valid for the duration of the call.
        Err(panic) => unsafe {
            let solver = &mut *solver;
            solver.set_error(format!(
                "panic in ay_check_sat_assuming: {}",
                z3_compat::panic_payload_to_string(&*panic)
            ));
            AY_ERROR
        },
    }
}

/// Get the unsat core from the last UNSAT check-sat-assuming result.
///
/// Returns the unsat assumptions as an SMT-LIB formatted string.
/// Only valid after a check-sat-assuming that returned UNSAT.
///
/// # Returns
/// Unsat core string (caller must free with `ay_string_free`), or null
///
/// # Safety
/// - `solver` must be a valid pointer from `ay_solver_new`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn ay_get_unsat_core(solver: *mut AYSolver) -> *mut c_char {
    if solver.is_null() {
        return std::ptr::null_mut();
    }

    // SAFETY: All raw pointers used inside this block were validated (null-checked and/or
    // bounds-checked) above, and the caller's `# Safety` contract on this extern "C" function
    // guarantees they remain valid for the duration of the call.
    match catch_unwind(AssertUnwindSafe(|| unsafe {
        let solver = &mut *solver;

        let commands = match parse("(get-unsat-assumptions)") {
            Ok(cmds) => cmds,
            Err(_) => return std::ptr::null_mut(),
        };

        let mut last_output = None;

        for cmd in &commands {
            match solver.executor.execute(cmd) {
                Ok(Some(output)) => last_output = Some(output),
                Ok(None) => {}
                Err(_) => return std::ptr::null_mut(),
            }
        }

        match last_output {
            Some(output) if !output.starts_with("(error") => match CString::new(output) {
                Ok(s) => s.into_raw(),
                Err(_) => std::ptr::null_mut(),
            },
            _ => std::ptr::null_mut(),
        }
    })) {
        Ok(val) => val,
        Err(_) => std::ptr::null_mut(),
    }
}

// ============================================================================
// Quick Solve Functions (One-shot, no handle needed)
// ============================================================================

/// Quick SMT solve (one-shot, no handle management)
///
/// Convenience function for simple solve operations. Creates a temporary
/// solver, runs the input, and returns the result.
///
/// # Arguments
/// - `smtlib` - Null-terminated UTF-8 string containing SMT-LIB commands
///
/// # Returns
/// - `AY_SAT`, `AY_UNSAT`, `AY_UNKNOWN`, or `AY_ERROR`
///
/// # Safety
/// - `smtlib` must be a valid null-terminated UTF-8 string
#[no_mangle]
pub unsafe extern "C" fn ay_quick_solve(smtlib: *const c_char) -> c_int {
    // SAFETY: The pointer arguments were validated above and are required to be valid by the
    // enclosing extern "C" function's `# Safety` contract.
    unsafe {
        let solver = ay_solver_new();
        if solver.is_null() {
            return AY_ERROR;
        }

        let result = ay_solve_smtlib(solver, smtlib);
        ay_solver_free(solver);
        result
    }
}

/// Shared helper: wrap a formula with a logic declaration and quick-solve.
///
/// # Safety
/// - `formula` must be a valid null-terminated UTF-8 string
unsafe fn solve_with_logic(formula: *const c_char, logic: &str) -> c_int {
    // SAFETY: The caller's `# Safety` contract requires the C string pointer to be non-null
    // and to point to a valid, null-terminated sequence of bytes owned by the caller for the
    // duration of this call. The pointer was null-checked before entering this block.
    unsafe {
        if formula.is_null() {
            return AY_ERROR;
        }

        let formula_str = match CStr::from_ptr(formula).to_str() {
            Ok(s) => s,
            Err(_) => return AY_ERROR,
        };

        let full_input = format!("(set-logic {logic})\n{formula_str}");

        let c_input = match CString::new(full_input) {
            Ok(s) => s,
            Err(_) => return AY_ERROR,
        };

        ay_quick_solve(c_input.as_ptr())
    }
}

/// Quick LIA solve for linear integer arithmetic formulas
///
/// Convenience function for QF_LIA problems. Automatically wraps the
/// formula with appropriate logic declaration.
///
/// # Arguments
/// - `formula` - SMT-LIB formula without logic declaration
///
/// # Example
/// ```c
/// // Just the assertions and check-sat
/// const char* formula = "(declare-const x Int)(assert (> x 0))(check-sat)";
/// int result = ay_solve_lia(formula);
/// ```
///
/// # Returns
/// - `AY_SAT`, `AY_UNSAT`, `AY_UNKNOWN`, or `AY_ERROR`
///
/// # Safety
/// - `formula` must be a valid null-terminated UTF-8 string
#[no_mangle]
pub unsafe extern "C" fn ay_solve_lia(formula: *const c_char) -> c_int {
    // SAFETY: The pointer arguments were validated above and are required to be valid by the
    // enclosing extern "C" function's `# Safety` contract.
    unsafe { solve_with_logic(formula, "QF_LIA") }
}

/// Quick SAT solve for propositional formulas
///
/// Convenience function for QF_UF (propositional) problems.
///
/// # Arguments
/// - `formula` - SMT-LIB formula with Bool declarations
///
/// # Returns
/// - `AY_SAT`, `AY_UNSAT`, `AY_UNKNOWN`, or `AY_ERROR`
///
/// # Safety
/// - `formula` must be a valid null-terminated UTF-8 string
#[no_mangle]
pub unsafe extern "C" fn ay_solve_sat(formula: *const c_char) -> c_int {
    // SAFETY: The pointer arguments were validated above and are required to be valid by the
    // enclosing extern "C" function's `# Safety` contract.
    unsafe { solve_with_logic(formula, "QF_UF") }
}

/// Quick BV solve for bitvector formulas
///
/// Convenience function for QF_BV problems.
///
/// # Arguments
/// - `formula` - SMT-LIB formula with BitVec declarations
///
/// # Returns
/// - `AY_SAT`, `AY_UNSAT`, `AY_UNKNOWN`, or `AY_ERROR`
///
/// # Safety
/// - `formula` must be a valid null-terminated UTF-8 string
#[no_mangle]
pub unsafe extern "C" fn ay_solve_bv(formula: *const c_char) -> c_int {
    // SAFETY: The pointer arguments were validated above and are required to be valid by the
    // enclosing extern "C" function's `# Safety` contract.
    unsafe { solve_with_logic(formula, "QF_BV") }
}

// ============================================================================
// Version and Info
// ============================================================================

/// Get the stamped AY build identity.
///
/// This returns the build stamp for the current `ay-ffi` artifact so consumers
/// can distinguish stale binaries from the current workspace build.
///
/// # Returns
/// - Pointer to heap-allocated version string (caller must free with `ay_string_free`)
/// - Null pointer if allocation fails (should not happen in practice)
#[no_mangle]
pub extern "C" fn ay_version() -> *mut c_char {
    // CString::new cannot fail here since BUILD_STAMP has no interior NULs.
    match CString::new(BUILD_STAMP) {
        Ok(s) => s.into_raw(),
        Err(_) => std::ptr::null_mut(),
    }
}

// ============================================================================
// wasm32 linear-memory staging allocator
// ============================================================================
//
// On wasm there is no shared address space between the JS host and the module.
// To pass an SMT-LIB *string* into a `*const c_char` FFI entry, JS must first
// stage the bytes inside the module's linear memory. `ay_malloc` reserves a
// buffer JS can write into (and hand to `ay_solve_smtlib`, `ay_assert`, ...);
// `ay_free` returns it. The 8-byte length prefix records the size so `ay_free`
// can reconstruct the exact `Layout` used by `alloc` (Rust's allocator is not
// size-oblivious). These are only compiled for wasm; the host uses the normal
// C `malloc`/`free` of the embedding process.
#[cfg(target_arch = "wasm32")]
#[no_mangle]
pub extern "C" fn ay_malloc(n: usize) -> *mut u8 {
    use std::alloc::{alloc, Layout};
    // Reserve `n` bytes plus an 8-byte header holding the allocation size.
    let total = match n.checked_add(8) {
        Some(t) => t,
        None => return std::ptr::null_mut(),
    };
    let layout = match Layout::from_size_align(total, 8) {
        Ok(l) => l,
        Err(_) => return std::ptr::null_mut(),
    };
    // SAFETY: `layout` has a non-zero size (>= 8).
    let base = unsafe { alloc(layout) };
    if base.is_null() {
        return std::ptr::null_mut();
    }
    // SAFETY: `base` points to at least `total` writable bytes; the header fits.
    unsafe {
        (base as *mut usize).write(total);
        base.add(8)
    }
}

#[cfg(target_arch = "wasm32")]
#[no_mangle]
pub unsafe extern "C" fn ay_free(ptr: *mut u8) {
    use std::alloc::{dealloc, Layout};
    if ptr.is_null() {
        return;
    }
    // SAFETY: `ptr` was produced by `ay_malloc`, so the 8-byte header directly
    // precedes it and records the total allocation size.
    let base = unsafe { ptr.sub(8) };
    let total = unsafe { (base as *const usize).read() };
    if let Ok(layout) = Layout::from_size_align(total, 8) {
        // SAFETY: `base`/`layout` match the original `ay_malloc` allocation.
        unsafe { dealloc(base, layout) };
    }
}

#[allow(clippy::unwrap_used)]
#[cfg(test)]
#[path = "lib_tests.rs"]
mod tests;
