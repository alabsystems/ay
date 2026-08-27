// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

// Textually included by `dimacs` to preserve private configuration scope.

fn finish_configure_dimacs_solver(solver: &mut SatSolver) {
    // Install the wall-clock deadline matching `--timeout` / `-T:` (the SMT
    // path does the same in run.rs). The watchdog thread stays the hard
    // backstop; this is what lets the solver SIZE its own work against the
    // budget rather than only discover the end when the flag flips. The
    // parked support enumeration (`solver/indep_enum.rs`) sizes its head start
    // and its slice from exactly this deadline — without it a probe cannot
    // tell a 60 s budget from a 5000 s one, and it was that blindness that
    // let it convert 0.15 s solves into 300 s timeouts.
    let timeout_ms = super::GLOBAL_TIMEOUT_MS.load(Ordering::SeqCst);
    if timeout_ms > 0 {
        if let Some(start) = super::START_TIME.get() {
            // An adversarially large CLI timeout can exceed the monotonic
            // clock's representable range; the watchdog still owns the hard
            // timeout, so omit only this cooperative deadline.
            if let Some(deadline) =
                start.checked_add(std::time::Duration::from_millis(timeout_ms))
            {
                solver.set_solve_deadline(Some(deadline));
            }
        }
    }
    // Size the learned clause database against the process memory budget.
    //
    // This runs AFTER the formula is loaded (every DIMACS entry point parses
    // first and configures second), which is what lets the ceiling be floored
    // at the cost of the original formula rather than guessed. Without it
    // `--memory` is a pure observer on the DIMACS path: the advisory trips at
    // 95% and the run publishes `c memout` instead of reducing harder.
    //
    // Default OFF pending its own paired A/B — it moves the reduction cadence,
    // hence the search, on every instance, and only 2 of the 23 memout rows in
    // the full-400 proof-mode run are search-time. `true` opts in.
    if ay_core::sat_ab_switches()
        .memory_aware_clause_db
        .unwrap_or(false)
    {
        let limit = ay_sys::get_process_memory_limit();
        if let Some(ceiling) = solver.arm_clause_db_budget_from_process_limit(limit) {
            safe_eprintln!(
                "c clause-db budget {} MB of {} MB process limit",
                ceiling / (1024 * 1024),
                limit / (1024 * 1024)
            );
        }
    }
    // Enable periodic progress reporting if --progress was set.
    if super::PROGRESS_ENABLED.load(Ordering::Relaxed) {
        solver.set_progress_enabled(true);
    }
    // Attach JSONL progress observer if configured (#8155 subtask 7b).
    if let Some(path) = super::PROGRESS_JSON_PATH.get() {
        if let Ok(observer) = ay_sat::json_observer::JsonProgressObserver::new_append(path) {
            solver.set_observer(Some(Box::new(observer)));
        }
    }
    // Apply --disable CLI flags for SAT technique disabling (#8331).
    // Reads the global populated by run_solve() instead of env vars.
    if let Some(techniques) = super::DISABLED_SAT_TECHNIQUES.get() {
        for &technique in techniques {
            solver.disable_technique(technique);
        }
    }
    // TLA trace setup is done in run_dimacs_from_content for the non-proof solver path.
    solver.maybe_enable_diagnostic_trace_from_env();
    solver.maybe_enable_decision_trace_from_env();
    solver.maybe_enable_replay_trace_from_env();
    solver.maybe_load_solution_from_env();
}
