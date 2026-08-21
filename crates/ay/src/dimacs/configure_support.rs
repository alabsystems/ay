// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

// Textually included by `dimacs` to preserve private configuration scope.

fn finish_configure_dimacs_solver(solver: &mut SatSolver) {
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
