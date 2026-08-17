// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates

#[test]
fn test_preprocess_propagate_checks_always_guard_empty_clause() {
    let source = include_str!("config_preprocess.rs");
    let start = source
        .find("pub(super) fn preprocess(&mut self) -> bool {")
        .expect("preprocess definition must exist");
    let end = source[start..]
        .find("/// Helper: count the number of fixed (assigned at level 0) variables")
        .map(|offset| start + offset)
        .expect("preprocess terminator must exist");
    let preprocess = &source[start..end];

    const CALL: &str = "self.propagate().is_some()";
    for (offset, _) in preprocess.match_indices(CALL) {
        let line_start = preprocess[..offset].rfind('\n').map_or(0, |i| i + 1);
        let line_end = preprocess[offset..]
            .find('\n')
            .map_or(preprocess.len(), |i| offset + i);
        let line = &preprocess[line_start..line_end];

        assert!(
            line.contains("self.has_empty_clause ||"),
            "preprocess propagate check must include has_empty_clause guard: {line}",
        );
    }
}

/// Regression guard: preprocess() must NOT disable inprocessing techniques
/// based on LRAT mode. The sole authority for LRAT technique disabling is
/// InprocessingControls::with_proof_overrides() in inproc_control.rs (#4569).
///
/// Note: preprocess() legitimately reads `self.cold.lrat_enabled` for conditional
/// behavior (probe path selection, subsumption hint collection). Only blanket
/// `inproc_ctrl.*.enabled = false` under an LRAT guard is forbidden.
///
/// The sat_disable_flags() override block at the top of preprocess()
/// is excluded from this scan — those are intentional debugging overrides
/// for bisecting preprocessing soundness bugs (#8477), not LRAT-conditional
/// disables.
#[test]
fn test_preprocess_has_no_manual_lrat_overrides() {
    let source = include_str!("config_preprocess.rs");
    // Scope: preprocess function body AFTER the sat_disable_flags() override block.
    // The block ends with the no_preprocess guard statement;
    // scanning starts after it to avoid false positives from debugging
    // overrides (#8477). #8506: migrated from env var to cached OnceLock.
    let env_block_end = source
        .find("sat_flags.no_preprocess")
        .expect("sat_flags.no_preprocess guard must exist in preprocess()");
    let test_mod = source.find("#[cfg(test)]").unwrap_or(source.len());
    let fn_body = &source[env_block_end..test_mod];

    // The anti-pattern: an inproc_ctrl technique disabled UNDER AN LRAT GUARD
    // (per the doc above, non-LRAT disables — e.g. the --sat-no-subst-auto
    // density-probe bail-out routing — are legitimate; only LRAT-conditional
    // blanket disables must go through with_proof_overrides()). A disable is
    // treated as LRAT-guarded when an `lrat` mention appears within the 25
    // preceding lines of scanned body text.
    // Build technique names dynamically to avoid include_str! self-matching.
    let lrat_disabled_techniques = ["congruence", "sweep", "factor"];
    for tech in &lrat_disabled_techniques {
        let pattern = format!("self.inproc_ctrl.{tech}.enabled = false");
        for (offset, _) in fn_body.match_indices(&pattern) {
            let preceding_lines: Vec<&str> = fn_body[..offset].lines().collect();
            let window_start = preceding_lines.len().saturating_sub(25);
            let window = preceding_lines[window_start..].join("\n").to_lowercase();
            assert!(
                !window.contains("lrat"),
                "preprocess() must not manually disable {tech} under an LRAT \
                 guard — use InprocessingControls::with_proof_overrides() (#4569)",
            );
        }
    }
}

/// `preprocess_once` is used before an incremental MaxSAT loop, whose caller
/// deliberately defers consuming an UNSAT result until the ordinary solve
/// path. Even an UNSAT early exit must therefore disarm preprocessing; rerunning
/// destructive preprocessing over the already-mutated database violates the
/// public one-shot contract.
#[test]
fn preprocess_once_unsat_exit_is_self_disabling() {
    use crate::{Literal, Solver, Variable};

    let mut solver = Solver::new(1);
    let x = Variable::new(0);
    solver.add_clause(vec![Literal::positive(x)]);
    solver.add_clause(vec![Literal::negative(x)]);

    assert!(
        solver.preprocess_once(),
        "contradictory units must be UNSAT"
    );
    assert!(
        !solver.is_preprocess_enabled(),
        "an UNSAT one-shot run must not leave preprocessing armed"
    );
    assert!(
        !solver.preprocess_once(),
        "a completed one-shot run must be inert on a second call"
    );
    assert!(
        solver.solve().into_inner().is_unsat(),
        "deferring the UNSAT result to the normal solve path must remain valid"
    );
}

#[test]
fn local_preprocess_deadline_is_normal_completion_not_solve_stop() {
    use super::*;

    let mut solver = Solver::new(1);
    solver.cold.preprocess_deadline = Some(ay_core::time::Instant::now());

    assert!(solver.preprocess_timed_out());
    assert_eq!(
        solver.classify_preprocess_outcome(false, &|| false),
        PreprocessOutcome::Complete
    );
}
