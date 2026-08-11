// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::panic)]

//! End-to-end tests for the FP forward-error tactic (QF_FPLRA rounding-error
//! claims discharged by sound interval propagation; see
//! `executor/theories/fp/forward_error.rs` and
//! the development design notes).
//!
//! The instance is the geometry_consumer GUARD claim: a 4-op f64 signed-distance dag
//! `r = nx*px + ny*py + nz*pz + d` (3 muls, 3 adds, RNE) with inputs normal,
//! `|n*| <= 1`, `|p*|,|d| <= 2^48`. The tactic certifies
//! `|to_real(rf) - exact| <= 13/64 = 0.203125`, so claims strictly above the
//! bound are refuted (unsat) while claims at or below it must be left to the
//! (incomplete) bit-precise lane — a sound unknown, never a wrong unsat.

use ay_core::{ProofStep, TheoryLemmaKind};
use ay_dpll::Executor;
use ay_frontend::parse;
use ntest::timeout;
use std::path::PathBuf;

/// The GUARD dag with a parametrized error claim asserted.
fn guard_claim_smt(claim: &str) -> String {
    format!(
        r#"
        (set-logic QF_FPLRA)
        (declare-const nx Float64) (declare-const ny Float64) (declare-const nz Float64)
        (declare-const px Float64) (declare-const py Float64) (declare-const pz Float64)
        (declare-const d Float64)
        (define-fun B () Real 281474976710656.0)
        (assert (and (fp.isNormal nx) (<= (fp.to_real (fp.abs nx)) 1.0)))
        (assert (and (fp.isNormal ny) (<= (fp.to_real (fp.abs ny)) 1.0)))
        (assert (and (fp.isNormal nz) (<= (fp.to_real (fp.abs nz)) 1.0)))
        (assert (and (fp.isNormal px) (<= (fp.to_real (fp.abs px)) B)))
        (assert (and (fp.isNormal py) (<= (fp.to_real (fp.abs py)) B)))
        (assert (and (fp.isNormal pz) (<= (fp.to_real (fp.abs pz)) B)))
        (assert (and (fp.isNormal d)  (<= (fp.to_real (fp.abs d))  B)))
        (define-fun t1 () Float64 (fp.mul RNE nx px))
        (define-fun t2 () Float64 (fp.mul RNE ny py))
        (define-fun t3 () Float64 (fp.mul RNE nz pz))
        (define-fun s1 () Float64 (fp.add RNE t1 t2))
        (define-fun s2 () Float64 (fp.add RNE s1 t3))
        (define-fun rf () Float64 (fp.add RNE s2 d))
        (define-fun rreal () Real (+ (* (fp.to_real nx) (fp.to_real px))
                                     (* (fp.to_real ny) (fp.to_real py))
                                     (* (fp.to_real nz) (fp.to_real pz))
                                     (fp.to_real d)))
        {claim}
        (check-sat)
    "#
    )
}

fn benchmark_path(name: &str) -> PathBuf {
    crate::common::workspace_path(format!("benchmarks/smt/QF_FPLRA/{name}"))
}

/// The geometry_consumer GUARD claim: error >= 0.3 is refuted (0.3 > 13/64).
#[test]
#[timeout(30_000)]
fn guard_claim_error_ge_0_3_unsat() {
    let smt = guard_claim_smt("(assert (>= (- (fp.to_real rf) rreal) 0.3))");
    assert_eq!(crate::common::solve_vec(&smt), vec!["unsat"]);
}

/// The geometry_consumer gdt.rs GUARD=2 band: error >= 2 is refuted with ~10x margin.
#[test]
#[timeout(30_000)]
fn guard_claim_error_ge_2_unsat() {
    let smt = guard_claim_smt("(assert (>= (- (fp.to_real rf) rreal) 2.0))");
    assert_eq!(crate::common::solve_vec(&smt), vec!["unsat"]);
}

/// Reversed orientation: mirror - computed <= -0.3 is the same claim.
#[test]
#[timeout(30_000)]
fn guard_claim_reversed_orientation_unsat() {
    let smt = guard_claim_smt("(assert (<= (- rreal (fp.to_real rf)) (- 0.3)))");
    assert_eq!(crate::common::solve_vec(&smt), vec!["unsat"]);
}

/// HONESTY: error >= 1e-7 is genuinely reachable (true status: sat; concrete
/// f64 witnesses hit ~0.15), and the certified bound 13/64 cannot rule it
/// out. The tactic must abstain and the answer must NOT be unsat.
#[test]
#[timeout(60_000)]
fn guard_claim_error_ge_1e7_not_unsat() {
    let smt = guard_claim_smt("(assert (>= (- (fp.to_real rf) rreal) 0.0000001))");
    let outputs = crate::common::solve_vec(&smt);
    assert_ne!(
        outputs,
        vec!["unsat"],
        "1e-7 claim is below the certified bound; refuting it would be UNSOUND"
    );
}

/// HONESTY: a claim exactly at the certified bound (13/64, non-strict) is not
/// refutable either — strict excess is required.
#[test]
#[timeout(60_000)]
fn guard_claim_error_ge_exact_bound_not_unsat() {
    let smt = guard_claim_smt("(assert (>= (- (fp.to_real rf) rreal) (/ 13.0 64.0)))");
    let outputs = crate::common::solve_vec(&smt);
    assert_ne!(outputs, vec!["unsat"]);
}

/// A strict claim just above the certified bound is refuted.
#[test]
#[timeout(30_000)]
fn guard_claim_error_gt_exact_bound_unsat() {
    let smt = guard_claim_smt("(assert (> (- (fp.to_real rf) rreal) (/ 13.0 64.0)))");
    assert_eq!(crate::common::solve_vec(&smt), vec!["unsat"]);
}

/// SIDE CONDITION: without fp.isNormal on one input, fp.to_real is
/// unconstrained on NaN/oo — the tactic must abstain (never unsat).
#[test]
#[timeout(60_000)]
fn guard_claim_missing_normality_not_unsat() {
    let smt = guard_claim_smt("(assert (>= (- (fp.to_real rf) rreal) 0.3))").replace(
        "(assert (and (fp.isNormal nx) (<= (fp.to_real (fp.abs nx)) 1.0)))",
        "(assert (<= (fp.to_real (fp.abs nx)) 1.0))",
    );
    let outputs = crate::common::solve_vec(&smt);
    assert_ne!(outputs, vec!["unsat"]);
}

/// SIDE CONDITION: a non-RNE op invalidates the half-ulp model — abstain.
#[test]
#[timeout(60_000)]
fn guard_claim_non_rne_not_unsat() {
    let smt = guard_claim_smt("(assert (>= (- (fp.to_real rf) rreal) 0.3))").replace(
        "(define-fun rf () Float64 (fp.add RNE s2 d))",
        "(define-fun rf () Float64 (fp.add RTZ s2 d))",
    );
    let outputs = crate::common::solve_vec(&smt);
    assert_ne!(outputs, vec!["unsat"]);
}

/// SIDE CONDITION: a mismatched real mirror (operands swapped across
/// products) is not a rounding-error claim — abstain.
#[test]
#[timeout(60_000)]
fn guard_claim_mirror_mismatch_not_unsat() {
    let smt = guard_claim_smt("(assert (>= (- (fp.to_real rf) rreal) 0.3))").replace(
        "(* (fp.to_real nx) (fp.to_real px))",
        "(* (fp.to_real nx) (fp.to_real py))",
    );
    let outputs = crate::common::solve_vec(&smt);
    assert_ne!(outputs, vec!["unsat"]);
}

/// Solve one guard-claim instance with proofs + fail-closed self-check
/// enabled, returning the executor for proof inspection.
fn solve_self_checked_unsat(smt: &str) -> Executor {
    let commands = parse(smt).unwrap_or_else(|err| panic!("parse failed: {err}\nSMT2:\n{smt}"));
    let mut exec = Executor::new();
    exec.set_produce_proofs(true);
    exec.set_self_check(true);
    let outputs = exec
        .execute_all(&commands)
        .unwrap_or_else(|err| panic!("execution failed: {err}\nSMT2:\n{smt}"));
    assert_eq!(
        outputs,
        vec!["unsat"],
        "forward-error UNSAT must survive --self-check (self-certified proof)"
    );
    exec
}

/// STRICT PROOF SUBSET: the forward-error UNSATs close through the
/// independently checked `FpForwardError` lemma kind, not internal trust — so the
/// proof is trust-free on the empty-clause path (the exact predicate the
/// `--strict-proofs` CLI gate applies via `terminal_trust_report`), passes
/// the strict checker with zero trust steps, and the verdict stays `unsat`
/// under `--self-check`.
#[test]
#[timeout(60_000)]
fn guard_claim_unsat_is_trust_free_and_self_check_certified() {
    for claim in [
        "(assert (>= (- (fp.to_real rf) rreal) 0.3))",
        "(assert (>= (- (fp.to_real rf) rreal) 2.0))",
        "(assert (<= (- rreal (fp.to_real rf)) (- 0.3)))",
        "(assert (> (- (fp.to_real rf) rreal) (/ 13.0 64.0)))",
    ] {
        let exec = solve_self_checked_unsat(&guard_claim_smt(claim));
        let proof = exec.last_proof().expect("proof after UNSAT");

        // Zero trust steps on the empty-clause path (the --strict-proofs gate).
        let report = ay_proof::terminal_trust_report(proof);
        assert!(
            report.is_trust_free(),
            "{claim}: empty-clause path must be trust-free, got {report:?}"
        );
        assert!(!report.has_terminal_trust(), "{claim}");

        // The whole proof passes the strict checker: the promoted
        // `FpForwardError` lemma is independently re-validated by the
        // analytic checker, and no unvalidated trust/hole step remains in the
        // internal proof IR.
        match ay_proof::check_proof_strict(proof, exec.terms()) {
            Ok(quality) => assert_eq!(
                quality.trust_count, 0,
                "{claim}: strict check must count zero trust steps"
            ),
            Err(e) => panic!("{claim}: proof must pass strict check, got {e:?}"),
        }

        assert!(
            proof.steps.iter().any(|step| matches!(
                step,
                ProofStep::TheoryLemma {
                    kind: TheoryLemmaKind::FpForwardError,
                    ..
                }
            )),
            "{claim}: proof IR must carry the checked FpForwardError kind"
        );

        // `fp_forward_error` is AY's internal checked kind, not a rule in the
        // shipped Alethe checker. The wire format must therefore use an honest
        // `hole`, not emit an unknown rule (which would make the document
        // invalid) and never regress to AY's internal `trust` fallback.
        let text = ay_proof::export_alethe(proof, exec.terms());
        assert!(
            text.contains(":rule hole"),
            "{claim}: Alethe wire proof must expose the custom lemma as a hole; got:\n{text}"
        );
        assert!(
            !text.contains("fp_forward_error"),
            "{claim}: must not emit a rule the external checker does not implement; got:\n{text}"
        );
        assert!(
            !text.contains(":rule trust"),
            "{claim}: proof must not fall back to :rule trust; got:\n{text}"
        );
    }
}

/// The checked-in benchmark files agree with their :status annotations
/// (unsat via the tactic; the sat-status tight variant answers a sound
/// non-unsat).
#[test]
#[timeout(120_000)]
fn guard_claim_benchmark_files() {
    use crate::common::{run_executor_file_with_timeout, SolverOutcome};
    let unsat_files = [
        "guard_claim_signed_distance.smt2",
        "guard_claim_guard2.smt2",
    ];
    for name in unsat_files {
        let outcome = run_executor_file_with_timeout(&benchmark_path(name), 60)
            .unwrap_or_else(|err| panic!("{name}: {err}"));
        assert_eq!(outcome, SolverOutcome::Unsat, "{name}");
    }
    let tight = run_executor_file_with_timeout(&benchmark_path("guard_claim_tight_1e7.smt2"), 60)
        .expect("tight variant runs");
    assert_ne!(
        tight,
        SolverOutcome::Unsat,
        "tight 1e-7 claim must never be refuted (true status is sat)"
    );
}
