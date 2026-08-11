// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Producer-side tests for the substituted-equality COLLAPSE promotion
//! (`plan_substituted_equality` + the deferred-array-leaf pass-through in
//! `proof_trust_surgery.rs`).
//!
//! `benchmarks/smt/QF_AX/storeinv_cross_1idx.smt2` is the reference shape:
//! `substitute-and-simplify` eliminates the two defined array constants
//! (`v0`, `v1`), so the three assertions that justify
//! `(= (store a2 i (select a1 i)) (store a1 i (select a2 i)))` never reach the
//! exported proof as `assume` steps and the equality itself was exported as a
//! premiseless unproved leaf. Hand-promoting it (plus the two congruence
//! lemmas around it) is what took the emitted certificate from
//! `[ERROR] checking failed on step 't4' with rule 'trust'` to `valid`.
//!
//! The repair re-introduces the ORIGINAL assertions — faithful, they ARE
//! assertions of the file — and closes the unit against them with the
//! existing certified EUF toolkit. These tests pin the three properties that
//! make the result publishable:
//!
//!  1. the exported certificate carries NO unproved step,
//!  2. every re-introduced `assume` sits in the ASSUMPTION PROLOGUE, before
//!     the first `step`/`anchor` (Alethe well-formedness; carcara warns
//!     otherwise), and
//!  3. every re-introduced `assume` is an assertion of the problem file —
//!     never an invented premise.

use ay_dpll::Executor;
use ay_frontend::parse;
use ntest::timeout;

/// The QF_AX reference file, inlined so the test does not depend on a path.
const STOREINV_CROSS_1IDX: &str = r#"
    (set-option :produce-proofs true)
    (set-logic QF_AX)
    (declare-sort Index 0)
    (declare-sort Element 0)
    (declare-fun a1 () (Array Index Element))
    (declare-fun a2 () (Array Index Element))
    (declare-fun i () Index)
    (declare-fun v0 () (Array Index Element))
    (assert (= v0 (store a2 i (select a1 i))))
    (declare-fun v1 () (Array Index Element))
    (assert (= v1 (store a1 i (select a2 i))))
    (assert (= v0 v1))
    (assert (not (= a1 a2)))
    (check-sat)
    (get-proof)
"#;

fn solve_unsat(script: &str) -> (Executor, String) {
    let commands = parse(script).expect("parse SMT-LIB script");
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).expect("execute SMT-LIB script");
    assert_eq!(
        outputs.first().map(String::as_str),
        Some("unsat"),
        "expected UNSAT, got {outputs:?}"
    );
    (exec, outputs.last().cloned().unwrap_or_default())
}

/// Every `assume` must precede the first `step`/`anchor` command.
fn assumes_are_in_the_prologue(alethe: &str) -> bool {
    let mut seen_step = false;
    for line in alethe.lines() {
        let line = line.trim_start();
        if line.starts_with("(step ") || line.starts_with("(anchor ") {
            seen_step = true;
        } else if line.starts_with("(assume ") && seen_step {
            // Subproof-local hypotheses are named `<step>.h…` and legitimately
            // follow their own `anchor`; only TOP-LEVEL assumes are prologue
            // material.
            let name = line
                .trim_start_matches("(assume ")
                .split_whitespace()
                .next()
                .unwrap_or_default();
            if !name.contains('.') {
                return false;
            }
        }
    }
    true
}

/// The collapse target must be re-derived, not trusted: the exported
/// certificate carries no `hole`/`trust` step at all.
#[test]
#[timeout(30_000)]
fn storeinv_cross_1idx_collapse_is_promoted_to_a_trust_free_certificate() {
    let (exec, alethe) = solve_unsat(STOREINV_CROSS_1IDX);
    let proof = exec.last_proof().expect("last proof after UNSAT");
    let report = ay_proof::terminal_trust_report(proof);
    assert!(
        report.is_trust_free(),
        "the promoted certificate must be trust-free, got {report:?}\n{alethe}"
    );
    assert!(
        !alethe.contains(":rule hole"),
        "printed Alethe must carry no unproved step:\n{alethe}"
    );
    assert!(
        !alethe.contains(":rule trust"),
        "printed Alethe must carry no trust step:\n{alethe}"
    );
}

/// WELL-FORMEDNESS: the re-introduced originals must be hoisted into the
/// assumption prologue. An inline re-introduction (where the collapsed step
/// sat) makes carcara warn `assume command … appears after step commands`.
#[test]
#[timeout(30_000)]
fn promoted_assumes_sit_in_the_assumption_prologue() {
    let (_exec, alethe) = solve_unsat(STOREINV_CROSS_1IDX);
    assert!(
        assumes_are_in_the_prologue(&alethe),
        "re-introduced assumes must precede every step:\n{alethe}"
    );
}

/// FAITHFULNESS: every top-level `assume` in the promoted certificate is an
/// assertion of the problem file. Re-introducing an original assertion is
/// faithful; inventing a premise is a soundness violation.
#[test]
#[timeout(30_000)]
fn promoted_assumes_are_all_original_assertions() {
    let (_exec, alethe) = solve_unsat(STOREINV_CROSS_1IDX);
    let originals = [
        "(= v0 (store a2 i (select a1 i)))",
        "(= v1 (store a1 i (select a2 i)))",
        "(= v0 v1)",
        "(not (= a1 a2))",
    ];
    let mut top_level = 0usize;
    for line in alethe.lines() {
        let line = line.trim_start();
        let Some(rest) = line.strip_prefix("(assume ") else {
            continue;
        };
        let mut parts = rest.splitn(2, ' ');
        let name = parts.next().unwrap_or_default();
        if name.contains('.') {
            continue; // subproof-local hypothesis
        }
        top_level += 1;
        let term = parts.next().unwrap_or_default().trim_end();
        let term = term.strip_suffix(')').unwrap_or(term);
        assert!(
            originals.iter().any(|o| *o == term),
            "assume '{term}' is not an assertion of the problem file:\n{alethe}"
        );
    }
    assert!(
        top_level >= 4,
        "expected the three substituted-away definitions to be re-introduced \
         alongside the surviving disequality, saw {top_level}:\n{alethe}"
    );
}

/// The promoted derivation must actually CONCLUDE the collapsed equality from
/// the re-introduced premises (rather than, say, dropping the step): the
/// exported text contains the target equality as a derived step conclusion.
#[test]
#[timeout(30_000)]
fn promoted_derivation_concludes_the_collapsed_equality() {
    let (_exec, alethe) = solve_unsat(STOREINV_CROSS_1IDX);
    let target = "(cl (= (store a2 i (select a1 i)) (store a1 i (select a2 i))))";
    assert!(
        alethe.contains(target),
        "expected a derived step concluding {target}:\n{alethe}"
    );
}
