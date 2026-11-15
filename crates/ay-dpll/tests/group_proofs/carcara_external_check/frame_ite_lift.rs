// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The array-frame update axiom's instances publish documents pinned carcara
//! accepts.
//!
//! `forall k. snew[k] = ite(k = 1, val, s[k])` is Shannon-lifted by
//! elaboration, so AY's instance at `0` is the FORMULA
//! `(ite (= 1 0) (= val (select snew 0)) (= (select snew 0) (select s 0)))`,
//! which the refutation consumes with `ite1` / `ite2`. The `forall_inst` has
//! to print the substituted AUTHORED body, and until the printer could derive
//! one from the other (`surface_equivalence::ite_lift`) the authored spelling
//! was the instance's text document-wide. At ad60a0707 pinned carcara 1.1.0
//! refused the published document under `unproved_steps=0 trust_free=yes
//! ay_self_checkable=yes`: "checking failed on step 't7' with rule 'ite1':
//! term '(= (select snew 0) (ite (= 0 1) val (select s 0)))' is of the wrong
//! form, expected '(ite phi_1 phi_2 phi_3)'".
//!
//! All three fixtures must now publish a document pinned carcara checks
//! trust-free as a literal `valid`: the plain update, the `u64`-guarded
//! witness and two stacked updates (whose lift meets the canonical formula
//! through `cong` over the canonical `ite`).
//!
//! The `u64` fixture's refutation also instantiates the axiom at the Skolem
//! witness of its `exists`. At c57bd8481 that document was `holey` with three
//! holes: the `ite2` / `ite1` projections of the witness instance, whose
//! premise printed as the authored equality because the confinement plan ran
//! before Skolem preparation (`alethe_printer/confined_forall_instance.rs`),
//! and the integer split `(cl (<= W 0) (<= 2 W) (= 1 W))`, whose lowering
//! paired each order of the guard with the wrong branch
//! (`alethe_printer/arith_disequality_split.rs`).

use super::{
    carcara_stdout_verdict, exact_carcara_verdict, refuse_pinned_carcara_misjudgments,
    require_carcara_or_skip, solve_unsat_and_get_proof, CarcaraVerdict,
};
use ay_dpll::Executor;
use ay_frontend::parse;
use ntest::timeout;
use std::path::Path;

/// `group_quantifiers::frame_quantifier_instance_resolve`'s
/// `ARRAY_FRAME_INVARIANT_PRESERVED_ACROSS_UPDATE`.
const FRAME_PRESERVED_ACROSS_UPDATE: &str = r#"
(set-logic ALL)
(declare-fun s () (Array Int Int))
(declare-fun snew () (Array Int Int))
(declare-fun val () Int)
(assert (= (select s 0) 10))
(assert (= (select s 1) 20))
(assert (= (select s 2) 30))
(assert (>= val 0))
(assert (forall ((k Int)) (= (select snew k) (ite (= k 1) val (select s k)))))
(assert (exists ((j Int)) (and (<= 0 j) (< j 3) (< (select snew j) 0))))
(check-sat)
"#;

/// The same goal with the Verus `u64` range guard on the witness
/// (`ARRAY_FRAME_U64_GUARDED_WITNESS`).
const FRAME_U64_GUARDED_WITNESS: &str = r#"
(set-logic ALL)
(declare-fun s () (Array Int Int))
(declare-fun snew () (Array Int Int))
(declare-fun val () Int)
(assert (= (select s 0) 10))
(assert (= (select s 1) 20))
(assert (= (select s 2) 30))
(assert (>= val 0))
(assert (forall ((k Int)) (= (select snew k) (ite (= k 1) val (select s k)))))
(assert (exists ((j Int))
    (and (>= j 0) (< j 18446744073709551616) (< j 3) (< (select snew j) 0))))
(check-sat)
"#;

/// The printed `ite1` / `ite2` commands of `proof` at top-level ids (the
/// derivation's own sub-steps read the `ite` DEFINITION and are not the
/// refutation's projections), each with its one premise token.
fn top_level_ite_projections(proof: &str) -> Vec<(&str, &str)> {
    proof
        .lines()
        .filter_map(|line| {
            let rule = line.split(":rule ").nth(1)?;
            let id = line.split_whitespace().nth(1)?;
            if !(rule.starts_with("ite1 ") || rule.starts_with("ite2 ")) || id.contains('.') {
                return None;
            }
            let premise = line.split(":premises (").nth(1)?.strip_suffix("))")?;
            Some((line, premise))
        })
        .collect()
}

/// Every projection's premise PRINTS as a unit clause over an `ite`, the
/// shape pinned carcara's `ite1` / `ite2` read — never the authored equality
/// `(= (select snew X) (ite (= X 1) val (select s X)))`. Returns how many
/// projections ship.
fn assert_projections_read_an_ite_premise(label: &str, proof: &str) -> usize {
    let projections = top_level_ite_projections(proof);
    for (line, premise) in &projections {
        let binding = proof
            .lines()
            .find(|candidate| {
                candidate.starts_with(&format!("(step {premise} "))
                    || candidate.starts_with(&format!("(assume {premise} "))
            })
            .unwrap_or_else(|| panic!("{label}: premise {premise} of `{line}` is not printed"));
        assert!(
            binding.starts_with(&format!("(step {premise} (cl (ite ")),
            "{label}: `{line}` reads a premise that does not print as an ite: {binding}"
        );
    }
    projections.len()
}

#[test]
#[timeout(120_000)]
fn frame_update_instances_publish_a_carcara_valid_document() {
    let label = "frame_ite_lift_update";
    let proof = solve_unsat_and_get_proof(FRAME_PRESERVED_ACROSS_UPDATE, label);
    for rule in [":rule hole", ":rule trust"] {
        assert!(
            !proof.contains(rule),
            "{label}: the document must carry no `{rule}` step:\n{proof}"
        );
    }
    assert!(
        proof
            .lines()
            .any(|line| line.contains(".fi (cl (or (not (forall ((k Int))")),
        "{label}: the update-axiom instance must be confined to its forall_inst:\n{proof}"
    );
    assert!(
        assert_projections_read_an_ite_premise(label, &proof) >= 3,
        "{label}: the refutation consumes the three instances through ite1/ite2:\n{proof}"
    );
    if let Some(carcara) = require_carcara_or_skip() {
        let (valid, diagnostic) =
            exact_carcara_verdict(&carcara, FRAME_PRESERVED_ACROSS_UPDATE, &proof);
        assert!(
            valid,
            "{label}: pinned carcara must check the document trust-free: {diagnostic}\n{proof}"
        );
    }
}

#[test]
#[timeout(120_000)]
fn frame_update_instances_with_u64_guard_publish_a_carcara_valid_document() {
    let label = "frame_ite_lift_u64";
    let proof = solve_unsat_and_get_proof(FRAME_U64_GUARDED_WITNESS, label);
    for rule in [":rule hole", ":rule trust"] {
        assert!(
            !proof.contains(rule),
            "{label}: the document must carry no `{rule}` step:\n{proof}"
        );
    }
    // The instance at the witness is confined like the ground ones: its
    // `forall_inst` names the witness by the `choice` term the document uses.
    assert!(
        proof
            .lines()
            .any(|line| line.contains(".fi (cl (or (not (forall ((k Int))")
                && line.contains(":rule forall_inst :args ((choice ((j Int))")),
        "{label}: the witness instance must be confined to its forall_inst:\n{proof}"
    );
    assert!(
        assert_projections_read_an_ite_premise(label, &proof) >= 5,
        "{label}: the ground instances and the witness instance are consumed through ite1/ite2:\n{proof}"
    );
    // The integer split over the witness is lowered through its printed guard.
    assert!(
        proof.lines().any(
            |line| line.contains(".split (cl (or (= 1 (choice ((j Int))")
                && line.ends_with(":rule la_disequality)")
        ),
        "{label}: the split over the witness must be lowered through la_disequality:\n{proof}"
    );
    let Some(carcara) = require_carcara_or_skip() else {
        return;
    };
    let (verdict, diagnostic) =
        guarded_carcara_verdict(&carcara, label, FRAME_U64_GUARDED_WITNESS, &proof);
    assert!(
        matches!(verdict, CarcaraVerdict::Valid),
        "{label}: pinned carcara must check the document trust-free ({verdict:?}): {diagnostic}\n{proof}"
    );
}

/// Pinned carcara's verdict under the corpus flags with no allowance, after
/// the shared refusal of a pair whose verdict is not evidence at all (an
/// `evaluate` step it misjudges, a binder it misreads): such a pair fails the
/// test here, so a `valid` resting on it cannot pass the assertion above.
fn guarded_carcara_verdict(
    carcara: &Path,
    label: &str,
    problem: &str,
    proof: &str,
) -> (CarcaraVerdict, String) {
    refuse_pinned_carcara_misjudgments(label, problem, proof);
    let directory = tempfile::tempdir().expect("temporary Carcara directory");
    let problem_path = directory.path().join("problem.smt2");
    let proof_path = directory.path().join("proof.alethe");
    std::fs::write(&problem_path, problem).expect("write problem");
    std::fs::write(&proof_path, proof).expect("write proof");
    let output = std::process::Command::new(carcara)
        .args(["check", "--expand-let-bindings", "--no-color", "--"])
        .arg(&proof_path)
        .arg(&problem_path)
        .output()
        .expect("run production Carcara checker");
    let stdout = String::from_utf8_lossy(&output.stdout);
    (
        carcara_stdout_verdict(output.status.success(), &stdout),
        format!(
            "stdout={} stderr={}",
            stdout.trim(),
            String::from_utf8_lossy(&output.stderr).trim()
        ),
    )
}

/// NEGATIVE CONTROL: the runner above refuses, before the checker runs, the
/// pair pinned carcara prints `valid` for only through its `evaluate` defect.
#[test]
#[should_panic(expected = "is not evidence")]
fn the_frame_runner_refuses_a_document_pinned_carcara_misjudges() {
    guarded_carcara_verdict(
        Path::new("carcara"),
        "frame_false_valid_control",
        ay_core::pinned_carcara::FALSE_VALID_CONTROL_PROBLEM,
        ay_core::pinned_carcara::FALSE_VALID_CONTROL_PROOF,
    );
}

/// Two stacked updates (`snew = s.update(1, val).update(2, w)`): the authored
/// instance is an atom over a NESTED term-level `ite`, and its lift reaches
/// the canonical formula only through `cong` over the canonical `ite`.
const FRAME_NESTED_UPDATE: &str = r#"
(set-logic ALL)
(declare-fun s () (Array Int Int))
(declare-fun snew () (Array Int Int))
(declare-fun val () Int)
(declare-fun w () Int)
(assert (= (select s 0) 10))
(assert (= (select s 1) 20))
(assert (= (select s 2) 30))
(assert (>= val 0))
(assert (>= w 0))
(assert (forall ((k Int)) (= (select snew k) (ite (= k 1) val (ite (= k 2) w (select s k))))))
(assert (exists ((j Int)) (and (<= 0 j) (< j 3) (< (select snew j) 0))))
(check-sat)
"#;

#[test]
#[timeout(120_000)]
fn frame_nested_update_instances_publish_a_carcara_valid_document() {
    let label = "frame_ite_lift_nested";
    let proof = solve_unsat_and_get_proof(FRAME_NESTED_UPDATE, label);
    for rule in [":rule hole", ":rule trust"] {
        assert!(
            !proof.contains(rule),
            "{label}: the document must carry no `{rule}` step:\n{proof}"
        );
    }
    assert!(
        assert_projections_read_an_ite_premise(label, &proof) >= 3,
        "{label}: the refutation consumes the instances through ite1/ite2:\n{proof}"
    );
    if let Some(carcara) = require_carcara_or_skip() {
        let (valid, diagnostic) = exact_carcara_verdict(&carcara, FRAME_NESTED_UPDATE, &proof);
        assert!(
            valid,
            "{label}: pinned carcara must check the document trust-free: {diagnostic}\n{proof}"
        );
    }
}

/// The satisfiable twin of the `u64` fixture: `val < 0` makes `j = 1` a model
/// (z3 4.8.12: `sat`).
const FRAME_U64_GUARDED_WITNESS_SAT: &str = r#"
(set-logic ALL)
(declare-fun s () (Array Int Int))
(declare-fun snew () (Array Int Int))
(declare-fun val () Int)
(assert (= (select s 0) 10))
(assert (= (select s 1) 20))
(assert (= (select s 2) 30))
(assert (< val 0))
(assert (forall ((k Int)) (= (select snew k) (ite (= k 1) val (select s k)))))
(assert (exists ((j Int))
    (and (>= j 0) (< j 18446744073709551616) (< j 3) (< (select snew j) 0))))
(check-sat)
"#;

/// The same twin with the update written as a `store`, which AY decides.
const FRAME_U64_GUARDED_WITNESS_STORE_SAT: &str = r#"
(set-logic ALL)
(declare-fun s () (Array Int Int))
(declare-fun snew () (Array Int Int))
(declare-fun val () Int)
(assert (= (select s 0) 10))
(assert (= (select s 1) 20))
(assert (= (select s 2) 30))
(assert (< val 0))
(assert (= snew (store s 1 val)))
(assert (exists ((j Int))
    (and (>= j 0) (< j 18446744073709551616) (< j 3) (< (select snew j) 0))))
(check-sat)
"#;

fn check_sat_with_proofs(problem: &str) -> String {
    let script = format!("(set-option :produce-proofs true)\n{problem}");
    let commands = parse(&script).expect("parse SMT-LIB script");
    let outputs = Executor::new()
        .execute_all(&commands)
        .expect("execute SMT-LIB script");
    outputs.first().cloned().unwrap_or_default()
}

/// NEGATIVE TWINS: the witness-instance confinement and the split lowering are
/// printer-only, and a satisfiable twin of the fixture must never be reported
/// `unsat`. The quantified twin is `unknown` (AY finds no model for the frame
/// quantifier; MEASURED at c57bd8481, before and after the printer change);
/// its `store` form is `sat`.
#[test]
#[timeout(120_000)]
fn satisfiable_twins_of_the_u64_fixture_are_never_unsat() {
    let quantified = check_sat_with_proofs(FRAME_U64_GUARDED_WITNESS_SAT);
    assert!(
        matches!(quantified.as_str(), "sat" | "unknown"),
        "the satisfiable quantified twin must never be `unsat`: {quantified}"
    );
    assert_eq!(
        check_sat_with_proofs(FRAME_U64_GUARDED_WITNESS_STORE_SAT),
        "sat",
        "the satisfiable store twin must stay `sat`"
    );
}
