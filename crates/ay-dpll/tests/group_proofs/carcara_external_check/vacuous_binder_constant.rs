// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! A Skolemized binder whose body the store folds to a Bool constant,
//! end to end (`alethe_printer/constant_skolem_bridge.rs`).
//!
//! `(forall ((q Int)) (not (= q q)))` is Trust's `forall-int-unsat`. The
//! store folds the body to `false`, so the Skolem instance is the SHARED
//! `false` term. The printer used to key the authored instance text on that
//! term, so every `false` printed as `(not (= c c))`, the `false` axiom was
//! demoted to `:rule hole`, and a strict consumer refused the document. The
//! same mechanism holed the `<` shape, the uninterpreted-sort shape, the
//! negated universals (at their `(= (not true) false)` bridge) and the
//! positive `exists` (at the `sko_ex` itself).
//!
//! Now the instance stays the constant and the anchor derives
//! `(= BODY b)` with rules the checker re-runs. MEASURED 2026-10-01 with
//! Trust's checker (`clean cert verify-external`): every shape below is
//! accepted with no hole, and each negative twin (the bridge's last
//! constant flipped) is refused. With `CLEAN_BIN` naming that binary the
//! test re-measures both; with a Carcara on the search path it runs the
//! pinned checker as well (MEASURED 2026-10-01 with carcara 1.1.0, git
//! `9a352ee`: every shape `valid`, every twin `invalid`). With neither, the
//! rule sequence of each bridge is still pinned per shape.

use super::{require_carcara_or_skip, run_carcara_trust_free, solve_unsat_and_get_proof};
use ntest::timeout;
use std::path::Path;

/// `(not (= q q))`: `(= q q)` to `true`, then the negation through `cong`,
/// `not_simplify` and `trans`.
const NEGATED_EQUALITY: &[&str] = &["eq_simplify", "cong", "not_simplify", "trans"];

/// `(label, problem, closing rule, the bridge's sub-step rules in order)`.
///
/// The rule sequence is pinned so that, with no checker installed, a bridge
/// that ships a wrong but checkable rule (`eq_simplify` where
/// `comp_simplify` belongs) still fails here; the in-process document check
/// is structural and would not see it.
const SHAPES: [(&str, &str, &str, &[&str]); 10] = [
    (
        "forall-not-eq",
        "(set-logic LIA)\n(assert (forall ((q Int)) (not (= q q))))\n(check-sat)\n",
        "sko_forall",
        NEGATED_EQUALITY,
    ),
    (
        "forall-not-eq-trust-spelling",
        "(set-logic LIA)\n\
         (assert (forall ((__trust_u_q Int)) (not (= __trust_u_q __trust_u_q))))\n\
         (check-sat)\n",
        "sko_forall",
        NEGATED_EQUALITY,
    ),
    // `|q|` is `q`: the printer spells the authored quoted symbol bare, so
    // the bridge reads `(not (= q q))` (its matcher alone would decline the
    // raw `(= q |q|)` text).
    (
        "forall-not-eq-quoted-symbol",
        "(set-logic LIA)\n(assert (forall ((q Int)) (not (= q |q|))))\n(check-sat)\n",
        "sko_forall",
        NEGATED_EQUALITY,
    ),
    (
        "forall-not-eq-uninterpreted-sort",
        "(set-logic UF)\n(declare-sort U 0)\n(assert (forall ((q U)) (not (= q q))))\n\
         (check-sat)\n",
        "sko_forall",
        NEGATED_EQUALITY,
    ),
    (
        "forall-lt",
        "(set-logic LIA)\n(assert (forall ((q Int)) (< q q)))\n(check-sat)\n",
        "sko_forall",
        &["comp_simplify"],
    ),
    (
        "forall-gt",
        "(set-logic LIA)\n(assert (forall ((q Int)) (> q q)))\n(check-sat)\n",
        "sko_forall",
        &[
            "comp_simplify",
            "comp_simplify",
            "cong",
            "not_simplify",
            "trans",
        ],
    ),
    (
        "not-forall-eq",
        "(set-logic LIA)\n(assert (not (forall ((q Int)) (= q q))))\n(check-sat)\n",
        "sko_forall",
        &["eq_simplify"],
    ),
    (
        "not-forall-le",
        "(set-logic LIA)\n(assert (not (forall ((q Int)) (<= q q))))\n(check-sat)\n",
        "sko_forall",
        &["comp_simplify"],
    ),
    (
        "not-forall-ge",
        "(set-logic LIA)\n(assert (not (forall ((q Int)) (>= q q))))\n(check-sat)\n",
        "sko_forall",
        &["comp_simplify"],
    ),
    (
        "exists-not-eq",
        "(set-logic LIA)\n(assert (exists ((q Int)) (not (= q q))))\n(check-sat)\n",
        "sko_ex",
        NEGATED_EQUALITY,
    ),
];

/// The document with the constant the bridge's LAST sub-step concludes
/// flipped: the line right before the closing `sko_forall` / `sko_ex`.
fn flip_last_bridge_constant(proof: &str, rule: &str) -> String {
    let lines: Vec<&str> = proof.lines().collect();
    let closing = lines
        .iter()
        .position(|line| line.contains(&format!(":rule {rule})")))
        .unwrap_or_else(|| panic!("no closing {rule}:\n{proof}"));
    assert!(closing > 0, "{proof}");
    let last = lines[closing - 1];
    let flipped = if last.contains(" true)) :rule ") {
        last.replacen(" true)) :rule ", " false)) :rule ", 1)
    } else {
        last.replacen(" false)) :rule ", " true)) :rule ", 1)
    };
    assert_ne!(
        flipped, last,
        "the last bridge step concludes a constant:\n{proof}"
    );
    let mut twin: Vec<String> = lines.iter().map(|line| (*line).to_string()).collect();
    twin[closing - 1] = flipped;
    twin.join("\n") + "\n"
}

/// The rules of the anchored sub-steps `{id}.t1` .. `{id}.tk` right before
/// the closing `sko_forall` / `sko_ex` step `{id}`, in order, after checking
/// that the anchor opening them binds that same step.
fn bridge_rules(proof: &str, rule: &str) -> Vec<String> {
    let lines: Vec<&str> = proof.lines().collect();
    let closing = lines
        .iter()
        .position(|line| line.contains(&format!(":rule {rule})")))
        .unwrap_or_else(|| panic!("no closing {rule}:\n{proof}"));
    let id = lines[closing]
        .strip_prefix("(step ")
        .and_then(|rest| rest.split(' ').next())
        .unwrap_or_else(|| panic!("the closing step has an id:\n{proof}"));
    let sub_step = format!("(step {id}.t");
    let first = lines[..closing]
        .iter()
        .rposition(|line| !line.starts_with(&sub_step))
        .unwrap_or_else(|| panic!("no anchor before {id}:\n{proof}"));
    assert!(
        lines[first].starts_with(&format!("(anchor :step {id} :args ")),
        "the bridge of {id} is not opened by its own anchor:\n{proof}"
    );
    lines[first + 1..closing]
        .iter()
        .map(|line| {
            let (_, after) = line
                .split_once(" :rule ")
                .unwrap_or_else(|| panic!("a sub-step without a rule: {line}"));
            after
                .split([' ', ')'])
                .next()
                .unwrap_or_default()
                .to_string()
        })
        .collect()
}

/// Trust's checker on one certificate, when `CLEAN_BIN` names it: `true`
/// only for a hole-free accepted proof (it exits 1 on a holey one).
pub(super) fn clean_verdict(
    clean: &Path,
    label: &str,
    problem: &str,
    proof: &str,
) -> (bool, String) {
    let directory = tempfile::tempdir().expect("temporary certificate directory");
    let path = directory.path().join(format!("{label}.json"));
    let certificate = serde_json::json!({
        "type": "alethe_certificate",
        "version": "1.0",
        "problem": problem,
        "proof": proof,
    });
    std::fs::write(&path, certificate.to_string()).expect("write certificate");
    let output = std::process::Command::new(clean)
        .args(["cert", "verify-external"])
        .arg(&path)
        .output()
        .expect("run clean cert verify-external");
    let stdout = String::from_utf8_lossy(&output.stdout).to_string();
    let stderr = String::from_utf8_lossy(&output.stderr).to_string();
    (
        output.status.success() && stdout.contains("External certificate verification: PASSED"),
        format!(
            "status={:?}\nstdout={stdout}\nstderr={stderr}",
            output.status.code()
        ),
    )
}

pub(super) fn clean_bin() -> Option<std::path::PathBuf> {
    let path = std::path::PathBuf::from(std::env::var_os("CLEAN_BIN")?);
    assert!(
        path.is_file(),
        "CLEAN_BIN is set but does not name a file: {}",
        path.display()
    );
    Some(path)
}

#[test]
#[timeout(120_000)]
fn a_binder_whose_body_folds_to_a_constant_is_skolemized_without_a_hole() {
    let carcara = require_carcara_or_skip();
    let clean = clean_bin();
    if carcara.is_none() && clean.is_none() {
        eprintln!(
            "vacuous_binder_constant: no Carcara and no CLEAN_BIN; the documents are \
             checked in-process only and the negative twins are NOT checked"
        );
    }
    for (label, problem, rule, bridge) in SHAPES {
        let proof = solve_unsat_and_get_proof(problem, label);
        assert!(
            !proof.contains(":rule hole") && !proof.contains(":rule trust"),
            "{label}: an unchecked step is left:\n{proof}"
        );
        assert!(
            proof.contains(&format!(":rule {rule})")),
            "{label}: the Skolem step is not certified as {rule}:\n{proof}"
        );
        assert_eq!(
            bridge_rules(&proof, rule),
            bridge,
            "{label}: the bridge ships other rules than the catalogue row:\n{proof}"
        );
        // The instance is the constant: no `choice` is ever compared with
        // itself, and `choice` appears only in the anchor that binds it.
        for line in proof.lines() {
            assert!(
                line.starts_with("(anchor ") || !line.contains("(choice "),
                "{label}: a choice term outside its anchor:\n{proof}"
            );
        }
        let scope = ay_proof::ProblemScope::from_smtlib_source(problem);
        ay_proof::check_alethe_document(&proof, &scope).unwrap_or_else(|defect| {
            panic!("{label}: the Alethe document check refused: {defect:?}\n{proof}")
        });

        let twin = flip_last_bridge_constant(&proof, rule);
        if let Some(carcara) = carcara.as_deref() {
            assert!(
                run_carcara_trust_free(carcara, label, problem, &proof),
                "{label}: Carcara must answer a literal `valid`:\n{proof}"
            );
            assert!(
                !run_carcara_trust_free(carcara, &format!("{label}-twin"), problem, &twin),
                "{label}: Carcara accepted the flipped bridge:\n{twin}"
            );
        }
        if let Some(clean) = clean.as_deref() {
            let (valid, diagnostic) = clean_verdict(clean, label, problem, &proof);
            assert!(
                valid,
                "{label}: Trust's checker refused:\n{diagnostic}\n{proof}"
            );
            let (valid, diagnostic) = clean_verdict(clean, label, problem, &twin);
            assert!(
                !valid,
                "{label}: Trust's checker accepted the flipped bridge:\n{diagnostic}\n{twin}"
            );
        }
    }
}

/// A body the store folds but the bridge does not recognise keeps the base
/// path: the verdict is still `unsat`, and the document still discloses its
/// one unchecked step instead of claiming a rewrite it did not derive.
#[test]
#[timeout(60_000)]
fn a_folded_body_outside_the_catalogue_keeps_its_honest_hole() {
    let problem = "(set-logic LIA)\n(assert (forall ((q Int)) (not (= q (+ q 0)))))\n(check-sat)\n";
    let proof = solve_unsat_and_get_proof(problem, "forall-not-eq-plus-zero");
    assert_no_bridge(&proof);
    // The base's document: the authored instance is keyed on `false`, so
    // the `false` axiom prints over it and is the one disclosed hole.
    assert_eq!(
        proof.matches(":rule hole").count(),
        1,
        "the base path keeps exactly its one hole:\n{proof}"
    );
    assert!(proof.contains(":rule sko_forall)"), "{proof}");
}

/// The same under an authored `exists`, whose body is read without the
/// skeleton check ONLY when the bridge derives it: a declined body keeps the
/// base's document (the same bytes `bca3b7c78` printed), whose one hole is
/// the `sko_ex` step itself and whose `false` axiom stays `(cl (not
/// false))`. Admitting every folded body would key the authored instance on
/// the shared `false` and respell the axiom as a hole over `(not (not ..))`.
#[test]
#[timeout(60_000)]
fn a_folded_exists_body_outside_the_catalogue_keeps_its_honest_hole() {
    for (label, quantifier) in [
        (
            "exists-not-eq-plus-zero",
            "(exists ((q Int)) (not (= q (+ q 0))))",
        ),
        (
            "exists-and-folded",
            "(exists ((q Int)) (and (= q q) (< q q)))",
        ),
    ] {
        let problem = format!("(set-logic LIA)\n(assert {quantifier})\n(check-sat)\n");
        let proof = solve_unsat_and_get_proof(&problem, label);
        assert_no_bridge(&proof);
        assert_eq!(
            proof.matches(":rule hole").count(),
            1,
            "{label}: the base path keeps exactly its one hole:\n{proof}"
        );
        assert!(
            proof.contains(&format!("(cl (= {quantifier} false)) :rule hole)")),
            "{label}: the hole is the Skolem step:\n{proof}"
        );
        assert!(
            proof.contains(" (cl (not false)) :rule false)"),
            "{label}: the `false` axiom is respelled:\n{proof}"
        );
        assert!(!proof.contains("(choice "), "{label}:\n{proof}");
    }
}

fn assert_no_bridge(proof: &str) {
    assert!(
        !proof.contains(":rule eq_simplify")
            && !proof.contains(":rule comp_simplify")
            && !proof.contains(":rule not_simplify"),
        "no bridge is offered for sides that differ in print:\n{proof}"
    );
}
