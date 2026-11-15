// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! A `cong` whose printed left application permutes the internal operands
//! must cite its premises in PRINTED argument order.
//!
//! The internal step is `(= (or r (not q)) (or false false))` from
//! `(= r false)` then `(= (not q) false)`. An authored override spells the
//! disjunction `(or (not q) r)`. The permuted reading validates both
//! positions against a certified premise with no repair step, and pinned
//! carcara 1.1.0 pairs premises with differing printed positions in order.
//! MEASURED before `in_stored_order`: the bridge returned nothing for a
//! repair-free reading, the default rendering cited the stored order, and
//! carcara refused the step ("premise '(= r false)' doesn't justify
//! conclusion arguments '(not q)' and 'false'").

use crate::try_export_alethe_with_problem_scope_and_overrides;
use ay_core::kani_compat::DetHashMap;
use ay_core::{AletheRule, Proof, Sort, Symbol, TermId, TermStore};
use std::process::Command;

struct Fixture {
    terms: TermStore,
    proof: Proof,
    scope: Vec<TermId>,
    disjunction: TermId,
}

/// `(= r false)`, `(= (not q) false)`, `cong`, and the assumed negation of
/// the `cong` conclusion, closed by one resolution.
fn build() -> Fixture {
    let mut terms = TermStore::new();
    let q = terms.mk_var("q", Sort::Bool);
    let r = terms.mk_var("r", Sort::Bool);
    let not_q = terms.mk_not_raw(q);
    let falsity = terms.mk_bool(false);
    let disjunction = terms.mk_app(Symbol::named("or"), [r, not_q], Sort::Bool);
    let folded = terms.mk_app(Symbol::named("or"), [falsity, falsity], Sort::Bool);
    let r_false = terms.mk_app(Symbol::named("="), [r, falsity], Sort::Bool);
    let not_q_false = terms.mk_app(Symbol::named("="), [not_q, falsity], Sort::Bool);
    let rewritten = terms.mk_app(Symbol::named("="), [disjunction, folded], Sort::Bool);
    let refuted = terms.mk_not_raw(rewritten);

    let mut proof = Proof::new();
    let first = proof.add_assume(r_false, None);
    let second = proof.add_assume(not_q_false, None);
    let negation = proof.add_assume(refuted, None);
    let congruence = proof.add_rule_step(
        AletheRule::Cong,
        vec![rewritten],
        vec![first, second],
        Vec::new(),
    );
    proof.add_resolution(vec![], rewritten, congruence, negation);
    Fixture {
        terms,
        proof,
        scope: vec![r_false, not_q_false, refuted],
        disjunction,
    }
}

fn export(fixture: &Fixture, spelling: Option<&str>) -> String {
    let mut overrides = DetHashMap::default();
    if let Some(spelling) = spelling {
        overrides.insert(fixture.disjunction, spelling.to_string());
    }
    try_export_alethe_with_problem_scope_and_overrides(
        &fixture.proof,
        &fixture.terms,
        &fixture.scope,
        Some(&overrides),
    )
    .expect("the step renders")
}

/// Pinned carcara's verdict with no allowance, or `None` when it is not on
/// PATH (the replay is then skipped, never passed).
fn carcara_verdict(case: &str, problem: &str, proof: &str) -> Option<String> {
    if let Err(misjudged) = ay_core::pinned_carcara::pinned_carcara_can_judge(problem, proof) {
        panic!("{case}: {misjudged}\n{proof}");
    }
    let probe = Command::new("carcara").arg("--version").output();
    if !probe.is_ok_and(|probe| probe.status.success()) {
        eprintln!("carcara not on PATH: the {case} replay is skipped");
        return None;
    }
    let dir = std::env::temp_dir().join(format!(
        "ay-cong-premise-order-{}-{case}",
        std::process::id()
    ));
    std::fs::create_dir_all(&dir).unwrap();
    std::fs::write(dir.join("p.smt2"), problem).unwrap();
    std::fs::write(dir.join("p.alethe"), proof).unwrap();
    let output = Command::new("carcara")
        .args(["check", "--expand-let-bindings", "--"])
        .arg(dir.join("p.alethe"))
        .arg(dir.join("p.smt2"))
        .output()
        .unwrap();
    let stdout = String::from_utf8_lossy(&output.stdout);
    let verdict = stdout.lines().last().unwrap_or("").trim().to_string();
    if verdict == "valid" {
        let _ = std::fs::remove_dir_all(&dir);
    }
    Some(format!(
        "{verdict}\n{}\nkept: {}",
        String::from_utf8_lossy(&output.stderr),
        dir.display()
    ))
}

/// NEGATIVE CONTROL: the replay refuses, before the checker runs (so with or
/// without carcara on PATH), the pair pinned carcara prints `valid` for only
/// through its `evaluate` defect (`ay_core::pinned_carcara`).
#[test]
#[should_panic(expected = "is not evidence")]
fn the_carcara_replay_refuses_a_document_pinned_carcara_misjudges() {
    carcara_verdict(
        "false_valid_control",
        ay_core::pinned_carcara::FALSE_VALID_CONTROL_PROBLEM,
        ay_core::pinned_carcara::FALSE_VALID_CONTROL_PROOF,
    );
}

fn assert_carcara_valid(case: &str, disjunction: &str, proof: &str) {
    let problem = format!(
        "(set-logic ALL)\n(declare-const q Bool)\n(declare-const r Bool)\n\
         (assert (= r false))\n(assert (= (not q) false))\n\
         (assert (not (= {disjunction} (or false false))))\n(check-sat)\n"
    );
    if let Some(verdict) = carcara_verdict(case, &problem, proof) {
        assert_eq!(
            verdict.lines().next().unwrap_or(""),
            "valid",
            "{case}: {verdict}\n{proof}"
        );
    }
}

#[test]
fn a_permuted_disjunction_cites_its_cong_premises_in_printed_order() {
    let fixture = build();
    let proof = export(&fixture, Some("(or (not q) r)"));
    assert!(
        proof.contains(
            "(step t3 (cl (= (or (not q) r) (or false false))) :rule cong :premises (t1 t0))"
        ),
        "{proof}"
    );
    assert_carcara_valid("permuted", "(or (not q) r)", &proof);
}

/// Negative twin: with the stored order printed, the default rendering is
/// kept byte for byte and cites the stored order.
#[test]
fn the_stored_order_keeps_the_default_cong_rendering() {
    let fixture = build();
    let proof = export(&fixture, None);
    assert!(
        proof.contains(
            "(step t3 (cl (= (or r (not q)) (or false false))) :rule cong :premises (t0 t1))"
        ),
        "{proof}"
    );
    assert_carcara_valid("stored", "(or r (not q))", &proof);
}
