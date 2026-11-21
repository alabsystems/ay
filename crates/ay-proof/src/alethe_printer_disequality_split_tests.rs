// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! External lowering tests for the guarded arithmetic disequality split.
//!
//! The `la_disequality` lowering re-expresses the lemma through the GUARD's own
//! operands — `(<= lhs rhs)` and `(<= rhs lhs)` — and pairs each with a branch.
//! That pairing is licensed only while the guard and the branches share one
//! linear form when using unit weights (`k = 1`). A guard scaled by `k >= 2`
//! (`q <= -1 ∨ q >= 1 ∨ 2q+1 = 4q+1`), those two `la_generic` sub-steps stop
//! holding — `(cl (<= 2q+1 4q+1) (<= 1 q))` is `q >= 0 ∨ q >= 1`, false at
//! `q = -1`. The checked scale now supplies the required weights `(1, k)`;
//! negative controls retain the rejection of the old invalid unit weights.
//!
//! The primitive lowering reads its operands off the guard AS PRINTED, in the
//! orientation the clause fixes (`arith_disequality_split.rs`); the carcara
//! replays below pin both orientations and the override-swapped guard, and
//! the negative controls pin what `judge_printed_la_disequality` refuses.

use super::printed_la_disequality::printed_la_disequality_holds;
use super::*;
use ay_core::proof_validation::arith_disequality_split_primitive_guard_is_reversed;
use ay_core::{Sort, Symbol, TermStore, TheoryLemmaKind};
use num_bigint::BigInt;
use std::process::Command;

fn split_step(clause: Vec<TermId>) -> ProofStep {
    ProofStep::TheoryLemma {
        theory: "LIA".to_string(),
        clause,
        farkas: None,
        kind: TheoryLemmaKind::ArithDisequalitySplit,
        lia: None,
    }
}

fn raw2(terms: &mut TermStore, op: &str, a: TermId, b: TermId, sort: Sort) -> TermId {
    terms.mk_app(Symbol::named(op), [a, b], sort)
}

#[test]
fn arithmetic_trichotomy_lowers_every_recorded_literal_order() {
    let mut terms = TermStore::new();
    let q = terms.mk_var("q", Sort::Int);
    let zero = terms.mk_int(BigInt::from(0));
    let eq = raw2(&mut terms, "=", q, zero, Sort::Bool);
    let lt = raw2(&mut terms, "<", q, zero, Sort::Bool);
    let le = raw2(&mut terms, "<=", q, zero, Sort::Bool);
    let gt = terms.mk_not_raw(le);
    for clause in [
        [eq, lt, gt],
        [eq, gt, lt],
        [lt, eq, gt],
        [lt, gt, eq],
        [gt, eq, lt],
        [gt, lt, eq],
    ] {
        assert!(crate::recognize_arith_clause_tautology(&terms, &clause));
        let step = ProofStep::TheoryLemma {
            theory: "arith".into(),
            clause: clause.to_vec(),
            farkas: None,
            kind: TheoryLemmaKind::ArithClauseTautology,
            lia: None,
        };
        let printer = AlethePrinter::new(&terms);
        let rendered = printer
            .format_step(&step, ProofId(3))
            .expect("trichotomy renders");
        assert!(!rendered.contains(":rule hole"), "{rendered}");
        let last = rendered.lines().last().expect("final step");
        assert!(
            last.starts_with(&format!("(step t3 {} ", printer.format_clause(&clause))),
            "the recorded order must be restored: {rendered}"
        );
        assert!(arith_disequality_split_lowering_supported(
            &terms,
            &TheoryLemmaKind::ArithClauseTautology,
            &clause,
            None
        ));
        assert_carcara_valid("permuted_trichotomy", &rendered);
    }
}

#[test]
fn arithmetic_trichotomy_refuses_forged_guards_and_changed_surface() {
    let mut terms = TermStore::new();
    let q = terms.mk_var("q", Sort::Int);
    let zero = terms.mk_int(BigInt::from(0));
    let one = terms.mk_int(BigInt::from(1));
    let eq = raw2(&mut terms, "=", q, zero, Sort::Bool);
    let wrong_eq = raw2(&mut terms, "=", q, one, Sort::Bool);
    let lt = raw2(&mut terms, "<", q, zero, Sort::Bool);
    let le = raw2(&mut terms, "<=", q, zero, Sort::Bool);
    let gt = terms.mk_not_raw(le);
    let forged = [wrong_eq, lt, gt];
    assert!(!crate::recognize_arith_clause_tautology(&terms, &forged));
    assert!(!arith_disequality_split_lowering_supported(
        &terms,
        &TheoryLemmaKind::ArithClauseTautology,
        &forged,
        None
    ));
    let clause = [eq, lt, gt];
    let mut overrides = HashMap::default();
    overrides.insert(eq, "(= q 1)".to_string());
    assert!(!arith_disequality_split_lowering_supported(
        &terms,
        &TheoryLemmaKind::ArithClauseTautology,
        &clause,
        Some(&overrides)
    ));
    assert!(!arith_disequality_split_lowering_supported(
        &terms,
        &TheoryLemmaKind::Generic,
        &clause,
        None
    ));
}

#[test]
fn arithmetic_trichotomy_reproves_the_clause_without_consuming_a_farkas_hint() {
    let mut terms = TermStore::new();
    let q = terms.mk_var("q", Sort::Int);
    let zero = terms.mk_int(BigInt::from(0));
    let eq = raw2(&mut terms, "=", q, zero, Sort::Bool);
    let lt = raw2(&mut terms, "<", q, zero, Sort::Bool);
    let le = raw2(&mut terms, "<=", q, zero, Sort::Bool);
    let gt = terms.mk_not_raw(le);
    let step = ProofStep::TheoryLemma {
        theory: "arith".into(),
        clause: vec![eq, lt, gt],
        farkas: Some(ay_core::FarkasAnnotation::from_ints(&[1, 1, 1])),
        kind: TheoryLemmaKind::ArithClauseTautology,
        lia: None,
    };
    let rendered = AlethePrinter::new(&terms)
        .format_step(&step, ProofId(3))
        .expect("the independent derivation renders");
    assert!(rendered.contains(":rule la_disequality"), "{rendered}");
    assert!(!rendered.contains(":rule hole"), "{rendered}");
    assert_carcara_valid("trichotomy_unused_hint", &rendered);
}

#[test]
fn primitive_guard_still_lowers_to_la_disequality() {
    let mut terms = TermStore::new();
    let q = terms.mk_var("q", Sort::Int);
    let minus_one = terms.mk_int(BigInt::from(-1));
    let one = terms.mk_int(BigInt::from(1));
    let zero = terms.mk_int(BigInt::from(0));
    let first = raw2(&mut terms, "<=", q, minus_one, Sort::Bool);
    let second = raw2(&mut terms, "<=", one, q, Sort::Bool);
    let guard = raw2(&mut terms, "=", q, zero, Sort::Bool);
    let step = split_step(vec![first, second, guard]);

    let rendered = AlethePrinter::new(&terms)
        .format_step(&step, ProofId(3))
        .expect("primitive guarded split must render");
    assert!(rendered.contains("la_disequality"), "{rendered}");
    assert!(!rendered.contains("hole"), "{rendered}");
}

#[test]
fn scaled_guard_lowers_with_checked_positive_multipliers() {
    // The dillig12_m clause. The internal strict checker certifies it; the
    // weighted external lowering must reconstruct both actual sub-steps.
    let mut terms = TermStore::new();
    let q = terms.mk_var("q", Sort::Int);
    let minus_one = terms.mk_int(BigInt::from(-1));
    let one = terms.mk_int(BigInt::from(1));
    let two = terms.mk_int(BigInt::from(2));
    let four = terms.mk_int(BigInt::from(4));
    let first = raw2(&mut terms, "<=", q, minus_one, Sort::Bool);
    let second = raw2(&mut terms, "<=", one, q, Sort::Bool);
    let two_q = raw2(&mut terms, "*", q, two, Sort::Int);
    let four_q = raw2(&mut terms, "*", q, four, Sort::Int);
    let lhs = raw2(&mut terms, "+", two_q, one, Sort::Int);
    let rhs = raw2(&mut terms, "+", four_q, one, Sort::Int);
    let guard = raw2(&mut terms, "=", lhs, rhs, Sort::Bool);
    let step = split_step(vec![first, second, guard]);

    let rendered = AlethePrinter::new(&terms)
        .format_step(&step, ProofId(3))
        .expect("scaled guarded split must still render");
    assert!(rendered.contains(":rule la_disequality"), "{rendered}");
    assert!(rendered.contains(":args (1 2)"), "{rendered}");
    assert!(!rendered.contains(":rule hole"), "{rendered}");
    assert_carcara_valid("scaled_benchmark", &rendered);
    for (case, coefficients) in [
        ("zero", "1 0"),
        ("wrong_negative_magnitude", "1 (- 1)"),
        ("wrong", "1 1"),
    ] {
        let forged = rendered.replace(":args (1 2)", &format!(":args ({coefficients})"));
        let (problem, document) = refutation(&forged);
        if let Some(verdict) = carcara_verdict(case, &problem, &document) {
            assert_eq!(verdict.lines().next(), Some("invalid"), "{case}: {verdict}");
        }
    }
}

#[test]
fn scaled_disequality_split_rejects_changed_scale_target_sort_and_surface() {
    let mut terms = TermStore::new();
    let q = terms.mk_var("q", Sort::Int);
    let r = terms.mk_var("r", Sort::Int);
    let zero = terms.mk_int(BigInt::from(0));
    let one = terms.mk_int(BigInt::from(1));
    let minus_one = terms.mk_int(BigInt::from(-1));
    let two = terms.mk_int(BigInt::from(2));
    let first = raw2(&mut terms, "<=", q, minus_one, Sort::Bool);
    let second = raw2(&mut terms, "<=", one, q, Sort::Bool);
    let scaled_q = raw2(&mut terms, "*", q, two, Sort::Int);
    let scaled_r = raw2(&mut terms, "*", r, two, Sort::Int);
    let valid = raw2(&mut terms, "=", scaled_q, zero, Sort::Bool);
    let shifted = raw2(&mut terms, "=", scaled_q, one, Sort::Bool);
    let unrelated = raw2(&mut terms, "=", scaled_r, zero, Sort::Bool);
    let real_q = terms.mk_var("real_q", Sort::Real);
    let real_guard = raw2(&mut terms, "=", real_q, real_q, Sort::Bool);
    for guard in [shifted, unrelated, real_guard] {
        assert!(!arith_disequality_split_lowering_supported(
            &terms,
            &TheoryLemmaKind::ArithClauseTautology,
            &[first, second, guard],
            None
        ));
    }
    let mut overrides = HashMap::default();
    overrides.insert(valid, "(= (* q 2) 1)".to_string());
    assert!(!arith_disequality_split_lowering_supported(
        &terms,
        &TheoryLemmaKind::ArithClauseTautology,
        &[first, second, valid],
        Some(&overrides)
    ));
}

/// `(cl (<= q 0) (<= 2 q) GUARD)` with `GUARD = (= a b)`, and the printed
/// branch literals.
fn one_gap_split(terms: &mut TermStore, guard_constant_first: bool) -> (Vec<TermId>, TermId) {
    let q = terms.mk_var("q", Sort::Int);
    let zero = terms.mk_int(BigInt::from(0));
    let one = terms.mk_int(BigInt::from(1));
    let two = terms.mk_int(BigInt::from(2));
    let first = raw2(terms, "<=", q, zero, Sort::Bool);
    let second = raw2(terms, "<=", two, q, Sort::Bool);
    let guard = if guard_constant_first {
        raw2(terms, "=", one, q, Sort::Bool)
    } else {
        raw2(terms, "=", q, one, Sort::Bool)
    };
    (vec![first, second, guard], guard)
}

/// The lowered step `t3` closed against the negations of its three literals,
/// as a problem and a document for pinned carcara.
fn refutation(rendered: &str) -> (String, String) {
    let clause = rendered
        .lines()
        .last()
        .and_then(|line| line.strip_prefix("(step t3 (cl "))
        .and_then(|rest| rest.split(") :rule ").next())
        .expect("the lowering binds t3 last");
    let literals = split_sexpr_tokens(clause).expect("printed literals");
    let mut problem = "(set-logic QF_LIA)\n(declare-const q Int)\n".to_string();
    let mut document = String::new();
    let mut premises = vec!["t3".to_string()];
    for (index, literal) in literals.iter().enumerate() {
        problem.push_str(&format!("(assert (not {literal}))\n"));
        document.push_str(&format!("(assume h{index} (not {literal}))\n"));
        premises.push(format!("h{index}"));
    }
    problem.push_str("(check-sat)\n");
    document.push_str(rendered);
    document.push_str(&format!(
        "\n(step done (cl) :rule resolution :premises ({}))\n",
        premises.join(" ")
    ));
    (problem, document)
}

/// Pinned carcara's last stdout line, or `None` when it is not on PATH.
/// Refuses, before the checker runs, a pair whose verdict is not evidence
/// (`ay_core::pinned_carcara`).
fn carcara_verdict(case: &str, problem: &str, document: &str) -> Option<String> {
    if let Err(misjudged) = ay_core::pinned_carcara::pinned_carcara_can_judge(problem, document) {
        panic!("{case}: {misjudged}\n{document}");
    }
    let probe = Command::new("carcara").arg("--version").output();
    if !probe.is_ok_and(|probe| probe.status.success()) {
        eprintln!("carcara not on PATH: the {case} replay is skipped");
        return None;
    }
    let dir = std::env::temp_dir().join(format!(
        "ay-disequality-split-{}-{case}",
        std::process::id()
    ));
    std::fs::create_dir_all(&dir).expect("temporary carcara directory");
    std::fs::write(dir.join("p.smt2"), problem).expect("write problem");
    std::fs::write(dir.join("p.alethe"), document).expect("write proof");
    let output = Command::new("carcara")
        .args(["check", "--expand-let-bindings", "--"])
        .arg(dir.join("p.alethe"))
        .arg(dir.join("p.smt2"))
        .output()
        .expect("run carcara");
    let _ = std::fs::remove_dir_all(&dir);
    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    let verdict = stdout.lines().last().unwrap_or("").trim().to_string();
    Some(format!("{verdict}\n{stderr}"))
}

/// NEGATIVE CONTROL: the replay refuses, before the checker runs (so with or
/// without carcara on PATH), the pair pinned carcara prints `valid` for only
/// through its `evaluate` defect.
#[test]
#[should_panic(expected = "is not evidence")]
fn the_split_replay_refuses_a_document_pinned_carcara_misjudges() {
    carcara_verdict(
        "false_valid_control",
        ay_core::pinned_carcara::FALSE_VALID_CONTROL_PROBLEM,
        ay_core::pinned_carcara::FALSE_VALID_CONTROL_PROOF,
    );
}

fn lowered(printer: &AlethePrinter<'_>, clause: Vec<TermId>) -> String {
    let rendered = printer
        .format_step(&split_step(clause), ProofId(3))
        .expect("the primitive split renders");
    assert!(rendered.contains(":rule la_disequality"), "{rendered}");
    assert!(!rendered.contains(":rule hole"), "{rendered}");
    rendered
}

fn assert_carcara_valid(case: &str, rendered: &str) {
    let (problem, document) = refutation(rendered);
    if let Some(verdict) = carcara_verdict(case, &problem, &document) {
        assert_eq!(
            verdict.lines().next(),
            Some("valid"),
            "{case}: {verdict}\n{document}"
        );
    }
}

/// The `u64` frame fixture's split: the guard `(= 1 q)` runs AGAINST the
/// branch form, so `(<= 1 q)` excludes the FIRST branch. At c57bd8481 the
/// lowering printed `(cl (<= 1 q) (<= 2 q))`, false at `q = 0`, and the step
/// was holed.
#[test]
fn a_reversed_guard_pairs_each_order_with_the_branch_it_excludes() {
    let mut terms = TermStore::new();
    let (clause, _) = one_gap_split(&mut terms, true);
    assert_eq!(
        arith_disequality_split_primitive_guard_is_reversed(&terms, &clause),
        Some(true)
    );
    let rendered = lowered(&AlethePrinter::new(&terms), clause);
    assert!(
        rendered.contains(
            "(step t3.split (cl (or (= 1 q) (not (<= 1 q)) (not (<= q 1)))) :rule la_disequality)"
        ) && rendered.contains("(step t3.b0 (cl (<= 1 q) (<= q 0)) :rule la_generic :args (1 1))")
            && rendered
                .contains("(step t3.b1 (cl (<= q 1) (<= 2 q)) :rule la_generic :args (1 1))"),
        "{rendered}"
    );
    assert_carcara_valid("reversed", &rendered);
}

/// The forward control: `(= q 1)` keeps the historical pairing.
#[test]
fn a_forward_guard_keeps_the_forward_pairing() {
    let mut terms = TermStore::new();
    let (clause, _) = one_gap_split(&mut terms, false);
    assert_eq!(
        arith_disequality_split_primitive_guard_is_reversed(&terms, &clause),
        Some(false)
    );
    let rendered = lowered(&AlethePrinter::new(&terms), clause);
    assert!(
        rendered.contains("(step t3.b0 (cl (<= q 1) (<= 2 q)) :rule la_generic :args (1 1))"),
        "{rendered}"
    );
    assert_carcara_valid("forward", &rendered);
}

/// `(assert (not (= 1 x)))` stores `(= x 1)` and prints the authored `(= 1 x)`.
/// At c57bd8481 the lowering read the operands off the TermId and shipped
/// `(or (= 1 q) (not (<= q 1)) (not (<= 1 q)))`, which pinned carcara refuses
/// (end to end on `x`, `ay-dpll`'s `carcara_external_check/printed_split_guard.rs`:
/// "expected terms to be equal: '1' and 'x'"). The operands and the
/// orientation now follow the printed guard.
#[test]
fn an_override_that_swaps_the_guard_moves_the_lowering_onto_the_printed_operands() {
    let mut terms = TermStore::new();
    let (clause, guard) = one_gap_split(&mut terms, false);
    let mut overrides: HashMap<TermId, String> = HashMap::default();
    overrides.insert(guard, "(= 1 q)".to_string());
    let printer = AlethePrinter::new_with_overrides(&terms, Some(&overrides));
    let rendered = lowered(&printer, clause);
    assert!(
        rendered.contains(
            "(step t3.split (cl (or (= 1 q) (not (<= 1 q)) (not (<= q 1)))) :rule la_disequality)"
        ) && rendered.contains("(step t3.b0 (cl (<= 1 q) (<= q 0)) :rule la_generic :args (1 1))"),
        "{rendered}"
    );
    assert_carcara_valid("override_swapped", &rendered);
}

/// A guard printed as neither orientation of its own equality has no
/// operands the lowering may read: the step keeps the honest hole.
#[test]
fn a_guard_printed_as_another_equality_keeps_the_hole() {
    let mut terms = TermStore::new();
    let (clause, guard) = one_gap_split(&mut terms, false);
    let mut overrides: HashMap<TermId, String> = HashMap::default();
    overrides.insert(guard, "(= (+ q 0) 1)".to_string());
    let printer = AlethePrinter::new_with_overrides(&terms, Some(&overrides));
    let rendered = printer
        .format_step(&split_step(clause), ProofId(3))
        .expect("the split renders");
    assert!(!rendered.contains("la_disequality"), "{rendered}");
    assert!(rendered.ends_with(":rule hole)"), "{rendered}");
}

/// A clause whose guard is not the gap value is no split at all.
#[test]
fn a_guard_off_the_gap_is_not_lowered() {
    let mut terms = TermStore::new();
    let q = terms.mk_var("q", Sort::Int);
    let zero = terms.mk_int(BigInt::from(0));
    let two = terms.mk_int(BigInt::from(2));
    let first = raw2(&mut terms, "<=", q, zero, Sort::Bool);
    let second = raw2(&mut terms, "<=", two, q, Sort::Bool);
    // `q <= 0 ∨ q >= 2 ∨ 2 = q` is false at `q = 1`.
    let guard = raw2(&mut terms, "=", two, q, Sort::Bool);
    let clause = vec![first, second, guard];
    assert_eq!(
        arith_disequality_split_primitive_guard_is_reversed(&terms, &clause),
        None
    );
    let rendered = AlethePrinter::new(&terms)
        .format_step(&split_step(clause), ProofId(3))
        .expect("the clause renders");
    assert!(!rendered.contains("la_disequality"), "{rendered}");
}

/// The judgement replays pinned carcara's `la_disequality` shape over the
/// bytes; the refused texts are the c57bd8481 shape and its relatives.
#[test]
fn printed_la_disequality_requires_identical_operand_copies() {
    let holds = |text: &str| printed_la_disequality_holds(&[text]);
    assert!(holds("(or (= 1 q) (not (<= 1 q)) (not (<= q 1)))"));
    assert!(holds(
        "(or (= (+ a b) c) (not (<= (+ a b) c)) (not (<= c (+ a b))))"
    ));
    assert!(!holds("(or (= 1 q) (not (<= q 1)) (not (<= 1 q)))"));
    assert!(!holds("(or (= q 1) (not (<= q 1)) (not (<= q 1)))"));
    assert!(!holds("(or (= q 1) (not (< q 1)) (not (<= 1 q)))"));
    assert!(!holds("(or (= q 1) (not (<= q 1)))"));
    assert!(!printed_la_disequality_holds(&[
        "(= q 1)",
        "(not (<= q 1))",
        "(not (<= 1 q))"
    ]));
}

/// A step that ships a malformed `la_disequality` is holed over its own
/// clause, and pinned carcara refuses the text the judgement refuses.
#[test]
fn a_step_shipping_a_malformed_la_disequality_is_holed() {
    let mut terms = TermStore::new();
    let (clause, _) = one_gap_split(&mut terms, false);
    let printer = AlethePrinter::new(&terms);
    let step = split_step(clause);
    let lowered = printer.format_step(&step, ProofId(3)).expect("renders");
    let malformed = lowered.replace(
        "(or (= q 1) (not (<= q 1)) (not (<= 1 q)))",
        "(or (= q 1) (not (<= 1 q)) (not (<= q 1)))",
    );
    assert_ne!(malformed, lowered, "the fixture must plant the defect");
    let judged = printer
        .judge_printed_la_disequality(&step, ProofId(3), malformed.clone())
        .expect("a step with a clause is holed, not refused");
    assert_eq!(
        judged,
        "(step t3 (cl (<= q 0) (<= 2 q) (= q 1)) :rule hole)"
    );
    let (problem, document) = refutation(&malformed);
    if let Some(verdict) = carcara_verdict("malformed", &problem, &document) {
        assert_eq!(
            verdict.lines().next(),
            Some("invalid"),
            "{verdict}\n{document}"
        );
    }
}

/// The chokepoint is wired into `format_step`: a producer `la_disequality`
/// step whose equality prints through an override that swaps its operands is
/// holed over its own clause, never shipped malformed.
#[test]
fn format_step_holes_a_producer_la_disequality_whose_equality_prints_swapped() {
    let mut terms = TermStore::new();
    let q = terms.mk_var("q", Sort::Int);
    let one = terms.mk_int(BigInt::from(1));
    let eq = raw2(&mut terms, "=", q, one, Sort::Bool);
    let le_f = raw2(&mut terms, "<=", q, one, Sort::Bool);
    let le_r = raw2(&mut terms, "<=", one, q, Sort::Bool);
    let nf = terms.mk_not_raw(le_f);
    let nr = terms.mk_not_raw(le_r);
    let packed = terms.mk_app(Symbol::named("or"), [eq, nf, nr], Sort::Bool);
    let step = ProofStep::Step {
        rule: ay_core::AletheRule::LaDisequality,
        clause: vec![packed],
        premises: vec![],
        args: vec![],
    };
    assert_eq!(
        AlethePrinter::new(&terms)
            .format_step(&step, ProofId(3))
            .expect("renders"),
        "(step t3 (cl (or (= q 1) (not (<= q 1)) (not (<= 1 q)))) :rule la_disequality)"
    );
    let mut overrides: HashMap<TermId, String> = HashMap::default();
    overrides.insert(eq, "(= 1 q)".to_string());
    let printer = AlethePrinter::new_with_overrides(&terms, Some(&overrides));
    assert_eq!(
        printer.format_step(&step, ProofId(3)).expect("renders"),
        format!(
            "(step t3 (cl (or (= 1 q) (not (<= q 1)) (not (<= 1 q)))) :rule {})",
            ay_core::UNPROVED_STEP_RULE
        )
    );
}
