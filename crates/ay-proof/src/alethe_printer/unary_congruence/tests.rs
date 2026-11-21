// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use ay_core::{FarkasAnnotation, Sort, Symbol, TheoryLemmaKind};
use std::process::Command;

fn eq(terms: &mut TermStore, a: TermId, b: TermId) -> TermId {
    terms.mk_app(Symbol::named("="), [a, b], Sort::Bool)
}

fn step(clause: &[TermId]) -> ProofStep {
    ProofStep::TheoryLemma {
        theory: "UFLIA".into(),
        clause: clause.to_vec(),
        // This is the actual arithmetic producer's annotation. It is not
        // consumed by this independent congruence proof.
        farkas: Some(FarkasAnnotation::from_ints(&[1, 1])),
        kind: TheoryLemmaKind::LiaGeneric,
        lia: None,
    }
}

fn carcara(case: &str, problem: &str, proof: &str) -> Option<String> {
    ay_core::pinned_carcara::pinned_carcara_can_judge(problem, proof)
        .expect("independent checker can judge this pair");
    if !Command::new("carcara")
        .arg("--version")
        .output()
        .is_ok_and(|out| out.status.success())
    {
        eprintln!("carcara unavailable: skipping external unary congruence control {case}");
        return None;
    }
    let dir =
        std::env::temp_dir().join(format!("ay-unary-congruence-{}-{case}", std::process::id()));
    std::fs::create_dir_all(&dir).expect("temporary checker directory");
    std::fs::write(dir.join("p.smt2"), problem).expect("problem");
    std::fs::write(dir.join("p.alethe"), proof).expect("proof");
    let out = Command::new("carcara")
        .args(["check", "--expand-let-bindings", "--"])
        .arg(dir.join("p.alethe"))
        .arg(dir.join("p.smt2"))
        .output()
        .expect("check congruence proof");
    let _ = std::fs::remove_dir_all(dir);
    Some(format!(
        "{}\n{}",
        String::from_utf8_lossy(&out.stdout),
        String::from_utf8_lossy(&out.stderr)
    ))
}

#[test]
fn checked_unary_congruence_preserves_clause_order_and_reversed_guard() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::Int);
    let b = terms.mk_var("b", Sort::Int);
    let fa = terms.mk_app(Symbol::named("f"), [a], Sort::Int);
    let fb = terms.mk_app(Symbol::named("f"), [b], Sort::Int);
    let goal = eq(&mut terms, fa, fb);
    for (orientation, (left, right)) in [(a, b), (b, a)].into_iter().enumerate() {
        let guard = eq(&mut terms, left, right);
        let negative = terms.mk_not_raw(guard);
        for (order, clause) in [[negative, goal], [goal, negative]].into_iter().enumerate() {
            let printer = AlethePrinter::new(&terms);
            let rendered = printer
                .format_step(&step(&clause), ProofId(3))
                .expect("export");
            assert!(rendered.contains(":rule eq_congruent"), "{rendered}");
            assert!(!rendered.contains(":rule hole"), "{rendered}");
            assert!(checked_unary_congruence_lowering_supported(
                &terms,
                &TheoryLemmaKind::LiaGeneric,
                &clause,
                None
            ));
            assert!(rendered
                .lines()
                .last()
                .expect("last step")
                .starts_with(&format!("(step t3 {} ", printer.format_clause(&clause))));
            let guard = printer.format_term(guard);
            let goal = printer.format_term(goal);
            let problem = format!(
                "(set-logic QF_UFLIA)\n(declare-const a Int)\n(declare-const b Int)\n\
                 (declare-fun f (Int) Int)\n(assert {guard})\n(assert (not {goal}))\n(check-sat)\n"
            );
            let proof = format!(
                "(assume h0 {guard})\n(assume h1 (not {goal}))\n{rendered}\n\
                 (step t4 (cl) :rule resolution :premises (h0 h1 t3))\n"
            );
            if let Some(out) = carcara(&format!("valid-{orientation}-{order}"), &problem, &proof) {
                assert_eq!(out.lines().next(), Some("valid"), "{out}\n{proof}");
            }
        }
    }
}

#[test]
fn checked_unary_congruence_refuses_forged_functions_arguments_and_sorts() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::Int);
    let b = terms.mk_var("b", Sort::Int);
    let c = terms.mk_var("c", Sort::Int);
    let fa = terms.mk_app(Symbol::named("f"), [a], Sort::Int);
    let fb = terms.mk_app(Symbol::named("f"), [b], Sort::Int);
    let fc = terms.mk_app(Symbol::named("f"), [c], Sort::Int);
    let gb = terms.mk_app(Symbol::named("g"), [b], Sort::Int);
    let wrong_sort = terms.mk_app(Symbol::named("f"), [b], Sort::Real);
    let guard = eq(&mut terms, b, a);
    let negative = terms.mk_not_raw(guard);
    let wrong_guard = eq(&mut terms, c, a);
    let wrong_guard = terms.mk_not_raw(wrong_guard);
    let valid_goal = eq(&mut terms, fa, fb);
    let bad_head = eq(&mut terms, fa, gb);
    let bad_argument = eq(&mut terms, fa, fc);
    let bad_sort = eq(&mut terms, fa, wrong_sort);
    for clause in [
        [bad_head, negative],
        [bad_argument, negative],
        [bad_sort, negative],
        [valid_goal, wrong_guard],
        [valid_goal, guard],
    ] {
        assert!(!checked_unary_congruence_lowering_supported(
            &terms,
            &TheoryLemmaKind::LiaGeneric,
            &clause,
            None
        ));
    }
    assert!(!checked_unary_congruence_lowering_supported(
        &terms,
        &TheoryLemmaKind::Generic,
        &[valid_goal, negative],
        None
    ));
    // The independently checkable forged-head control fails the exact rule
    // rather than merely missing a producer annotation.
    let proof = "(assume h0 (= a b))\n(assume h1 (not (= (f a) (g b))))\n\
        (step t3 (cl (not (= a b)) (= (f a) (g b))) :rule eq_congruent)\n\
        (step t4 (cl) :rule resolution :premises (h0 h1 t3))\n";
    let problem = "(set-logic QF_UFLIA)\n(declare-const a Int)\n(declare-const b Int)\n\
        (declare-fun f (Int) Int)\n(declare-fun g (Int) Int)\n\
        (assert (= a b))\n(assert (not (= (f a) (g b))))\n(check-sat)\n";
    if let Some(out) = carcara("forged-head", problem, proof) {
        assert_eq!(out.lines().next(), Some("invalid"), "{out}");
    }
}

#[test]
fn checked_unary_congruence_rechecks_effective_surface() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::Int);
    let b = terms.mk_var("b", Sort::Int);
    let fa = terms.mk_app(Symbol::named("f"), [a], Sort::Int);
    let fb = terms.mk_app(Symbol::named("f"), [b], Sort::Int);
    let goal = eq(&mut terms, fa, fb);
    let guard = eq(&mut terms, b, a);
    let negative = terms.mk_not_raw(guard);
    let clause = [goal, negative];
    for (term, replacement) in [
        (goal, "(= (f a) (g b))"),
        (goal, "(= (f a) (f c))"),
        (negative, "(not (= c a))"),
    ] {
        let mut overrides = HashMap::default();
        overrides.insert(term, replacement.to_owned());
        assert!(!checked_unary_congruence_lowering_supported(
            &terms,
            &TheoryLemmaKind::LiaGeneric,
            &clause,
            Some(&overrides)
        ));
    }
}
