// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use ay_core::{Sort, Symbol, TermStore};

const GATE: &str = "(not (and p SOURCE q))";

/// `(forall ((binder (_ BitVec 8))) (or (= (g binder) x) (not (bvult binder n))))`,
/// the canonical projection of the authored guarded universal.
fn canonical_universal(terms: &mut TermStore, binder: &str) -> TermId {
    let bound = terms.mk_var(binder, Sort::bitvec(8));
    let n = terms.mk_var("n", Sort::bitvec(8));
    let x = terms.mk_var("x", Sort::bitvec(8));
    let applied = terms.mk_app(Symbol::named("g"), vec![bound], Sort::bitvec(8));
    let equality = terms.mk_app(Symbol::named("="), vec![applied, x], Sort::Bool);
    let guard = terms.mk_app(Symbol::named("bvult"), vec![bound, n], Sort::Bool);
    let negated_guard = terms.mk_not_raw(guard);
    let body = terms.mk_app(
        Symbol::named("or"),
        vec![equality, negated_guard],
        Sort::Bool,
    );
    terms.mk_forall(vec![(binder.to_string(), Sort::bitvec(8))], body)
}

fn bridge(terms: &TermStore, universal: TermId, source: &str) -> Option<String> {
    let printer = AlethePrinter::new(terms);
    let target = printer.format_term(universal);
    printer
        .quantified_body_and_pos_bridge(ProofId(3), universal, 1, GATE, source, &target)
        .expect("within budget")
}

#[test]
fn respelled_binder_implication_body_derives_under_bind() {
    let mut terms = TermStore::new();
    let universal = canonical_universal(&mut terms, "i_1");
    let source = "(forall ((i (_ BitVec 8))) (=> (bvult i n) (= (g i) x)))";
    let text = bridge(&terms, universal, source).expect("an implication body under bind");
    let target = "(forall ((i_1 (_ BitVec 8))) (or (= (g i_1) x) (not (bvult i_1 n))))";
    let renamed = "(forall ((i_1 (_ BitVec 8))) (=> (bvult i_1 n) (= (g i_1) x)))";
    let lines: Vec<&str> = text.lines().collect();
    assert_eq!(
        lines.first().copied(),
        Some(format!("(step t3.qa (cl {GATE} {source}) :rule and_pos :args (1))").as_str())
    );
    for expected in [
        format!("(step t3.qr (cl (= {source} {renamed})) :rule refl)"),
        "(anchor :step t3.qb :args ((i_1 (_ BitVec 8))))".to_string(),
        format!("(step t3.qb (cl (= {renamed} {target})) :rule bind)"),
        format!("(step t3.qt (cl (= {source} {target})) :rule trans :premises (t3.qr t3.qb))"),
    ] {
        assert!(lines.contains(&expected.as_str()), "{expected}\n{text}");
    }
    // The subproof's last step concludes exactly the two bodies `bind` reads.
    let anchor = lines
        .iter()
        .position(|line| line.starts_with("(anchor :step t3.qb"))
        .expect("anchor");
    let bind = lines
        .iter()
        .position(|line| line.starts_with("(step t3.qb "))
        .expect("bind");
    assert!(lines[bind - 1].starts_with(
        "(step t3.qd (cl (= (=> (bvult i_1 n) (= (g i_1) x)) (or (= (g i_1) x) (not (bvult i_1 n))))) "
    ));
    assert!(anchor + 1 < bind);
    assert_eq!(
        lines.last().copied(),
        Some(
            format!("(step t3 (cl {GATE} {target}) :rule resolution :premises (t3.qa t3.qc))")
                .as_str()
        )
    );
}

#[test]
fn shared_binder_names_bind_without_a_respelling() {
    let mut terms = TermStore::new();
    let universal = canonical_universal(&mut terms, "i");
    let source = "(forall ((i (_ BitVec 8))) (=> (bvult i n) (= (g i) x)))";
    let text = bridge(&terms, universal, source).expect("an implication body under bind");
    assert!(!text.contains(":rule refl)\n(anchor"), "{text}");
    assert!(!text.contains(":rule trans :premises (t3.qr"), "{text}");
    assert!(
        text.contains("(anchor :step t3.qt :args ((i (_ BitVec 8))))"),
        "{text}"
    );
    assert!(text.contains(&format!(
        "(step t3.qt (cl (= {source} (forall ((i (_ BitVec 8))) (or (= (g i) x) (not (bvult i n)))))) :rule bind)"
    )));
}

/// NEGATIVE TWIN: every other body, a capturing respelling, another sort and
/// a non-quantified projection keep the caller's refusal.
#[test]
fn unrelated_bodies_captures_and_sorts_decline() {
    let mut terms = TermStore::new();
    let universal = canonical_universal(&mut terms, "i_1");
    for source in [
        // The consequent names another constant.
        "(forall ((i (_ BitVec 8))) (=> (bvult i n) (= (g i) n)))",
        // The guard under the wrong polarity.
        "(forall ((i (_ BitVec 8))) (=> (not (bvult i n)) (= (g i) x)))",
        // Respelling `i` as `i_1` would capture the free `i_1`, and the
        // captured text is exactly the canonical body's implication.
        "(forall ((i (_ BitVec 8))) (=> (bvult i_1 n) (= (g i) x)))",
        // Another binder sort.
        "(forall ((i (_ BitVec 16))) (=> (bvult i n) (= (g i) x)))",
        // Two binders against one.
        "(forall ((i (_ BitVec 8)) (j (_ BitVec 8))) (=> (bvult i n) (= (g i) x)))",
        // Another quantifier.
        "(exists ((i (_ BitVec 8))) (=> (bvult i n) (= (g i) x)))",
    ] {
        assert_eq!(bridge(&terms, universal, source), None, "{source}");
    }
    let p = terms.mk_var("p", Sort::Bool);
    let printer = AlethePrinter::new(&terms);
    assert_eq!(
        printer
            .quantified_body_and_pos_bridge(
                ProofId(3),
                p,
                1,
                GATE,
                "(forall ((i (_ BitVec 8))) (=> (bvult i n) (= (g i) x)))",
                "p",
            )
            .expect("within budget"),
        None
    );
}

#[test]
fn an_exhausted_budget_refuses_instead_of_rendering() {
    let mut terms = TermStore::new();
    let universal = canonical_universal(&mut terms, "i_1");
    let printer = AlethePrinter::new_with_overrides_and_budget(&terms, None, Some(1));
    let target = printer.format_term(universal);
    assert!(printer
        .quantified_body_and_pos_bridge(
            ProofId(3),
            universal,
            1,
            GATE,
            "(forall ((i (_ BitVec 8))) (=> (bvult i n) (= (g i) x)))",
            &target,
        )
        .is_err());
}

#[test]
fn respelling_touches_symbols_only() {
    let renames = vec![
        ("i".to_string(), "j".to_string()),
        ("j".to_string(), "i".to_string()),
    ];
    assert_eq!(
        rename_symbols(r#"(f i |i| "i ""i""" |a\|i| (g j) ij)"#, &renames).as_deref(),
        Some(r#"(f j j "i ""i""" |a\|i| (g i) ij)"#)
    );
    assert_eq!(rename_symbols("(f \"i)", &renames), None);
    assert_eq!(rename_symbols("(f |i)", &renames), None);
}

/// The whole `and_pos` step for `(and guard UNIVERSAL)` whose root prints as
/// `authored`.
fn project(authored: &str) -> Result<String, AlethePrintError> {
    use ay_core::kani_compat::DetHashMap;
    use ay_core::{AletheRule, ProofStep};
    let mut terms = TermStore::new();
    let universal = canonical_universal(&mut terms, "i_1");
    let guard = terms.mk_var("guard", Sort::Bool);
    let source = terms.mk_app(Symbol::named("and"), vec![guard, universal], Sort::Bool);
    let gate = terms.mk_not_raw(source);
    let mut overrides = DetHashMap::default();
    overrides.insert(source, authored.to_string());
    let printer = AlethePrinter::new_with_overrides(&terms, Some(&overrides));
    let step = ProofStep::Step {
        rule: AletheRule::AndPos(1),
        clause: vec![gate, universal],
        premises: Vec::new(),
        args: vec![source],
    };
    printer.format_step(&step, ProofId(3))
}

#[test]
fn a_flat_and_pos_over_a_rewritten_universal_projects_through_bind() {
    let authored = "(and guard (forall ((i (_ BitVec 8))) (=> (bvult i n) (= (g i) x))))";
    let printed = project(authored).expect("the bodies are related by a checked schema");
    assert!(printed.contains("\n(anchor :step t3.qb :args ((i_1 (_ BitVec 8))))\n"));
    assert!(printed.ends_with(&format!(
        "(step t3 (cl (not {authored}) (forall ((i_1 (_ BitVec 8))) (or (= (g i_1) x) (not (bvult i_1 n))))) :rule resolution :premises (t3.qa t3.qc))"
    )));
}

/// NEGATIVE TWIN: the same step over a universal whose body is another
/// formula keeps the export refusal it had before the bridge existed.
#[test]
fn a_flat_and_pos_over_an_unrelated_universal_still_refuses() {
    for authored in [
        "(and guard (forall ((i (_ BitVec 8))) (=> (bvult i n) (= (g i) n))))",
        "(and guard (forall ((i (_ BitVec 8))) (=> (bvult i_1 n) (= (g i) x))))",
    ] {
        let refused = project(authored).expect_err(authored);
        assert!(
            refused
                .to_string()
                .contains("and_pos indexed conjunct is absent from its effective source"),
            "{authored}: {refused}"
        );
    }
}
