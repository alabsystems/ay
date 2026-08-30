// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Let-bridge boundary barriers for derived resolution literals.

use crate::alethe_printer::AlethePrinter;
use crate::try_export_alethe_with_problem_scope_and_overrides;
use ay_core::kani_compat::DetHashMap;
use ay_core::{Proof, Sort, Symbol, TermId, TermStore};

#[test]
fn binary_resolution_uses_the_eliminated_complement_of_a_let_assumption() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let equality = terms.mk_app(Symbol::named("="), vec![x, x], Sort::Bool);
    let disequality = terms.mk_not_raw(equality);

    let let_surface = "(let ((?v_0 x)) (= ?v_0 ?v_0))";
    let mut overrides: DetHashMap<TermId, String> = DetHashMap::default();
    overrides.insert(equality, let_surface.to_string());
    // This independent outer override caused the QF_AX failure: after the
    // positive assumption was let-eliminated, its derived negative complement
    // still printed the authored binder and no longer cancelled.
    overrides.insert(disequality, format!("(not {let_surface})"));

    let mut proof = Proof::new();
    let positive = proof.add_assume(equality, None);
    let negative = proof.add_theory_lemma("test", vec![disequality]);
    proof.add_resolution(Vec::new(), equality, positive, negative);

    let output = try_export_alethe_with_problem_scope_and_overrides(
        &proof,
        &terms,
        &[equality],
        Some(&overrides),
    )
    .expect("the let bridge must keep downstream resolution syntactic");

    assert!(
        output.contains(&format!("(assume t0.a {let_surface})")),
        "the original assumption must remain source-exact:\n{output}"
    );
    assert!(
        output.contains("(step t1 (cl (not (= x x))) :rule hole)"),
        "the derived complement must use the eliminated spelling:\n{output}"
    );
    assert!(
        output.contains("(step t2 (cl) :rule resolution :premises (t0 t1))"),
        "the final resolution must cancel exact printed complements:\n{output}"
    );

    let probe = AlethePrinter::new_with_overrides(&terms, Some(&overrides));
    probe.prepare_proof(&proof).unwrap();
    probe
        .format_step(proof.get_step(positive).unwrap(), positive)
        .unwrap();
    let positive_work = probe.work_used();
    assert!(positive_work > 0);
    let bounded = AlethePrinter::new_with_overrides_and_budget(
        &terms,
        Some(&overrides),
        Some(positive_work - 1),
    );
    bounded.prepare_proof(&proof).unwrap();
    bounded
        .format_step(proof.get_step(positive).unwrap(), positive)
        .unwrap();
    assert!(bounded.work_budget_exhausted());
    let exhausted_work = bounded.work_used();
    let discarded = bounded
        .format_step(proof.get_step(negative).unwrap(), negative)
        .unwrap();
    assert!(discarded.contains("@a2b_emission_budget_exhausted"));
    assert_eq!(bounded.work_used(), exhausted_work);
}
