// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

fn fixture(residue: i64) -> (Executor, Proof, Vec<TermId>) {
    let mut exec = Executor::new();
    exec.set_produce_proofs(true);
    let t = &mut exec.ctx.terms;
    let x = t.mk_var("subset_x", Sort::Int);
    let map_sort = Sort::Uninterpreted("SubsetMapping".to_owned());
    let map = t.mk_var("subset_map", map_sort.clone());
    let frame = t.mk_var("subset_frame", map_sort);
    let zero = t.mk_int(0.into());
    let one = t.mk_int(1.into());
    let two = t.mk_int(2.into());
    let minus_two = t.mk_int((-2).into());
    let residue = t.mk_int(residue.into());
    let x2 = t.mk_app(Symbol::named("+"), [x, two], Sort::Int);
    let q0 = t.mk_app(Symbol::named("subset_q"), [x, two], Sort::Int);
    let q2 = t.mk_app(Symbol::named("subset_q"), [x2, two], Sort::Int);
    let qzero = t.mk_app(Symbol::named("subset_q"), [zero, two], Sort::Int);
    let n0 = t.mk_app(Symbol::named("*"), [q0, minus_two], Sort::Int);
    let n2 = t.mk_app(Symbol::named("*"), [q2, minus_two], Sort::Int);
    let nz = t.mk_app(Symbol::named("*"), [qzero, minus_two], Sort::Int);
    let r0 = t.mk_app(Symbol::named("+"), [x, n0], Sort::Int);
    let r2 = t.mk_app(Symbol::named("+"), [x, n2, two], Sort::Int);
    let get = t.mk_app(Symbol::named("subset_get"), [map, x2], Sort::Int);
    let framed_get = t.mk_app(Symbol::named("subset_get"), [frame, x2], Sort::Int);
    let next = t.mk_app(Symbol::named("+"), [qzero, one], Sort::Int);
    let original = [
        t.mk_eq(r2, residue),
        t.mk_eq(zero, get),
        t.mk_app(Symbol::named("<="), [zero, nz], Sort::Bool),
        t.mk_eq(zero, framed_get),
        t.mk_eq(zero, r0),
        t.mk_app(Symbol::named("<="), [next, zero], Sort::Bool),
    ];
    let mut clause: Vec<_> = original[..5]
        .iter()
        .map(|&term| t.mk_not_raw(term))
        .collect();
    clause.push(original[5]);
    let mut proof = Proof::new();
    let mut tail = proof.add_rule_step(AletheRule::Trust, clause.clone(), vec![], vec![]);
    let mut residual = clause.clone();
    let roots: Vec<_> = clause
        .iter()
        .map(|&term| match t.get(term) {
            TermData::Not(inner) => *inner,
            _ => t.mk_not_raw(term),
        })
        .collect();
    for (&literal, &root) in clause.iter().zip(&roots) {
        let premise = proof.add_assume(root, None);
        residual.remove(0);
        tail = proof.add_resolution(residual.clone(), literal, tail, premise);
    }
    (exec, proof, roots)
}

fn problem(exec: &Executor, roots: &[TermId]) -> String {
    let mut text = "(set-logic QF_UFLIA)\n(declare-sort SubsetMapping 0)\n(declare-const subset_x Int)\n(declare-const subset_map SubsetMapping)\n(declare-const subset_frame SubsetMapping)\n(declare-fun subset_q (Int Int) Int)\n(declare-fun subset_get (SubsetMapping Int) Int)\n".to_owned();
    for &root in roots {
        text.push_str(&format!(
            "(assert {})\n",
            ay_proof::format_term_alethe(&exec.ctx.terms, root)
        ));
    }
    text.push_str("(check-sat)\n");
    text
}

#[test]
fn native_ite_clausification_captured_six_literal_integer_subset_whole_and_forgery() {
    let (mut exec, mut proof, roots) = fixture(-1);
    begin(&mut exec, &roots, true);
    assert!(exec.replace_with_checked_small_integer_leaves(&mut proof));
    assert!(proof.steps.iter().any(|s| matches!(
        s,
        ProofStep::Step {
            rule: AletheRule::Weakening,
            ..
        }
    )));
    assert!(proof.steps.iter().any(|s| matches!(
        s,
        ProofStep::Step {
            rule: AletheRule::Reordering,
            ..
        }
    )));
    assert!(ay_proof::validate_reachable_assumes_in_problem_scope(&proof, &roots).is_ok());
    let wire = ay_proof::try_export_alethe_with_problem_scope_and_overrides(
        &proof,
        &exec.ctx.terms,
        &roots,
        None,
    )
    .unwrap();
    let text = problem(&exec, &roots);
    assert_eq!(
        external_check("native-six-int-subset", &text, &wire)
            .lines()
            .last(),
        Some("valid")
    );
    let (other, _, changed_roots) = fixture(0);
    let forged = external_check(
        "forged-six-int-subset",
        &problem(&other, &changed_roots),
        &wire,
    );
    assert!(forged.contains("invalid"), "{forged}");
    assert!(
        forged.contains("rule 'assume'")
            && forged.contains("could not match term to any of the original problem premises"),
        "{forged}"
    );
}

#[test]
fn native_ite_clausification_integer_subset_preserves_sat_scope_and_shared_stop() {
    for mutation in 0..3 {
        let (mut exec, mut proof, mut roots) = fixture(if mutation == 0 { 0 } else { -1 });
        if mutation == 1 {
            roots.remove(0);
        }
        begin(&mut exec, &roots, true);
        if mutation == 2 {
            exec.set_interrupt(std::sync::Arc::new(std::sync::atomic::AtomicBool::new(
                true,
            )));
        }
        let original = proof.clone();
        assert!(
            !exec.replace_with_checked_small_integer_leaves(&mut proof),
            "mutation {mutation}"
        );
        assert_eq!(proof, original);
    }
}
