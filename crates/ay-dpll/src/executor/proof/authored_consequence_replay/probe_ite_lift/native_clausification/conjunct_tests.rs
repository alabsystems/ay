// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

#[test]
fn native_ite_clausification_integer_bound_clauses_whole_carcara() {
    for three_bounds in [false, true] {
        let mut exec = Executor::new();
        exec.set_produce_proofs(true);
        let t = &mut exec.ctx.terms;
        let x = t.mk_var("cut_x", Sort::Int);
        let one = t.mk_int(1.into());
        let two = t.mk_int(2.into());
        let minus_two = t.mk_int((-2).into());
        let x2 = t.mk_app(Symbol::named("+"), [x, two], Sort::Int);
        let q0 = t.mk_app(Symbol::named("cut_q"), [x, two], Sort::Int);
        let q2 = t.mk_app(Symbol::named("cut_q"), [x2, two], Sort::Int);
        let n0 = t.mk_app(Symbol::named("*"), [q0, minus_two], Sort::Int);
        let n2 = t.mk_app(Symbol::named("*"), [q2, minus_two], Sort::Int);
        let r0 = t.mk_app(Symbol::named("+"), [x, n0], Sort::Int);
        let r2 = t.mk_app(Symbol::named("+"), [x, n2], Sort::Int);
        let first = t.mk_app(Symbol::named("<="), [r0, r2], Sort::Bool);
        let next = t.mk_app(Symbol::named("+"), [q0, one], Sort::Int);
        let second = t.mk_app(Symbol::named("<="), [next, q2], Sort::Bool);
        let clause = if three_bounds {
            let shifted = t.mk_app(Symbol::named("+"), [x2, n2], Sort::Int);
            let upper = t.mk_app(Symbol::named("<"), [shifted, two], Sort::Bool);
            let minus_one = t.mk_int((-1).into());
            let last = t.mk_app(Symbol::named("<="), [r0, minus_one], Sort::Bool);
            vec![t.mk_not_raw(first), t.mk_not_raw(upper), last]
        } else {
            vec![first, second]
        };
        let roots: Vec<_> = clause
            .iter()
            .map(|&literal| match t.get(literal) {
                TermData::Not(inner) => *inner,
                _ => t.mk_not_raw(literal),
            })
            .collect();
        let mut proof = Proof::new();
        let mut tail = proof.add_rule_step(AletheRule::Trust, clause.clone(), vec![], vec![]);
        let mut residual = clause.clone();
        for (&literal, &root) in clause.iter().zip(&roots) {
            let assumption = proof.add_assume(root, None);
            residual.remove(0);
            tail = proof.add_resolution(residual.clone(), literal, tail, assumption);
        }
        begin(&mut exec, &roots, true);
        assert!(exec.replace_with_checked_small_integer_leaves(&mut proof));
        let wire = ay_proof::try_export_alethe_with_problem_scope_and_overrides(
            &proof,
            &exec.ctx.terms,
            &roots,
            None,
        )
        .unwrap();
        let mut problem =
            "(set-logic QF_UFLIA)\n(declare-const cut_x Int)\n(declare-fun cut_q (Int Int) Int)\n"
                .to_owned();
        for root in roots {
            problem.push_str(&format!(
                "(assert {})\n",
                ay_proof::format_term_alethe(&exec.ctx.terms, root)
            ));
        }
        problem.push_str("(check-sat)\n");
        assert_eq!(
            external_check(
                if three_bounds {
                    "native-three-int-bounds"
                } else {
                    "native-two-int-cover"
                },
                &problem,
                &wire
            )
            .lines()
            .last(),
            Some("valid")
        );
    }
}

fn conjunct_fixture(exec: &mut Executor) -> (TermId, TermId) {
    let t = &mut exec.ctx.terms;
    let x = t.mk_var("conjunct_x", Sort::Int);
    let zero = t.mk_int(0.into());
    let one = t.mk_int(1.into());
    let p = t.mk_eq(x, one);
    let q = t.mk_eq(x, zero);
    let not_q = t.mk_not_raw(q);
    let target = t.mk_app(Symbol::named("or"), [p, not_q], Sort::Bool);
    let mut children = Vec::new();
    for i in 0..84 {
        children.push(t.mk_var(format!("conjunct_{i}"), Sort::Bool));
    }
    children[79] = target;
    let inner = t.mk_app(Symbol::named("and"), children, Sort::Bool);
    let root = t.mk_app(Symbol::named("and"), [inner, p], Sort::Bool);
    (root, target)
}

#[test]
fn native_ite_clausification_projects_large_exact_native_conjunction_without_ite() {
    let mut exec = Executor::new();
    exec.set_produce_proofs(true);
    let (root, target) = conjunct_fixture(&mut exec);
    let (mut proof, negated) = closed_trust(&mut exec, target);
    begin(&mut exec, &[root, negated, root], true);
    assert!(
        select_ite_sources(&exec, &[root, negated, root], &RepairBudget::new(&exec))
            .unwrap()
            .is_empty()
    );
    assert!(exec.try_rebuild_native_ite_clausification(&mut proof));
    assert!(exec
        .check_proof_strict_with_datatypes(&proof)
        .unwrap()
        .is_complete());
    assert!(
        ay_proof::validate_reachable_assumes_in_problem_scope(&proof, &[root, negated]).is_ok()
    );
    assert!(proof.steps.iter().any(|s| matches!(
        s,
        ProofStep::Step {
            rule: AletheRule::AndPos(79),
            ..
        }
    )));
    assert!(!proof
        .steps
        .iter()
        .any(|s| matches!(s, ProofStep::Assume(t) if *t == target)));
    let wire = ay_proof::try_export_alethe_with_problem_scope_and_overrides(
        &proof,
        &exec.ctx.terms,
        &[root, negated],
        None,
    )
    .unwrap();
    let mut problem = "(set-logic QF_LIA)\n(declare-const conjunct_x Int)\n".to_owned();
    for i in 0..84 {
        problem.push_str(&format!("(declare-const conjunct_{i} Bool)\n"));
    }
    for term in [root, negated] {
        problem.push_str(&format!(
            "(assert {})\n",
            ay_proof::format_term_alethe(&exec.ctx.terms, term)
        ));
    }
    problem.push_str("(check-sat)\n");
    assert_eq!(
        external_check("native-conjunct-exact", &problem, &wire)
            .lines()
            .last(),
        Some("valid")
    );
}

#[test]
fn native_ite_clausification_conjunct_projection_refuses_foreign_polarity_text_and_epoch() {
    for mutation in 0..5 {
        let mut exec = Executor::new();
        exec.set_produce_proofs(true);
        let (root, target) = conjunct_fixture(&mut exec);
        let (mut proof, negated) = closed_trust(&mut exec, target);
        let original = proof.clone();
        let source = match mutation {
            0 => exec.ctx.terms.mk_var("foreign_conjunction", Sort::Bool),
            1 => exec.ctx.terms.mk_not_raw(root),
            _ => root,
        };
        begin(&mut exec, &[source, negated], mutation != 2);
        if mutation == 3 {
            exec.begin_public_solve(false);
        }
        if mutation == 4 {
            exec.set_interrupt(std::sync::Arc::new(std::sync::atomic::AtomicBool::new(
                true,
            )));
        }
        assert!(
            !exec.try_rebuild_native_ite_clausification(&mut proof),
            "mutation {mutation}"
        );
        assert_eq!(proof, original);
    }
}

#[test]
fn native_ite_clausification_conjunct_projection_shares_budget_and_rejects_malformed_parent() {
    let mut exec = Executor::new();
    let (root, target) = conjunct_fixture(&mut exec);
    let mut remaining = MAX_NATIVE_TERM_OCCURRENCES;
    let mut path = Vec::new();
    let budget = RepairBudget::new(&exec);
    budget.set_remaining(1, 1024);
    assert!(
        conjunct_leaves::find_path(&exec, root, target, &mut path, &mut remaining, &budget)
            .is_none()
    );
    assert!(!budget.pay(0, 0));
    let int = exec.ctx.terms.mk_int(0.into());
    let malformed = exec
        .ctx
        .terms
        .mk_app(Symbol::named("and"), [target, int], Sort::Bool);
    let budget = RepairBudget::new(&exec);
    let mut remaining = MAX_NATIVE_TERM_OCCURRENCES;
    assert!(conjunct_leaves::find_path(
        &exec,
        malformed,
        target,
        &mut path,
        &mut remaining,
        &budget
    )
    .is_none());
}
