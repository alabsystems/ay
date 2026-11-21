// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The original 1411 -> raw Boolean ITE 241 -> working unit 1412 route.
//! Raw children are derived with AndPos, never installed as new assumptions.

use super::*;

struct BooleanConjunct {
    exec: Executor,
    root: TermId,
    sources: Vec<TermId>,
    targets: Vec<TermId>,
    irrelevant: TermId,
}

fn fixture() -> BooleanConjunct {
    let mut exec = Executor::new();
    exec.set_produce_proofs(true);
    exec.execute_all(&ay_frontend::parse(
        "(declare-sort Mapping 0)(declare-fun branch_q (Int Int) Int)(declare-fun branch_get (Mapping Int) Int)",
    ).unwrap()).unwrap();
    let t = &mut exec.ctx.terms;
    let x = t.mk_var("branch_x", Sort::Int);
    let map = t.mk_var("branch_map", Sort::Uninterpreted("Mapping".to_owned()));
    let zero = t.mk_int(0.into());
    let one = t.mk_int(1.into());
    let two = t.mk_int(2.into());
    let minus_two = t.mk_int((-2).into());
    let mut sources = Vec::new();
    let mut targets = Vec::new();
    for offset in 0..3 {
        let offset = t.mk_int(offset.into());
        let arg = t.mk_app(Symbol::named("+"), [x, offset], Sort::Int);
        let quotient = t.mk_app(Symbol::named("branch_q"), [arg, two], Sort::Int);
        let product = t.mk_app(Symbol::named("*"), [quotient, minus_two], Sort::Int);
        let remainder = t.mk_app(Symbol::named("+"), [arg, product], Sort::Int);
        let condition = t.mk_app(Symbol::named("="), [zero, remainder], Sort::Bool);
        let value = t.mk_app(Symbol::named("branch_get"), [map, arg], Sort::Int);
        let yes = t.mk_app(Symbol::named("="), [one, value], Sort::Bool);
        let no = t.mk_app(Symbol::named("="), [zero, value], Sort::Bool);
        let source = t.mk_ite_raw(condition, yes, no);
        let not_condition = t.mk_not_raw(condition);
        // Keep both physical literal orders. This is candidate routing, not
        // authority to replace a different condition, polarity, or branch.
        targets.push(t.mk_app(Symbol::named("or"), [yes, not_condition], Sort::Bool));
        targets.push(t.mk_app(Symbol::named("or"), [condition, no], Sort::Bool));
        sources.push(source);
    }
    let mut children = (0..84)
        .map(|i| t.mk_var(format!("branch_padding_{i}"), Sort::Bool))
        .collect::<Vec<_>>();
    children[79..82].copy_from_slice(&sources);
    let inner = t.mk_app(Symbol::named("and"), children, Sort::Bool);
    let root = t.mk_app(Symbol::named("and"), [inner, t.true_term()], Sort::Bool);
    let bound = t.mk_var("irrelevant_branch_bound", Sort::Int);
    let reflexive = t.mk_app(Symbol::named("="), [bound, bound], Sort::Bool);
    let irrelevant = t.mk_forall(
        vec![("irrelevant_branch_bound".to_owned(), Sort::Int)],
        reflexive,
    );
    BooleanConjunct {
        exec,
        root,
        sources,
        targets,
        irrelevant,
    }
}

fn close_targets(exec: &mut Executor, targets: &[TermId]) -> (Proof, TermId) {
    let t = &mut exec.ctx.terms;
    let target = t.mk_app(Symbol::named("and"), targets.to_vec(), Sort::Bool);
    let negated = t.mk_not_raw(target);
    let mut proof = Proof::new();
    let mut clause = vec![target];
    clause.extend(targets.iter().map(|&term| t.mk_not_raw(term)));
    let mut tail = proof.add_rule_step(AletheRule::AndNeg, clause.clone(), vec![], vec![target]);
    for &term in targets {
        let source = proof.add_rule_step(AletheRule::Trust, vec![term], vec![], vec![]);
        clause.remove(1);
        tail = proof.add_resolution(clause.clone(), term, source, tail);
    }
    let assumption = proof.add_assume(negated, None);
    proof.add_resolution(vec![], target, tail, assumption);
    (proof, negated)
}

fn problem(exec: &Executor, roots: &[TermId]) -> String {
    let mut result = "(set-logic UFLIA)\n(declare-sort Mapping 0)\n(declare-const branch_map Mapping)\n(declare-const branch_x Int)\n(declare-fun branch_q (Int Int) Int)\n(declare-fun branch_get (Mapping Int) Int)\n".to_owned();
    for i in 0..84 {
        result.push_str(&format!("(declare-const branch_padding_{i} Bool)\n"));
    }
    for &root in roots {
        result.push_str(&format!(
            "(assert {})\n",
            ay_proof::format_term_alethe(&exec.ctx.terms, root)
        ));
    }
    result.push_str("(check-sat)\n");
    result
}

#[test]
fn native_ite_clausification_boolean_conjuncts_derive_six_clauses_whole_carcara() {
    let mut f = fixture();
    let (mut proof, negated) = close_targets(&mut f.exec, &f.targets);
    let roots = [f.irrelevant, f.root, negated, f.root];
    begin(&mut f.exec, &roots, true);
    // Actual working preprocessing replaces raw ITEs. The immutable origin
    // remains the wide conjunction, including its duplicate occurrence.
    f.exec.ctx.assertions.clear();
    f.exec.ctx.assertions.extend(f.targets.iter().copied());
    assert!(f.exec.try_rebuild_native_ite_clausification(&mut proof));
    assert!(f
        .exec
        .check_proof_strict_with_datatypes(&proof)
        .is_ok_and(|q| q.is_complete()));
    assert!(ay_proof::validate_reachable_assumes_in_problem_scope(&proof, &roots).is_ok());
    for step in &proof.steps {
        if let ProofStep::Assume(term) = step {
            assert!(roots.contains(term));
            assert!(!f.sources.contains(term));
            assert!(!f.targets.contains(term));
        }
        assert!(!matches!(
            step,
            ProofStep::Step {
                rule: AletheRule::Trust | AletheRule::Hole,
                ..
            }
        ));
    }
    assert!(proof.steps.iter().any(|s| matches!(
        s,
        ProofStep::Step {
            rule: AletheRule::AndPos(79),
            ..
        }
    )));
    assert!(proof.steps.iter().any(|s| matches!(
        s,
        ProofStep::Step {
            rule: AletheRule::ItePos2,
            ..
        }
    )));
    assert!(proof.steps.iter().any(|s| matches!(
        s,
        ProofStep::Step {
            rule: AletheRule::ItePos1,
            ..
        }
    )));
    let document = ay_proof::try_export_alethe_with_problem_scope_and_overrides(
        &proof,
        &f.exec.ctx.terms,
        &roots,
        None,
    )
    .unwrap();
    assert_eq!(
        external_check("boolean-conjunct-six", &problem(&f.exec, &roots), &document)
            .lines()
            .last(),
        Some("valid")
    );
    let not_root = f.exec.ctx.terms.mk_not_raw(f.root);
    let forged_roots = [f.irrelevant, not_root, negated, not_root];
    let output = external_check(
        "forged-boolean-conjunct-source",
        &problem(&f.exec, &forged_roots),
        &document,
    );
    assert!(
        output.contains("rule 'assume'")
            && output.contains("could not match term to any of the original problem premises"),
        "{output}"
    );
}

#[test]
fn native_ite_clausification_boolean_conjuncts_refuse_wrong_branch_scope_epoch_and_stop() {
    for mutation in 0..7 {
        let mut f = fixture();
        let target = f.targets[0];
        let (mut proof, negated) = closed_trust(&mut f.exec, target);
        let original = proof.clone();
        let t = &mut f.exec.ctx.terms;
        let source = match mutation {
            0 => t.mk_not_raw(f.root),
            1 => {
                let TermData::Ite(condition, yes, no) = *t.get(f.sources[0]) else {
                    unreachable!()
                };
                t.mk_ite_raw(condition, no, yes)
            }
            2 => {
                let TermData::Ite(_, yes, no) = *t.get(f.sources[0]) else {
                    unreachable!()
                };
                let foreign = t.mk_var("foreign_branch_condition", Sort::Bool);
                t.mk_ite_raw(foreign, yes, no)
            }
            _ => f.root,
        };
        begin(&mut f.exec, &[source, negated], mutation != 3);
        if mutation == 4 {
            f.exec.begin_public_solve(false);
        }
        if mutation == 5 {
            f.exec
                .set_interrupt(std::sync::Arc::new(std::sync::atomic::AtomicBool::new(
                    true,
                )));
        }
        if mutation == 6 {
            f.exec.proof_reconstruction_step_budget = Some(0);
        }
        assert!(
            !f.exec.try_rebuild_native_ite_clausification(&mut proof),
            "mutation {mutation}"
        );
        assert_eq!(proof, original);
    }
}

#[test]
fn native_ite_clausification_boolean_conjuncts_routing_and_admission_share_limits() {
    let mut f = fixture();
    let budget = RepairBudget::new(&f.exec);
    let sources = select_ite_sources(&f.exec, &[f.root, f.root], &budget).unwrap();
    assert_eq!(
        sources.iter().map(|s| s.plan.source).collect::<Vec<_>>(),
        f.sources
    );
    assert!(sources
        .iter()
        .all(|s| s.contents == AdmittedItes::BooleanOnly
            && s.plan.root == f.root
            && s.plan.path.len() == 2));
    let budget = RepairBudget::new(&f.exec);
    budget.set_remaining(1, 1024);
    assert!(select_ite_sources(&f.exec, &[f.root], &budget).is_none());
    assert!(!budget.pay(0, 0));
    let budget = RepairBudget::new(&f.exec);
    let source = f.sources[0];
    let TermData::Ite(condition, yes, _) = *f.exec.ctx.terms.get(source) else {
        unreachable!()
    };
    let wrong_polarity = f
        .exec
        .ctx
        .terms
        .mk_app(Symbol::named("or"), [yes, condition], Sort::Bool);
    assert_eq!(
        boolean_branch_target(
            &f.exec,
            source,
            wrong_polarity,
            AdmittedItes::BooleanOnly,
            &budget
        ),
        Some(false)
    );
    let int = f.exec.ctx.terms.mk_int(0.into());
    let malformed = f
        .exec
        .ctx
        .terms
        .mk_app(Symbol::named("and"), [source, int], Sort::Bool);
    assert!(select_ite_sources(&f.exec, &[malformed], &budget).is_none());
    let repeated = f.exec.ctx.terms.mk_app(
        Symbol::named("and"),
        vec![source; MAX_NATIVE_TERM_OCCURRENCES + 1],
        Sort::Bool,
    );
    assert!(select_ite_sources(&f.exec, &[repeated], &RepairBudget::new(&f.exec)).is_none());
    let mut deep = source;
    for _ in 0..=MAX_NATIVE_DEPTH {
        let truth = f.exec.ctx.terms.true_term();
        deep = f
            .exec
            .ctx
            .terms
            .mk_app(Symbol::named("and"), [deep, truth], Sort::Bool);
    }
    assert!(select_ite_sources(&f.exec, &[deep], &RepairBudget::new(&f.exec)).is_none());
}

#[test]
fn native_ite_clausification_boolean_conjuncts_index_once_and_preprice_copy() {
    let mut f = fixture();
    let mut proof = Proof::new();
    // None of these targets is a source conjunct. One physical traversal is
    // still within4096; forty independent84-child scans would exhaust it.
    for i in 0..48 {
        let target = f
            .exec
            .ctx
            .terms
            .mk_var(format!("not_a_conjunct_{i}"), Sort::Bool);
        proof.add_rule_step(AletheRule::Trust, vec![target], vec![], vec![]);
    }
    proof.add_rule_step(AletheRule::Trust, vec![f.sources[0]], vec![], vec![]);
    let budget = RepairBudget::new(&f.exec);
    assert_eq!(
        f.exec
            .stage_native_conjunct_leaves(&mut proof, &[f.root], &budget),
        Some(1)
    );
    assert!(proof.steps.iter().any(|s| matches!(
        s,
        ProofStep::Step {
            rule: AletheRule::AndPos(79),
            ..
        }
    )));
    let budget = RepairBudget::new(&f.exec);
    budget.set_remaining(1024 * 1024, 1);
    assert!(super::super::projection::admit_rebuild_copy(&proof, &budget).is_none());
    assert!(!budget.pay(0, 0));
}

#[test]
fn native_ite_clausification_boolean_conjuncts_actual_sat_twin_stays_sat() {
    let _diagnostics = diagnostic_flags();
    use crate::executor::quantifier_loop::result_mapping::CheckedGroundDecision;
    use crate::executor::unsat_cert::ProbeUnsatAuthority;
    let mut f = fixture();
    let t = &mut f.exec.ctx.terms;
    let TermData::Ite(condition, yes, no) = *t.get(f.sources[0]) else {
        unreachable!()
    };
    let swapped = t.mk_ite_raw(condition, no, yes);
    let TermData::App(_, outer) = t.get(f.root) else {
        unreachable!()
    };
    let inner = outer[0];
    let TermData::App(_, children) = t.get(inner) else {
        unreachable!()
    };
    let mut children = children.clone();
    children[79] = swapped;
    let root = t.mk_app(Symbol::named("and"), children, Sort::Bool);
    let negated = t.mk_not_raw(f.targets[0]);
    let roots = vec![root, negated];
    let (decision, authority) = f
        .exec
        .checked_model_check_solve_classified(roots.clone(), 200)
        .expect("the unchanged ground SAT twin must retain a checked model");
    assert_eq!(authority, ProbeUnsatAuthority::Checked);
    let CheckedGroundDecision::Sat(checked) = decision else {
        panic!("wrong branch must not gain UNSAT authority")
    };
    assert!(checked.consume(&mut f.exec, &roots));
}
