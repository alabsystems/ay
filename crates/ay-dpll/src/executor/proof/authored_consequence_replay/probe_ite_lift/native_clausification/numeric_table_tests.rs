// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The exact ground matrices left by numeric UF-table substitution in two
//! public QMC failures. The checked proof must use the pre-lift assumptions.

use super::*;
use crate::executor::quantifier_loop::result_mapping::CheckedGroundDecision;
use crate::executor::unsat_cert::ProbeUnsatAuthority;

fn bool_app(terms: &mut TermStore, name: &str, args: &[TermId]) -> TermId {
    terms.mk_app(Symbol::named(name), args.to_vec(), Sort::Bool)
}

fn differs(terms: &mut TermStore, left: TermId, right: TermId) -> TermId {
    let equal = bool_app(terms, "=", &[left, right]);
    terms.mk_not_raw(equal)
}

fn nonzero_matrix() -> (Executor, TermId, TermId, TermId) {
    let mut exec = Executor::new();
    exec.set_produce_proofs(true);
    let terms = &mut exec.ctx.terms;
    let z = terms.mk_var("z", Sort::Int);
    let zero = terms.mk_int(0.into());
    let one = terms.mk_int(1.into());
    let at_zero = bool_app(terms, "=", &[zero, z]);
    let not_at_zero = terms.mk_not_raw(at_zero);
    let table = terms.mk_ite_raw(at_zero, zero, one);
    let wrong_zero = differs(terms, zero, table);
    let wrong_one = differs(terms, one, table);
    let source = terms.mk_ite_raw(at_zero, wrong_zero, wrong_one);
    let target = terms.mk_ite_raw(at_zero, not_at_zero, at_zero);
    let sat_twin = terms.mk_ite_raw(at_zero, wrong_one, wrong_zero);
    (exec, source, target, sat_twin)
}

struct MappingMatrix {
    exec: Executor,
    source: TermId,
    targets: [TermId; 2],
    equal_aliases: TermId,
    equal_predicates: TermId,
    distinct_predicates: TermId,
}

fn mapping_matrix() -> MappingMatrix {
    let mut exec = Executor::new();
    exec.set_produce_proofs(true);
    let terms = &mut exec.ctx.terms;
    let sort = Sort::Uninterpreted("Mapping".to_owned());
    let m1 = terms.mk_var("m1", sort.clone());
    let m2 = terms.mk_var("m2", sort.clone());
    let m3 = terms.mk_var("m3", sort);
    let z = terms.mk_var("z", Sort::Int);
    let zero = terms.mk_int(0.into());
    let one = terms.mk_int(1.into());
    let equal_aliases = bool_app(terms, "=", &[m1, m2]);
    let equal_predicates = bool_app(terms, "=", &[m1, m3]);
    let distinct_predicates = terms.mk_not_raw(equal_predicates);
    let a = bool_app(terms, "=", &[zero, z]);
    let b = bool_app(terms, "=", &[one, z]);
    let guard = bool_app(terms, "and", &[equal_predicates, b]);
    let inner = terms.mk_ite_raw(guard, one, zero);
    let table = terms.mk_ite_raw(a, one, inner);
    let wrong_one = differs(terms, one, table);
    let wrong_zero = differs(terms, zero, table);
    let source = terms.mk_ite_raw(a, wrong_one, wrong_zero);
    let not_a = terms.mk_not_raw(a);
    let not_b = terms.mk_not_raw(b);
    let split_else = bool_app(terms, "or", &[distinct_predicates, not_b]);
    let prefix = bool_app(terms, "and", &[not_a, split_else]);
    let first = bool_app(terms, "or", &[prefix, not_a]);
    let suffix = bool_app(terms, "or", &[a, guard]);
    let second = bool_app(terms, "or", &[a, suffix]);
    MappingMatrix {
        exec,
        source,
        targets: [first, second],
        equal_aliases,
        equal_predicates,
        distinct_predicates,
    }
}

struct AliasedMatrix {
    exec: Executor,
    source: TermId,
    at_zero: TermId,
    second_guard: TermId,
    p12: TermId,
    p13: TermId,
    p23: TermId,
}

/// The second captured universal uses m2 in its table while the retained
/// representative is m1. Its proof additionally needs packed transitivity.
fn aliased_matrix() -> AliasedMatrix {
    let mut exec = Executor::new();
    exec.set_produce_proofs(true);
    let terms = &mut exec.ctx.terms;
    let sort = Sort::Uninterpreted("Mapping".to_owned());
    let m1 = terms.mk_var("m1", sort.clone());
    let m2 = terms.mk_var("m2", sort.clone());
    let m3 = terms.mk_var("m3", sort);
    let z = terms.mk_var("z", Sort::Int);
    let zero = terms.mk_int(0.into());
    let one = terms.mk_int(1.into());
    let p12 = bool_app(terms, "=", &[m1, m2]);
    let p13 = bool_app(terms, "=", &[m1, m3]);
    let p23 = bool_app(terms, "=", &[m2, m3]);
    let at_zero = bool_app(terms, "=", &[zero, z]);
    let at_one = bool_app(terms, "=", &[one, z]);
    let first_guard = bool_app(terms, "and", &[p12, at_zero]);
    let second_guard = bool_app(terms, "and", &[p23, at_one]);
    let inner = terms.mk_ite_raw(second_guard, one, zero);
    let table = terms.mk_ite_raw(first_guard, one, inner);
    let wrong_one = differs(terms, one, table);
    let wrong_zero = differs(terms, zero, table);
    let source = terms.mk_ite_raw(at_zero, wrong_one, wrong_zero);
    AliasedMatrix {
        exec,
        source,
        at_zero,
        second_guard,
        p12,
        p13,
        p23,
    }
}

fn check_consequence(
    exec: &mut Executor,
    source: TermId,
    target: TermId,
    prefix: &str,
    tag: &str,
) -> Proof {
    let (mut proof, negated) = closed_trust(exec, target);
    let roots = [source, negated];
    begin(exec, &roots, true);
    assert!(exec.try_rebuild_native_ite_clausification(&mut proof));
    assert!(exec
        .check_proof_strict_with_datatypes(&proof)
        .is_ok_and(|quality| quality.is_complete()));
    assert!(ay_proof::validate_reachable_assumes_in_problem_scope(&proof, &roots).is_ok());
    let document = ay_proof::try_export_alethe_with_problem_scope_and_overrides(
        &proof,
        &exec.ctx.terms,
        &roots,
        None,
    )
    .expect("strict numeric-table derivation exports");
    let source = ay_proof::format_term_alethe(&exec.ctx.terms, source);
    let negated = ay_proof::format_term_alethe(&exec.ctx.terms, negated);
    let problem = format!("{prefix}(assert {source})\n(assert {negated})\n(check-sat)\n");
    let output = external_check(tag, &problem, &document);
    assert_eq!(output.lines().last(), Some("valid"), "{output}");
    let forged = format!("{prefix}(assert (not {source}))\n(assert {negated})\n(check-sat)\n");
    let output = external_check(&format!("forged-{tag}"), &forged, &document);
    assert_ne!(output.lines().last(), Some("valid"), "{output}");
    proof
}

#[test]
fn native_ite_clausification_nonzero_table_weakens_a_checked_empty_clause() {
    let _diagnostics = diagnostic_flags();
    let (mut exec, source, target, _) = nonzero_matrix();
    let proof = check_consequence(
        &mut exec,
        source,
        target,
        "(set-logic QF_LIA)\n(declare-const z Int)\n",
        "nonzero-table",
    );
    assert!(proof.steps.iter().any(|step| matches!(
        step,
        ProofStep::Step {
            rule: AletheRule::Weakening,
            clause,
            premises,
            ..
        } if clause.as_slice() == [target]
            && premises.len() == 1
            && step_clause(&proof, premises[0]).is_some_and(|clause| clause.is_empty())
    )));
}

#[test]
fn native_ite_clausification_nested_table_derives_both_captured_targets() {
    let _diagnostics = diagnostic_flags();
    for position in 0..2 {
        let mut f = mapping_matrix();
        check_consequence(
            &mut f.exec,
            f.source,
            f.targets[position],
            "(set-logic QF_UFLIA)\n(declare-sort Mapping 0)\n(declare-const m1 Mapping)\n(declare-const m2 Mapping)\n(declare-const m3 Mapping)\n(declare-const z Int)\n",
            &format!("nested-table-{position}"),
        );
    }
}

#[test]
fn native_ite_clausification_numeric_tables_check_actual_probes_and_sat_twins() {
    let _diagnostics = diagnostic_flags();
    for variant in 0..6 {
        let (mut exec, roots) = match variant {
            0 | 1 => {
                let (exec, source, _, sat_twin) = nonzero_matrix();
                (exec, vec![if variant == 0 { source } else { sat_twin }])
            }
            2 | 3 => {
                let f = mapping_matrix();
                let pin = if variant == 2 {
                    f.distinct_predicates
                } else {
                    f.equal_predicates
                };
                (f.exec, vec![f.equal_aliases, pin, f.source])
            }
            _ => {
                let mut f = aliased_matrix();
                let terms = &mut f.exec.ctx.terms;
                let pin = if variant == 4 {
                    f.p12
                } else {
                    terms.mk_not_raw(f.p12)
                };
                let not_p13 = terms.mk_not_raw(f.p13);
                (f.exec, vec![pin, not_p13, f.source])
            }
        };
        let (decision, authority) = exec
            .checked_model_check_solve_classified(roots.clone(), 200)
            .expect("actual QMC probe must establish a checked decision");
        assert_eq!(authority, ProbeUnsatAuthority::Checked);
        match decision {
            CheckedGroundDecision::Unsat(checked) => {
                assert_eq!(variant % 2, 0);
                assert!(checked.consume(&mut exec, &roots));
            }
            CheckedGroundDecision::Sat(checked) => {
                assert_eq!(variant % 2, 1);
                assert!(checked.consume(&mut exec, &roots));
            }
        }
    }
}

/// Both leaves are reachable: the ITE source forces the second guard at a
/// nonzero key, and the packed equality theorem refutes its carrier test.
fn mixed_table_proof(f: &mut AliasedMatrix) -> (Proof, [TermId; 4]) {
    let terms = &mut f.exec.ctx.terms;
    let not_zero = terms.mk_not_raw(f.at_zero);
    let not_p12 = terms.mk_not_raw(f.p12);
    let not_p13 = terms.mk_not_raw(f.p13);
    let not_p23 = terms.mk_not_raw(f.p23);
    let not_guard = terms.mk_not_raw(f.second_guard);
    let consequence = bool_app(terms, "or", &[f.at_zero, f.second_guard]);
    let packed = bool_app(terms, "or", &[not_p23, not_p12, f.p13]);
    let mut proof = Proof::new();
    let add_trust = |proof: &mut Proof, term| {
        proof.add_rule_step(AletheRule::Trust, vec![term], Vec::new(), Vec::new())
    };
    let source_step = add_trust(&mut proof, consequence);
    let split = proof.add_rule_step(
        AletheRule::Or,
        vec![f.at_zero, f.second_guard],
        vec![source_step],
        Vec::new(),
    );
    let key = proof.add_assume(not_zero, None);
    let guard = proof.add_resolution(vec![f.second_guard], f.at_zero, split, key);
    let carrier_projection = proof.add_rule_step(
        AletheRule::AndPos(0),
        vec![not_guard, f.p23],
        Vec::new(),
        vec![f.second_guard],
    );
    let p23 = proof.add_resolution(vec![f.p23], f.second_guard, guard, carrier_projection);

    let euf = add_trust(&mut proof, packed);
    let split = proof.add_rule_step(
        AletheRule::Or,
        vec![not_p23, not_p12, f.p13],
        vec![euf],
        Vec::new(),
    );
    let alias = proof.add_assume(f.p12, None);
    let carrier = proof.add_assume(not_p13, None);
    let remaining = proof.add_resolution(vec![not_p23, f.p13], not_p12, split, alias);
    let not_p23_step = proof.add_resolution(vec![not_p23], f.p13, remaining, carrier);
    proof.add_resolution(Vec::new(), f.p23, p23, not_p23_step);
    (proof, [f.p12, not_p13, not_zero, f.source])
}

#[test]
fn native_ite_clausification_packed_euf_and_nested_ite_commit_together() {
    let _diagnostics = diagnostic_flags();
    let mut f = aliased_matrix();
    let (mut proof, roots) = mixed_table_proof(&mut f);
    begin(&mut f.exec, &roots, true);
    assert!(f.exec.try_rebuild_native_ite_clausification(&mut proof));
    assert!(f
        .exec
        .check_proof_strict_with_datatypes(&proof)
        .is_ok_and(|quality| quality.is_complete()));
    assert!(ay_proof::validate_reachable_assumes_in_problem_scope(&proof, &roots).is_ok());
    let document = ay_proof::try_export_alethe_with_problem_scope_and_overrides(
        &proof,
        &f.exec.ctx.terms,
        &roots,
        None,
    )
    .expect("the mixed certificate exports as a complete document");
    assert!(document.contains(":rule ite_intro"));
    assert!(document.contains(":rule eq_transitive"));
    let prefix = "(set-logic QF_UFLIA)\n(declare-sort Mapping 0)\n(declare-const m1 Mapping)\n(declare-const m2 Mapping)\n(declare-const m3 Mapping)\n(declare-const z Int)\n";
    let make_problem = |roots: &[TermId]| {
        let mut problem = prefix.to_owned();
        for &root in roots {
            let term = ay_proof::format_term_alethe(&f.exec.ctx.terms, root);
            problem.push_str(&format!("(assert {term})\n"));
        }
        problem.push_str("(check-sat)\n");
        problem
    };
    let output = external_check("mixed-table", &make_problem(&roots), &document);
    assert_eq!(output.lines().last(), Some("valid"), "{output}");

    let mut f = aliased_matrix();
    let (mut proof, mut roots) = mixed_table_proof(&mut f);
    roots[3] = f.exec.ctx.terms.mk_not_raw(roots[3]);
    begin(&mut f.exec, &roots, true);
    let original = proof.clone();
    assert!(!f.exec.try_rebuild_native_ite_clausification(&mut proof));
    assert_eq!(proof, original, "neither partial candidate may commit");
    let mut forged = prefix.to_owned();
    for &root in &roots {
        let term = ay_proof::format_term_alethe(&f.exec.ctx.terms, root);
        forged.push_str(&format!("(assert {term})\n"));
    }
    forged.push_str("(check-sat)\n");
    let output = external_check("forged-mixed-table", &forged, &document);
    assert_ne!(output.lines().last(), Some("valid"), "{output}");
}

#[test]
fn native_ite_clausification_still_refuses_a_numeric_ite_in_a_guard() {
    let (mut exec, _, _, _) = nonzero_matrix();
    let terms = &mut exec.ctx.terms;
    let z = terms.mk_var("guard_z", Sort::Int);
    let zero = terms.mk_int(0.into());
    let one = terms.mk_int(1.into());
    let a = bool_app(terms, "=", &[zero, z]);
    let inner = terms.mk_ite_raw(a, zero, one);
    let guard = bool_app(terms, "=", &[inner, zero]);
    let outer = terms.mk_ite_raw(guard, one, zero);
    let root = bool_app(terms, "=", &[outer, z]);
    assert!(collect_ite_sites(terms, root).is_none());
}
