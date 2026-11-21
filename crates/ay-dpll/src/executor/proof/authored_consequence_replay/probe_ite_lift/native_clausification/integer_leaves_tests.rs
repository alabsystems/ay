// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::super::tests::{begin, external_check};
use super::*;

struct Fixture {
    exec: Executor,
    proof: Proof,
    clause: [TermId; 2],
    roots: Vec<TermId>,
}

/// `2*x <= 2*y || y+gap <= x`: gap=1 is a theorem over Int; gap=2
/// is false at x=y+1. The two rows require different positional weights.
fn fixture(kind: TheoryLemmaKind, coefficients: &[i64], gap: i64) -> Fixture {
    let mut exec = Executor::new();
    exec.set_produce_proofs(true);
    let t = &mut exec.ctx.terms;
    let x = t.mk_var("retained_bound_x", Sort::Int);
    let y = t.mk_var("retained_bound_y", Sort::Int);
    let two = t.mk_int(2.into());
    let gap = t.mk_int(gap.into());
    let twice_x = t.mk_app(Symbol::named("*"), [two, x], Sort::Int);
    let twice_y = t.mk_app(Symbol::named("*"), [two, y], Sort::Int);
    let shifted_y = t.mk_app(Symbol::named("+"), [y, gap], Sort::Int);
    let first = t.mk_app(Symbol::named("<="), [twice_x, twice_y], Sort::Bool);
    let second = t.mk_app(Symbol::named("<="), [shifted_y, x], Sort::Bool);
    let not_first = t.mk_not_raw(first);
    let not_second = t.mk_not_raw(second);
    let clause = [first, second];
    let mut proof = Proof::new();
    let a = proof.add_assume(not_first, None);
    let b = proof.add_assume(not_second, None);
    let retained = proof.add_step(ProofStep::TheoryLemma {
        theory: "LIA".to_owned(),
        clause: clause.to_vec(),
        kind,
        farkas: Some(FarkasAnnotation::from_ints(coefficients)),
        lia: None,
    });
    let last = proof.add_resolution(vec![second], first, retained, a);
    proof.add_resolution(vec![], second, last, b);
    Fixture {
        exec,
        proof,
        clause,
        // Repeated roots are part of the original scope, not normalized away
        // merely because the derivation uses only its first occurrence.
        roots: vec![not_first, not_second, not_first],
    }
}

fn complete(f: &mut Fixture) -> bool {
    f.exec
        .check_proof_strict_with_datatypes(&f.proof)
        .is_ok_and(|quality| quality.is_complete())
}

#[test]
fn native_ite_clausification_retained_bounds_rederive_wrong_and_malformed_coefficients() {
    for kind in [TheoryLemmaKind::LiaGeneric, TheoryLemmaKind::LraFarkas] {
        for coefficients in [&[1, 1][..], &[1][..], &[-1, 1][..], &[0, 0][..]] {
            let mut f = fixture(kind, coefficients, 1);
            begin(&mut f.exec, &f.roots, true);
            assert!(!complete(&mut f), "{kind:?} {coefficients:?}");
            assert!(f
                .exec
                .replace_with_checked_small_integer_leaves(&mut f.proof));
            assert!(complete(&mut f));
            assert_eq!(f.exec.proof_original_problem_assertions_slice(), f.roots);
            assert!(
                ay_proof::validate_reachable_assumes_in_problem_scope(&f.proof, &f.roots).is_ok()
            );
            assert!(f.proof.steps.iter().any(|step| matches!(
                step,
                ProofStep::TheoryLemma {
                    kind: TheoryLemmaKind::IntCgCutChain,
                    clause,
                    farkas: None,
                    lia: None,
                    ..
                } if clause.as_slice() == f.clause.as_slice()
            )));
            assert!(!f.proof.steps.iter().any(|step| matches!(
                step,
                ProofStep::Step {
                    rule: AletheRule::Trust | AletheRule::Hole,
                    ..
                }
            )));
        }
    }
}

#[test]
fn native_ite_clausification_retained_bounds_preserve_valid_annotations_and_attempts() {
    let mut f = fixture(TheoryLemmaKind::LiaGeneric, &[1, 1], 1);
    let valid = ProofStep::TheoryLemma {
        theory: "original-producer-LIA".to_owned(),
        clause: f.clause.to_vec(),
        kind: TheoryLemmaKind::LiaGeneric,
        farkas: Some(FarkasAnnotation::from_ints(&[1, 2])),
        lia: None,
    };
    let mut proof = Proof::new();
    for _ in 0..MAX_INTEGER_ATTEMPTS {
        proof.add_step(valid.clone());
    }
    let original_valid = proof.clone();
    proof.add_step(f.proof.steps[2].clone());
    // Stage directly so projection cannot discard the deliberately unused
    // valid leaves before this test exercises their attempt accounting.
    assert_eq!(f.exec.stage_small_integer_leaves(&mut proof), 1);
    assert_eq!(&proof.steps[..MAX_INTEGER_ATTEMPTS], original_valid.steps);
    assert!(matches!(
        proof.steps.last(),
        Some(ProofStep::TheoryLemma {
            kind: TheoryLemmaKind::IntCgCutChain,
            ..
        })
    ));
    // A complete proof with only valid retained arithmetic is left identical,
    // rather than republished merely because its annotation was encountered.
    let mut valid_fixture = fixture(TheoryLemmaKind::LiaGeneric, &[1, 2], 1);
    begin(&mut valid_fixture.exec, &valid_fixture.roots, true);
    assert!(complete(&mut valid_fixture));
    let original = valid_fixture.proof.clone();
    assert!(!valid_fixture
        .exec
        .replace_with_checked_small_integer_leaves(&mut valid_fixture.proof));
    assert_eq!(valid_fixture.proof, original);
}

#[test]
fn native_ite_clausification_retained_bounds_decline_non_tautology_unchanged() {
    let mut f = fixture(TheoryLemmaKind::LiaGeneric, &[1, 1], 2);
    begin(&mut f.exec, &f.roots, true);
    let original = f.proof.clone();
    assert_eq!(f.exec.stage_small_integer_leaves(&mut f.proof), 0);
    assert_eq!(f.proof, original);
    assert!(!f
        .exec
        .replace_with_checked_small_integer_leaves(&mut f.proof));
    assert_eq!(f.proof, original);
    assert!(!complete(&mut f));
}

#[test]
fn native_ite_clausification_retained_bounds_preserve_other_annotation_fragments() {
    let mut f = fixture(TheoryLemmaKind::LiaGeneric, &[1, 1], 1);
    if let ProofStep::TheoryLemma { lia, .. } = &mut f.proof.steps[2] {
        *lia = Some(ay_core::LiaAnnotation::BoundsGap);
    }
    let original = f.proof.clone();
    assert_eq!(f.exec.stage_small_integer_leaves(&mut f.proof), 0);
    assert_eq!(f.proof, original);

    // Equality-bearing clauses can be valid in the checker's stronger span
    // or congruence lane even when a strict linear annotation check declines.
    // This route must not reclassify them as invalid retained annotations.
    let t = &mut f.exec.ctx.terms;
    let x = t.mk_var("retained_equality_x", Sort::Int);
    let zero = t.mk_int(0.into());
    let equality = t.mk_eq(x, zero);
    let not_equality = t.mk_not_raw(equality);
    let mut proof = Proof::new();
    proof.add_step(ProofStep::TheoryLemma {
        theory: "LIA".to_owned(),
        clause: vec![equality, not_equality],
        kind: TheoryLemmaKind::LraFarkas,
        farkas: Some(FarkasAnnotation::from_ints(&[1, 1])),
        lia: None,
    });
    let original = proof.clone();
    assert_eq!(f.exec.stage_small_integer_leaves(&mut proof), 0);
    assert_eq!(proof, original);
}

#[test]
fn native_ite_clausification_retained_bounds_share_sticky_budget_before_old_check() {
    let mut f = fixture(TheoryLemmaKind::LiaGeneric, &[1, 1], 1);
    let leaf = integer_leaf(&f.proof.steps[2]).unwrap();
    let budget = RepairBudget::new(&f.exec);
    // Establish admission before the recorded annotation's independent walk.
    assert!(
        IntrinsicIntegerClause::admit(&f.exec.ctx.terms, leaf.clause, &mut |work, bytes| budget
            .pay(work, bytes),)
        .is_some()
    );
    let before = budget.remaining();
    assert_eq!(
        rejected_retained_bounds(&f.exec.ctx.terms, &leaf, &budget),
        Some(true)
    );
    let after = budget.remaining();
    assert!(after.0 < before.0 && after.1 < before.1);
    budget.set_remaining(0, 0);
    assert_eq!(
        rejected_retained_bounds(&f.exec.ctx.terms, &leaf, &budget),
        None
    );
    budget.set_remaining(before.0, before.1);
    assert!(!budget.pay(0, 0), "refusal cannot renew the original owner");

    begin(&mut f.exec, &f.roots, true);
    f.exec
        .set_interrupt(std::sync::Arc::new(std::sync::atomic::AtomicBool::new(
            true,
        )));
    let original = f.proof.clone();
    assert!(!f
        .exec
        .replace_with_checked_small_integer_leaves(&mut f.proof));
    assert_eq!(f.proof, original);
}

#[test]
fn native_ite_clausification_retained_bounds_keep_full_source_gate() {
    let mut f = fixture(TheoryLemmaKind::LiaGeneric, &[1, 1], 1);
    // The arithmetic theorem alone cannot authenticate the omitted original
    // assumption. Failed scope validation leaves the caller's proof unchanged.
    begin(&mut f.exec, &f.roots[..1], true);
    let original = f.proof.clone();
    assert!(!f
        .exec
        .replace_with_checked_small_integer_leaves(&mut f.proof));
    assert_eq!(f.proof, original);
}

#[test]
fn native_ite_clausification_retained_bounds_preflight_dag_and_raw_ratios() {
    let mut f = fixture(TheoryLemmaKind::LiaGeneric, &[1, 1], 1);
    let t = &mut f.exec.ctx.terms;
    let long = t.mk_var("retained_oversized_".repeat(32), Sort::Int);
    let zero = t.mk_int(0.into());
    let a = t.mk_app(Symbol::named("<="), [long, zero], Sort::Bool);
    let b = t.mk_app(Symbol::named(">="), [long, zero], Sort::Bool);
    if let ProofStep::TheoryLemma { clause, .. } = &mut f.proof.steps[2] {
        *clause = vec![a, b];
    }
    let original = f.proof.clone();
    assert_eq!(f.exec.stage_small_integer_leaves(&mut f.proof), 0);
    assert_eq!(f.proof, original);

    let mut f = fixture(TheoryLemmaKind::LiaGeneric, &[1, 1], 1);
    if let ProofStep::TheoryLemma {
        farkas: Some(annotation),
        ..
    } = &mut f.proof.steps[2]
    {
        annotation.coefficients[0] = num_rational::Rational64::new_raw(-1, -1);
    }
    let original = f.proof.clone();
    assert_eq!(f.exec.stage_small_integer_leaves(&mut f.proof), 0);
    assert_eq!(
        f.proof, original,
        "raw noncanonical metadata is not normalized by this route"
    );
}

#[test]
fn native_ite_clausification_retained_bounds_whole_carcara_and_forged_rule() {
    let mut f = fixture(TheoryLemmaKind::LiaGeneric, &[1, 1], 1);
    begin(&mut f.exec, &f.roots, true);
    assert!(f
        .exec
        .replace_with_checked_small_integer_leaves(&mut f.proof));
    assert!(complete(&mut f));
    let document = ay_proof::try_export_alethe_with_problem_scope_and_overrides(
        &f.proof,
        &f.exec.ctx.terms,
        &f.roots,
        None,
    )
    .expect("independent retained-bound derivation exports");
    let mut problem = "(set-logic QF_LIA)\n(declare-const retained_bound_x Int)\n(declare-const retained_bound_y Int)\n".to_owned();
    for &root in &f.roots {
        problem.push_str(&format!(
            "(assert {})\n",
            ay_proof::format_term_alethe(&f.exec.ctx.terms, root)
        ));
    }
    problem.push_str("(check-sat)\n");
    assert_eq!(
        external_check("retained-bound-pair", &problem, &document)
            .lines()
            .last(),
        Some("valid")
    );
    let (prefix, final_rule) = document.rsplit_once(":rule ").expect("final rule exists");
    let (_, suffix) = final_rule
        .split_once(char::is_whitespace)
        .expect("rule has following syntax");
    let forged = format!("{prefix}:rule refl {suffix}");
    let result = external_check("forged-retained-bound-final-rule", &problem, &forged);
    assert!(result.lines().any(|line| line == "invalid"), "{result}");
}
