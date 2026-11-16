// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Exact candidate semantics and native authority, not a consumer timing claim.

use super::*;
use ay_core::{Constant, TermData};
use std::sync::{
    atomic::{AtomicBool, Ordering},
    Arc,
};

mod resources;

fn fixture(source: &str) -> (Executor, Vec<TermId>) {
    let mut executor = Executor::new();
    for command in ay_frontend::parse(source).unwrap() {
        assert!(!matches!(command, ay_frontend::Command::CheckSat));
        executor.execute(&command).unwrap();
    }
    let roots = (0..executor.ctx.assertions_parsed().len())
        .map(|index| {
            let source =
                source::expand(&executor.ctx, &executor.ctx.assertions_parsed()[index]).unwrap();
            executor.raw_intern_ground_bv_surface(&source).unwrap()
        })
        .collect();
    (executor, roots)
}

fn range_source(width: u32) -> String {
    format!(
        "(declare-const numerator (_ BitVec {width}))
       (declare-const denominator (_ BitVec {width}))
       (declare-const renamed_result (_ BitVec {width}))
       (assert (= renamed_result (bvurem numerator denominator)))
       (assert (distinct denominator (_ bv0 {width})))
       (assert (not (bvult renamed_result denominator)))"
    )
}

fn candidate(executor: &mut Executor, roots: &[TermId]) -> Proof {
    let mut control = Control::capture(executor, &|| false).unwrap();
    let found = collect::occurrences(executor, roots, &mut control).unwrap();
    assert_ne!(found, [] as [(TermId, TermId, u32); 0]);
    augmented(
        &mut executor.ctx.terms,
        &executor.proof_source_work,
        roots,
        &found,
        &mut control,
    )
    .unwrap()
}

fn complete(executor: &Executor, proof: &Proof) -> bool {
    ay_proof::check_proof_strict_with_context(proof, &executor.ctx.terms, None, None, None)
        .is_ok_and(|quality| quality.is_complete())
}

#[test]
fn exact_joint_derives_bounds_and_preserves_every_original_assumption() {
    let (mut executor, roots) = fixture(&range_source(4));
    let proof = candidate(&mut executor, &roots);
    assert!(complete(&executor, &proof));
    let assumptions: Vec<_> = proof
        .steps
        .iter()
        .filter_map(|step| match step {
            ProofStep::Assume(root) => Some(*root),
            _ => None,
        })
        .collect();
    assert_eq!(assumptions, roots);
    assert!(ay_proof::validate_reachable_assumes_in_problem_scope(&proof, &roots).is_ok());
    assert!(proof.steps.iter().any(|step| matches!(
        step,
        ProofStep::TheoryLemma {
            kind: TheoryLemmaKind::BvUremBound,
            ..
        }
    )));
    assert!(proof.steps.iter().any(|step| matches!(
        step,
        ProofStep::TheoryLemma {
            kind: TheoryLemmaKind::BvBitBlast,
            ..
        }
    )));
}

#[test]
fn actual_guarded_promotion_uses_checked_bound_without_extra_assumptions() {
    let (mut executor, roots) = fixture(&range_source(4));
    let mut proof = Proof::new();
    proof.add_rule_step(AletheRule::Trust, Vec::new(), Vec::new(), Vec::new());
    assert!(executor.promote_bv_guarded_collapse(&mut proof, GuardedCollapseStage::Final));
    assert!(complete(&executor, &proof));
    assert!(ay_proof::validate_reachable_assumes_in_problem_scope(&proof, &roots).is_ok());
    assert!(proof.steps.iter().any(|step| matches!(
        step,
        ProofStep::TheoryLemma {
            kind: TheoryLemmaKind::BvUremBound,
            ..
        }
    )));
}

#[test]
fn public_check_sat_keeps_source_bound_strict_proof_for_general_divisor() {
    let mut executor = Executor::new();
    executor.set_produce_proofs(true);
    let text = format!("{} (check-sat)", range_source(4));
    assert_eq!(
        executor
            .execute_all(&ay_frontend::parse(&text).unwrap())
            .unwrap(),
        ["unsat"]
    );
    let proof = executor.last_proof().unwrap();
    assert!(complete(&executor, proof));
    assert!(ay_proof::validate_reachable_assumes_in_problem_scope(
        proof,
        &executor.proof_export_scope_assertions()
    )
    .is_ok());
}

#[test]
fn every_supported_width_builds_a_native_checked_total_theorem() {
    for width in [1, 2, 8, 16, 32, 64, 128] {
        let (mut executor, roots) = fixture(&range_source(width));
        let proof = candidate(&mut executor, &roots);
        // Check the actual derived unit independently; the final large-width
        // bit-blast is covered by original-run qualification, not this loop.
        let step = proof
            .steps
            .iter()
            .find(|step| {
                matches!(
                    step,
                    ProofStep::TheoryLemma {
                        kind: TheoryLemmaKind::BvUremBound,
                        ..
                    }
                )
            })
            .unwrap()
            .clone();
        let bound = match &step {
            ProofStep::TheoryLemma { clause, .. } => clause[0],
            _ => unreachable!(),
        };
        let negative = executor.ctx.terms.mk_not_raw(bound);
        let mut theorem = Proof::new();
        let lemma = theorem.add_step(step);
        let assumption = theorem.add_assume(negative, None);
        theorem.add_resolution(Vec::new(), bound, lemma, assumption);
        assert!(complete(&executor, &theorem), "width {width}");
        assert!(
            ay_proof::validate_reachable_assumes_in_problem_scope(&theorem, &[negative]).is_ok()
        );
    }
}

#[test]
fn zero_divisor_does_not_create_a_false_refutation() {
    let (mut executor, roots) =
        fixture("(declare-const x (_ BitVec 4)) (assert (= (bvurem x #x0) #xf))");
    let proof = candidate(&mut executor, &roots);
    assert!(!complete(&executor, &proof), "x=15 is a real witness");
}

#[test]
fn changed_divisor_in_bound_is_rejected_independently() {
    let (mut executor, roots) = fixture(&range_source(4));
    let mut proof = candidate(&mut executor, &roots);
    let wrong = executor.ctx.terms.mk_bitvec(1.into(), 4);
    let bad = executor
        .ctx
        .terms
        .mk_app(Symbol::named("bvult"), vec![wrong, wrong], Sort::Bool);
    let step = proof
        .steps
        .iter_mut()
        .find(|step| {
            matches!(
                step,
                ProofStep::TheoryLemma {
                    kind: TheoryLemmaKind::BvUremBound,
                    ..
                }
            )
        })
        .unwrap();
    if let ProofStep::TheoryLemma { clause, .. } = step {
        *clause = vec![bad];
    }
    assert!(!complete(&executor, &proof));
}

#[test]
fn forged_bound_assumption_is_not_original_authority() {
    let (mut executor, roots) = fixture(&range_source(4));
    let mut proof = candidate(&mut executor, &roots);
    let step = proof
        .steps
        .iter_mut()
        .find(|step| {
            matches!(
                step,
                ProofStep::TheoryLemma {
                    kind: TheoryLemmaKind::BvUremBound,
                    ..
                }
            )
        })
        .unwrap();
    let bound = match step {
        ProofStep::TheoryLemma { clause, .. } => clause[0],
        _ => unreachable!(),
    };
    *step = ProofStep::Assume(bound);
    assert!(ay_proof::validate_reachable_assumes_in_problem_scope(&proof, &roots).is_err());
}

#[test]
fn shadowed_name_and_wrong_operand_sort_never_gain_theorem_authority() {
    let (mut executor, roots) = fixture(&range_source(4));
    let var = executor.ctx.terms.find_var("numerator").unwrap();
    executor
        .ctx
        .register_symbol("bvurem".into(), var, Sort::bitvec(4));
    let mut control = Control::capture(&executor, &|| false).unwrap();
    assert_eq!(
        collect::occurrences(&executor, &roots, &mut control).unwrap(),
        [] as [(TermId, TermId, u32); 0]
    );
    let (mut executor, _) = fixture("(declare-const x (_ BitVec 4))");
    let x = executor.ctx.terms.find_var("x").unwrap();
    let boolean = executor.ctx.terms.mk_bool(true);
    let malformed =
        executor
            .ctx
            .terms
            .mk_app(Symbol::named("bvurem"), vec![x, boolean], Sort::bitvec(4));
    let malformed_root =
        executor
            .ctx
            .terms
            .mk_app(Symbol::named("="), vec![x, malformed], Sort::Bool);
    assert_eq!(
        collect::occurrences(&executor, &[malformed_root], &mut control).unwrap(),
        [] as [(TermId, TermId, u32); 0]
    );
}

#[test]
fn duplicate_shared_occurrences_create_one_derived_bound() {
    let (mut executor, roots) = fixture(
        "(declare-const x (_ BitVec 4)) (declare-const d (_ BitVec 4))
        (assert (= (bvurem x d) #x0)) (assert (= (bvurem x d) #x1))",
    );
    let proof = candidate(&mut executor, &roots);
    assert_eq!(
        proof
            .steps
            .iter()
            .filter(|step| matches!(
                step,
                ProofStep::TheoryLemma {
                    kind: TheoryLemmaKind::BvUremBound,
                    ..
                }
            ))
            .count(),
        1
    );
    assert!(complete(&executor, &proof));
}

#[test]
fn wire_advice_requires_exact_typed_unoverridden_bound_not_a_new_assumption() {
    let (mut executor, roots) = fixture(&range_source(4));
    let proof = candidate(&mut executor, &roots);
    let clause = proof
        .steps
        .iter()
        .find_map(|step| match step {
            ProofStep::TheoryLemma {
                kind: TheoryLemmaKind::BvUremBound,
                clause,
                ..
            } => Some(clause),
            _ => None,
        })
        .unwrap();
    assert!(executor.urem_bound_wire_supported(clause, None));
    let mut overrides = ay_core::kani_compat::DetHashMap::default();
    overrides.insert(clause[0], "false".into());
    assert!(!executor.urem_bound_wire_supported(clause, Some(&overrides)));
    let negative = executor.ctx.terms.mk_not_raw(clause[0]);
    assert!(!executor.urem_bound_wire_supported(&[negative], None));
    assert!(
        executor.certification_stop().is_none(),
        "unsupported is not cancellation"
    );
}

#[test]
fn malformed_remainder_literal_cannot_hide_in_theorem_operands() {
    let (mut executor, _) = fixture("(declare-const x (_ BitVec 4))");
    let x = executor.ctx.terms.find_var("x").unwrap();
    let mut entries = executor.ctx.terms.entries_snapshot();
    let bad = TermId(u32::try_from(entries.len()).unwrap());
    entries.push((
        TermData::Const(Constant::BitVec {
            value: 256.into(),
            width: 4,
        }),
        Sort::bitvec(4),
    ));
    let rem = TermId(u32::try_from(entries.len()).unwrap());
    entries.push((
        TermData::App(Symbol::named("bvurem"), vec![bad, x]),
        Sort::bitvec(4),
    ));
    let zero = TermId(u32::try_from(entries.len()).unwrap());
    entries.push((
        TermData::Const(Constant::BitVec {
            value: 0.into(),
            width: 4,
        }),
        Sort::bitvec(4),
    ));
    let guard = TermId(u32::try_from(entries.len()).unwrap());
    entries.push((TermData::App(Symbol::named("="), vec![x, zero]), Sort::Bool));
    let less = TermId(u32::try_from(entries.len()).unwrap());
    entries.push((
        TermData::App(Symbol::named("bvult"), vec![rem, x]),
        Sort::Bool,
    ));
    let bound = TermId(u32::try_from(entries.len()).unwrap());
    entries.push((
        TermData::App(Symbol::named("or"), vec![guard, less]),
        Sort::Bool,
    ));
    let negative = TermId(u32::try_from(entries.len()).unwrap());
    entries.push((TermData::Not(bound), Sort::Bool));
    executor.ctx.terms =
        TermStore::from_entries(entries, None, None, executor.ctx.terms.var_counter());
    let mut proof = Proof::new();
    let lemma = proof.add_theory_lemma_with_kind("bv", vec![bound], TheoryLemmaKind::BvUremBound);
    let assumption = proof.add_assume(negative, None);
    proof.add_resolution(Vec::new(), bound, lemma, assumption);
    assert!(!complete(&executor, &proof));
}
