// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::super::emit::ClosureEmitter;
use super::*;

fn equal(exec: &mut Executor, left: TermId, right: TermId) -> TermId {
    exec.ctx
        .terms
        .mk_app(Symbol::named("="), [left, right], Sort::Bool)
}

#[test]
fn checked_ground_single_edge_symmetry_retains_earlier_source_and_pinned_derivation() {
    let mut exec = Executor::new();
    let x = exec.ctx.terms.mk_var("x", Sort::bitvec(8));
    let y = exec.ctx.terms.mk_var("y", Sort::bitvec(8));
    let pin = equal(&mut exec, x, y);
    let reverse = equal(&mut exec, y, x);
    let negative = exec.ctx.terms.mk_not_raw(reverse);
    let mut search = GroundSearch::default();
    search.closure.register(x);
    search.closure.register(y);
    assert!(search.closure.merge(x, y, EdgeReason::Authored(pin)));
    let mut emitter = ClosureEmitter::new(&search);
    assert!(exec.emit_closure_path_unit(&mut emitter, y, x, 0).is_none());
    assert!(emitter.proof.steps.is_empty(), "no future edge authority");
    let unit = exec.emit_closure_path_unit(&mut emitter, y, x, 1).unwrap();
    assert_eq!(intrinsic_count(&emitter.proof, AletheRule::Symm), 1);
    assert_eq!(emitter.proof.steps.len(), 2);
    let denied = emitter.proof.add_assume(negative, None);
    emitter
        .proof
        .add_resolution(vec![], reverse, unit.step, denied);
    ay_proof::check_proof_strict_with_context(
        &emitter.proof,
        &exec.ctx.terms,
        None,
        None,
        Some(&[pin, negative]),
    )
    .unwrap();
    assert!(
        ay_proof::check_proof_strict_with_context(
            &emitter.proof,
            &exec.ctx.terms,
            None,
            None,
            Some(&[negative]),
        )
        .is_err(),
        "symmetry cannot manufacture the source pin"
    );
    let mut forged = emitter.proof.clone();
    let ProofStep::Step { premises, .. } = &mut forged.steps[1] else {
        panic!("symmetry")
    };
    premises[0] = ProofId(3);
    assert!(exec
        .check_proof_strict_derivation_with_datatypes(&forged)
        .is_err());
    exec.set_alethe_dialect(ay_proof::AletheDialect::PinnedCarcara);
    let mut pinned = ClosureEmitter::new(&search);
    exec.emit_closure_path_unit(&mut pinned, y, x, 1).unwrap();
    assert_eq!(intrinsic_count(&pinned.proof, AletheRule::Symm), 0);
    assert_eq!(
        lemma_count(&pinned.proof, |kind, _| matches!(
            kind,
            TheoryLemmaKind::EufTransitive
        )),
        1
    );
}

#[test]
fn checked_ground_intrinsic_proposal_precharge_and_cancellation_are_real() {
    type Probe = fn(&TermStore, &[TermId], &mut dyn FnMut(usize, usize) -> bool) -> bool;
    let mut exec = Executor::new();
    let x = exec.ctx.terms.mk_var("x", Sort::bitvec(8));
    let extraction =
        exec.ctx
            .terms
            .mk_app(Symbol::indexed("extract", vec![7, 0]), [x], Sort::bitvec(8));
    let reconstruction = equal(&mut exec, extraction, x);
    let source = equal(&mut exec, x, x);
    let truth = exec.ctx.terms.true_term();
    let offset = equal(&mut exec, source, truth);
    for (probe, root, work, bytes) in [
        (
            ay_proof::recognize_bv_offset_spines_with_progress as Probe,
            offset,
            8192,
            4096,
        ),
        (
            ay_proof::recognize_bv_reconstruct_with_progress as Probe,
            reconstruction,
            524288,
            16384,
        ),
    ] {
        let mut events = Vec::new();
        assert!(!probe(&exec.ctx.terms, &[TermId(u32::MAX)], &mut |w, b| {
            events.push((w, b));
            false
        }));
        assert_eq!(
            events,
            [(work, bytes)],
            "denial precedes malformed-ID access"
        );
        assert!(probe(&exec.ctx.terms, &[root], &mut |_, _| true));
        let mut admitted = false;
        assert!(
            !probe(&exec.ctx.terms, &[root], &mut |w, b| {
                if !admitted {
                    assert_eq!((w, b), (work, bytes));
                    admitted = true;
                    true
                } else {
                    false
                }
            }),
            "a stop after fixed admission reaches the original inspector"
        );
    }
}

#[test]
fn checked_ground_offsets_share_only_the_unconditional_boolean_unit() {
    let mut exec = Executor::new();
    let x = exec.ctx.terms.mk_var("x", Sort::bitvec(8));
    let mut equalities = Vec::new();
    for constant in [1, 2] {
        let number = exec.ctx.terms.mk_bitvec(constant.into(), 8);
        let shifted = exec
            .ctx
            .terms
            .mk_app(Symbol::named("bvadd"), [x, number], Sort::bitvec(8));
        equalities.push(equal(&mut exec, x, shifted));
    }
    let search = GroundSearch::default();
    let mut emitter = ClosureEmitter::new(&search);
    let first = exec
        .emit_ground_offset_intrinsic(&mut emitter, equalities[0], false)
        .unwrap()
        .unwrap();
    let _second = exec
        .emit_ground_offset_intrinsic(&mut emitter, equalities[1], false)
        .unwrap()
        .unwrap();
    assert_eq!(
        intrinsic_count(&emitter.proof, AletheRule::BvOffsetSpinesV1),
        2
    );
    assert_eq!(intrinsic_count(&emitter.proof, AletheRule::False), 1);
    assert_eq!(emitter.proof.steps.len(), 7);
    let denied = emitter.proof.add_assume(equalities[0], None);
    emitter
        .proof
        .add_resolution(vec![], equalities[0], first.step, denied);
    assert!(exec
        .check_proof_strict_derivation_with_datatypes(&emitter.proof)
        .unwrap()
        .is_complete());
    ay_proof::check_proof_strict_with_context(
        &emitter.proof,
        &exec.ctx.terms,
        None,
        None,
        Some(&[equalities[0]]),
    )
    .unwrap();
    let satisfiable_source = equal(&mut exec, x, x);
    assert!(ay_proof::check_proof_strict_with_context(
        &emitter.proof,
        &exec.ctx.terms,
        None,
        None,
        Some(&[satisfiable_source])
    )
    .is_err());
    let mut full = ClosureEmitter::new(&search);
    for _ in 0..16384 {
        full.proof.add_assume(equalities[0], None);
    }
    let arena = exec.ctx.terms.len();
    assert!(exec
        .emit_ground_offset_intrinsic(&mut full, equalities[0], false)
        .is_none());
    assert_eq!(exec.ctx.terms.len(), arena);
    assert_eq!(full.proof.steps.len(), 16384);
    exec.set_interrupt(std::sync::Arc::new(std::sync::atomic::AtomicBool::new(
        true,
    )));
    let mut stopped = ClosureEmitter::new(&search);
    assert!(exec
        .emit_ground_offset_intrinsic(&mut stopped, equalities[0], false)
        .is_none());
    assert!(stopped.proof.steps.is_empty());
    assert_eq!(exec.ctx.terms.len(), arena);
}

#[test]
fn checked_ground_long_spines_retain_the_general_fallback_and_pinned_path() {
    let mut left = "x".to_string();
    for _ in 0..17 {
        left = format!("(bvadd {left} (_ bv1 8))");
    }
    let input=format!("(set-option :produce-proofs true)(set-logic QF_BV)(declare-const x (_ BitVec 8))(assert (not (= {left} (bvadd x (_ bv17 8)))))(check-sat)");
    let (mut exec, root) = super::packing::prepared(&input);
    let proof = exec.early_ground_closure_memory_candidate(root).unwrap();
    assert!(
        lemma_count(&proof, |kind, _| matches!(
            kind,
            TheoryLemmaKind::ArithClauseTautology
        )) > 0
    );
    assert!(exec
        .check_proof_strict_derivation_with_datatypes(&proof)
        .unwrap()
        .is_complete());
    ay_proof::check_proof_strict_with_context(&proof, &exec.ctx.terms, None, None, Some(&[root]))
        .unwrap();
    let pure="(set-option :produce-proofs true)(set-logic QF_BV)(declare-const x (_ BitVec 8))(assert (not (= (bvor ((_ zero_extend 4) ((_ extract 3 0) x)) (bvshl ((_ zero_extend 4) ((_ extract 7 4) x)) (_ bv4 8))) x)))(check-sat)";
    let (mut exec, root) = super::packing::prepared(pure);
    exec.set_alethe_dialect(ay_proof::AletheDialect::PinnedCarcara);
    let proof = exec.early_ground_closure_memory_candidate(root).unwrap();
    assert_eq!(intrinsic_count(&proof, AletheRule::BvReconstructV1), 0);
    assert_eq!(intrinsic_count(&proof, AletheRule::BvOffsetSpinesV1), 0);
    assert!(
        lemma_count(&proof, |kind, _| matches!(
            kind,
            TheoryLemmaKind::BvBitBlast
        )) > 0
    );
    assert!(exec
        .check_proof_strict_derivation_with_datatypes(&proof)
        .unwrap()
        .is_complete());
}

#[test]
fn checked_ground_intrinsic_surfaces_allow_only_the_same_bv_literal_value_and_width() {
    let mut exec = Executor::new();
    let x = exec.ctx.terms.mk_var("x", Sort::bitvec(8));
    let one = exec.ctx.terms.mk_bitvec(1.into(), 8);
    let two = exec.ctx.terms.mk_bitvec(2.into(), 8);
    let a = exec
        .ctx
        .terms
        .mk_app(Symbol::named("bvadd"), [x, one], Sort::bitvec(8));
    let b = exec
        .ctx
        .terms
        .mk_app(Symbol::named("bvadd"), [x, two], Sort::bitvec(8));
    let equality = equal(&mut exec, a, b);
    let value = exec.ctx.terms.false_term();
    let claim = equal(&mut exec, equality, value);
    assert!(ay_proof::bv_eq_simplify_step_lowering_supported(
        ay_proof::AletheDialect::Clean,
        &exec.ctx.terms,
        &[claim],
        0,
        0,
        None
    ));
    for (surface, accepted) in [
        ("#x01", true),
        ("(_ bv1 8)", true),
        ("#x02", false),
        ("#x0001", false),
        ("|#x01|", false),
    ] {
        let mut overrides = ay_core::kani_compat::DetHashMap::default();
        overrides.insert(one, surface.to_string());
        assert_eq!(
            ay_proof::bv_offset_spines_step_lowering_supported(
                ay_proof::AletheDialect::Clean,
                &exec.ctx.terms,
                &[claim],
                0,
                0,
                Some(&overrides)
            ),
            accepted,
            "{surface}"
        );
        assert!(
            !ay_proof::bv_eq_simplify_step_lowering_supported(
                ay_proof::AletheDialect::Clean,
                &exec.ctx.terms,
                &[claim],
                0,
                0,
                Some(&overrides)
            ),
            "older immediate rule keeps its byte-identity contract"
        );
        assert!(!ay_proof::bv_offset_spines_step_lowering_supported(
            ay_proof::AletheDialect::PinnedCarcara,
            &exec.ctx.terms,
            &[claim],
            0,
            0,
            Some(&overrides)
        ));
    }
    let extraction =
        exec.ctx
            .terms
            .mk_app(Symbol::indexed("extract", vec![7, 0]), [x], Sort::bitvec(8));
    let zero = exec.ctx.terms.mk_bitvec(0.into(), 8);
    let packed = exec
        .ctx
        .terms
        .mk_app(Symbol::named("bvor"), [extraction, zero], Sort::bitvec(8));
    let claim = equal(&mut exec, packed, x);
    for (surface, accepted) in [
        ("#x00", true),
        ("(_ bv0 8)", true),
        ("#x01", false),
        ("#x0000", false),
    ] {
        let mut overrides = ay_core::kani_compat::DetHashMap::default();
        overrides.insert(zero, surface.to_string());
        assert_eq!(
            ay_proof::bv_reconstruct_step_lowering_supported(
                ay_proof::AletheDialect::Clean,
                &exec.ctx.terms,
                &[claim],
                0,
                0,
                Some(&overrides)
            ),
            accepted,
            "{surface}"
        );
    }
    let mut changed = ay_core::kani_compat::DetHashMap::default();
    changed.insert(packed, "(private_bvor ((_ extract 7 0) x) #x00)".into());
    assert!(!ay_proof::bv_reconstruct_step_lowering_supported(
        ay_proof::AletheDialect::Clean,
        &exec.ctx.terms,
        &[claim],
        0,
        0,
        Some(&changed)
    ));
}
