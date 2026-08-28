// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The BOUND half of the `and_pos` charge evidence: the tightening sweep, the
//! three adversarial shapes, the measured `clearsy` payload, the oversize
//! refusal, the printer check, and the guard-mutation ledger.
//!
//! Split from `metering_and_pos.rs` so each file stays inside the repository's
//! 500-line ceiling. That file owns the module-level argument, the fixtures, the
//! routing test and the REFUTATION; `metering_and_pos_mirror.rs` owns the
//! independent op-counting mirror.

use super::metering_and_pos::{
    and_pos_step, app, charge, clearsy_shaped_conjunction, doubling_conjunction, emitted_and_pos,
    general_charge, measured_payload, shallow_model, shared_store_chain_conjunction, validate_one,
    PRODUCTION_ENVELOPE,
};
use super::metering_and_pos_mirror::mirror_and_pos;
use super::*;

fn payload(work: usize, unfolded: usize) -> PayloadStats {
    PayloadStats {
        work,
        bytes: 64,
        unfolded_work: unfolded,
        order_assignments: 0,
    }
}

/// TIGHTENING: over a wide payload sweep the class never charges more than the
/// `General` product it replaces, on either limb. This is the property that
/// makes the corpus-wide `ResourceLimit` count unable to RISE, without needing
/// a corpus argument.
#[test]
fn the_shallow_class_never_charges_more_than_the_general_product() {
    let mut strictly_cheaper = 0_usize;
    let step = ProofStep::Step {
        rule: AletheRule::AndPos(0),
        clause: Vec::new(),
        premises: Vec::new(),
        args: Vec::new(),
    };
    for unfolded in [
        1_usize, 2, 3, 8, 16, 64, 733, 5_502, 18_708, 100_000, 20_000_000,
    ] {
        for work in [
            1_usize,
            2,
            unfolded / 2 + 1,
            unfolded,
            40_922,
            unfolded * 4 + 7,
        ] {
            let stats = payload(work, unfolded);
            let (tight, bytes) =
                semantic_validator_charge(&step, stats, SemanticChargeClass::AndPosShallowMatch)
                    .expect("the modelled charge stays far below usize overflow");
            let legacy = general_charge(stats);
            assert!(
                tight <= legacy,
                "tightening must never charge more: unfolded={unfolded} work={work} \
                 tight={tight} legacy={legacy}"
            );
            assert_eq!(
                bytes, stats.bytes,
                "the byte limb must stay exactly where `General` left it"
            );
            if tight < legacy {
                strictly_cheaper += 1;
            }
        }
    }
    assert!(
        strictly_cheaper > 0,
        "the class must actually be cheaper somewhere, else it is a no-op"
    );
}

/// The MEASURED corpus payload, and the two numbers that motivated this class.
///
/// `--no-proof -T:10 --probe-strict-check` on
/// `benchmarks/smt/regression/soundness_qf_uf_incremental/
/// clearsy_0000_00307_falsesat13.smt2` printed, twice per strict check:
///
/// ```text
/// class=General on rule AndPos(29): work=225152844 bytes=580154
///   from payload(work=40922, unfolded_work=5502, bytes=580154)
/// class=General on rule AndPos(37): work=225152844 bytes=580154
///   from payload(work=40922, unfolded_work=5502, bytes=580154)
/// strict-check envelope refused: budget: work 239178107+225152848 of 350000000
/// ```
///
/// The payload and the per-step charge reproduce EXACTLY; the running total in
/// the refusal line does not, so only the former is asserted below.
///
/// Pinned here: the `General` product on that exact payload, WHICH LIMB
/// produces it, and what this class charges instead.
#[test]
fn the_measured_clearsy_payload_is_the_one_this_class_fixes() {
    let measured = payload(40_922, 5_502);
    assert_eq!(
        general_charge(measured),
        225_152_844,
        "the corpus figure must be reproduced exactly by the shipped model"
    );
    // The ask attributed this to the `unfolded_work^2` limb over a deeply
    // shared DAG. It is the `work * unfolded_work` limb, and the DAG payload is
    // 7.4x LARGER than the tree unfolding — there is no sharing-squared here.
    assert_eq!(measured.work * measured.unfolded_work, 225_152_844);
    assert_eq!(measured.unfolded_work * measured.unfolded_work, 30_272_004);
    assert!(measured.work > measured.unfolded_work * 7);

    let step = ProofStep::Step {
        rule: AletheRule::AndPos(29),
        clause: Vec::new(),
        premises: Vec::new(),
        args: Vec::new(),
    };
    let (tight, _) =
        semantic_validator_charge(&step, measured, SemanticChargeClass::AndPosShallowMatch)
            .expect("the modelled charge stays far below usize overflow");
    assert_eq!(tight, 1_309_536, "32 * 40_922 + 32");
    // Two such steps exhausted a 350 M envelope by themselves; two of the new
    // charge is under 1% of it.
    assert!(2 * general_charge(measured) > PRODUCTION_ENVELOPE);
    assert!(2 * tight < PRODUCTION_ENVELOPE / 100);
}

/// ADVERSARIAL 1 — DEEP SHARING, in the EMITTED shape.
///
/// A 40-level `store` chain whose value at each level reads the chain below it,
/// conjoined 24 ways: the reachable DAG is linear in the depth and the tree
/// unfolding is exponential. The `and_pos` step over it is
/// `(cl (not source) source_args[12])`, exactly what `proof_tracker` emits.
///
/// Checks, on the payload the REAL metering walk produces:
///  * the step is genuinely VALID and genuinely admitted to the class;
///  * the tree-unfolded payload is astronomically larger than the DAG;
///  * the `General` product alone exceeds the whole 350 M envelope;
///  * the new charge fits it with orders of magnitude to spare; and
///  * the new charge STILL BOUNDS the validator's own primitive count.
#[test]
fn a_deeply_shared_store_chain_and_pos_is_charged_on_its_dag() {
    let mut terms = TermStore::new();
    let source = shared_store_chain_conjunction(&mut terms, "deep", 40, 24);
    let (step, _) = emitted_and_pos(&mut terms, source, 12);
    validate_one(&terms, &step).expect("the emitted shape is a valid and_pos step");
    assert_eq!(
        select_semantic_charge_class(&step, &terms),
        SemanticChargeClass::AndPosShallowMatch
    );

    let stats = measured_payload(&step, &terms);
    assert!(
        stats.unfolded_work > stats.work * 1_000,
        "the fixture must really be sharing-dominated: work={} unfolded={}",
        stats.work,
        stats.unfolded_work
    );
    let legacy = general_charge(stats);
    assert!(
        legacy > PRODUCTION_ENVELOPE,
        "the charge this class replaces must genuinely exceed the envelope: {legacy}"
    );

    let (tight, bytes) = charge(&step, &terms, stats);
    assert_eq!(tight, shallow_model(stats));
    assert_eq!(bytes, stats.bytes);
    assert!(
        tight < PRODUCTION_ENVELOPE / 1_000,
        "and the replacement must fit with room to spare: {tight}"
    );

    let clause = step_clause(&step);
    let (ok, ops) = mirror_and_pos(&terms, &clause, 12, Some(source));
    assert!(ok, "the mirror must agree the step is valid");
    assert!(
        tight >= ops,
        "the model must BOUND the validator's real work: {tight} vs {ops}"
    );
}

/// ADVERSARIAL 2 — WIDE FAN-OUT, at the route's genuine worst case.
///
/// The only part of the admitted route that is not `O(1)` is the gate scan's
/// `inner_args == args` slice comparison, and reaching it at full width takes a
/// DECOY: a second `and` term sharing a 4_095-element prefix with the 4_096-wide
/// source, offered as `(not decoy)`. The emitted shape never gets there —
/// `strip_not(lit) == Some(source)` hits on the matcher's first line, which
/// `a_doubling_dag_in_the_emitted_shape_is_admitted_and_still_bounded` measures
/// at 11 primitives — so this fixture is what makes the `+ 2n` term of
/// `AND_POS_SHALLOW_WORK_FACTOR`'s derivation observable.
///
/// The step is REFUSED by the validator, and that is the point: the precharge is
/// levied BEFORE validation runs, so the model has to bound the work of a step
/// that will be rejected just as much as one that will be accepted.
#[test]
fn a_wide_fan_out_and_pos_is_still_charged_above_its_slice_comparison() {
    const WIDTH: usize = 4_096;
    let mut terms = TermStore::new();
    let source = clearsy_shaped_conjunction(&mut terms, WIDTH);
    let TermData::App(_, args) = terms.get(source).clone() else {
        panic!("the fixture must build an `and` application");
    };
    let odd_one_out = terms.mk_var("wide_decoy", Sort::Bool);
    let mut decoy_args = args.clone();
    let last = decoy_args.len() - 1;
    decoy_args[last] = odd_one_out;
    let decoy = app(&mut terms, "and", decoy_args);
    assert_ne!(decoy, source, "the decoy must be a DIFFERENT interned term");
    let gate = terms.mk_not_raw(decoy);
    let step = and_pos_step(vec![gate, args[2_048]], 2_048, source);

    assert_eq!(
        select_semantic_charge_class(&step, &terms),
        SemanticChargeClass::AndPosShallowMatch,
        "a `not`-headed decoy is still shallow: no literal or negand is or-headed"
    );
    validate_one(&terms, &step)
        .expect_err("the decoy is not the source's negation, so the step is refused");

    let stats = measured_payload(&step, &terms);
    let (tight, _) = charge(&step, &terms, stats);
    let clause = step_clause(&step);
    let (ok, ops) = mirror_and_pos(&terms, &clause, 2_048, Some(source));
    assert!(!ok, "the mirror must agree the step is refused");
    assert!(
        ops > WIDTH,
        "the fixture must really exercise the wide slice compare: ops={ops}"
    );
    assert!(
        tight >= ops,
        "the model must bound it: {tight} vs {ops} at width {WIDTH}"
    );

    // The charge must GROW with the payload, or it is a blanket exemption.
    let mut narrow_terms = TermStore::new();
    let narrow_source = clearsy_shaped_conjunction(&mut narrow_terms, 8);
    let (narrow_step, _) = emitted_and_pos(&mut narrow_terms, narrow_source, 4);
    let narrow_stats = measured_payload(&narrow_step, &narrow_terms);
    let (narrow, _) = charge(&narrow_step, &narrow_terms, narrow_stats);
    assert!(
        tight > narrow,
        "the charge must grow with the step's payload: {narrow} -> {tight}"
    );
}

/// ADVERSARIAL 3 — an EXPONENTIALLY UNFOLDING DAG that the class DOES admit.
///
/// The doubling conjunction `T_k = (and T_{k-1} T_{k-1})` in the emitted shape:
/// gate `(not T_k)`, conjunct `T_{k-1}`. The gate literal is a `Not`, not an
/// `or`, so the class admits it — and it must, because on THIS clause the
/// matcher really does return in `O(1)`: `strip_not((not T_k)) == Some(T_k)`
/// hits on the first line. Same DAG, same astronomical unfolding, opposite
/// verdict from
/// `metering_and_pos::a_doubling_and_pos_still_keeps_the_general_product` —
/// which is the whole point of gating on the LITERAL rather than on the term.
#[test]
fn a_doubling_dag_in_the_emitted_shape_is_admitted_and_still_bounded() {
    const DEPTH: usize = 20;
    let mut terms = TermStore::new();
    let (source, _) = doubling_conjunction(&mut terms, "emit", DEPTH);
    let (step, _) = emitted_and_pos(&mut terms, source, 0);
    validate_one(&terms, &step).expect("the emitted shape over a doubling DAG is valid");
    assert_eq!(
        select_semantic_charge_class(&step, &terms),
        SemanticChargeClass::AndPosShallowMatch
    );

    let stats = measured_payload(&step, &terms);
    assert!(
        stats.unfolded_work > (1_usize << DEPTH),
        "the unfolding must explode: {}",
        stats.unfolded_work
    );
    let clause = step_clause(&step);
    let (ok, ops) = mirror_and_pos(&terms, &clause, 0, Some(source));
    assert!(ok);
    assert!(
        ops < 64,
        "the admitted route really is constant-time here: ops={ops}"
    );
    let (tight, _) = charge(&step, &terms, stats);
    assert!(tight >= ops, "{tight} vs {ops}");
    assert!(
        tight < general_charge(stats),
        "and it must be strictly cheaper than the product it replaces"
    );
}

/// PARITY: the charge is not a blanket exemption. A genuinely enormous
/// `and_pos` still exhausts the envelope up front, and the end-to-end metered
/// entry point still refuses one.
#[test]
fn the_metering_still_refuses_an_oversized_and_pos_proof() {
    // Linear in `work`, so a large enough DAG payload still exceeds the
    // envelope by itself.
    let huge = payload(usize::MAX / 64, usize::MAX / 64);
    let step = ProofStep::Step {
        rule: AletheRule::AndPos(0),
        clause: Vec::new(),
        premises: Vec::new(),
        args: Vec::new(),
    };
    let (charged, _) =
        semantic_validator_charge(&step, huge, SemanticChargeClass::AndPosShallowMatch)
            .expect("a saturating cap keeps this representable");
    assert!(
        charged > PRODUCTION_ENVELOPE,
        "a genuinely huge payload must still exhaust the envelope: {charged}"
    );
    // The threshold is exact and stated on the constant: 350M / 32.
    let below = payload(10_000_000, 10_000_000);
    let (small, _) =
        semantic_validator_charge(&step, below, SemanticChargeClass::AndPosShallowMatch)
            .expect("representable");
    assert!(small < PRODUCTION_ENVELOPE);
    let above = payload(11_000_000, 11_000_000);
    let (big, _) = semantic_validator_charge(&step, above, SemanticChargeClass::AndPosShallowMatch)
        .expect("representable");
    assert!(big > PRODUCTION_ENVELOPE);

    // End to end, through the REAL metered entry point.
    let mut terms = TermStore::new();
    let source = clearsy_shaped_conjunction(&mut terms, 2_048);
    let (real_step, _) = emitted_and_pos(&mut terms, source, 1_024);
    let mut proof = Proof::new();
    proof.add_step(real_step);
    let mut spent = 0_usize;
    let mut tiny = |work: usize, _bytes: usize| {
        spent += work;
        spent <= 64
    };
    let refused =
        check_proof_strict_with_context_and_progress(&proof, &terms, None, None, None, &mut tiny)
            .expect_err("a 64-unit envelope cannot afford a 2048-conjunct and_pos");
    assert_eq!(refused, ProofCheckError::ResourceLimit);

    let mut unbounded = |_: usize, _: usize| true;
    let accepted = check_proof_strict_with_context_and_progress(
        &proof,
        &terms,
        None,
        None,
        None,
        &mut unbounded,
    );
    assert!(
        !matches!(accepted, Err(ProofCheckError::ResourceLimit)),
        "the same proof must not be resource-refused under an unbounded \
         envelope, or the test above proves nothing about the METER: {accepted:?}"
    );
}

/// PRINTER: the exact wire text of an `and_pos` step, pinned byte for byte.
///
/// This pass changes a CHARGE, and a charge must be invisible on the wire. The
/// step still prints `:rule and_pos` with its position `:args`, carries no
/// `hole` and no `trust`, and is unchanged whether or not the step is admitted
/// to the new class — the second assertion uses an `or`-headed conjunct with
/// the clause REVERSED, which both admission arms refuse (the identity arm is
/// ORDER-pinned; the emitted-order or-headed conjunct is now admitted by
/// `and_pos_is_emitted_identity_shape` and its printer invariance is carried
/// by the first pinned string), and gets the same shape of output.
#[test]
fn the_and_pos_wire_text_is_unchanged_by_the_charge_model() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("wire_a", Sort::Bool);
    let b = terms.mk_var("wire_b", Sort::Bool);
    let source = app(&mut terms, "and", vec![a, b]);
    let (admitted, _) = emitted_and_pos(&mut terms, source, 0);
    assert_eq!(
        select_semantic_charge_class(&admitted, &terms),
        SemanticChargeClass::AndPosShallowMatch
    );
    let disjunction = app(&mut terms, "or", vec![a, b]);
    let wide_source = app(&mut terms, "and", vec![disjunction, b]);
    let wide_gate = terms.mk_not_raw(wide_source);
    let declined = ProofStep::Step {
        rule: AletheRule::AndPos(0),
        clause: vec![disjunction, wide_gate],
        premises: Vec::new(),
        args: vec![wide_source],
    };
    assert_eq!(
        select_semantic_charge_class(&declined, &terms),
        SemanticChargeClass::General,
        "a reversed clause with an or-headed conjunct literal is declined by \
         both admission arms"
    );

    let printer = crate::AlethePrinter::new(&terms);
    let printed = printer
        .format_step(&admitted, ProofId(7))
        .expect("an emitted and_pos step prints");
    assert_eq!(
        printed,
        "(step t7 (cl (not (and wire_a wire_b)) wire_a) :rule and_pos :args (0))"
    );
    assert!(!printed.contains("hole"));
    assert!(!printed.contains("trust"));

    let declined_text = printer
        .format_step(&declined, ProofId(7))
        .expect("a declined and_pos step prints identically in shape");
    // The printer canonicalizes the gate literal first, so the DECLINED
    // (reversed-clause) step prints byte-identically to how the previously
    // pinned declined fixture printed — the charge boundary is invisible on
    // the wire in both directions.
    assert_eq!(
        declined_text,
        "(step t7 (cl (not (and (or wire_a wire_b) wire_b)) (or wire_a wire_b)) \
         :rule and_pos :args (0))"
    );
}

/// The FLOOR the whole derivation rests on: `payload.work >= n + 3`.
///
/// `AND_POS_SHALLOW_WORK_FACTOR`'s bound is `53 + 2n <= 32*work + 32`, and it is
/// only sound because the metering walk debits at least `n + 3` on a step this
/// class admits — 2 clause literals plus 1 `args` entry from `push_term_slice`,
/// then `args.len()` when `append_term_children` expands the source's `and`
/// node. That is a claim about `meter_step_term_payload`, not about
/// `validate_and_pos`, so it is measured against the REAL walk here, over four
/// orders of magnitude of arity — including `n = 1`, the smallest conjunction an
/// `and_pos` step can name.
///
/// Without this the constant could be justified by a derivation whose premise
/// had silently stopped holding.
#[test]
fn the_payload_walk_floor_the_derivation_rests_on_holds() {
    for arity in [1_usize, 2, 3, 8, 64, 1_024, 4_096] {
        let mut terms = TermStore::new();
        let source = clearsy_shaped_conjunction(&mut terms, arity);
        let (step, _) = emitted_and_pos(&mut terms, source, (arity - 1) as u32);
        validate_one(&terms, &step).expect("the emitted shape is a valid and_pos step");
        assert_eq!(
            select_semantic_charge_class(&step, &terms),
            SemanticChargeClass::AndPosShallowMatch
        );
        let stats = measured_payload(&step, &terms);
        assert!(
            stats.work >= arity + 3,
            "the payload floor must hold at arity {arity}: work={}",
            stats.work
        );
        // And the charge the floor licenses really does dominate the counted
        // worst case `53 + 2n` at this arity.
        let (tight, _) = charge(&step, &terms, stats);
        assert!(
            tight >= 53 + 2 * arity,
            "the charge must dominate the counted worst case at arity {arity}: \
             {tight} vs {}",
            53 + 2 * arity
        );
    }
}

fn step_clause(step: &ProofStep) -> Vec<TermId> {
    match step {
        ProofStep::Step { clause, .. } => clause.clone(),
        _ => panic!("expected an Alethe step"),
    }
}
