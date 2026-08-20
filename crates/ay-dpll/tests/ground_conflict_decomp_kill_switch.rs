// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Kill-switch coverage for the ground-conflict decomposition arms
//! (#ground-conflict-decomp).
//!
//! This file deliberately holds ONE switch test in its own binary: it
//! installs a thread-local `MiscCliFlags` override, which must never race a
//! sibling test that could run interleaved on the same thread. The two
//! checker-authority tests below read no override and share the binary
//! safely.

#![allow(clippy::panic)]

mod common;

/// Two GROUND-conflict quantified refutations whose certification dies at
/// baseline on Generic theory lemmas: the array-frame invariant (fused
/// EUF+LIA conflicts, healed by the EUF-chain + Farkas-bridge arm plus the
/// EUF-leaf const-clash conclusion) and the read-over-write-under-equality
/// instance (healed by the guarded `ArrayRowChain` arm). With
/// `--no-ground-conflict-decomp` both decomposition arms are disabled, every
/// Generic lemma stays byte-identical, and the mandatory certification gate
/// must restore the baseline `unknown`s; with the switch back on the same
/// inputs must decide `unsat`. A genuinely satisfiable soundness control
/// must stay non-unsat in BOTH modes.
#[test]
fn ground_conflict_decomp_is_fully_covered_by_the_kill_switch() {
    let frame_smt = r#"
        (set-logic ALL)
        (declare-fun s () (Array Int Int))
        (declare-fun snew () (Array Int Int))
        (declare-fun val () Int)
        (assert (= (select s 0) 10))
        (assert (= (select s 1) 20))
        (assert (= (select s 2) 30))
        (assert (>= val 0))
        (assert (forall ((k Int)) (= (select snew k) (ite (= k 1) val (select s k)))))
        (assert (exists ((j Int)) (and (<= 0 j) (< j 3) (< (select snew j) 0))))
        (check-sat)
    "#;
    let row_smt = r#"
        (set-logic AUFLIA)
        (declare-fun a () (Array Int Int))
        (declare-fun b () (Array Int Int))
        (assert (= b (store a 3 9)))
        (assert (forall ((i Int)) (=> (distinct i 3) (= (select b i) (+ (select a i) 1)))))
        (check-sat)
    "#;
    // The full Verus-faithful u64-guarded frame shape (#ground-conflict-decomp
    // residual): its consequence-replay probe used to die on the guard-dropped
    // integer disequality-split core `(cl (<= sk 0) (<= 2 sk))` — the
    // combined-theory decomposition classified the all-integer sub-conflict
    // `LiaGeneric` without verification and the weakened recorder downgraded
    // it to a Generic trust step falsified at sk=1. The same switch now covers
    // BOTH the whole-conflict `ArithDisequalitySplit` classifier arm and the
    // decomposition's refusal of evidence-free `LiaGeneric` cores.
    //
    // Only the never-unsat OFF half is asserted here: with the arms ON the
    // fixture certifies `unsat` on the RELEASE binary (measured repeatedly at
    // the CLI), but the dev-profile solve does not fit the fixed
    // consequence-replay probe budget, so an ON->unsat assertion would pin a
    // wall-clock property this profile cannot deliver (the sibling group
    // test `array_frame_u64_guarded_witness_discharges_unsat` pins the
    // ON-side verdict).
    let guarded_frame_smt = r#"
        (set-logic ALL)
        (declare-fun s () (Array Int Int))
        (declare-fun snew () (Array Int Int))
        (declare-fun val () Int)
        (assert (= (select s 0) 10))
        (assert (= (select s 1) 20))
        (assert (= (select s 2) 30))
        (assert (>= val 0))
        (assert (forall ((k Int)) (= (select snew k) (ite (= k 1) val (select s k)))))
        (assert (exists ((j Int))
            (and (>= j 0) (< j 18446744073709551616) (< j 3) (< (select snew j) 0))))
        (check-sat)
    "#;
    // Genuinely SAT: the update writes -1 at index 0, so the frame goal is
    // violated and a certified `unsat` here would be a false Verified.
    let control_smt = r#"
        (set-logic ALL)
        (declare-fun a () (Array Int Int))
        (declare-fun anew () (Array Int Int))
        (assert (= (select a 0) 5))
        (assert (= (select a 1) 7))
        (assert (forall ((k Int)) (= (select anew k) (ite (= k 0) (- 1) (select a k)))))
        (assert (exists ((j Int)) (and (<= 0 j) (< j 2) (< (select anew j) 0))))
        (check-sat)
    "#;

    let off_guard = ay_core::misc_test_override::set(ay_core::MiscCliFlags {
        no_ground_conflict_decomp: true,
        ..Default::default()
    });
    let off_frame = common::solve_vec(frame_smt);
    let off_guarded_frame = common::solve_vec(guarded_frame_smt);
    let off_row = common::solve_vec(row_smt);
    let off_control = common::solve_vec(control_smt);
    drop(off_guard);
    assert!(
        !off_frame.iter().any(|r| r == "unsat"),
        "with the kill switch off the frame refutation's Generic lemmas stay \
         uncertifiable and the mandatory gate must restore the baseline \
         downgrade; got {off_frame:?}"
    );
    assert!(
        !off_guarded_frame.iter().any(|r| r == "unsat"),
        "with the kill switch off the disequality-split classifier arm and \
         the decomposition core filter are both disabled, the guard-dropped \
         2-literal core is recorded as trust again, and the mandatory gate \
         must restore the baseline downgrade; got {off_guarded_frame:?}"
    );
    assert!(
        !off_row.iter().any(|r| r == "unsat"),
        "with the kill switch off the RoW-under-equality Generic lemma stays \
         uncertifiable and the mandatory gate must restore the baseline \
         downgrade; got {off_row:?}"
    );
    assert!(
        !off_control.iter().any(|r| r == "unsat"),
        "the genuinely satisfiable control must never decide unsat (switch \
         off); got {off_control:?}"
    );

    let on_frame = common::solve_vec(frame_smt);
    let on_guarded_frame = common::solve_vec(guarded_frame_smt);
    let on_row = common::solve_vec(row_smt);
    let on_control = common::solve_vec(control_smt);
    assert!(
        on_frame.iter().any(|r| r == "unsat"),
        "with the kill switch on (default) the decomposition arms must let \
         the frame refutation certify; got {on_frame:?}"
    );
    assert!(
        !on_guarded_frame.iter().any(|r| r == "sat"),
        "the u64-guarded frame obligation is genuinely UNSAT and must never \
         decide sat; got {on_guarded_frame:?}"
    );
    assert!(
        on_row.iter().any(|r| r == "unsat"),
        "with the kill switch on (default) the guarded ArrayRowChain arm \
         must let the RoW refutation certify; got {on_row:?}"
    );
    assert!(
        !on_control.iter().any(|r| r == "unsat"),
        "the genuinely satisfiable control must never decide unsat (switch \
         on); got {on_control:?}"
    );
}

/// GUARD-REMOVAL PROOF (checker authority, arm 2): the strict checker — not
/// the producer — is the authority on the `ArrayRowChain` schema. The exact
/// lemma the producer emits for the v11 RoW instance validates WITH its
/// `(= 1 3)` skip-guard literal and is REJECTED without it, so deleting the
/// guard from the emitted clause can never survive certification.
#[test]
fn row_chain_without_skip_guard_is_rejected_by_the_untouched_checker() {
    use ay_core::{ProofStep, Sort, Symbol, TheoryLemmaKind};

    let mut terms = ay_core::TermStore::new();
    let array_sort = Sort::array(Sort::Int, Sort::Int);
    let a = terms.mk_var("kill_switch_row_a", array_sort.clone());
    let b = terms.mk_var("kill_switch_row_b", array_sort);
    let one = terms.mk_int(1.into());
    let three = terms.mk_int(3.into());
    let nine = terms.mk_int(9.into());
    let store = terms.mk_app(Symbol::named("store"), [a, three, nine], {
        Sort::array(Sort::Int, Sort::Int)
    });
    let eq_arrays = terms.mk_app(Symbol::named("="), [b, store], Sort::Bool);
    let not_eq_arrays = terms.mk_not_raw(eq_arrays);
    let read_b = terms.mk_app(Symbol::named("select"), [b, one], Sort::Int);
    let read_a = terms.mk_app(Symbol::named("select"), [a, one], Sort::Int);
    let read_eq = terms.mk_app(Symbol::named("="), [read_b, read_a], Sort::Bool);
    let guard = terms.mk_app(Symbol::named("="), [one, three], Sort::Bool);

    let not_read_eq = terms.mk_not_raw(read_eq);
    let not_guard = terms.mk_not_raw(guard);
    let guard_farkas = ay_core::FarkasAnnotation::from_ints(&[1]);

    // The exact derivation the producer emits: guarded RowChain lemma, the
    // certified `(cl ¬(= 1 3))` unit, and resolutions to the empty clause
    // against the two assumed complements.
    let mut guarded = ay_core::Proof::new();
    let h_eq = guarded.add_assume(eq_arrays, None);
    let h_neq = guarded.add_assume(not_read_eq, None);
    let lemma = guarded.add_step(ProofStep::TheoryLemma {
        theory: "array".to_string(),
        clause: vec![not_eq_arrays, guard, read_eq],
        farkas: None,
        kind: TheoryLemmaKind::ArrayRowChain,
        lia: None,
    });
    let diseq = guarded.add_step(ProofStep::TheoryLemma {
        theory: "LIA".to_string(),
        clause: vec![not_guard],
        farkas: Some(guard_farkas.clone()),
        kind: TheoryLemmaKind::LiaGeneric,
        lia: None,
    });
    let r1 = guarded.add_resolution(vec![not_eq_arrays, read_eq], guard, diseq, lemma);
    let r2 = guarded.add_resolution(vec![read_eq], eq_arrays, r1, h_eq);
    guarded.add_resolution(Vec::new(), read_eq, h_neq, r2);
    assert!(
        ay_proof::check_proof_strict(&guarded, &terms).is_ok(),
        "the guarded RowChain derivation is the exact schema the checker \
         accepts: {:?}",
        ay_proof::check_proof_strict(&guarded, &terms)
    );

    // Identical derivation with the skip-guard literal DELETED from the
    // lemma: structurally still an empty-clause proof, but the lemma no
    // longer matches the RowChain schema and must be rejected.
    let mut unguarded = ay_core::Proof::new();
    let h_eq = unguarded.add_assume(eq_arrays, None);
    let h_neq = unguarded.add_assume(not_read_eq, None);
    let lemma = unguarded.add_step(ProofStep::TheoryLemma {
        theory: "array".to_string(),
        clause: vec![not_eq_arrays, read_eq],
        farkas: None,
        kind: TheoryLemmaKind::ArrayRowChain,
        lia: None,
    });
    let r1 = unguarded.add_resolution(vec![read_eq], eq_arrays, lemma, h_eq);
    unguarded.add_resolution(Vec::new(), read_eq, h_neq, r1);
    assert!(
        ay_proof::check_proof_strict(&unguarded, &terms).is_err(),
        "dropping the (= 1 3) skip-guard literal must be rejected by the \
         untouched checker — the guard is load-bearing, not decorative"
    );
}

/// GUARD-REMOVAL PROOF (checker authority, arm 1 bridge): the independently
/// verified Farkas certificate is what carries the constant-disequality unit
/// `(cl ¬(= 1 20))`; a unit over two EQUAL numerals (a satisfiable claim) is
/// refused by the same verifier, so the producer cannot mint a certificate
/// for a wrong clause.
#[test]
fn constant_disequality_unit_certificate_is_checker_refereed() {
    use ay_core::{ProofStep, Sort, Symbol, TheoryLemmaKind};

    let mut terms = ay_core::TermStore::new();
    let one = terms.mk_int(1.into());
    let twenty = terms.mk_int(20.into());
    let raw_diseq = terms.mk_app(Symbol::named("="), [one, twenty], Sort::Bool);
    let unit = terms.mk_not_raw(raw_diseq);
    let farkas = ay_core::FarkasAnnotation::from_ints(&[1]);

    let mut valid = ay_core::Proof::new();
    let h = valid.add_assume(raw_diseq, None);
    let lemma = valid.add_step(ProofStep::TheoryLemma {
        theory: "LIA".to_string(),
        clause: vec![unit],
        farkas: Some(farkas.clone()),
        kind: TheoryLemmaKind::LiaGeneric,
        lia: None,
    });
    valid.add_resolution(Vec::new(), raw_diseq, lemma, h);
    assert!(
        ay_proof::check_proof_strict(&valid, &terms).is_ok(),
        "the certified distinct-numeral disequality unit must validate: {:?}",
        ay_proof::check_proof_strict(&valid, &terms)
    );

    // (= 1 1) raw: asserting it is satisfiable — no certificate exists.
    let raw_refl = terms.mk_app(Symbol::named("="), [one, one], Sort::Bool);
    let wrong_unit = terms.mk_not_raw(raw_refl);
    let mut wrong = ay_core::Proof::new();
    let h = wrong.add_assume(raw_refl, None);
    let lemma = wrong.add_step(ProofStep::TheoryLemma {
        theory: "LIA".to_string(),
        clause: vec![wrong_unit],
        farkas: Some(farkas),
        kind: TheoryLemmaKind::LiaGeneric,
        lia: None,
    });
    wrong.add_resolution(Vec::new(), raw_refl, lemma, h);
    assert!(
        ay_proof::check_proof_strict(&wrong, &terms).is_err(),
        "a unit refuting an EQUAL-numeral equality must be rejected — the \
         Farkas verifier, not the producer, is the authority"
    );
}
