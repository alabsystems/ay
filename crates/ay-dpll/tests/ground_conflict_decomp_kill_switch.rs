// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Kill-switch coverage for the ground-conflict decomposition arms
//! (#ground-conflict-decomp).
//!
//! This file deliberately holds ONE switch test in its own binary: it
//! installs a thread-local `MiscCliFlags` override, which must never race a
//! sibling test that could run interleaved on the same thread. The three
//! checker-authority tests below read no override and share the binary
//! safely.

#![allow(clippy::panic)]

mod common;

/// Two GROUND-conflict quantified refutations whose certification died at
/// baseline on Generic theory lemmas: the array-frame invariant (fused
/// EUF+LIA conflicts, healed by the EUF-chain + Farkas-bridge arm plus the
/// EUF-leaf const-clash conclusion) and the read-over-write-under-equality
/// instance (healed by the guarded `ArrayRowChain` arm). With
/// `--no-ground-conflict-decomp` both decomposition arms are disabled and
/// every Generic lemma stays byte-identical; with the switch on the same
/// inputs must decide `unsat`. A genuinely satisfiable soundness control must
/// stay non-unsat in BOTH modes.
///
/// WHAT THE `OFF` HALF PINS, AND WHY IT IS NO LONGER A DOWNGRADE. Both unsat
/// fixtures once dropped to `unknown` with the switch off; both have since
/// acquired certification routes that do not run either arm (for the frame
/// goal see the note at its own `off_frame` assertion below), so pinning a
/// downgrade here would pin the ABSENCE of a capability rather than the
/// coverage of this switch. For the RoW instance the route is MEASURED.
/// Commit `18eb6a62c7` taught the checker's `eval_chain_at` to discharge a
/// skip guard between two DISTINCT INTERPRETED NUMERALS itself, so
/// `ay_proof::recognize_array_theory_lemma` now answers `ArrayRowChain` for
/// the raw or-packed instance `(or ¬(= b (store a 3 9)) (= b[1] a[1]))`, and
/// `Executor::record_array_axiom_proof` — the array solver's own
/// axiom-instantiation recorder in `executor/theories/euf.rs`, which asks that
/// same recognizer for a rule and takes no authority of its own — records a
/// CHECKED array lemma where it used to record an explicit TRUST leaf. Both
/// decomposition arms live in `split_euf_congruence_lemmas`'s trust-lemma
/// cascade, which only a trust leaf can reach; with the leaf gone they are
/// never consulted.
///
/// THE SWITCH ITSELF IS NOT LEAKING. Measured with per-arm probes on this
/// fixture: with the switch OFF neither arm is planned even once, and with
/// the switch ON they are not planned for the RoW input either — the fixture
/// stopped needing arm 2 rather than the arm escaping the switch. Reverting
/// only that one checker disjunct restores, verdict for verdict, `unknown`
/// with the switch off and `unsat` through a planned arm 2 with it on. So the
/// `unsat` below is a route the switch never claimed to cover; what must
/// never weaken is the soundness direction, asserted for every fixture here.
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
    // The frame goal is GENUINELY unsat (snew = [10, val>=0, 30] has no
    // negative entry), and it is now reachable with this switch off: other
    // certification routes have since landed that do not depend on ground-
    // conflict decomposition, so pinning a downgrade here would pin the
    // absence of capability rather than the coverage of this switch.
    // Verified at the CLI with BOTH this switch and --no-consequence-replay
    // set: still `unsat`. What must never weaken is the soundness direction,
    // asserted for the genuinely-SAT control below in both modes.
    assert!(
        off_frame.iter().all(|r| r != "sat"),
        "the frame goal is unsatisfiable; a `sat` here would be a wrong \
         answer regardless of which lane produced it; got {off_frame:?}"
    );
    assert!(
        off_guarded_frame.iter().all(|r| r != "sat"),
        "the guarded frame goal is unsatisfiable; a `sat` here would be a \
         wrong answer regardless of lane; got {off_guarded_frame:?}"
    );
    assert!(
        off_row.iter().all(|r| r != "sat"),
        "the RoW goal is unsatisfiable; a `sat` here would be a wrong answer \
         regardless of which lane produced it (the doc comment names the lane \
         that reaches it without either arm); got {off_row:?}"
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
        "the RoW refutation must certify with the switch on (today through \
         the recorder lane, not arm 2 — see the doc comment); got {on_row:?}"
    );
    assert!(
        !on_control.iter().any(|r| r == "unsat"),
        "the genuinely satisfiable control must never decide unsat (switch \
         on); got {on_control:?}"
    );
}

/// GUARD-REMOVAL PROOF (checker authority, arm 2): the strict checker — not
/// the producer — is the authority on the `ArrayRowChain` schema. The lemma
/// shape the producer emits for a read-over-write-under-equality instance
/// validates WITH its skip-guard literal and is REJECTED without it, so
/// deleting the guard from an emitted clause can never survive certification.
///
/// STATED OVER VARIABLE INDICES `i`/`j`, and that is the point. This control
/// was originally written over the v11 instance's NUMERAL pair `1`/`3`, where
/// the unguarded clause `(cl ¬(= b (store a 3 9)) (= b[1] a[1]))` is a
/// THEOREM: `1 != 3` holds in every model, so no clause literal has to
/// discharge it and accepting the clause is SOUND. Commit `18eb6a62c7` taught
/// `eval_chain_at` exactly that side condition (`distinct_interpreted_indices`
/// — byte-identically the one `TermStore::mk_select` already uses to perform
/// the same fold), so the checker now discharges a numeral guard itself and
/// the numeral form of this control stopped catching anything. That capability
/// is pinned as a positive by
/// `a_numeral_skip_guard_is_discharged_by_the_checker_itself` below.
///
/// Nothing discharges `i != j`, so over variables the unguarded clause is not
/// merely unrecognized — it is FALSE. At `i = j`, `a[i] = 0`, `v = 1` the
/// premise `b = store(a, j, v)` HOLDS, so `¬(b = store(a, j, v))` is false;
/// and `b[i] = 1` while `a[i] = 0`, so the conclusion is false too. A checker
/// that accepted it would be UNSOUND, which is strictly more than the numeral
/// form ever tested.
#[test]
fn row_chain_without_skip_guard_is_rejected_by_the_untouched_checker() {
    use ay_core::{ProofStep, Sort, Symbol, TheoryLemmaKind};

    let mut terms = ay_core::TermStore::new();
    let array_sort = Sort::array(Sort::Int, Sort::Int);
    let a = terms.mk_var("kill_switch_row_a", array_sort.clone());
    let b = terms.mk_var("kill_switch_row_b", array_sort);
    let read_index = terms.mk_var("kill_switch_row_i", Sort::Int);
    let write_index = terms.mk_var("kill_switch_row_j", Sort::Int);
    let written = terms.mk_var("kill_switch_row_v", Sort::Int);
    let store = terms.mk_app(Symbol::named("store"), [a, write_index, written], {
        Sort::array(Sort::Int, Sort::Int)
    });
    let eq_arrays = terms.mk_app(Symbol::named("="), [b, store], Sort::Bool);
    let not_eq_arrays = terms.mk_not_raw(eq_arrays);
    let read_b = terms.mk_app(Symbol::named("select"), [b, read_index], Sort::Int);
    let read_a = terms.mk_app(Symbol::named("select"), [a, read_index], Sort::Int);
    let read_eq = terms.mk_app(Symbol::named("="), [read_b, read_a], Sort::Bool);
    let guard = terms.mk_app(Symbol::named("="), [read_index, write_index], Sort::Bool);

    let not_read_eq = terms.mk_not_raw(read_eq);
    let not_guard = terms.mk_not_raw(guard);

    // The derivation the producer emits: the guarded RowChain lemma resolved
    // against the skip disequality and the two assumed complements. `i != j`
    // is NOT a theorem, so it enters as an ASSUMPTION rather than as the
    // certified Farkas unit the numeral instance is entitled to mint (see
    // `constant_disequality_unit_certificate_is_checker_refereed`).
    let mut guarded = ay_core::Proof::new();
    let h_eq = guarded.add_assume(eq_arrays, None);
    let h_neq = guarded.add_assume(not_read_eq, None);
    let h_diseq = guarded.add_assume(not_guard, None);
    let lemma = guarded.add_step(ProofStep::TheoryLemma {
        theory: "array".to_string(),
        clause: vec![not_eq_arrays, guard, read_eq],
        farkas: None,
        kind: TheoryLemmaKind::ArrayRowChain,
        lia: None,
    });
    let r1 = guarded.add_resolution(vec![not_eq_arrays, read_eq], guard, h_diseq, lemma);
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
    let verdict = ay_proof::check_proof_strict(&unguarded, &terms);
    assert!(
        verdict.is_err(),
        "dropping the (= i j) skip-guard literal must be rejected by the \
         untouched checker — the guard is load-bearing, not decorative"
    );
    // ...and rejected for THAT reason. Without this the control would also
    // pass on an unrelated structural complaint about the surrounding
    // resolution chain, which is not the property it exists to pin.
    let reason = format!("{verdict:?}");
    assert!(
        matches!(
            verdict,
            Err(ay_proof::ProofCheckError::InvalidTheoryLemma { .. })
        ) && reason.contains("does not match the exact schema"),
        "the rejection must come from the RowChain schema refusing the \
         unjustified skip; got {reason}"
    );
}

/// The capability that made the numeral form of the control above stale,
/// pinned as an explicit POSITIVE rather than merely tolerated: when the read
/// index and the skipped store index are DISTINCT INTERPRETED NUMERALS the
/// checker discharges the skip guard itself and accepts the guard-free lemma.
/// That is sound — `1 != 3` is true in every model, so
/// `(cl ¬(= b (store a 3 9)) (= b[1] a[1]))` is a theorem, and the checker is
/// only re-deriving the fold `TermStore::mk_select` already performs under the
/// same side condition.
///
/// The paired MUTATION is the same derivation with the write moved ONTO the
/// read index, `store(a, 1, 9)`. The two numerals then coincide, the clause is
/// genuinely FALSE (`b[1] = 9` while `a[1]` is unconstrained), and the same
/// checker must refuse it — so the acceptance is keyed on numeral
/// DISTINCTNESS, not on the indices merely being numerals.
#[test]
fn a_numeral_skip_guard_is_discharged_by_the_checker_itself() {
    use ay_core::{ProofStep, Sort, Symbol, TheoryLemmaKind};

    // `(cl ¬(= b (store a <write_at> 9)) (= b[1] a[1]))` with NO skip guard,
    // closed into an empty-clause derivation, put to the strict checker.
    let unguarded_numeral_chain_checks = |write_at: i64| -> bool {
        let mut terms = ay_core::TermStore::new();
        let array_sort = Sort::array(Sort::Int, Sort::Int);
        let a = terms.mk_var("kill_switch_row_a", array_sort.clone());
        let b = terms.mk_var("kill_switch_row_b", array_sort);
        let one = terms.mk_int(1.into());
        let write_index = terms.mk_int(write_at.into());
        let nine = terms.mk_int(9.into());
        let store = terms.mk_app(Symbol::named("store"), [a, write_index, nine], {
            Sort::array(Sort::Int, Sort::Int)
        });
        let eq_arrays = terms.mk_app(Symbol::named("="), [b, store], Sort::Bool);
        let not_eq_arrays = terms.mk_not_raw(eq_arrays);
        let read_b = terms.mk_app(Symbol::named("select"), [b, one], Sort::Int);
        let read_a = terms.mk_app(Symbol::named("select"), [a, one], Sort::Int);
        let read_eq = terms.mk_app(Symbol::named("="), [read_b, read_a], Sort::Bool);
        let not_read_eq = terms.mk_not_raw(read_eq);

        let mut proof = ay_core::Proof::new();
        let h_eq = proof.add_assume(eq_arrays, None);
        let h_neq = proof.add_assume(not_read_eq, None);
        let lemma = proof.add_step(ProofStep::TheoryLemma {
            theory: "array".to_string(),
            clause: vec![not_eq_arrays, read_eq],
            farkas: None,
            kind: TheoryLemmaKind::ArrayRowChain,
            lia: None,
        });
        let r1 = proof.add_resolution(vec![read_eq], eq_arrays, lemma, h_eq);
        proof.add_resolution(Vec::new(), read_eq, h_neq, r1);
        ay_proof::check_proof_strict(&proof, &terms).is_ok()
    };

    assert!(
        unguarded_numeral_chain_checks(3),
        "`1 != 3` is ground, so the checker discharges the skip guard itself \
         and the guard-free numeral lemma must validate"
    );
    assert!(
        !unguarded_numeral_chain_checks(1),
        "writing AT the read index makes the same guard-free clause FALSE \
         (b[1] = 9 with a[1] unconstrained), so the checker must refuse it — \
         the acceptance above is keyed on numeral DISTINCTNESS, not on the \
         index being a numeral"
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
