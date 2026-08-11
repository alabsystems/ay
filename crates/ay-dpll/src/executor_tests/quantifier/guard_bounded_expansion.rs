// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Guard-bounded finite-binder expansion in the quantified model gate
//! (#quantified-model-gate, `quantified_gate_guard_bounded_bv_domain`).
//!
//! The guarded pointwise-axiom shape verifier encoders emit for fixed-length
//! collections — `∀i. i <u len ⇒ a[i] = f(i)` with a LITERAL `len` — used to
//! fail closed at the gate: the wide (BV64) binder is not enumerable by
//! width, and the nested certification solve cannot decide the folded
//! bv2nat-mixing residue, so a genuinely satisfiable out-of-range read
//! degraded Sat → Unknown (deductive-checks `seq_from_fn` red, R1 2026-07-18). The
//! guard makes the matrix vacuous outside `[0, len)`, so expanding the binder
//! over exactly that range is a pure logical equivalence; the instances then
//! ground-fold and evaluate exactly against the emitted witness.

use super::*;

/// Int-element collection axiom + out-of-range read: the read at index 7 is
/// unconstrained (len 5), so the query is SAT and the gate must certify the
/// witness through the guard-bounded expansion (the nested-solve route cannot
/// decide the `bv2nat`-mixing residue).
#[test]
fn guarded_pointwise_axiom_out_of_range_int_read_is_sat() {
    let input = r#"
        (set-logic ALL)
        (declare-const s (Array (_ BitVec 64) Int))
        (assert (forall ((i (_ BitVec 64)))
          (! (=> (bvult i #x0000000000000005) (= (select s i) (* 10 (bv2int i))))
             :pattern ((select s i)))))
        (assert (=> (bvult #x0000000000000000 #x0000000000000005) (= (select s #x0000000000000000) 0)))
        (assert (=> (bvult #x0000000000000001 #x0000000000000005) (= (select s #x0000000000000001) 10)))
        (assert (=> (bvult #x0000000000000002 #x0000000000000005) (= (select s #x0000000000000002) 20)))
        (assert (=> (bvult #x0000000000000003 #x0000000000000005) (= (select s #x0000000000000003) 30)))
        (assert (=> (bvult #x0000000000000004 #x0000000000000005) (= (select s #x0000000000000004) 40)))
        (assert (= (select s #x0000000000000007) 0))
        (check-sat)
    "#;

    let commands = parse(input).expect("valid SMT-LIB input");
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).expect("execution succeeds");

    assert_eq!(
        outputs,
        vec!["sat"],
        "out-of-range read of a guarded pointwise Seq axiom must stay SAT (R1)"
    );
}

/// Pure-BV element variant of the same shape (deductive-checks
/// `seq_from_fn_out_of_bounds_region_is_unconstrained` encoding).
#[test]
fn guarded_pointwise_axiom_out_of_range_bv_read_is_sat() {
    let input = r#"
        (set-logic ALL)
        (declare-const s (Array (_ BitVec 64) (_ BitVec 32)))
        (assert (forall ((i (_ BitVec 64)))
          (! (=> (bvult i #x0000000000000002) (= (select s i) ((_ extract 31 0) i)))
             :pattern ((select s i)))))
        (assert (= (select s #x0000000000000005) #x00000000))
        (check-sat)
    "#;

    let commands = parse(input).expect("valid SMT-LIB input");
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).expect("execution succeeds");

    assert_eq!(outputs, vec!["sat"]);
}

/// Soundness twin: an IN-range read conflicting with the axiom must stay
/// refuted — the expansion is an equivalence, so it can never weaken the
/// UNSAT direction.
#[test]
fn guarded_pointwise_axiom_in_range_conflict_stays_unsat() {
    let input = r#"
        (set-logic ALL)
        (declare-const s (Array (_ BitVec 64) Int))
        (assert (forall ((i (_ BitVec 64)))
          (! (=> (bvult i #x0000000000000005) (= (select s i) (* 10 (bv2int i))))
             :pattern ((select s i)))))
        (assert (= (select s #x0000000000000002) 25))
        (check-sat)
    "#;

    let commands = parse(input).expect("valid SMT-LIB input");
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).expect("execution succeeds");

    assert_eq!(
        outputs,
        vec!["unsat"],
        "in-range conflicting read must stay refuted under the expansion"
    );
}

// ---------------------------------------------------------------------------
// #bv-forall-const-expansion — the expansion PROVENANCE record must survive an
// expansion whose instances constant-fold.
//
// `expand_finite_domains` replaces a guard-bounded BV `forall` in place by the
// conjunction over its guard range and records a `QuantExpansionRecord`. That
// struct carries two independent things:
//
//   * `instances` — proof-export PAYLOAD (the conjuncts a `forall_inst`
//     derivation can re-derive). A constant instance has nothing to derive, so
//     dropping it is right.
//   * the record's EXISTENCE — the authenticated fact that this exact authored
//     `forall` was replaced in place by the canonical expansion, which
//     `result_mapping`'s BV full-domain recognizer reads ("capability is not
//     evidence") before granting `bv_quantifier_full_domain_proof`, the
//     certificate that lets the restored `forall` keep its `Sat`.
//
// Gating the record on a non-empty payload conflated the two and withdrew the
// authentication for exactly the expansions that discharged the quantifier
// COMPLETELY. Measured at cbb3157aeb, release binary, oracle z3 5.0.0:
//
//   forall x:BV8. (0 <u x or f(x) = 0)  -> ay sat      z3 sat  (payload survives)
//   forall x:BV8. (0 <u x or x = 0)     -> ay unknown  z3 sat  (payload empties)
//
// Same guard, same expansion range [0,0], same route; the only difference is
// whether the instantiated body constant-folds.

/// The instance `(= #x00 #x00)` folds to `true`, emptying the record's payload.
/// Measured `unknown` before the fix (`(:reason-unknown (incomplete
/// quantifier-ematching-exists))` — the quantifier loop refuses, the model gate
/// never runs); z3 5.0.0 answers `sat`.
#[test]
fn constant_folded_guard_expansion_keeps_sat() {
    let input = r#"
        (set-logic ALL)
        (assert (forall ((x (_ BitVec 8))) (or (bvult #x00 x) (= x #x00))))
        (check-sat)
    "#;

    let commands = parse(input).expect("valid SMT-LIB input");
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).expect("execution succeeds");

    assert_eq!(
        outputs,
        vec!["sat"],
        "a guard-bounded BV forall the expansion fully discharged must keep its \
         Sat even when every instance constant-folds (#bv-forall-const-expansion)"
    );
}

/// The same defect through the OTHER exit: the two guard disjuncts pin an EMPTY
/// range (`hi < lo`), so the expander folds straight to `true` and records no
/// instance at all. Also measured `unknown` before the fix; z3 5.0.0: `sat`.
#[test]
fn empty_guard_range_expansion_keeps_sat() {
    let input = r#"
        (set-logic ALL)
        (assert (forall ((x (_ BitVec 8))) (or (bvult #x00 x) (bvule x #x00))))
        (check-sat)
    "#;

    let commands = parse(input).expect("valid SMT-LIB input");
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).expect("execution succeeds");

    assert_eq!(
        outputs,
        vec!["sat"],
        "an empty-guard-range BV forall folded to `true` must keep its Sat \
         (#bv-forall-const-expansion)"
    );
}

/// NON-VACUITY, half 1 of 2. A three-point guard range `[0, 2]` whose instances
/// ALL constant-fold to `true`, so the certificate this change restores is what
/// carries the verdict. Measured `unknown` before the fix; z3 5.0.0: `sat`.
#[test]
fn constant_folded_multipoint_guard_expansion_keeps_sat() {
    let input = r#"
        (set-logic ALL)
        (assert (forall ((x (_ BitVec 8))) (or (bvult #x02 x) (= (bvand x #x03) x))))
        (check-sat)
    "#;

    let commands = parse(input).expect("valid SMT-LIB input");
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).expect("execution succeeds");

    assert_eq!(
        outputs,
        vec!["sat"],
        "a fully discharged multi-point guard expansion must keep its Sat \
         (#bv-forall-const-expansion)"
    );
}

/// NON-VACUITY, half 2 of 2 — the MUTANT the machinery must reject. One mask bit
/// away from the test above (`#x03` -> `#x01`): the instances at `x = #x00` and
/// `x = #x01` still fold to `true`, the one at `x = #x02` folds to `false`, and
/// the authored `forall` is genuinely FALSE. Identical guard, identical range,
/// identical route — so a certificate that granted `Sat` without depending on
/// the per-point value of the quantified body would answer `sat` here. It must
/// answer `unsat` (z3 5.0.0: `unsat`; measured `unsat` before and after).
#[test]
fn constant_folded_multipoint_guard_expansion_refutes_a_false_forall() {
    let input = r#"
        (set-logic ALL)
        (assert (forall ((x (_ BitVec 8))) (or (bvult #x02 x) (= (bvand x #x01) x))))
        (check-sat)
    "#;

    let commands = parse(input).expect("valid SMT-LIB input");
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).expect("execution succeeds");

    assert_eq!(
        outputs,
        vec!["unsat"],
        "flipping ONE point of the guard range must flip the verdict: the \
         expansion record may never grant Sat to a false forall \
         (#bv-forall-const-expansion non-vacuity)"
    );
}

/// The certificate discharges the QUANTIFIER, never the ground siblings: a
/// refuted ground conjunct alongside a fully discharged `forall` must still be
/// `unsat` (z3 5.0.0: `unsat`).
#[test]
fn constant_folded_guard_expansion_does_not_mask_a_ground_conflict() {
    let input = r#"
        (set-logic ALL)
        (declare-fun c () (_ BitVec 8))
        (assert (forall ((x (_ BitVec 8))) (or (bvult #x00 x) (= x #x00))))
        (assert (= c #x01))
        (assert (= c #x02))
        (check-sat)
    "#;

    let commands = parse(input).expect("valid SMT-LIB input");
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).expect("execution succeeds");

    assert_eq!(
        outputs,
        vec!["unsat"],
        "a discharged quantifier must not mask a refuted ground sibling \
         (#bv-forall-const-expansion non-vacuity)"
    );
}
