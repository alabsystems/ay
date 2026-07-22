// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Regression (#dt-ite-ctor-payload): the COMBINED composite-return obligation
//! deductive-checks lowers from a contract like
//!   `result == if feasible { Accept(actual) } else { Reject }`
//! over an enum `Verdict { Reject, Accept(i128) }` body (with `i128` lowered to
//! `BitVec 128`) must DECIDE directly — `unsat` when the contract is VALID — in
//! the combined DT+BV route, instead of returning `Unknown`.
//!
//! The fix (`dt_selector_axioms_to_depth`, the (F3) pass) emits the
//! constructor-equality biconditional
//!   `(t = C(b)) <=> (is-C(t) AND sel_0(t)=b_0 AND ... AND sel_n(t)=b_n)`
//! for every equality atom between a datatype TERM `t` and a constructor
//! application `C(b)`. It decides a datatype-VARIABLE-vs-constructor (dis)equality
//! through the variable's selectors/tester (BV/Bool facts the eager bit-blast CAN
//! decide), WITHOUT relying on EUF transitivity across datatype-sorted equality
//! atoms (which the eager DT+BV bit-blast does not maintain). The BV theory then
//! handles a constructor argument that is itself a nested ITE natively
//! (`objv(t) = ite(g, claimed, actual)` is a plain BV ITE). The biconditional is a
//! valid datatype tautology, so it can only turn `Unknown` into the GENUINE
//! verdict, never a wrong one.
//!
//! NON-VACUITY / SOUNDNESS: the structural wrong-controls (drop the feasibility
//! guard, swap the arms) are genuinely falsifiable and are REFUTED with a concrete
//! model (`sat`) — proving the now-`unsat` valid forms are not vacuously accepted.
//!
//! KNOWN FAIL-CLOSED RESIDUAL (`..._not_unsat`): the OBJECTIVE-MISMATCH composite
//! wrong-control (accept path stores an UNCHECKED `claimed != actual`) needs a SAT
//! model with TWO DISTINCT free `BitVec 128` values; the eager BV+DT SAT
//! model-COMPLETION defaults both free vars to the SAME constant (`#x0`), the
//! strict DT model-validation oracle correctly rejects that collided model, and
//! the solve degrades to `Unknown` (NEVER a wrong `sat`/`unsat` — fail-closed).
//! That exact objective-exactness property is already a crisp `Counterexample` at
//! the i128 SCALAR level (`incumbent_stored_objective_trust_claim_wrong`,
//! `incumbent_accept_objective_exact_wrong` in
//! the development proof harness), unaffected by this
//! change, and as the Int variant below. The residual is pinned so it is not
//! silently lost.

use crate::Executor;
use ay_frontend::parse;

fn run(smt: &str) -> Vec<String> {
    let commands = parse(smt).expect("valid SMT-LIB input");
    let mut exec = Executor::new();
    exec.execute_all(&commands).expect("execution succeeds")
}

// ===========================================================================
// PRIMARY: the COMBINED composite-return VALID form decides as UNSAT.
// ===========================================================================

/// THE COMBINED FORM (BV128 payload, the deductive-checks i128 lowering). The body assigns
///   result = ite(feasible, Accept(ite(g, claimed, actual)), Reject)
/// and the negated contract asserts result != ite(feasible, Accept(actual), Reject).
/// With g = (has_claim AND claimed = actual), the inner ite collapses to `actual`
/// in BOTH arms, so the two outer ites are equal: UNSAT (the contract is VALID).
/// This is the named completeness gap in
/// the development proof harness: before the fix this
/// returned `Unknown`; after the fix it is `unsat`.
#[test]
fn dt_ite_ctor_ite_payload_bv128_combined_unsat() {
    let smt = r#"
        (set-logic ALL)
        (declare-datatypes ((Verdict 0)) (((Reject) (Accept (objv (_ BitVec 128))))))
        (declare-const result Verdict)
        (declare-const feasible Bool)
        (declare-const actual (_ BitVec 128))
        (declare-const claimed (_ BitVec 128))
        (declare-const has_claim Bool)
        (assert (= result
                   (ite feasible
                        (Accept (ite (and has_claim (= claimed actual)) claimed actual))
                        Reject)))
        (assert (not (= result
                        (ite feasible (Accept actual) Reject))))
        (check-sat)
    "#;
    assert_eq!(
        run(smt),
        vec!["unsat"],
        "Ite over ctor branches with a nested-Ite BV128 payload: the contract is \
         VALID, must be UNSAT (the #dt-ite-ctor-payload gap)"
    );
}

/// STRUCT / Option analogue: a single-constructor datatype carrying TWO fields
/// (one Bool, one nested-Ite BV payload), under an outer Ite over the constructor
/// and a distinct sentinel constructor. Mirrors the `Option<(.., i128)>` / struct
/// return shapes the same decomposition workaround recurs over.
#[test]
fn dt_ite_struct_payload_bv64_combined_unsat() {
    let smt = r#"
        (set-logic ALL)
        (declare-datatypes ((Res 0))
          (((None) (Some (ok Bool) (val (_ BitVec 64))))))
        (declare-const result Res)
        (declare-const feasible Bool)
        (declare-const actual (_ BitVec 64))
        (declare-const claimed (_ BitVec 64))
        (declare-const has_claim Bool)
        (assert (= result
                   (ite feasible
                        (Some true (ite (and has_claim (= claimed actual)) claimed actual))
                        None)))
        (assert (not (= result
                        (ite feasible (Some true actual) None))))
        (check-sat)
    "#;
    assert_eq!(
        run(smt),
        vec!["unsat"],
        "struct/Option analogue: contract is VALID, must be UNSAT"
    );
}

/// Int payload variant (QF_UFDTLIA): the arithmetic DT route already lifts
/// downstream in solve_harness, but the (F3) constructor-equality biconditional
/// applies there too. Pinned as a same-family companion.
#[test]
fn dt_ite_ctor_ite_payload_int_combined_unsat() {
    let smt = r#"
        (set-logic QF_UFDTLIA)
        (declare-datatypes ((Verdict 0)) (((Reject) (Accept (objv Int)))))
        (declare-const result Verdict)
        (declare-const feasible Bool)
        (declare-const actual Int)
        (declare-const claimed Int)
        (declare-const has_claim Bool)
        (assert (= result
                   (ite feasible
                        (Accept (ite (and has_claim (= claimed actual)) claimed actual))
                        Reject)))
        (assert (not (= result
                        (ite feasible (Accept actual) Reject))))
        (check-sat)
    "#;
    assert_eq!(
        run(smt),
        vec!["unsat"],
        "Int payload: contract is VALID, must be UNSAT"
    );
}

// ===========================================================================
// NON-VACUITY WRONG-CONTROLS: genuinely falsifiable composite obligations that
// MUST be REFUTED (Counterexample / `sat`), proving the UNSAT verdicts above are
// not vacuous (the fix did not over-constrain).
// ===========================================================================

/// WRONG-CONTROL — DROP THE FEASIBILITY GUARD (the exact VIG bug the warmup
/// flagged: "the accept path could store a value without a feasibility check").
/// Body accepts `Accept(actual)` UNCONDITIONALLY; the contract still gates accept
/// on `feasible`. Witness: feasible=false -> body=Accept(actual), contract=Reject,
/// distinct -> the contract is FALSIFIED. MUST be `sat` (REFUTED), never UNSAT.
#[test]
fn dt_ite_ctor_drop_guard_wrong_control_sat() {
    let smt = r#"
        (set-logic ALL)
        (declare-datatypes ((Verdict 0)) (((Reject) (Accept (objv (_ BitVec 128))))))
        (declare-const result Verdict)
        (declare-const feasible Bool)
        (declare-const actual (_ BitVec 128))
        (assert (= result (Accept actual)))
        (assert (not (= result (ite feasible (Accept actual) Reject))))
        (check-sat)
    "#;
    assert_eq!(
        run(smt),
        vec!["sat"],
        "drop-the-feasibility-guard wrong control: accept without the VIG gate is \
         FALSIFIABLE (feasible=false), must be SAT (REFUTED) — never vacuously UNSAT"
    );
}

/// WRONG-CONTROL — SWAPPED ARMS. Body returns `Reject` on the feasible arm and
/// `Accept(actual)` on the reject arm — the inverse of the contract. Witness:
/// feasible=true -> body=Reject, contract=Accept(actual), distinct -> FALSIFIED.
/// MUST be `sat` (REFUTED).
#[test]
fn dt_ite_ctor_swapped_arms_wrong_control_sat() {
    let smt = r#"
        (set-logic ALL)
        (declare-datatypes ((Verdict 0)) (((Reject) (Accept (objv (_ BitVec 128))))))
        (declare-const result Verdict)
        (declare-const feasible Bool)
        (declare-const actual (_ BitVec 128))
        (assert (= result (ite feasible Reject (Accept actual))))
        (assert (not (= result (ite feasible (Accept actual) Reject))))
        (check-sat)
    "#;
    assert_eq!(
        run(smt),
        vec!["sat"],
        "swapped-arms wrong control: FALSIFIABLE (feasible=true), must be SAT (REFUTED)"
    );
}

/// Int objective-mismatch wrong-control (QF_UFDTLIA): on the accept path the body
/// stores the UNCHECKED `claimed` instead of `actual`. The arithmetic route
/// constructs a distinct-value model, so this is a crisp `sat` (Counterexample).
/// (Its BV128 analogue hits the fail-closed completion residual; see below.)
#[test]
fn dt_ite_ctor_objective_mismatch_wrong_control_int_sat() {
    let smt = r#"
        (set-logic QF_UFDTLIA)
        (declare-datatypes ((Verdict 0)) (((Reject) (Accept (objv Int)))))
        (declare-const result Verdict)
        (declare-const feasible Bool)
        (declare-const actual Int)
        (declare-const claimed Int)
        (assert (= result (ite feasible (Accept claimed) Reject)))
        (assert (not (= result (ite feasible (Accept actual) Reject))))
        (check-sat)
    "#;
    assert_eq!(
        run(smt),
        vec!["sat"],
        "Int objective-mismatch wrong control: FALSIFIABLE (feasible, claimed!=actual), \
         must be SAT (REFUTED)"
    );
}

// ===========================================================================
// CONSTRUCTOR-EQUALITY BICONDITIONAL — unit-level coverage of the (F3) axiom in
// both directions, pinning that it is SOUND (decides, never mis-decides).
// ===========================================================================

/// Injectivity direction over a datatype VARIABLE (was already decided; pinned as
/// a soundness companion): result=Accept(claimed) AND result=Accept(actual) AND
/// claimed!=actual is UNSAT.
#[test]
fn dt_var_ctor_injectivity_unsat() {
    let smt = r#"
        (set-logic ALL)
        (declare-datatypes ((Verdict 0)) (((Reject) (Accept (objv (_ BitVec 8))))))
        (declare-const result Verdict)
        (declare-const actual (_ BitVec 8))
        (declare-const claimed (_ BitVec 8))
        (assert (= result (Accept claimed)))
        (assert (= result (Accept actual)))
        (assert (not (= claimed actual)))
        (check-sat)
    "#;
    assert_eq!(
        run(smt),
        vec!["unsat"],
        "var-ctor injectivity: must be UNSAT"
    );
}

/// Forward-congruence direction over a datatype VARIABLE: result=Accept(claimed)
/// AND result!=Accept(actual) AND claimed=actual is UNSAT (the (F3) biconditional
/// forces result=Accept(actual) when claimed=actual). This is precisely the
/// constructor functional-congruence the selector-derived injectivity lacked.
#[test]
fn dt_var_ctor_forward_congruence_unsat() {
    let smt = r#"
        (set-logic ALL)
        (declare-datatypes ((Verdict 0)) (((Reject) (Accept (objv (_ BitVec 8))))))
        (declare-const result Verdict)
        (declare-const actual (_ BitVec 8))
        (declare-const claimed (_ BitVec 8))
        (assert (= result (Accept claimed)))
        (assert (not (= result (Accept actual))))
        (assert (= claimed actual))
        (check-sat)
    "#;
    assert_eq!(
        run(smt),
        vec!["unsat"],
        "var-ctor forward congruence: claimed=actual must force result=Accept(actual), UNSAT"
    );
}

/// Nullary-constructor biconditional: result=Reject AND result!=Accept(actual) is
/// SAT (Reject is distinct from every Accept). The witness is STRUCTURAL (no two
/// distinct free BV values), so model construction succeeds.
#[test]
fn dt_var_nullary_ctor_distinct_sat() {
    let smt = r#"
        (set-logic ALL)
        (declare-datatypes ((Verdict 0)) (((Reject) (Accept (objv (_ BitVec 128))))))
        (declare-const result Verdict)
        (declare-const actual (_ BitVec 128))
        (assert (= result Reject))
        (assert (not (= result (Accept actual))))
        (check-sat)
    "#;
    assert_eq!(
        run(smt),
        vec!["sat"],
        "Reject distinct from Accept: must be SAT"
    );
}

// ===========================================================================
// KNOWN FAIL-CLOSED RESIDUAL — committed so it is not silently lost. The BV128
// objective-mismatch wrong-control needs a SAT model with two DISTINCT free
// BitVec128 values; eager BV+DT model-COMPLETION collides both free vars at the
// default `#x0`, the strict DT oracle rejects the collided model, and the solve
// degrades to `Unknown`. This is FAIL-CLOSED (never a wrong sat/unsat). The guard
// below pins the soundness-critical invariant: it is NOT vacuously `unsat` (which
// would mean the (F3) axioms over-constrained a falsifiable obligation). The crisp
// Counterexample for this exact property lives at the i128 scalar level
// (incumbent_vig_realbody.rs) and in the Int variant above.
// ===========================================================================
#[test]
fn dt_ite_ctor_objective_mismatch_wrong_control_bv128_not_unsat() {
    let smt = r#"
        (set-logic ALL)
        (declare-datatypes ((Verdict 0)) (((Reject) (Accept (objv (_ BitVec 128))))))
        (declare-const result Verdict)
        (declare-const feasible Bool)
        (declare-const actual (_ BitVec 128))
        (declare-const claimed (_ BitVec 128))
        (assert (= result (ite feasible (Accept claimed) Reject)))
        (assert (not (= result (ite feasible (Accept actual) Reject))))
        (check-sat)
    "#;
    let out = run(smt);
    assert_ne!(
        out,
        vec!["unsat"],
        "SOUNDNESS: the BV128 objective-mismatch wrong control is FALSIFIABLE; it must \
         never be vacuously UNSAT. (It is currently `unknown` — a fail-closed model-\
         completion residual, documented in the module header.)"
    );
}
