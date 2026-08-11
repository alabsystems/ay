// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

#[test]
fn test_cegqi_valid_implication() {
    // forall x. (x > 0) => (x >= 1) is valid for integers
    // CE lemma: Not((e > 0) => (e >= 1)) = (e > 0) AND Not(e >= 1) = (e > 0) AND (e < 1)
    // For integers: e > 0 AND e < 1 is UNSAT (no integers in (0,1))
    let input = r#"
        (set-logic QF_LIA)
        (assert (forall ((x Int)) (=> (> x 0) (>= x 1))))
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    // Valid quantified formula - CEGQI proves it via CE lemma being UNSAT
    assert_eq!(outputs, vec!["sat"]);
}
#[test]
fn test_cegqi_invalid_strict_positive() {
    // forall x. x > 0 is NOT valid (counterexample: x = 0 or x = -1)
    // #3441: Enumerative instantiation finds ground term 0, adds (0 > 0) = false.
    // This directly refutes the forall, proving UNSAT.
    let input = r#"
        (set-logic QF_LIA)
        (assert (forall ((x Int)) (> x 0)))
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    // Invalid forall: enumerative instantiation with x=0 produces false,
    // proving the formula unsatisfiable.
    assert_eq!(outputs, vec!["unsat"]);
}
#[test]
fn test_cegqi_valid_nonstrict_positive() {
    // forall x. (x >= 0) => (x + 1 > 0) is valid
    // CE lemma: Not((e >= 0) => (e + 1 > 0)) = (e >= 0) AND (e + 1 <= 0)
    // This means e >= 0 AND e <= -1, which is UNSAT
    let input = r#"
        (set-logic QF_LIA)
        (assert (forall ((x Int)) (=> (>= x 0) (> (+ x 1) 0))))
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    // Valid quantified formula
    assert_eq!(outputs, vec!["sat"]);
}
#[test]
fn test_cegqi_exists_witness_sat() {
    // exists x. x > 0 is satisfiable (witness: x = 1).
    // CE lemma for exists is phi(e) (no negation), which is SAT.
    let input = r#"
        (set-logic QF_LIA)
        (assert (exists ((x Int)) (> x 0)))
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs, vec!["sat"]);
}
/// #7883: triggerless quantifiers over Seq-sorted binders must not enter
/// arithmetic CEGQI.
///
/// This verification-consumer-style standard-library axiom mixes a non-arithmetic binder
/// sort (`Seq`) with an Int-valued accessor. The formula is satisfiable: the
/// model can interpret `seq_len` as a non-negative function, and the concrete
/// ground term `a` is consistent with `seq_len(a) = 0`.
///
/// The arithmetic sort guard should leave this quantifier to the general
/// triggerless path instead of creating a CE lemma over a Seq binder.
#[test]
fn test_cegqi_seq_binder_guard_end_to_end_7883() {
    let input = r#"
        (set-logic AUFLIA)
        (declare-sort Seq 0)
        (declare-fun seq_len (Seq) Int)
        (declare-const a Seq)
        (assert (= (seq_len a) 0))
        (assert (forall ((s Seq)) (>= (seq_len s) 0)))
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert!(
        outputs == vec!["sat"] || outputs == vec!["unknown"],
        "non-arithmetic Seq binders must not cause false-UNSAT via arithmetic CEGQI: {outputs:?}"
    );
}
/// Test that arithmetic CEGQI with bound-based instantiation works (#5690).
///
/// This test exercises the ArithInstantiator in the CEGQI refinement loop:
/// 1. CEGQI creates CE lemma for the forall (negation of body)
/// 2. CE lemma is SAT (counterexample found) or the CE lemma + bounds
///    directly determine the formula status
/// 3. ArithInstantiator collects bounds and computes selection terms
///
/// Formula: forall x. (x >= 0 AND x <= 5) => (2*x <= 10)
/// This is VALID: if 0 <= x <= 5, then 2x <= 10.
/// CE lemma: NOT((e >= 0 AND e <= 5) => (2*e <= 10))
///         = (e >= 0) AND (e <= 5) AND NOT(2*e <= 10)
///         = (e >= 0) AND (e <= 5) AND (2*e > 10)
/// For integers: 0 <= e <= 5 AND 2e > 10, so e > 5 AND e <= 5 → UNSAT.
/// CEGQI proves this directly via CE lemma.
#[test]
fn test_cegqi_arith_bounds_valid_implication_5690() {
    let input = r#"
        (set-logic LIA)
        (assert (forall ((x Int))
            (=> (and (>= x 0) (<= x 5))
                (<= (* 2 x) 10))))
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    // Valid quantified formula — CEGQI proves via CE lemma UNSAT
    assert_eq!(outputs, vec!["sat"]);
}
/// Test arithmetic CEGQI refinement with model-based instantiation (#5690).
///
/// This exercises the case where CEGQI's CE lemma returns SAT (counterexample
/// found), triggering the ArithInstantiator-based refinement in
/// try_cegqi_arith_refinement. The refinement extracts model values for CE
/// variables, computes selection terms using bound analysis, and adds a ground
/// instantiation that proves the formula unsatisfiable.
///
/// Formula: forall x. NOT(x + 1 > x)
/// This is INVALID (x + 1 > x is always true).
/// The assertion says the universally quantified NOT(x+1 > x) holds,
/// which is equivalent to asserting "false for all x" — UNSAT.
///
/// CE lemma: NOT(NOT(e + 1 > e)) = (e + 1 > e)
/// This is SAT (any integer e works), so refinement fires.
/// Refinement creates phi(model_value) = NOT(v + 1 > v) = false for any v.
/// Adding this ground instance makes the system UNSAT.
#[test]
fn test_cegqi_arith_refinement_invalid_formula_5690() {
    let input = r#"
        (set-logic LIA)
        (assert (forall ((x Int)) (not (> (+ x 1) x))))
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    // Invalid formula — should be UNSAT (the forall of a falsehood can't hold).
    // Before #5690: could return "unknown" if enumerative didn't fire.
    // After #5690: CEGQI refinement instantiates with model value, proves UNSAT.
    assert_eq!(outputs, vec!["unsat"]);
}
/// Test CEGQI with strict inequality bounds (#5690, P1:16 strictness audit).
///
/// This exercises ArithInstantiator's handling of strict `<` and `>` operators.
/// The formula uses `<` (strict less-than) rather than `<=` (weak):
///   forall x. (x > 0 AND x < 5) => (x >= 1 AND x <= 4)
///
/// This is VALID for integers: if 0 < x < 5, then 1 <= x <= 4.
/// CE lemma: (e > 0) AND (e < 5) AND NOT(e >= 1 AND e <= 4)
///         = (e > 0) AND (e < 5) AND (e < 1 OR e > 4)
/// For integers: 1 <= e <= 4 AND (e < 1 OR e > 4) → UNSAT.
///
/// If ArithInstantiator treats `<` the same as `<=` (no strictness tracking),
/// it might select boundary values 0 or 5 which violate the strict bounds.
/// For integer arithmetic this is less critical (x < 5 ↔ x <= 4), but the
/// bound collection must still handle strict operators correctly.
#[test]
fn test_cegqi_arith_strict_bounds_5690() {
    let input = r#"
        (set-logic LIA)
        (assert (forall ((x Int))
            (=> (and (> x 0) (< x 5))
                (and (>= x 1) (<= x 4)))))
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    // Valid formula — should be SAT (the universal quantification holds).
    assert_eq!(outputs, vec!["sat"]);
}
/// Test CEGQI with NOT(strict) bounds — exercises Not(<) and Not(>) paths.
///
/// Formula: forall x. NOT(x < 3) => (x >= 3)
/// This is VALID: NOT(x < 3) is x >= 3.
/// CE lemma: NOT(NOT(e < 3) => (e >= 3)) = NOT(e < 3) AND NOT(e >= 3)
///         = (e >= 3) AND (e < 3) → UNSAT for integers.
///
/// If ArithInstantiator doesn't handle Not(<), the bound from NOT(e < 3)
/// (which is e >= 3) will be silently dropped, potentially causing the
/// refinement loop to fail or select a wrong instantiation.
#[test]
fn test_cegqi_arith_negated_strict_bounds_5690() {
    let input = r#"
        (set-logic LIA)
        (assert (forall ((x Int))
            (=> (not (< x 3))
                (>= x 3))))
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    // Valid formula — should be SAT.
    assert_eq!(outputs, vec!["sat"]);
}
/// Test CEGQI refinement with strict bound at the boundary (#5690, P1:16).
///
/// This INVALID formula requires CEGQI refinement (CE lemma is SAT) and
/// tests whether the ArithInstantiator correctly handles strict vs weak
/// bounds at the exact boundary value.
///
/// Formula: forall x. (x > 0) => (x > 1)
/// INVALID: x=1 satisfies x>0 but not x>1.
/// Expected: UNSAT (asserting an invalid universally quantified formula).
///
/// CE lemma: NOT((e > 0) => (e > 1)) = (e > 0) AND NOT(e > 1)
///         = (e > 0) AND (e <= 1)
/// For integers: e >= 1 AND e <= 1, so e = 1. CE lemma is SAT with e=1.
/// Refinement should instantiate with x=1: (1 > 0) AND NOT(1 > 1) = counterexample.
#[test]
fn test_cegqi_arith_strict_boundary_refinement_5690() {
    let input = r#"
        (set-logic LIA)
        (assert (forall ((x Int)) (=> (> x 0) (> x 1))))
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    // INVALID formula — should be UNSAT.
    // If CEGQI refinement works correctly, it finds x=1 as counterexample
    // and the ground instance makes the system UNSAT.
    // If CEGQI is incomplete, this may return "unknown" — also acceptable.
    assert!(
        outputs == vec!["unsat"] || outputs == vec!["unknown"],
        "Expected unsat or unknown for invalid forall with strict bounds, got: {outputs:?}",
    );
}

/// WF-CEGQI-SOUNDNESS discriminating repro (independent verification).
///
/// Read-relation form of a VALID universal goal routed through the CEGQI /
/// quantifier-loop disambiguation. Array extensionality:
///   (forall i. select(a,i) = select(b,i)) AND (a != b)
/// is UNSAT (z3/cvc5 agree: extensionality makes a = b, contradicting a != b).
/// The ground solver (with the CE-lemma instances) can derive an interleaved
/// UNSAT, which the CEGQI disambiguation historically read as "forall valid =>
/// SAT" (ay #8729 / Z3 #6303) — a WRONG SAT. The prime directive forbids a
/// definitive `sat` here. Sound outcomes: `unsat` (true answer) or `unknown`
/// (incomplete). A `sat` verdict is a soundness bug.
#[test]
fn test_cegqi_array_extensionality_no_wrong_sat_wfcegqi() {
    let input = r#"
        (set-logic AUFLIA)
        (declare-fun a () (Array Int Int))
        (declare-fun b () (Array Int Int))
        (assert (forall ((i Int)) (= (select a i) (select b i))))
        (assert (not (= a b)))
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_ne!(
        outputs,
        vec!["sat"],
        "WRONG-SAT soundness bug: array extensionality is UNSAT, AY must not emit definitive sat. got: {outputs:?}",
    );
    assert!(
        outputs == vec!["unsat"] || outputs == vec!["unknown"],
        "Expected unsat or unknown for UNSAT extensionality goal, got: {outputs:?}",
    );
}

/// GENUINE-SAT control (anti-over-suppression): a real finite-model SAT that
/// routes through CEGQI must STILL be sat. forall x. (x>0 => x>=1) is VALID over
/// Int, so asserting it is satisfiable -> sat. This guards the fail-closed logic
/// from over-suppressing genuine sats.
#[test]
fn test_cegqi_genuine_sat_preserved_wfcegqi() {
    let input = r#"
        (set-logic LIA)
        (assert (forall ((x Int)) (=> (> x 0) (>= x 1))))
        (check-sat)
    "#;
    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();
    assert_eq!(
        outputs,
        vec!["sat"],
        "genuine valid-forall SAT must be preserved, got: {outputs:?}"
    );
}

/// WF-CEGQI-SOUNDNESS adversarial soundness guard (independent verification).
///
/// A battery of quantified goals that are GENUINELY UNSAT (each cross-checked
/// with z3 == unsat), spanning array extensionality / read-relation, UF range
/// constraints, monotonicity, negated-valid arithmetic, and a forall/exists
/// alternation. The CEGQI / quantifier-loop disambiguation must NEVER emit a
/// definitive `sat` on any of these (a `sat` would be a prime-directive wrong
/// answer). Sound outcomes per case: `unsat` (true answer) or `unknown`
/// (incomplete). This pins the fail-closed behaviour of the override path.
#[test]
fn test_wfcegqi_batch_unsat_no_wrong_sat() {
    let cases: &[(&str, &str)] = &[
        (
            "ext_store",
            r#"(set-logic AUFLIA)(declare-fun a () (Array Int Int))(declare-fun b () (Array Int Int))(assert (forall ((i Int)) (= (select a i) (select b i))))(assert (not (= a b)))(check-sat)"#,
        ),
        (
            "ext_impl",
            r#"(set-logic AUFLIA)(declare-fun a () (Array Int Int))(declare-fun b () (Array Int Int))(declare-fun c () Int)(assert (forall ((i Int)) (=> true (= (select a i) (select b i)))))(assert (= (select a c) 5))(assert (= (select b c) 7))(check-sat)"#,
        ),
        (
            "uf_rel",
            r#"(set-logic UFLIA)(declare-fun f (Int) Int)(assert (forall ((x Int)) (= (f x) 0)))(assert (= (f 3) 1))(check-sat)"#,
        ),
        (
            "uf_rel2",
            r#"(set-logic UFLIA)(declare-fun f (Int) Int)(declare-fun g (Int) Int)(assert (forall ((x Int)) (> (f x) (g x))))(assert (= (f 2) 1))(assert (= (g 2) 4))(check-sat)"#,
        ),
        (
            "neg_valid_arith",
            r#"(set-logic LIA)(assert (not (forall ((x Int)) (=> (> x 0) (>= x 1)))))(check-sat)"#,
        ),
        (
            "neg_row",
            r#"(set-logic AUFLIA)(declare-fun a () (Array Int Int))(declare-fun i () Int)(declare-fun v () Int)(assert (not (= (select (store a i v) i) v)))(check-sat)"#,
        ),
        (
            "forall_le",
            r#"(set-logic LIA)(assert (forall ((x Int)) (<= x 0)))(check-sat)"#,
        ),
        (
            "mono",
            r#"(set-logic UFLIA)(declare-fun f (Int) Int)(assert (forall ((x Int) (y Int)) (=> (<= x y) (<= (f x) (f y)))))(assert (< (f 5) (f 1)))(check-sat)"#,
        ),
        (
            "arr_two_pt",
            r#"(set-logic AUFLIA)(declare-fun a () (Array Int Int))(assert (forall ((i Int)) (= (select a i) 0)))(assert (= (select a 7) 9))(check-sat)"#,
        ),
        (
            "alt_unsat",
            r#"(set-logic LIA)(assert (forall ((x Int)) (exists ((y Int)) (and (> y x) (< y x)))))(check-sat)"#,
        ),
    ];
    let mut wrong = Vec::new();
    for (name, input) in cases {
        let commands = parse(input).unwrap();
        let mut exec = Executor::new();
        let outputs = exec.execute_all(&commands).unwrap();
        println!("WFBATCH {name} => {outputs:?}");
        if outputs == vec!["sat"] {
            wrong.push(*name);
        }
    }
    assert!(wrong.is_empty(), "WRONG-SAT on UNSAT instances: {wrong:?}");
}

/// (#cegqi-attribution) FALSE-UNSAT on an ENTAILED inner forall.
///
/// `∀x. a(x) ⇒ ∀y. A[y] ≠ x` together with `a(k2)` is SATISFIABLE (z3: sat) —
/// e.g. `k2:=0`, `a := λx. x=0`, `A := (as const) 1`. AY answered `unsat`.
///
/// Unlike the disjunction-position false-unsats fixed in cf0a5789b, the inner
/// forall genuinely IS entailed (`a(k2) ∧ (¬a(k2) ∨ Q2) ⊨ Q2`) and the
/// entailment gate correctly admits it. The failure is downstream: CEGQI asserts
/// the quantifier's NEGATION as the CE lemma, the ground lane consumes that
/// equality as a DEFINITIONAL substitution (`k2 := A[c]`), rewrites away the
/// genuine assertion `a(k2)` and constant-folds the residue to a bare `false`.
/// The CE strip in `disambiguate_cegqi_unsat_ext` then deletes the real
/// assertions (they now mention the CE variable) and KEEPS the CE-derived
/// `false`, so the "ground-minus-CE" probe re-solves `{true,false}` and reports
/// a GLOBAL unsat — a conflict that depends ENTIRELY on the CE lemma, which per
/// `cegqi/mod.rs` ("forall: UNSAT on CE lemma -> SAT") means the quantifier
/// HOLDS.
///
/// `cegqi_probe_unsat_is_attributable` now requires the probe set to still carry
/// every CE-free ground conjunct of the pre-instantiation snapshot; `(a k2)` is
/// absent, so the UNSAT is unattributable and fails closed to Unknown.
///
/// Each variant below is the same semantic shape written differently, so the fix
/// cannot be a syntactic special case. `sat` would also be correct here; only
/// `unsat` is wrong.
#[test]
fn test_cegqi_entailed_inner_forall_never_unsat() {
    let variants: &[(&str, &str)] = &[
        (
            "implies",
            r#"
            (set-logic AUFLIA)
            (declare-fun a (Int) Bool)
            (declare-fun k2 () Int)
            (declare-fun A () (Array Int Int))
            (assert (forall ((x Int)) (=> (a x) (forall ((y Int)) (not (= (select A y) x))))))
            (assert (a k2))
            (check-sat)
        "#,
        ),
        (
            "or_not",
            r#"
            (set-logic AUFLIA)
            (declare-fun a (Int) Bool)
            (declare-fun k2 () Int)
            (declare-fun A () (Array Int Int))
            (assert (forall ((x Int)) (or (not (a x)) (forall ((y Int)) (not (= (select A y) x))))))
            (assert (a k2))
            (check-sat)
        "#,
        ),
        (
            "nnf_not_and_exists",
            r#"
            (set-logic AUFLIA)
            (declare-fun a (Int) Bool)
            (declare-fun k2 () Int)
            (declare-fun A () (Array Int Int))
            (assert (forall ((x Int)) (not (and (a x) (exists ((y Int)) (= (select A y) x))))))
            (assert (a k2))
            (check-sat)
        "#,
        ),
    ];
    let mut wrong = Vec::new();
    for (name, input) in variants {
        let commands = parse(input).unwrap();
        let mut exec = Executor::new();
        let outputs = exec.execute_all(&commands).unwrap();
        let out = outputs.last().cloned().unwrap_or_default();
        println!("CEGQI-ENTAILED-INNER {name} => {out}");
        if out == "unsat" {
            wrong.push(*name);
        }
    }
    assert!(
        wrong.is_empty(),
        "WRONG-UNSAT on satisfiable entailed-inner-forall instances: {wrong:?}"
    );
}

/// (#cegqi-attribution) Self-refutation control for the family above: AY itself
/// answers `sat` once the witnessing interpretation is substituted in, so no
/// external oracle is needed to show `unsat` is wrong. A model of the
/// interpreted instance is a model of the uninterpreted one.
#[test]
fn test_cegqi_entailed_inner_forall_witness_is_sat() {
    let input = r#"
        (set-logic AUFLIA)
        (define-fun a ((x Int)) Bool (= x 0))
        (define-fun k2 () Int 0)
        (define-fun A () (Array Int Int) ((as const (Array Int Int)) 1))
        (assert (forall ((x Int)) (=> (a x) (forall ((y Int)) (not (= (select A y) x))))))
        (assert (a k2))
        (check-sat)
    "#;
    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();
    assert_eq!(
        outputs.last().map(String::as_str),
        Some("sat"),
        "witnessed instance must stay SAT (this is the self-refutation control)"
    );
}

// ---------------------------------------------------------------------------
// #satgate-vacuous-binder — regression tests for the mechanism that degraded
// the control above.
//
// BISECT: `66538b006f` ("feat(parity): define exact Z3 5 replacement gate")
// changed ONE condition in `apply_quantified_model_failclosed_gate`
// (`crates/ay-dpll/src/executor/model/independent_gate.rs`):
//
//     -   if deferred_any && self.self_check {      // --self-check only
//     +   if deferred_any {                         // every solve
//
// so a quantified conjunct the gate could not DECIDE started publishing
// `unknown` instead of the solver's `sat`. Measured: the witness control above
// answered `sat` at `e22fb87f0` / `03c7b6667` and `unknown` 5/5 at HEAD, with
// `unknown.phase = "independent-model-check-gate"` and the `(deferred:` detail
// unique to that site.
//
// ROOT CAUSE (measured with `AY_DEBUG_QMG=1`): the conjunct the gate receives
// is `(forall ((x Int)) (or (forall ((y Int)) (not (= 1 x))) (not (= 0 x))))`
// — `y` is VACUOUS (the const-array `select` already folded to `1`). Neither
// decision route can handle a binder buried in the matrix: the prefix route
// requires a quantifier-free matrix, and the general route's `deep_qe` refuses
// a vacuous binder by design (`find_bound_var -> None` is not a proof of
// non-occurrence there) and then fails closed on the residual quantifier.
//
// FIX: drop provably-vacuous binders inside the gate (`∀v.φ ≡ φ ≡ ∃v.φ` over
// SMT-LIB's non-empty sorts — an unconditional equivalence), which lets the
// gate MINT the certificate that was missing: the nested solve now refutes the
// skolemized negation and the conjunct is `Confirmed`, not `Deferred`. The
// fail-closed funnel itself is untouched — see the third test.

/// Vacuous UNIVERSAL inner binder. Fails (`unknown`) without the
/// #satgate-vacuous-binder drop: the gate cannot decide
/// `∀x. x = 5 => ∀y. 1 < x + x` while `y` is in the way, so it defers and the
/// post-`66538b006f` funnel publishes `unknown`. No arrays, so this isolates
/// the binder mechanism from the const-array fold in the control above.
#[test]
fn test_quantified_gate_certifies_vacuous_inner_forall() {
    let input = r#"
        (set-logic AUFLIA)
        (declare-fun c () Int)
        (assert (> c 3))
        (assert (forall ((x Int)) (=> (= x 5) (forall ((y Int)) (< 1 (+ x x))))))
        (check-sat)
    "#;
    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();
    assert_eq!(
        outputs.last().map(String::as_str),
        Some("sat"),
        "a vacuous inner FORALL must not stop the model gate from certifying \
         a valid quantified conjunct (#satgate-vacuous-binder, 66538b006f)"
    );
}

/// Same, EXISTENTIAL inner binder — the drop must cover both quantifiers
/// (`∃v.φ ≡ φ` is the same non-empty-sort equivalence). Also `unknown` without
/// the fix.
#[test]
fn test_quantified_gate_certifies_vacuous_inner_exists() {
    let input = r#"
        (set-logic AUFLIA)
        (declare-fun c () Int)
        (assert (> c 3))
        (assert (forall ((x Int)) (=> (= x 5) (exists ((y Int)) (< 1 (+ x x))))))
        (check-sat)
    "#;
    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();
    assert_eq!(
        outputs.last().map(String::as_str),
        Some("sat"),
        "a vacuous inner EXISTS must not stop the model gate from certifying \
         a valid quantified conjunct (#satgate-vacuous-binder, 66538b006f)"
    );
}

/// GUARD: the fix must not become a blanket relaxation of the fail-closed
/// funnel. The same shape with a LIVE inner binder — `y` really occurs, under
/// an uninterpreted `f` the witness says nothing about — is exactly the case
/// the gate exists for, and must still degrade to `unknown`. (Measured: HEAD
/// `unknown`, fix `unknown`; disabling the gate site outright instead turns
/// `crates/ay-dpll/tests/fixtures/ufbv_uf_completion_strict_leg_wrong_sat.smt2`
/// — declared `unsat` — into a WRONG `sat`.)
#[test]
fn test_quantified_gate_still_failcloses_live_inner_binder() {
    let input = r#"
        (set-logic AUFLIA)
        (declare-fun f (Int) Int)
        (declare-fun c () Int)
        (assert (> c 3))
        (assert (forall ((x Int)) (=> (= x 5) (forall ((y Int)) (< (f y) (+ x x))))))
        (check-sat)
    "#;
    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();
    assert_eq!(
        outputs.last().map(String::as_str),
        Some("unknown"),
        "a LIVE inner binder is not vacuous: the gate must still fail closed \
         rather than publish an uncertified `sat` (#satgate-vacuous-binder)"
    );
}
