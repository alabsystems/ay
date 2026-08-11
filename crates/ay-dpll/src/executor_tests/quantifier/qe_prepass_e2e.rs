// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! End-to-end conformance tests for the deep QE pre-pass (#qe-prepass):
//! quantified LIA/LRA alternations that previously returned `unknown` now
//! decide via Cooper (Int) / Loos-Weispfenning (Real) elimination on the
//! check-sat path. Every newly-decided SAT class is paired with a mutated
//! UNSAT twin (and vice versa); all verdicts verified against z3.

use super::*;
use ay_core::Sort;
use num_bigint::BigInt;

// ---------------------------------------------------------------------------
// LIA: same-direction ∀∃ alternation (previously unknown)
// ---------------------------------------------------------------------------

#[test]
fn qe_prepass_lia_forall_exists_same_direction_sat() {
    // ∀x.∃y.(y > x ∧ y > 5) — valid over Int (z3: sat; formerly unknown).
    let input = r#"
        (set-logic LIA)
        (assert (forall ((x Int)) (exists ((y Int)) (and (> y x) (> y 5)))))
        (check-sat)
    "#;
    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();
    assert_eq!(outputs, vec!["sat"]);
}

#[test]
fn qe_prepass_lia_forall_exists_same_direction_negated_unsat() {
    // The negation twin of the newly-decided SAT probe (z3: unsat).
    let input = r#"
        (set-logic LIA)
        (assert (not (forall ((x Int)) (exists ((y Int)) (and (> y x) (> y 5))))))
        (check-sat)
    "#;
    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();
    assert_eq!(outputs, vec!["unsat"]);
}

// ---------------------------------------------------------------------------
// LIA: three-level alternation (previously unknown)
// ---------------------------------------------------------------------------

#[test]
fn qe_prepass_lia_three_level_alternation_sat() {
    // ∀x.∃y.∀z.(z < y ⇒ z < x + 10) (z3: sat; formerly unknown).
    let input = r#"
        (set-logic LIA)
        (assert (forall ((x Int)) (exists ((y Int))
            (forall ((z Int)) (=> (< z y) (< z (+ x 10)))))))
        (check-sat)
    "#;
    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();
    assert_eq!(outputs, vec!["sat"]);
}

#[test]
fn qe_prepass_lia_three_level_alternation_negated_unsat() {
    // The negation twin (z3: unsat).
    let input = r#"
        (set-logic LIA)
        (assert (not (forall ((x Int)) (exists ((y Int))
            (forall ((z Int)) (=> (< z y) (< z (+ x 10))))))))
        (check-sat)
    "#;
    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();
    assert_eq!(outputs, vec!["unsat"]);
}

// ---------------------------------------------------------------------------
// LIA: pre-existing wins must not regress (solved by the quantifier loop
// before the pre-pass existed; now solved by elimination).
// ---------------------------------------------------------------------------

#[test]
fn qe_prepass_lia_bounded_window_stays_sat() {
    // ∀x.∃y.(y > x ∧ y < x + 3) — already SAT before the pre-pass.
    let input = r#"
        (set-logic LIA)
        (assert (forall ((x Int)) (exists ((y Int)) (and (> y x) (< y (+ x 3))))))
        (check-sat)
    "#;
    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();
    assert_eq!(outputs, vec!["sat"]);
}

#[test]
fn qe_prepass_lia_empty_window_stays_unsat() {
    // ∀x.∃y.(y > x ∧ y < x) — already UNSAT before the pre-pass.
    let input = r#"
        (set-logic LIA)
        (assert (forall ((x Int)) (exists ((y Int)) (and (> y x) (< y x)))))
        (check-sat)
    "#;
    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();
    assert_eq!(outputs, vec!["unsat"]);
}

// ---------------------------------------------------------------------------
// LRA: ∀∃ over Real via Loos-Weispfenning (previously unknown)
// ---------------------------------------------------------------------------

#[test]
fn qe_prepass_lra_shifted_equality_sat() {
    // ∀x.∃y. y = x + 1 over Real (z3: sat; formerly unknown).
    let input = r#"
        (set-logic LRA)
        (assert (forall ((x Real)) (exists ((y Real)) (= y (+ x 1.0)))))
        (check-sat)
    "#;
    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();
    assert_eq!(outputs, vec!["sat"]);
}

#[test]
fn qe_prepass_lra_conflicting_equalities_unsat() {
    // Wrong-twin: ∀x.∃y.(y = x+1 ∧ y = x+2) (z3: unsat).
    let input = r#"
        (set-logic LRA)
        (assert (forall ((x Real)) (exists ((y Real))
            (and (= y (+ x 1.0)) (= y (+ x 2.0))))))
        (check-sat)
    "#;
    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();
    assert_eq!(outputs, vec!["unsat"]);
}

#[test]
fn qe_prepass_lra_open_interval_dense_sat() {
    // ∀x.∃y.(y > x ∧ y < x + 1/2) — TRUE over the dense reals, where the
    // Int analogue would be false (z3: sat; formerly unknown).
    let input = r#"
        (set-logic LRA)
        (assert (forall ((x Real)) (exists ((y Real)) (and (> y x) (< y (+ x 0.5))))))
        (check-sat)
    "#;
    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();
    assert_eq!(outputs, vec!["sat"]);
}

#[test]
fn qe_prepass_lra_punctured_point_unsat() {
    // ∀x.∃y.(y ≥ x ∧ y ≤ x ∧ y ≠ x) — the single point is punctured away
    // (z3: unsat).
    let input = r#"
        (set-logic LRA)
        (assert (forall ((x Real)) (exists ((y Real))
            (and (>= y x) (<= y x) (not (= y x))))))
        (check-sat)
    "#;
    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();
    assert_eq!(outputs, vec!["unsat"]);
}

// ---------------------------------------------------------------------------
// Incremental: push/pop around quantified + ground assertions (the pre-pass
// is in-place and length-preserving; scope assertion counts must survive).
// ---------------------------------------------------------------------------

#[test]
fn qe_prepass_incremental_push_pop_sequence() {
    // Verdicts verified against z3 (per-state, non-incrementally).
    let input = r#"
        (set-logic LIA)
        (declare-const a Int)
        (assert (forall ((x Int)) (exists ((y Int)) (and (> y x) (> y 5)))))
        (check-sat)
        (push 1)
        (assert (> a 5))
        (assert (< a 3))
        (check-sat)
        (pop 1)
        (check-sat)
    "#;
    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();
    assert_eq!(outputs, vec!["sat", "unsat", "sat"]);
}

#[test]
fn qe_prepass_incremental_quantified_inside_scope() {
    // A quantified assertion confined to a pushed scope must vanish on pop.
    let input = r#"
        (set-logic LIA)
        (declare-const a Int)
        (assert (> a 0))
        (check-sat)
        (push 1)
        (assert (forall ((x Int)) (exists ((y Int)) (and (> y x) (< y x)))))
        (check-sat)
        (pop 1)
        (check-sat)
    "#;
    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();
    assert_eq!(outputs, vec!["sat", "unsat", "sat"]);
}

// ---------------------------------------------------------------------------
// Mixed ground + quantified: model produced on the eliminated set must
// satisfy the ground constraints.
// ---------------------------------------------------------------------------

#[test]
fn qe_prepass_mixed_ground_constraint_respected() {
    // The eliminated universal is valid; the verdict must be driven by the
    // ground part (a > 5 ∧ a < 4 unsat; a > 5 alone sat).
    let sat_input = r#"
        (set-logic LIA)
        (declare-const a Int)
        (assert (> a 5))
        (assert (forall ((x Int)) (exists ((y Int)) (and (> y x) (> y a)))))
        (check-sat)
    "#;
    let commands = parse(sat_input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();
    assert_eq!(outputs, vec!["sat"]);

    let unsat_input = r#"
        (set-logic LIA)
        (declare-const a Int)
        (assert (> a 5))
        (assert (< a 4))
        (assert (forall ((x Int)) (exists ((y Int)) (and (> y x) (> y a)))))
        (check-sat)
    "#;
    let commands = parse(unsat_input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();
    assert_eq!(outputs, vec!["unsat"]);
}

/// #qe-prepass-restore-cert: a ground constraint next to a quantified
/// assertion the deep-QE pre-pass ELIMINATES. The eliminated form drives the
/// verdict and the restored (authored) universal must still be certified
/// against the emitted model. z3: sat (`a = 10`) / unsat.
#[test]
fn qe_prepass_restore_cert_model_dependent_universal_sat() {
    // ∀x.(0 ≤ x ≤ 3 ⇒ x < a) eliminates to `a > 3`, so the disjunctive ground
    // constraint is forced to the `a = 10` branch (z3: sat).
    let input = r#"
        (set-logic LIA)
        (declare-const a Int)
        (assert (or (= a 0) (= a 10)))
        (assert (forall ((x Int)) (=> (and (<= 0 x) (<= x 3)) (< x a))))
        (check-sat)
    "#;
    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();
    assert_eq!(outputs, vec!["sat"]);
}

/// Opposite-verdict twin: pinning `a` to the falsifying branch refutes
/// (z3: unsat). A certificate that confirmed the universal without reading
/// the model would leave this `sat`.
#[test]
fn qe_prepass_restore_cert_model_dependent_universal_twin_unsat() {
    let input = r#"
        (set-logic LIA)
        (declare-const a Int)
        (assert (= a 0))
        (assert (forall ((x Int)) (=> (and (<= 0 x) (<= x 3)) (< x a))))
        (check-sat)
    "#;
    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();
    assert_eq!(outputs, vec!["unsat"]);
}

/// #qe-prepass-restore-cert NON-VACUITY. The restore certificate must actually
/// EVALUATE the eliminated universal against the EMITTED MODEL, not merely
/// observe that the pre-pass could eliminate it.
///
/// Same assertion, same code path, two models: `∀x.(0 ≤ x ≤ 3 ⇒ x < a)`
/// eliminates to `a > 3`, so the certificate must ACCEPT under a model pinning
/// `a = 10` and REJECT the falsifying `a = 0`. (The accept leg also pins the
/// wiring: were the rebuilt `a` a different node from the declared constant,
/// the equivalent would be unevaluable and BOTH legs would return `false`.)
#[test]
fn qe_prepass_restore_cert_rejects_falsifying_model() {
    fn cert_under_pin(pin: i64) -> bool {
        let input = format!("(set-logic LIA)(declare-const a Int)(assert (= a {pin}))(check-sat)");
        let commands = parse(&input).unwrap();
        let mut exec = Executor::new();
        assert_eq!(exec.execute_all(&commands).unwrap(), vec!["sat"]);
        // Install the quantified assertion into the emitted model's window
        // without disturbing the model (a `Command::Assert` would invalidate
        // it), exactly as `restore_assertions` hands it to the certificate.
        // `a` must be the DECLARED constant's own node: the front end mints it
        // with `mk_fresh_named_var`, so re-interning the name would build a
        // different (unpinned) leaf.
        let a = exec
            .ctx
            .symbol_iter()
            .find(|(name, _)| name.as_str() == "a")
            .and_then(|(_, info)| info.term)
            .expect("declared constant `a` must carry a term");
        let x = exec.ctx.terms.mk_var("x", Sort::Int);
        let zero = exec.ctx.terms.mk_int(BigInt::from(0));
        let three = exec.ctx.terms.mk_int(BigInt::from(3));
        let lo = exec.ctx.terms.mk_le(zero, x);
        let hi = exec.ctx.terms.mk_le(x, three);
        let guard = exec.ctx.terms.mk_and(vec![lo, hi]);
        let concl = exec.ctx.terms.mk_lt(x, a);
        let body = exec.ctx.terms.mk_implies(guard, concl);
        let fa = exec
            .ctx
            .terms
            .mk_forall(vec![("x".to_string(), Sort::Int)], body);
        exec.ctx.assertions.push(fa);
        exec.qe_prepass_certifies_restored_quantifiers()
    }

    assert!(
        cert_under_pin(10),
        "a = 10 satisfies the eliminated universal (a > 3): the certificate must confirm"
    );
    assert!(
        !cert_under_pin(0),
        "a = 0 FALSIFIES the eliminated universal (a > 3): the certificate must refuse — \
         a confirmation here would be vacuous"
    );
}

// ---------------------------------------------------------------------------
// Mixed-sort ∀Int ∃Real blocks via to_real purification (previously unknown)
// ---------------------------------------------------------------------------

#[test]
fn qe_prepass_mixed_sort_block_sat() {
    // ∀n:Int.∃r:Real. r = to_real(n) (z3: sat; formerly unknown).
    let input = r#"
        (set-logic ALL)
        (assert (forall ((n Int)) (exists ((r Real)) (= r (to_real n)))))
        (check-sat)
    "#;
    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();
    assert_eq!(outputs, vec!["sat"]);
}

#[test]
fn qe_prepass_mixed_sort_block_twin_unsat() {
    // Opposite-verdict twin: the inner matrix is unsatisfiable for every n
    // (z3: unsat), exercising purification + LW + self-check end to end.
    let input = r#"
        (set-logic ALL)
        (assert (forall ((n Int)) (exists ((r Real))
            (and (= r (to_real n)) (< r (to_real n))))))
        (check-sat)
    "#;
    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();
    assert_eq!(outputs, vec!["unsat"]);
}

// ---------------------------------------------------------------------------
// Cooper negated divisibility via ∀-duality (previously unknown)
// ---------------------------------------------------------------------------

#[test]
fn qe_prepass_ndiv_duality_residue_cover_sat() {
    // ∀x.(2|x ∨ 2|x+1) — duality gives ∃x.(¬(2|x) ∧ ¬(2|x+1)) ≡ false, so
    // the universal holds (z3: sat; formerly unknown).
    let input = r#"
        (set-logic ALL)
        (assert (forall ((x Int)) (or (= (mod x 2) 0) (= (mod (+ x 1) 2) 0))))
        (check-sat)
    "#;
    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();
    assert_eq!(outputs, vec!["sat"]);
}

#[test]
fn qe_prepass_ndiv_duality_twin_unsat() {
    // Opposite-verdict twin ∀x.¬(2|x) (z3: unsat).
    let input = r#"
        (set-logic ALL)
        (assert (forall ((x Int)) (not (= (mod x 2) 0))))
        (check-sat)
    "#;
    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();
    assert_eq!(outputs, vec!["unsat"]);
}

// ---------------------------------------------------------------------------
// QF to_real substitution route (solve_lira full preprocessing; formerly
// unknown on plain check-sat while check-sat-assuming decided)
// ---------------------------------------------------------------------------

#[test]
fn lira_to_real_bridge_open_unit_interval_unsat() {
    // r = to_real(n) ∧ 0 < r < 1 has no integral witness (z3: unsat).
    let input = r#"
        (set-logic ALL)
        (declare-const n Int)
        (declare-const r Real)
        (assert (= r (to_real n)))
        (assert (< 0.0 r))
        (assert (< r 1.0))
        (check-sat)
    "#;
    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();
    assert_eq!(outputs, vec!["unsat"]);
}

#[test]
fn lira_to_real_bridge_closed_interval_sat_model_validates() {
    // The half-open twin admits n = 0 (z3: sat); the recovered model must
    // carry the substituted vars (r = to_real(n) with 0 ≤ r < 1 forces 0).
    let input = r#"
        (set-logic ALL)
        (declare-const n Int)
        (declare-const r Real)
        (assert (= r (to_real n)))
        (assert (<= 0.0 r))
        (assert (< r 1.0))
        (check-sat)
        (get-value (n r))
    "#;
    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();
    assert_eq!(outputs.len(), 2);
    assert_eq!(outputs[0], "sat");
    assert_eq!(outputs[1], "((n 0) (r 0.0))");
}

#[test]
fn lira_to_real_bridge_incremental_push_pop() {
    // Verdict sequence across scopes on the substitution route
    // (z3: sat, unsat, sat, sat, sat).
    let input = r#"
        (set-logic ALL)
        (declare-const n Int)
        (declare-const r Real)
        (assert (= r (to_real n)))
        (check-sat)
        (push 1)
        (assert (< 0.0 r))
        (assert (< r 1.0))
        (check-sat)
        (pop 1)
        (check-sat)
        (push 1)
        (assert (<= 0.0 r))
        (assert (< r 1.0))
        (check-sat)
        (pop 1)
        (check-sat)
    "#;
    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();
    assert_eq!(outputs, vec!["sat", "unsat", "sat", "sat", "sat"]);
}
