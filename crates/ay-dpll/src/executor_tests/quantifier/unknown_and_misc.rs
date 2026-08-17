// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use ay_core::{Sort, Symbol};
use num_bigint::BigInt;

/// Test that unknown_reason returns correct reason for quantifier-related Unknown
#[test]
fn test_unknown_reason_quantifiers() {
    // Create a formula with quantifiers that will return Unknown
    let smt = r#"
        (set-logic LIA)
        (declare-fun P (Int) Bool)
        (assert (forall ((x Int)) (P x)))
        (assert (not (P 0)))
        (check-sat)
    "#;

    let commands = parse(smt).unwrap();
    let mut exec = Executor::new();
    let _result = exec.execute_all(&commands).unwrap();

    // After check-sat with quantifiers, if result is Unknown, reason should be
    // one of the quantifier sub-reasons (not the generic Incomplete/Unknown).
    if exec.last_result().is_some_and(|r| r.is_unknown()) {
        let reason = exec.unknown_reason();
        assert!(reason.is_some(), "Should have a reason for Unknown result");
        let r = reason.unwrap();
        assert!(
            matches!(
                r,
                UnknownReason::QuantifierRoundLimit
                    | UnknownReason::QuantifierDeferred
                    | UnknownReason::QuantifierUnhandled
                    | UnknownReason::QuantifierCegqiIncomplete
            ),
            "Reason should be a quantifier sub-reason, got: {r:?}"
        );
    }
}

/// A dead trigger controls instantiation only; it does not weaken the universal.
/// An E-matching-only (`no_mbqi`) quantifier can have an impossible body even
/// without a ground trigger head; the old vacuous-trigger shortcut fabricated SAT.
#[test]
fn no_mbqi_dead_trigger_with_impossible_body_never_sat() {
    let mut executor = Executor::new();
    executor.ctx.set_logic("UFBV".to_string());

    let bit = Sort::bitvec(1);
    let x = executor.ctx.terms.mk_var("x", bit.clone());
    let fx = executor.ctx.terms.mk_app(Symbol::named("f"), vec![x], bit);
    let zero = executor.ctx.terms.mk_bitvec(BigInt::from(0), 1);
    let one = executor.ctx.terms.mk_bitvec(BigInt::from(1), 1);
    let eq_zero = executor.ctx.terms.mk_eq(fx, zero);
    let eq_one = executor.ctx.terms.mk_eq(fx, one);
    let body = executor.ctx.terms.mk_and(vec![eq_zero, eq_one]);
    let forall = executor.ctx.terms.mk_forall_with_triggers(
        vec![("x".to_string(), Sort::bitvec(1))],
        body,
        vec![vec![fx]],
    );
    executor.ctx.terms.mark_no_mbqi(forall);
    executor.ctx.assertions.push(forall);

    let result = executor.check_sat();
    assert!(
        !matches!(result, Ok(SolveResult::Sat)),
        "an impossible no_mbqi forall must never be reported sat: {result:?}"
    );
}
/// Test that unknown_reason returns None when result is SAT or UNSAT
#[test]
fn test_unknown_reason_sat_unsat() {
    // SAT case
    let smt = r#"
        (set-logic QF_LIA)
        (declare-const x Int)
        (assert (= x 5))
        (check-sat)
    "#;
    let commands = parse(smt).unwrap();
    let mut exec = Executor::new();
    let _result = exec.execute_all(&commands).unwrap();
    assert!(exec.last_result().is_some_and(|r| r.is_sat()));
    assert!(
        exec.unknown_reason().is_none(),
        "Should be None for SAT result"
    );

    // UNSAT case
    let smt2 = r#"
        (set-logic QF_LIA)
        (declare-const x Int)
        (assert (and (> x 5) (< x 3)))
        (check-sat)
    "#;
    let commands2 = parse(smt2).unwrap();
    let mut exec2 = Executor::new();
    let _result2 = exec2.execute_all(&commands2).unwrap();
    assert!(exec2.last_result().is_some_and(|r| r.is_unsat()));
    assert!(
        exec2.unknown_reason().is_none(),
        "Should be None for UNSAT result"
    );
}
/// Test that UnknownReason Display formats correctly for SMT-LIB output
#[test]
fn test_unknown_reason_display() {
    assert_eq!(format!("{}", UnknownReason::Timeout), "timeout");
    assert_eq!(format!("{}", UnknownReason::Interrupted), "interrupted");
    assert_eq!(format!("{}", UnknownReason::Incomplete), "incomplete");
    assert_eq!(
        format!("{}", UnknownReason::QuantifierRoundLimit),
        "(incomplete quantifier-round-limit)"
    );
    assert_eq!(
        format!("{}", UnknownReason::QuantifierDeferred),
        "(incomplete quantifier-deferred)"
    );
    assert_eq!(
        format!("{}", UnknownReason::QuantifierUnhandled),
        "(incomplete quantifier-unhandled)"
    );
    assert_eq!(
        format!("{}", UnknownReason::QuantifierCegqiIncomplete),
        "(incomplete quantifier-cegqi)"
    );
    assert_eq!(format!("{}", UnknownReason::SplitLimit), "incomplete");
    assert_eq!(format!("{}", UnknownReason::ResourceLimit), "resourceout");
    assert_eq!(format!("{}", UnknownReason::MemoryLimit), "memout");
    assert_eq!(format!("{}", UnknownReason::Unsupported), "unsupported");
    assert_eq!(format!("{}", UnknownReason::Unknown), "unknown");
}

// ============================================================================
// #5042: Enumerative instantiation fallback for triggerless quantifiers
// ============================================================================
/// Triggerless forall over uninterpreted sort with ground terms: enumerative
/// instantiation should produce x:=a and x:=b, yielding UNSAT from (= b a)
/// contradicting (not (= b a)).
#[test]
fn test_enumerative_instantiation_uninterpreted_sort_5042() {
    let input = r#"
        (declare-sort S 0)
        (declare-fun a () S)
        (declare-fun b () S)
        (assert (forall ((x S)) (= x a)))
        (assert (not (= b a)))
        (check-sat)
    "#;
    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();
    assert_eq!(outputs, vec!["unsat"]);
}
/// Triggerless forall over uninterpreted sort with no ground terms:
/// enumerative instantiation cannot produce any bindings, but the
/// (#p2-mbqi-empty-universe) singleton-witness certificate now decides this
/// SAT (z3 parity: 1-element universe, `P ≡ true`). Formerly pinned the
/// fail-closed `unknown`.
#[test]
fn test_enumerative_instantiation_no_ground_terms_5042() {
    let input = r#"
        (declare-sort U 0)
        (declare-fun P (U) Bool)
        (assert (forall ((x U)) (P x)))
        (check-sat)
    "#;
    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();
    assert_eq!(outputs, vec!["sat"]);
}
/// Multi-variable enumerative instantiation: forall x y. x=y with two distinct
/// ground constants should find x:=c1, y:=c2 producing (= c1 c2), contradicting
/// (not (= c1 c2)).
#[test]
fn test_enumerative_instantiation_multi_var_5042() {
    let input = r#"
        (declare-sort T 0)
        (declare-fun c1 () T)
        (declare-fun c2 () T)
        (assert (forall ((x T) (y T)) (= x y)))
        (assert (not (= c1 c2)))
        (check-sat)
    "#;
    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();
    assert_eq!(outputs, vec!["unsat"]);
}
/// CEGQI with div operator: forall x. (x > 0) => (div x 2) > 0
/// INVALID: x=1 gives div(1,2)=0, not > 0.
/// Expected: unsat (asserting an invalid forall).
///
/// The key challenge is that `pv` appears under `(div pv 2)`, so bound extraction
/// fails for that assertion. CEGQI must rely on:
/// 1. The `x > 0` bound (tightened to `x >= 1` for integers) for selection
/// 2. The model-value fallback or neighbor enumeration to find x=1
///
/// (#5888: div/mod in quantified formulas is a key deductive-checks pattern)
#[test]
fn test_cegqi_div_counterexample_5888() {
    use std::sync::atomic::{AtomicBool, Ordering};
    use std::sync::Arc;
    use std::time::Duration;

    let input = r#"
        (set-logic LIA)
        (assert (forall ((x Int))
            (=> (> x 0)
                (> (div x 2) 0))))
        (check-sat)
    "#;

    let commands = parse(input).expect("valid SMT-LIB input");
    let mut exec = Executor::new();

    // Set a 15s timeout to prevent debug-mode hangs (#6889).
    // The CEGQI div/mod refinement loop can diverge in debug builds
    // where each LIA solve iteration is much slower.
    let interrupt = Arc::new(AtomicBool::new(false));
    exec.set_interrupt(Arc::clone(&interrupt));
    let timer_interrupt = Arc::clone(&interrupt);
    let timer = std::thread::spawn(move || {
        std::thread::sleep(Duration::from_secs(15));
        timer_interrupt.store(true, Ordering::Relaxed);
    });

    let outputs = exec.execute_all(&commands).expect("execution succeeds");
    let () = interrupt.store(true, Ordering::Relaxed); // cancel timer
    let _ = timer.join();

    // INVALID formula — x=1 is a counterexample. Should be UNSAT.
    // Currently returns "unknown" due to CEGQI div/mod incompleteness gap
    // (see #5888). Accepting "unsat" (complete) or "unknown" (sound-but-incomplete).
    // "sat" would be unsound — the formula is invalid.
    assert!(
        outputs == vec!["unsat"] || outputs == vec!["unknown"],
        "Must not return sat — formula is invalid (x=1 counterexample). Got: {outputs:?}",
    );
}
/// Diagnostic test for #6045: 13-chain E-matching budget exhaustion.
///
/// Z3 returns UNSAT on this formula. AY should return either UNSAT (if
/// all 13 instantiation rounds complete) or UNKNOWN (if budget is exhausted).
/// Returning SAT is unsound.
///
/// This test inspects `last_result()` and `unknown_reason()` to determine
/// whether the SAT-to-Unknown guard in `map_quantifier_result` fired.
#[test]
fn test_6045_13chain_ematching_budget_must_not_return_sat() {
    let smt = r#"
        (set-logic UFLIA)
        (declare-fun P0 (Int) Bool)
        (declare-fun P1 (Int) Bool)
        (declare-fun P2 (Int) Bool)
        (declare-fun P3 (Int) Bool)
        (declare-fun P4 (Int) Bool)
        (declare-fun P5 (Int) Bool)
        (declare-fun P6 (Int) Bool)
        (declare-fun P7 (Int) Bool)
        (declare-fun P8 (Int) Bool)
        (declare-fun P9 (Int) Bool)
        (declare-fun P10 (Int) Bool)
        (declare-fun P11 (Int) Bool)
        (declare-fun P12 (Int) Bool)
        (assert (forall ((x Int)) (! (=> (P0 x) (P1 x)) :pattern ((P0 x)))))
        (assert (forall ((x Int)) (! (=> (P1 x) (P2 x)) :pattern ((P1 x)))))
        (assert (forall ((x Int)) (! (=> (P2 x) (P3 x)) :pattern ((P2 x)))))
        (assert (forall ((x Int)) (! (=> (P3 x) (P4 x)) :pattern ((P3 x)))))
        (assert (forall ((x Int)) (! (=> (P4 x) (P5 x)) :pattern ((P4 x)))))
        (assert (forall ((x Int)) (! (=> (P5 x) (P6 x)) :pattern ((P5 x)))))
        (assert (forall ((x Int)) (! (=> (P6 x) (P7 x)) :pattern ((P6 x)))))
        (assert (forall ((x Int)) (! (=> (P7 x) (P8 x)) :pattern ((P7 x)))))
        (assert (forall ((x Int)) (! (=> (P8 x) (P9 x)) :pattern ((P8 x)))))
        (assert (forall ((x Int)) (! (=> (P9 x) (P10 x)) :pattern ((P9 x)))))
        (assert (forall ((x Int)) (! (=> (P10 x) (P11 x)) :pattern ((P10 x)))))
        (assert (forall ((x Int)) (! (=> (P11 x) (P12 x)) :pattern ((P11 x)))))
        (assert (forall ((x Int)) (! (=> (P12 x) false) :pattern ((P12 x)))))
        (assert (P0 0))
        (check-sat)
    "#;

    let commands = parse(smt).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    let result = exec.last_result();
    let reason = exec.unknown_reason();

    let assertion_count = exec.context().assertions.len();

    // SAT is unsound: Z3 confirms this is UNSAT.
    // Acceptable: UNSAT (correct) or UNKNOWN (conservative).
    assert_ne!(
        outputs,
        vec!["sat"],
        "BUG #6045: returning SAT on an UNSAT formula is unsound.\n\
         last_result={result:?}, reason_unknown={reason:?}, assertions={assertion_count}"
    );
}

// #quantifier_consumer-arith soundness regression (deductive-checks exec_spec_unverified
// five_wrong): a spec-fn UF definition axiom over BV8 alongside a GROUND
// counterexample query whose atoms are pure BV comparisons over free constants.
// The formula is satisfiable, but a ground model plus one matched definition
// point does not construct a total model for the universal: cost filtering and
// presolve-model filtering can omit other indexed applications. Without an
// independently materialized and re-checked interpretation, fail closed.
#[test]
fn test_bv_uf_definition_axiom_ground_counterexample_fails_closed() {
    let smt = r#"
        (set-logic ALL)
        (declare-fun five ((_ BitVec 8) (_ BitVec 8) (_ BitVec 8) (_ BitVec 8) (_ BitVec 8)) Bool)
        (declare-const x1 (_ BitVec 8))
        (declare-const x2 (_ BitVec 8))
        (declare-const x3 (_ BitVec 8))
        (declare-const x4 (_ BitVec 8))
        (declare-const x5 (_ BitVec 8))
        (declare-const result Bool)
        (assert (= result (= x1 x2)))
        (assert (forall ((v1 (_ BitVec 8)) (v2 (_ BitVec 8)) (v3 (_ BitVec 8)) (v4 (_ BitVec 8)) (v5 (_ BitVec 8)))
            (= (five v1 v2 v3 v4 v5)
               (and (= v1 v2) (not (= v3 v4)) (not (= v3 v5)) (not (= v2 v5))))))
        (assert (not (= (= x1 x2) (five x1 x2 x3 x4 x5))))
        (assert (= (five x1 x2 x3 x4 x5)
                   (and (= x1 x2) (not (= x3 x4)) (not (= x3 x5)) (not (= x2 x5)))))
        (check-sat)
    "#;

    let commands = parse(smt).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();
    assert_eq!(
        outputs,
        vec!["unknown"],
        "a syntactic UF-definition candidate must not grant sat"
    );
}

/// UNSAT twin of the test above: the wrapper body matches the spec exactly,
/// so the refutation query has no counterexample. The sound UNSAT-only
/// consequence probe still decides it.
#[test]
fn test_bv_uf_definition_axiom_valid_wrapper_is_unsat() {
    let smt = r#"
        (set-logic ALL)
        (declare-fun five ((_ BitVec 8) (_ BitVec 8) (_ BitVec 8) (_ BitVec 8) (_ BitVec 8)) Bool)
        (declare-const x1 (_ BitVec 8))
        (declare-const x2 (_ BitVec 8))
        (declare-const x3 (_ BitVec 8))
        (declare-const x4 (_ BitVec 8))
        (declare-const x5 (_ BitVec 8))
        (assert (forall ((v1 (_ BitVec 8)) (v2 (_ BitVec 8)) (v3 (_ BitVec 8)) (v4 (_ BitVec 8)) (v5 (_ BitVec 8)))
            (= (five v1 v2 v3 v4 v5)
               (and (= v1 v2) (not (= v3 v4)) (not (= v3 v5)) (not (= v2 v5))))))
        (assert (not (= (and (= x1 x2) (not (= x3 x4)) (not (= x3 x5)) (not (= x2 x5)))
                        (five x1 x2 x3 x4 x5))))
        (assert (= (five x1 x2 x3 x4 x5)
                   (and (= x1 x2) (not (= x3 x4)) (not (= x3 x5)) (not (= x2 x5)))))
        (check-sat)
    "#;

    let commands = parse(smt).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();
    assert_eq!(
        outputs,
        vec!["unsat"],
        "a wrapper body identical to the spec has no counterexample"
    );
}

/// #quantifier_consumer-arith no-regression control: an UNSAT pure-arithmetic ground atom
/// (`(> (mod (mod x0 5) 3) (abs (+ -5 x0)))`) next to a completable
/// UF-definition axiom. The mod/div ground core is where the lower solve can
/// return Unknown with nothing verified, so the STRICT certificate must keep
/// gating that leg: the answer must never be `sat`.
#[test]
fn test_quantifier_consumer_arith_unsat_ground_atom_never_sat_under_uf_axiom() {
    let smt = r#"
        (set-logic ALL)
        (declare-fun g (Int) Int)
        (declare-const x0 Int)
        (assert (forall ((v Int)) (= (g v) (+ v 1))))
        (assert (> (mod (mod x0 5) 3) (abs (+ (- 5) x0))))
        (check-sat)
    "#;

    let commands = parse(smt).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();
    assert_eq!(outputs.len(), 1);
    assert_ne!(
        outputs[0], "sat",
        "an UNSAT pure-arith ground atom must never be certified sat (#quantifier_consumer-arith)"
    );
}

fn check_sat_output(smt: &str) -> String {
    let commands = parse(smt).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();
    outputs.last().cloned().unwrap_or_default()
}

/// (#p2-nested-forall) Nested forall towers are merged and decided: a ground violation is UNSAT
/// (z3 parity; previously `Unknown(QuantifierUnhandled)` before binder merging).
#[test]
fn test_nested_forall_tower_merged_unsat() {
    let out = check_sat_output(
        r#"
        (set-logic UFLIA)
        (declare-fun p (Int Int) Bool)
        (declare-fun a () Int)
        (declare-fun b () Int)
        (assert (forall ((x Int)) (forall ((y Int)) (=> (p x y) (< x y)))))
        (assert (p a b))
        (assert (>= a b))
        (check-sat)
    "#,
    );
    assert_eq!(out, "unsat", "merged binder tower must decide UNSAT");
}

/// (#p2-nested-forall) Triple-deep tower over an uninterpreted sort.
#[test]
fn test_nested_forall_triple_tower_unsat() {
    let out = check_sat_output(
        r#"
        (set-logic UF)
        (declare-sort U 0)
        (declare-fun P (U U U) Bool)
        (declare-fun a () U)
        (assert (forall ((x U)) (forall ((y U)) (forall ((z U)) (P x y z)))))
        (assert (not (P a a a)))
        (check-sat)
    "#,
    );
    assert_eq!(out, "unsat", "triple tower must decide UNSAT");
}

/// (#p2-nested-forall) Shadowed-name capture twin: a naive no-rename merge
/// would weaken `∀x. q(x) ⇒ ∀x. p(x)` to the SATISFIABLE `∀x. q(x) ⇒ p(x)`.
/// The problem is UNSAT and must STAY unsat.
#[test]
fn test_nested_forall_shadowed_merge_stays_unsat() {
    let out = check_sat_output(
        r#"
        (set-logic UFLIA)
        (declare-fun q (Int) Bool)
        (declare-fun p (Int) Bool)
        (assert (forall ((x Int)) (=> (q x) (forall ((x Int)) (p x)))))
        (assert (q 0))
        (assert (not (p 1)))
        (check-sat)
    "#,
    );
    assert_eq!(out, "unsat", "shadowed nested forall must stay UNSAT");
}

/// (#p2-nested-forall) SAT twin of the tower shape: must never flip to unsat.
#[test]
fn test_nested_forall_tower_sat_twin_never_unsat() {
    let out = check_sat_output(
        r#"
        (set-logic UFLIA)
        (declare-fun p (Int Int) Bool)
        (declare-fun a () Int)
        (declare-fun b () Int)
        (assert (forall ((x Int)) (forall ((y Int)) (=> (p x y) (< x y)))))
        (assert (p a b))
        (assert (< a b))
        (check-sat)
    "#,
    );
    assert_ne!(out, "unsat", "satisfiable tower twin must never be unsat");
}

/// (#p2-ufnia-refutation) The instance-closure fresh re-solve decides the
/// UFNIA refutation `f(0)=0 ∧ ∀x. f(x)² ≥ 1` (z3 parity; the in-place lane
/// returns Unknown on the instance-augmented window).
#[test]
fn test_ufnia_instance_closure_refutation_unsat() {
    let out = check_sat_output(
        r#"
        (set-logic UFNIA)
        (declare-fun f (Int) Int)
        (assert (forall ((x Int)) (>= (* (f x) (f x)) 1)))
        (assert (= (f 0) 0))
        (check-sat)
    "#,
    );
    assert_eq!(out, "unsat", "instance-closure re-solve must decide UNSAT");
}

/// (#p2-ufnia-refutation) Boundary twin `f(0)=1` is SAT (z3): must never be
/// unsat (sat or a fail-closed unknown are both acceptable).
#[test]
fn test_ufnia_instance_closure_sat_twin_never_unsat() {
    let out = check_sat_output(
        r#"
        (set-logic UFNIA)
        (declare-fun f (Int) Int)
        (assert (forall ((x Int)) (>= (* (f x) (f x)) 1)))
        (assert (= (f 0) 1))
        (check-sat)
    "#,
    );
    assert_ne!(out, "unsat", "satisfiable UFNIA twin must never be unsat");
}

/// (#p2-ufnia-refutation) Disjunctively-positioned forall: the closure
/// re-solve must NOT conjoin its instances — `(or r (forall x. p x)) ∧ ¬p(0)`
/// is SAT via `r` (z3 sat) and must never be unsat.
#[test]
fn test_disjunctive_forall_never_unsat_via_closure() {
    let out = check_sat_output(
        r#"
        (declare-fun p (Int) Bool)
        (declare-const r Bool)
        (assert (or r (forall ((x Int)) (p x))))
        (assert (not (p 0)))
        (check-sat)
    "#,
    );
    assert_ne!(
        out, "unsat",
        "disjunctive forall must never be conjoined into UNSAT"
    );
}

/// (#p2-mbqi-empty-universe) Empty uninterpreted universe, bare predicate:
/// SAT with a synthesized singleton witness (z3 parity).
#[test]
fn test_empty_universe_singleton_sat() {
    let out = check_sat_output(
        r#"
        (declare-sort U 0)
        (declare-fun p (U) Bool)
        (assert (forall ((x U)) (p x)))
        (check-sat)
    "#,
    );
    assert_eq!(out, "sat", "empty-universe EPR forall must certify SAT");
}

/// (#eu-uf-interp) REFUTATION WITNESS. A `sat` whose only constraint on a UF
/// is a UNIVERSAL quantifier over an empty uninterpreted universe must publish
/// an interpretation for that UF, and the interpretation must actually satisfy
/// the assertion it is offered as a witness for.
///
/// This is ay's half of deductive-checks's trait-conformance soundness controls. The
/// query is the NEGATED obligation ("some `dm` is >100 at every receiver, and
/// the candidate body returns 0"), so `sat` IS the refutation and the printed
/// `define-fun` IS the counterexample the control needs to display.
///
/// The regression: the singleton-universe lane
/// (`mbqi_empty_universe_singleton_decide`) decided the value in its sub-solve
/// and then dropped it, because the BV lanes Ackermannize UF applications and
/// build no EUF function table. `(get-model)` then printed literally
/// `(model )` and the quantified model-check gate, seeing a witness that pins
/// no interpretation for `DT__dm`, deferred and failed the verdict CLOSED to
/// `unknown (:reason-unknown incomplete)`. The refutation survived; the
/// counterexample did not.
///
/// The assertion below is deliberately NOT "a model came back": it replays the
/// published constant back through the solver and requires the assertion's
/// NEGATION at that value to be `unsat` — i.e. the witness really does what a
/// witness must.
#[test]
fn empty_universe_bv_uf_refutation_publishes_a_checkable_witness() {
    let commands = parse(
        r#"
        (set-logic ALL)
        (declare-sort Poly 0)
        (declare-fun DT__dm (Poly) (_ BitVec 32))
        (declare-const impl_result (_ BitVec 32))
        (assert (forall ((self Poly)) (bvult #x00000064 (DT__dm self))))
        (assert (= impl_result #x00000000))
        (check-sat)
    "#,
    )
    .expect("script parses");
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).expect("script executes");
    assert_eq!(
        outputs.last().map(String::as_str),
        Some("sat"),
        "the refutation query must stay decided, not degrade to unknown"
    );

    assert_published_constant_witness_beats_100(&exec.model());
}

/// (#eu-uf-interp) The SAME refutation shape as the test above, but with the
/// `:pattern` deductive-checks actually attaches. A triggered `forall` is not
/// "completely unhandled", so this shape used to bypass the singleton theorem
/// and rely on a bare model-extension claim. That claim was never cashed out:
/// the emitted witness was empty and the quantified gate deferred it to
/// `unknown (incomplete)`. Patterned and unpatterned forms must now use the
/// same checked singleton-model transaction. This is the shape the
/// trait-conformance controls actually send.
#[test]
fn vacuous_trigger_bv_uf_refutation_publishes_a_checkable_witness() {
    let commands = parse(
        r#"
        (set-logic ALL)
        (declare-sort Poly 0)
        (declare-fun DT__dm (Poly) (_ BitVec 32))
        (declare-const impl_result (_ BitVec 32))
        (assert (forall ((self Poly))
                  (! (bvult #x00000064 (DT__dm self)) :pattern ((DT__dm self)))))
        (assert (= impl_result #x00000000))
        (check-sat)
    "#,
    )
    .expect("script parses");
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).expect("script executes");
    assert_eq!(
        outputs.last().map(String::as_str),
        Some("sat"),
        "the triggered refutation query must stay decided, not degrade to unknown"
    );
    assert_published_constant_witness_beats_100(&exec.model());
}

/// Shared checker for the two tests above: the published model must NAME
/// `DT__dm`, its interpretation must be a CONSTANT over the singleton universe,
/// and that constant must actually satisfy `(bvult #x00000064 DT__dm(_))` —
/// re-decided by the solver, not re-derived here. Deliberately not "a model came
/// back": an empty or unrelated model fails every one of these.
fn assert_published_constant_witness_beats_100(model: &str) {
    let start = model
        .find("define-fun DT__dm")
        .unwrap_or_else(|| panic!("published model names no interpretation for DT__dm:\n{model}"));
    let body = &model[start..];
    let body = match body[1..].find("(define-fun ") {
        Some(next) => &body[..=next],
        None => body,
    };
    assert!(
        !body.contains("ite"),
        "expected a constant interpretation over the singleton universe, got:\n{body}"
    );
    let value_at = body
        .find("#x")
        .unwrap_or_else(|| panic!("no bit-vector value in the DT__dm interpretation:\n{body}"));
    let value: String = body[value_at..]
        .chars()
        .take_while(|c| *c == '#' || *c == 'x' || c.is_ascii_hexdigit())
        .collect();

    // THE WITNESS MUST DO ITS JOB. `sat` claims some `DT__dm` is >100
    // everywhere; the published one is the constant `value`, so
    // `(bvult #x00000064 value)` must be VALID.
    let replay = check_sat_output(&format!(
        "(set-logic ALL)(assert (not (bvult #x00000064 {value})))(check-sat)"
    ));
    assert_eq!(
        replay, "unsat",
        "published witness DT__dm = {value} does NOT satisfy the assertion it witnesses"
    );

    // And the ground half of the counterexample is published too.
    assert!(
        model.contains("impl_result"),
        "the counterexample must also pin the violating body's result:\n{model}"
    );
}

/// (#p2-mbqi-empty-universe) Nonempty-sort refutation: `∀x.p(x) ∧ ∀x.¬p(x)`
/// over an empty ground universe is UNSAT (SMT-LIB sorts are nonempty).
#[test]
fn test_empty_universe_conflict_unsat() {
    let out = check_sat_output(
        r#"
        (declare-sort U 0)
        (declare-fun p (U) Bool)
        (assert (forall ((x U)) (p x)))
        (assert (forall ((x U)) (not (p x))))
        (check-sat)
    "#,
    );
    assert_eq!(
        out, "unsat",
        "EPR conflict over a nonempty sort must be UNSAT"
    );
}

/// (#p2-mbqi-empty-universe) REVIEW GUARD 1: a nested binder inside the body
/// makes the singleton sub-solve unsound for SAT (it could invent a second
/// element). The problem is UNSAT (any nonempty universe has p everywhere and
/// somewhere not) — it must NEVER answer sat.
#[test]
fn test_empty_universe_nested_exists_never_sat() {
    let out = check_sat_output(
        r#"
        (declare-sort U 0)
        (declare-fun p (U) Bool)
        (assert (forall ((x U)) (and (p x) (exists ((y U)) (not (p y))))))
        (check-sat)
    "#,
    );
    assert_ne!(out, "sat", "nested-binder body must not be certified SAT");
}

/// (#p2-mbqi-empty-universe) REVIEW GUARD 2 (coverage): a forall binding the
/// empty sort hiding under `or` outside the certified roots must fail closed
/// for the SAT direction — the problem is SAT via `r` (z3), and certifying
/// sat from the root forall alone would ignore the disjunct; equally it must
/// never be unsat.
#[test]
fn test_empty_universe_forall_under_or_fails_closed() {
    let out = check_sat_output(
        r#"
        (declare-sort U 0)
        (declare-fun p (U) Bool)
        (declare-const r Bool)
        (assert (forall ((x U)) (p x)))
        (assert (or r (forall ((y U)) (not (p y)))))
        (check-sat)
    "#,
    );
    assert_ne!(out, "unsat", "under-or forall must never turn UNSAT");
}

/// (#p2-mbqi-empty-universe) Cardinality control: ground distinctness forces
/// ground U terms, so the empty-universe branch never fires and the existing
/// enumerator keeps deciding UNSAT.
#[test]
fn test_cardinality_two_distinct_stays_unsat() {
    let out = check_sat_output(
        r#"
        (declare-sort U 0)
        (declare-fun a () U)
        (declare-fun b () U)
        (assert (forall ((x U) (y U)) (= x y)))
        (assert (distinct a b))
        (check-sat)
    "#,
    );
    assert_eq!(out, "unsat", "cardinality conflict must stay UNSAT");
}

/// (#p2-default-row) c2: n-ary bare-tuple default-row certificate decides
/// `∀x,y:Int. p(x,y)` SAT with `p ≡ true` (z3 parity).
#[test]
fn test_default_row_nary_bare_predicate_sat() {
    let out = check_sat_output(
        r#"
        (declare-fun p (Int Int) Bool)
        (assert (forall ((x Int) (y Int)) (p x y)))
        (check-sat)
    "#,
    );
    assert_eq!(out, "sat", "n-ary bare predicate forall must certify SAT");
}

/// (#p2-default-row) REVIEW GUARD (mixed table/default tuples): the UNSAT
/// shape `q(0) ∧ ∀x,y.(q(x)→p(x,y)) ∧ ∀x,y.(q(x)→¬p(x,y))` has an empty
/// full-ground table for `p`, and a naive "ground points + all-default row"
/// residual would certify a wrong SAT. The symbolic full-expansion residual
/// must reject every default vector: the answer must never be sat.
#[test]
fn test_default_row_mixed_tuple_twin_never_sat() {
    let out = check_sat_output(
        r#"
        (declare-fun q (Int) Bool)
        (declare-fun p (Int Int) Bool)
        (assert (q 0))
        (assert (forall ((x Int) (y Int)) (=> (q x) (p x y))))
        (assert (forall ((x Int) (y Int)) (=> (q x) (not (p x y)))))
        (check-sat)
    "#,
    );
    assert_ne!(
        out, "sat",
        "mixed-tuple UNSAT twin must never be certified SAT"
    );
}

/// (#p2-diag-position) WRONG-VERDICT REPAIR (skeptic probe a12): a nested
/// forall TOWER that is only a DISJUNCT — `(or c (∀x.∀y. p(x,y)))` — must
/// never have its diagonal instance `p(0,0)` conjoined: with `¬p(0,0)` the
/// formula is trivially SAT (`c:=true, p≡false`; z3: sat), but the
/// merge-then-diagonal interaction manufactured a wrong `unsat`.
#[test]
fn test_disjunct_tower_diagonal_never_unsat() {
    let out = check_sat_output(
        r#"
        (declare-fun p (Int Int) Bool)
        (declare-const c Bool)
        (assert (or c (forall ((x Int)) (forall ((y Int)) (p x y)))))
        (assert (not (p 0 0)))
        (check-sat)
    "#,
    );
    assert_ne!(
        out, "unsat",
        "a forall that is only a disjunct must never be diagonally conjoined into UNSAT"
    );
}

/// (#p2-diag-position) Same class, pre-existing FLAT form (skeptic probe u2):
/// a multi-binder forall directly under `or` (no merge involved). Trivially
/// SAT (`r:=true, p≡false`; z3: sat) — was a wrong `unsat` on main before the
/// positional gate on the diagonal pass.
#[test]
fn test_disjunct_flat_multibinder_diagonal_never_unsat() {
    let out = check_sat_output(
        r#"
        (declare-fun p (Int Int) Bool)
        (declare-const r Bool)
        (assert (or r (forall ((x Int) (y Int)) (p x y))))
        (assert (not (p 0 0)))
        (check-sat)
    "#,
    );
    assert_ne!(
        out, "unsat",
        "a flat multi-binder forall under or must never be diagonally conjoined into UNSAT"
    );
}

/// (#p2-diag-position) Same class under `ite` (skeptic probe x2/t2) and `xor`
/// (t3) and `=>` (t1): every non-conjunctive position must fail closed, never
/// wrong-`unsat`.
#[test]
fn test_tower_under_ite_impl_xor_never_unsat() {
    for (name, smt) in [
        (
            "ite",
            r#"
            (declare-fun p (Int Int) Bool)
            (declare-const c Bool)
            (assert (ite c true (forall ((x Int)) (forall ((y Int)) (p x y)))))
            (assert (not (p 0 0)))
            (check-sat)
        "#,
        ),
        (
            "impl",
            r#"
            (declare-fun p (Int Int) Bool)
            (declare-const c Bool)
            (assert (=> (not c) (forall ((x Int)) (forall ((y Int)) (p x y)))))
            (assert (not (p 0 0)))
            (check-sat)
        "#,
        ),
        (
            "xor",
            r#"
            (declare-fun p (Int Int) Bool)
            (declare-const c Bool)
            (assert (xor c (forall ((x Int)) (forall ((y Int)) (p x y)))))
            (assert (not (p 0 0)))
            (check-sat)
        "#,
        ),
    ] {
        let out = check_sat_output(smt);
        assert_ne!(
            out, "unsat",
            "tower under {name} is satisfiable (z3: sat) and must never be wrong-unsat"
        );
    }
}

/// (#p2-diag-position) EPR variant over an uninterpreted sort (skeptic probe
/// x3/x4): disjunct tower + ground negative literal — SAT via the disjunct
/// escape hatch; must never be wrong-`unsat`.
#[test]
fn test_disjunct_tower_epr_never_unsat() {
    let out = check_sat_output(
        r#"
        (declare-sort U 0)
        (declare-const a U)
        (declare-fun p (U U) Bool)
        (declare-const c Bool)
        (assert (or c (forall ((x U)) (forall ((y U)) (p x y)))))
        (assert (not (p a a)))
        (check-sat)
    "#,
    );
    assert_ne!(
        out, "unsat",
        "EPR disjunct tower is satisfiable and must never be wrong-unsat"
    );
}

/// (#p2-diag-position) POSITIVE CONTROL (fuzzer Class B must keep refuting):
/// a top-level-conjunct multi-binder forall still gets its diagonal
/// instance — `∀x,y:U. s(x,y)` with `¬s(d,d)` is UNSAT (z3 parity).
#[test]
fn test_conjunct_forall_diagonal_still_refutes() {
    let out = check_sat_output(
        r#"
        (declare-sort U 0)
        (declare-const d U)
        (declare-fun s (U U) Bool)
        (assert (not (s d d)))
        (assert (forall ((x U) (y U)) (s x y)))
        (check-sat)
    "#,
    );
    assert_eq!(
        out, "unsat",
        "top-level-conjunct forall must keep its diagonal refutation"
    );
}

/// (#p2-diag-position) POSITIVE CONTROL (NNF dual): a top-level NEGATED
/// EXISTS is an entailed universal — `¬∃x,y:U. ¬s(x,y)` with `¬s(d,d)` must
/// still refute via the minted dual's diagonal instance (z3: unsat).
#[test]
fn test_negated_exists_diagonal_still_refutes() {
    let out = check_sat_output(
        r#"
        (declare-sort U 0)
        (declare-const d U)
        (declare-fun s (U U) Bool)
        (assert (not (s d d)))
        (assert (not (exists ((x U) (y U)) (not (s x y)))))
        (check-sat)
    "#,
    );
    assert_eq!(
        out, "unsat",
        "negated-exists dual universal must keep its diagonal refutation"
    );
}

mod negated_exists_sat;
