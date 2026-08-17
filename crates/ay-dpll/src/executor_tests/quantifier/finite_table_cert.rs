// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! CAP-1 finite-table + default certified-SAT tests
//! (`try_finite_table_sat_certificate`).
//!
//! The positive tests pin the certificate's GRANTS (class-A shapes that must
//! be certified SAT). The adversarial tests pin its REFUSALS: every way the
//! certificate could be fooled must fail closed — the engine may prove a
//! decisive verdict through other sound machinery, but it must NEVER report
//! `sat` for the unsatisfiable shapes, and the out-of-class satisfiable
//! shapes must not be certified by THIS certificate (they stay `unknown`
//! today; a future sound certificate for non-constant defaults may upgrade
//! them).

use super::*;

fn solve_one(input: &str) -> String {
    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();
    outputs.last().cloned().unwrap_or_default()
}

// ---------------------------------------------------------------------------
// Grants.
// ---------------------------------------------------------------------------

/// The CAP-1 repro: `forall x. f(x) >= 0` with a pinned point `f(3) = 5`.
/// Certified by table {3 -> 5} + default 0 (residual `0 >= 0` is ground-true).
#[test]
fn finite_table_cert_grants_table_plus_default() {
    let verdict = solve_one(
        r#"
        (set-logic UFLIA)
        (declare-fun f (Int) Int)
        (assert (forall ((x Int)) (>= (f x) 0)))
        (assert (= (f 3) 5))
        (check-sat)
    "#,
    );
    assert_eq!(verdict, "sat");
}

/// The certificate's proof object is the TOTAL table-plus-default
/// interpretation. The public model and evaluator must retain both halves,
/// including the default at a point absent from the ground snapshot.
#[test]
fn finite_table_cert_publishes_exact_table_plus_default_model() {
    let commands = parse(
        r#"
        (set-logic UFLIA)
        (declare-fun f (Int) Int)
        (assert (forall ((x Int)) (>= (f x) 0)))
        (assert (= (f 3) 5))
        (check-sat)
        (get-model)
        (get-value ((f 3) (f 99)))
    "#,
    )
    .unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs[0], "sat");
    assert!(
        exec.finite_table_cert_grant_active,
        "the CAP-1 certificate must own this quantified SAT"
    );
    assert!(
        outputs[1].contains("(define-fun f ((x0 Int)) Int"),
        "the certified function must be printable: {}",
        outputs[1]
    );
    assert_eq!(
        outputs[2], "(((f 3) 5) ((f 99) 0))",
        "listed and default points must agree with the certified interpretation"
    );
}

/// Two table symbols in one body: residual needs the JOINT default vector
/// (d_f + d_g >= 0).
#[test]
fn finite_table_cert_grants_joint_defaults() {
    let verdict = solve_one(
        r#"
        (set-logic UFLIA)
        (declare-fun f (Int) Int)
        (declare-fun g (Int) Int)
        (assert (forall ((x Int)) (>= (+ (f x) (g x)) 0)))
        (assert (= (f 3) 1))
        (assert (= (g 3) 2))
        (check-sat)
    "#,
    );
    assert_eq!(verdict, "sat");
}

/// `ite` on the binder: the table point x=3 is covered pointwise and the
/// residual solver leg carries the x != 3 disequality.
#[test]
fn finite_table_cert_grants_ite_body() {
    let verdict = solve_one(
        r#"
        (set-logic UFLIA)
        (declare-fun f (Int) Int)
        (assert (forall ((x Int)) (ite (= x 3) (= (f x) 5) (>= (f x) 0))))
        (assert (= (f 3) 5))
        (check-sat)
    "#,
    );
    // #quantified-model-gate: satisfiable, but the emitted table can carry
    // leaked CE-probe rows (e.g. `f(9) = -2`) that FALSIFY the forall; the
    // gate then fail-closes to `unknown` rather than print a falsifying
    // witness. `sat` is acceptable only with a valid printed model.
    assert!(
        verdict == "sat" || verdict == "unknown",
        "expected sat (with a valid model) or fail-closed unknown, got {verdict}"
    );
}

/// Arbitrary-precision bound: the evaluator works over BigInt, so a bound
/// beyond machine words must not overflow (adversarial review item:
/// overflow).
#[test]
fn finite_table_cert_grants_bigint_bound_no_overflow() {
    let verdict = solve_one(
        r#"
        (set-logic UFLIA)
        (declare-fun f (Int) Int)
        (assert (forall ((x Int)) (>= (f x) (- 1000000000000000000000000))))
        (assert (= (f 3) 5))
        (check-sat)
    "#,
    );
    assert_eq!(verdict, "sat");
}

/// A free constant (`declare-const`) in the body is a model-pinned x-free
/// leaf, not a bound variable.
#[test]
fn finite_table_cert_grants_free_constant_bound() {
    let verdict = solve_one(
        r#"
        (set-logic UFLIA)
        (declare-fun f (Int) Int)
        (declare-const k Int)
        (assert (forall ((x Int)) (>= (f x) k)))
        (assert (= (f 3) 5))
        (assert (= k (- 2)))
        (check-sat)
    "#,
    );
    assert_eq!(verdict, "sat");
}

/// Two foralls sharing a symbol: ONE interpretation (shared default vector)
/// must satisfy both simultaneously.
///
/// REPINNED after 161d781cc (fix(proof): certify nested integer decrease
/// obligations) — verified by running this test at 161d781cc (fails) and its
/// parent b5a635d06 (passes). The widened authored-linear certification now
/// discharges the demand search's successor-instance refutation INLINE
/// (`--debug-cert` shows the instance sub-solves classifying `Unsat` with no
/// parked residue), so the search completes without parking and the exact
/// public-root table RESCUE — the previously pinned route — is never needed.
/// The user-visible contract is unchanged and still pinned: `sat`, and ONE
/// shared interpretation printed for both foralls. The route pins flip to the
/// new contract: nothing parks, so no rescue grant and no parked stat.
#[test]
fn finite_table_cert_grants_shared_symbol_two_foralls() {
    let commands = parse(
        r#"
        (set-logic UFLIA)
        (declare-fun f (Int) Int)
        (declare-fun g (Int) Int)
        (assert (forall ((x Int)) (>= (f x) 0)))
        (assert (forall ((y Int)) (>= (+ (f y) (g y)) 0)))
        (assert (= (f 2) 3))
        (assert (= (g 2) 0))
        (check-sat)
        (get-value ((f 2) (f 99) (g 2) (g 99)))
    "#,
    )
    .unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs.first().map(String::as_str), Some("sat"));
    assert_eq!(
        outputs.get(1).map(String::as_str),
        Some("(((f 2) 3) ((f 99) 0) ((g 2) 0) ((g 99) 0))")
    );
    assert_eq!(
        exec.statistics()
            .get_int("quantifier.demand.exact_root_theorem_superseded_parked"),
        None,
        "since 161d781cc the successor instance is refuted inline, so the \
         demand search completes without parking and the table rescue is \
         never engaged"
    );
    assert!(
        !exec.finite_table_cert_grant_active,
        "no parked residue means the exact-table rescue lane must stay idle"
    );
}

/// A conflicting ground sibling must never be hidden by separately grantable
/// universal subsets. The query may be refuted before reaching the all-roots
/// producer; either route must refuse SAT.
#[test]
fn finite_table_cert_shared_symbol_ground_conflict_never_sat() {
    let verdict = solve_one(
        r#"
        (set-logic UFLIA)
        (declare-fun f (Int) Int)
        (declare-fun g (Int) Int)
        (assert (forall ((x Int)) (>= (f x) 0)))
        (assert (forall ((y Int)) (>= (+ (f y) (g y)) 0)))
        (assert (= (f 2) (- 1)))
        (assert (= (g 2) 0))
        (check-sat)
    "#,
    );
    assert_ne!(verdict, "sat");
}

/// Direct assumption solving captures the same immutable base snapshot as
/// plain check-sat and appends the active literal to the exact public root
/// vector used by the rescue and final postflight.
///
/// REPINNED after 161d781cc — same mechanism and evidence as
/// [`finite_table_cert_grants_shared_symbol_two_foralls`]: the successor
/// instance now refutes inline, nothing parks, and the rescue is never
/// engaged. The direct-assumption route's user-visible contract (`sat` with
/// the active literal honored) is unchanged and stays pinned.
#[test]
fn finite_table_cert_assumption_is_in_public_rescue_root_window() {
    let commands = parse(
        r#"
        (set-logic UFLIA)
        (declare-fun f (Int) Int)
        (declare-fun g (Int) Int)
        (declare-const enabled Bool)
        (assert (forall ((x Int)) (>= (f x) 0)))
        (assert (forall ((y Int)) (>= (+ (f y) (g y)) 0)))
        (assert (= (f 2) 3))
        (assert (= (g 2) 0))
        (check-sat-assuming (enabled))
    "#,
    )
    .unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs.first().map(String::as_str), Some("sat"));
    assert_eq!(
        exec.statistics()
            .get_int("quantifier.demand.exact_root_theorem_superseded_parked"),
        None,
        "since 161d781cc the successor instance is refuted inline on the \
         direct-assumption route too, so nothing parks and the rescue is \
         never engaged"
    );
}

/// Plain check-sat's named-core redirect solves through assumptions internally,
/// but its affine table model stays Pending until the outer plain SAT funnel
/// consumes it. A second emission would treat Installed transport as stale and
/// lose this satisfiable query to Unknown.
///
/// REPINNED after 161d781cc — same mechanism and evidence as
/// [`finite_table_cert_grants_shared_symbol_two_foralls`]: the successor
/// instance now refutes inline, nothing parks, and no exact-root transport is
/// left for an outer emission. The user-visible contract (`sat` and the one
/// shared interpretation) is unchanged and stays pinned.
#[test]
fn finite_table_cert_named_core_redirect_emits_pending_model_once() {
    let commands = parse(
        r#"
        (set-option :produce-unsat-cores true)
        (set-logic UFLIA)
        (declare-fun f (Int) Int)
        (declare-fun g (Int) Int)
        (assert (forall ((x Int)) (>= (f x) 0)))
        (assert (forall ((y Int)) (>= (+ (f y) (g y)) 0)))
        (assert (= (f 2) 3))
        (assert (! (= (g 2) 0) :named g_pin))
        (check-sat)
        (get-value ((f 2) (f 99) (g 2) (g 99)))
    "#,
    )
    .unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs.first().map(String::as_str), Some("sat"));
    assert_eq!(
        outputs.get(1).map(String::as_str),
        Some("(((f 2) 3) ((f 99) 0) ((g 2) 0) ((g 99) 0))")
    );
    assert_eq!(
        exec.statistics()
            .get_int("quantifier.demand.exact_root_theorem_superseded_parked"),
        None,
        "since 161d781cc the successor instance is refuted inline on the \
         named-core redirect too, so nothing parks and no exact-root \
         transport is left for an outer emission"
    );
}

/// Temporary and named-core assumptions are part of the exact public root
/// vector. A theorem for the base assertions cannot be retargeted around the
/// contradictory active literal.
#[test]
fn finite_table_cert_assumption_conflict_never_sat() {
    let verdict = solve_one(
        r#"
        (set-option :produce-unsat-cores true)
        (set-logic UFLIA)
        (declare-fun f (Int) Int)
        (declare-fun g (Int) Int)
        (declare-const bad Bool)
        (assert (forall ((x Int)) (>= (f x) 0)))
        (assert (forall ((y Int)) (>= (+ (f y) (g y)) 0)))
        (assert (= (g 2) 0))
        (assert (! (=> bad (= (f 2) (- 1))) :named conflict_when_bad))
        (check-sat-assuming (bad))
    "#,
    );
    assert_ne!(verdict, "sat");
}

/// Bool-codomain table symbol with a pinned false point (sort-mismatch
/// adversarial item: Int/Bool codomains must stay strictly typed).
#[test]
fn finite_table_cert_grants_bool_codomain() {
    let verdict = solve_one(
        r#"
        (set-logic UFLIA)
        (declare-fun p (Int) Bool)
        (declare-fun f (Int) Int)
        (assert (forall ((x Int)) (or (p x) (>= (f x) 0))))
        (assert (not (p 1)))
        (assert (= (f 1) 0))
        (check-sat)
    "#,
    );
    assert_eq!(verdict, "sat");
}

/// SMT shadowing: a ground constant named like the binder is a DIFFERENT
/// symbol; inside the body the name refers to the binder (adversarial item:
/// nested/shadowed binders).
#[test]
fn finite_table_cert_grants_shadowed_name() {
    let verdict = solve_one(
        r#"
        (set-logic UFLIA)
        (declare-fun f (Int) Int)
        (declare-const x Int)
        (assert (= x 7))
        (assert (forall ((x Int)) (>= (f x) 0)))
        (assert (= (f 3) 5))
        (check-sat)
    "#,
    );
    assert_eq!(verdict, "sat");
}

// ---------------------------------------------------------------------------
// Refusals: unsatisfiable shapes must NEVER come back `sat`.
// ---------------------------------------------------------------------------

/// Pinned point violating the forall: the certificate's pointwise leg checks
/// x=3 exactly (ite constant-folding adversarial item: the evaluator computes
/// the ite branch exactly instead of folding it away).
#[test]
fn finite_table_cert_refuses_ite_point_conflict() {
    let verdict = solve_one(
        r#"
        (set-logic UFLIA)
        (declare-fun f (Int) Int)
        (assert (forall ((x Int)) (>= (ite (= x 3) (f x) 0) 0)))
        (assert (= (f 3) (- 5)))
        (check-sat)
    "#,
    );
    assert_ne!(verdict, "sat", "unsatisfiable ite point conflict certified");
}

/// f applied to g(x) (adversarial item): the table argument shape is only the
/// bare `f(x)` — `f(g(x))` must be rejected by the body scan. The problem is
/// UNSAT (instance x=1 gives f(g(1)) = f(7) = -2 < 0).
#[test]
fn finite_table_cert_refuses_uf_of_uf_argument() {
    let verdict = solve_one(
        r#"
        (set-logic UFLIA)
        (declare-fun f (Int) Int)
        (declare-fun g (Int) Int)
        (assert (forall ((x Int)) (>= (f (g x)) 0)))
        (assert (= (g 1) 7))
        (assert (= (f 7) (- 2)))
        (check-sat)
    "#,
    );
    assert_ne!(verdict, "sat", "f(g(x)) shape wrongly certified");
}

/// Conflicting defaults: `forall x. f(x) >= 0` and `forall y. f(y) <= -1`
/// with NO ground point. No shared default vector exists; the joint check
/// must refuse (the problem is UNSAT).
#[test]
fn finite_table_cert_refuses_conflicting_foralls() {
    let verdict = solve_one(
        r#"
        (set-logic UFLIA)
        (declare-fun f (Int) Int)
        (assert (forall ((x Int)) (>= (f x) 0)))
        (assert (forall ((y Int)) (<= (f y) (- 1))))
        (check-sat)
    "#,
    );
    assert_ne!(verdict, "sat", "jointly unsatisfiable foralls certified");
}

/// The direct point conflict from the CAP-1 gate: never `sat`.
#[test]
fn finite_table_cert_refuses_point_conflict() {
    let verdict = solve_one(
        r#"
        (set-logic UFLIA)
        (declare-fun f (Int) Int)
        (assert (forall ((x Int)) (>= (f x) 0)))
        (assert (= (f 3) (- 1)))
        (check-sat)
    "#,
    );
    assert_ne!(verdict, "sat");
}

/// Shadowed-name UNSAT variant: the ground `x` and the binder `x` are
/// different symbols; the point conflict on f(3) must still refute.
#[test]
fn finite_table_cert_refuses_shadowed_name_conflict() {
    let verdict = solve_one(
        r#"
        (set-logic UFLIA)
        (declare-fun f (Int) Int)
        (declare-const x Int)
        (assert (= x 7))
        (assert (forall ((x Int)) (>= (f x) 0)))
        (assert (= (f 3) (- 1)))
        (check-sat)
    "#,
    );
    assert_ne!(verdict, "sat");
}

// ---------------------------------------------------------------------------
// Out-of-class satisfiable shapes: the certificate must NOT fire (they stay
// honestly `unknown` today; other sound machinery may upgrade them later).
// ---------------------------------------------------------------------------

/// Residual still mentions x with no constant default that works
/// (`f(x) > x` needs the non-constant default λx. x+1): the residual solver
/// leg cannot prove `d > x` valid, so the certificate must refuse.
#[test]
fn finite_table_cert_fail_closed_residual_mentions_x() {
    let verdict = solve_one(
        r#"
        (set-logic UFLIA)
        (declare-fun f (Int) Int)
        (assert (forall ((x Int)) (> (f x) x)))
        (assert (= (f 3) 5))
        (check-sat)
    "#,
    );
    assert_eq!(
        verdict, "unknown",
        "non-constant-default shape must fail closed (sat would need an \
         unimplemented lambda-default certificate; unsat is plain wrong)"
    );
}

/// Nested quantifier (adversarial item): outside CAP-1's single-binder
/// class. The (#p2-nested-forall) binder-merge prepass flattens the solver
/// view to `∀x,y. f(x)+g(y) >= 0`; at publication the (#p2-default-row)
/// certificate peels the exact authored tower read-only and checks that same
/// multi-binder obligation without changing its root identity. This now
/// decides `sat` (matching z3; verified with --debug-cert: the grant is
/// `CERT/default-row`, NOT the finite-table certificate, whose single-binder
/// gate is unchanged). The model is real: `f = ite(x=0,1,d_f)`,
/// `g = ite(y=0,1,d_g)` with `d_f = d_g = 0` passes the z3 re-assert gate.
/// `unsat` remains plain wrong.
#[test]
fn finite_table_cert_fail_closed_nested_quantifier() {
    let verdict = solve_one(
        r#"
        (set-logic UFLIA)
        (declare-fun f (Int) Int)
        (declare-fun g (Int) Int)
        (assert (forall ((x Int)) (forall ((y Int)) (>= (+ (f x) (g y)) 0))))
        (assert (= (f 0) 1))
        (assert (= (g 0) 1))
        (check-sat)
    "#,
    );
    assert_ne!(verdict, "unsat", "satisfiable nested forall reported unsat");
    assert_eq!(
        verdict, "sat",
        "merged tower + default-row certificate must decide this SAT"
    );
}

/// Shifted UF argument `f(x+1)` (adversarial item, argument-shape guard):
/// semantically equivalent to `f(x) >= 0` but outside the bare-`f(x)` class,
/// which the finite-table scan still rejects (`finite_table_scan_body`'s
/// xdep-argument guard; --debug-cert shows no finite-table grant here).
///
/// The `sat` this now reports comes from a DIFFERENT sound lane: the CEGQI
/// UF-graph model-pin certificate (#cegqi-mdef v2, b517b967) reached through
/// `disambiguate_cegqi_unsat` — per-universal refutation of the
/// de-skolemized counterexample `G0 ∧ pins ∧ ¬(f(c+1) >= 0)` with fresh `c`,
/// where the pins encode the completed graph-else-default interpretation of
/// `f`. The fresh-constant rule is argument-shape-agnostic (congruence
/// handles `f(c+1)`), and the shift handling was adversarially re-verified
/// when this expectation was updated: `f(3) = -1` and `f(-7) = -2` variants
/// answer `unsat` (violated points ARE in the shifted image), the
/// even-points-only variant `forall x. f(2x) >= 0` with `f(1) = -3` answers
/// `sat` (odd points unconstrained — a shift-blind certifier would refuse or
/// report a wrong verdict; see the companion tests below), and the
/// non-constant-default `f(x+1) > x` stays `unknown`.
///
/// `unknown` remains acceptable: the CEGQI certificate runs under a tight
/// wall-clock budget and fails closed when it expires. Only `unsat` is wrong.
#[test]
fn finite_table_cert_fail_closed_shifted_argument() {
    let verdict = solve_one(
        r#"
        (set-logic UFLIA)
        (declare-fun f (Int) Int)
        (assert (forall ((x Int)) (>= (f (+ x 1)) 0)))
        (assert (= (f 3) 5))
        (check-sat)
    "#,
    );
    assert!(
        verdict == "sat" || verdict == "unknown",
        "unexpected verdict {verdict:?}: expected sat (CEGQI UF-graph-pin \
         certificate) or a fail-closed unknown"
    );
}

/// Shift soundness pin: the shifted image covers `f(3)` (at `x = 2`), so a
/// conflicting pinned point is UNSAT. Guards the CEGQI UF-pin lane (and any
/// future lane) against treating `f(x+1)` as constraining a shifted/partial
/// set of points incorrectly.
#[test]
fn shifted_argument_violated_point_is_unsat() {
    let verdict = solve_one(
        r#"
        (set-logic UFLIA)
        (declare-fun f (Int) Int)
        (assert (forall ((x Int)) (>= (f (+ x 1)) 0)))
        (assert (= (f 3) (- 1)))
        (check-sat)
    "#,
    );
    assert_eq!(verdict, "unsat", "f(3) = -1 violates forall x. f(x+1) >= 0");
}

/// Shift soundness pin, negative point: `x = -8` reaches `f(-7)`.
#[test]
fn shifted_argument_violated_negative_point_is_unsat() {
    let verdict = solve_one(
        r#"
        (set-logic UFLIA)
        (declare-fun f (Int) Int)
        (assert (forall ((x Int)) (>= (f (+ x 1)) 0)))
        (assert (= (f (- 7)) (- 2)))
        (check-sat)
    "#,
    );
    assert_eq!(
        verdict, "unsat",
        "f(-7) = -2 violates forall x. f(x+1) >= 0 at x = -8"
    );
}

/// Non-surjective argument shape `f(2x)`: only EVEN points are constrained,
/// so a negative value at the ODD point 1 is satisfiable. A certifier that
/// conflates "the argument mentions x" with "all points are constrained"
/// would report a wrong unsat here; a fabricating one a wrong sat on the
/// unsat variants above. Only `unsat` is wrong (`sat` expected; `unknown`
/// is a fail-closed budget miss).
#[test]
fn multiplied_argument_odd_point_stays_sat() {
    let verdict = solve_one(
        r#"
        (set-logic UFLIA)
        (declare-fun f (Int) Int)
        (assert (forall ((x Int)) (>= (f (* 2 x)) 0)))
        (assert (= (f 4) 5))
        (assert (= (f 1) (- 3)))
        (check-sat)
    "#,
    );
    assert_ne!(
        verdict, "unsat",
        "f(1) = -3 sits at an ODD point, outside the image of 2x — \
         reporting unsat treats f(2x) as constraining all of Z"
    );
    assert!(
        verdict == "sat" || verdict == "unknown",
        "unexpected verdict {verdict:?}"
    );
}

/// The fail-closed infinite-domain guard must not suppress an actually
/// exhaustive finite-domain universal. Bool preprocessing enumerates both
/// values, so this remains a genuine SAT control.
#[test]
fn finite_domain_bool_forall_remains_sat() {
    let verdict = solve_one(
        r#"
        (set-logic UF)
        (declare-fun p (Bool) Bool)
        (assert (forall ((b Bool)) (= (p b) b)))
        (assert (p true))
        (assert (not (p false)))
        (check-sat)
    "#,
    );
    assert_eq!(verdict, "sat");
}

/// An INTERPRETED unary Int operator must never be classified as a table
/// symbol: `forall x. abs(x) = 0` is UNSAT (abs(1) = 1), but fabricating
/// `abs := λ_.0` would certify it. The scan must reject `abs` as out of
/// class; the engine may then decide it through the arithmetic pipeline —
/// only `sat` is wrong.
#[test]
fn finite_table_cert_refuses_interpreted_abs() {
    let verdict = solve_one(
        r#"
        (set-logic UFLIA)
        (assert (forall ((x Int)) (= (abs x) 0)))
        (check-sat)
    "#,
    );
    assert_ne!(verdict, "sat", "interpreted abs treated as free table UF");
}

/// A theory function must never acquire an invented finite-table
/// interpretation.  This was a concrete wrong-SAT vector: the one-binder
/// scanner could mistake `rem` for a free UF and choose the constant-zero
/// default, even though `rem 2 3 = 2` in integer arithmetic.
#[test]
fn finite_table_cert_never_reinterprets_rem() {
    let verdict = solve_one(
        r#"
        (set-logic UFLIA)
        (assert (forall ((y Int)) (= (rem 2 y) 0)))
        (check-sat)
    "#,
    );
    assert_eq!(
        verdict, "unsat",
        "interpreted rem was not solved with its arithmetic semantics"
    );
}

/// The n-ary default-row lane had the same authority flaw as the
/// single-binder finite-table lane.  Exact positive declaration binding must
/// reject `rem` before either certificate can synthesize a table for it.
#[test]
fn default_row_cert_never_reinterprets_rem() {
    let verdict = solve_one(
        r#"
        (set-logic UFLIA)
        (assert (forall ((x Int) (y Int)) (= (rem x y) 0)))
        (check-sat)
    "#,
    );
    assert_eq!(
        verdict, "unsat",
        "interpreted rem was not solved with its arithmetic semantics"
    );
}

/// Non-Int/Bool/Real sort in the body (sort-mismatch adversarial item): an
/// uninterpreted-codomain UF leaves the certified fragment entirely, so the
/// finite-table certificate must not fire. The problem is satisfiable
/// (u := λx. c); other sound machinery (EUF completion) may still decide it —
/// only `unsat` would be wrong.
#[test]
fn finite_table_cert_fail_closed_uninterpreted_codomain() {
    let verdict = solve_one(
        r#"
        (set-logic UFLIA)
        (declare-sort U 0)
        (declare-fun u (Int) U)
        (declare-const c U)
        (assert (forall ((x Int)) (= (u x) c)))
        (assert (= (u 1) c))
        (check-sat)
    "#,
    );
    assert_ne!(
        verdict, "unsat",
        "satisfiable uninterpreted-codomain forall reported unsat"
    );
}

// ---------------------------------------------------------------------------
// Real codomains (exact BigRational lane). The binder stays Int-only.
// ---------------------------------------------------------------------------

/// The tracked AUFLIRA fixture: Real-codomain table {3 -> 5.0} + default 0.0
/// (residual `0.0 >= 0.0` is ground-true). Was `unknown` before the Real
/// extension; `unsat` would be the old cross-sort bug.
#[test]
fn finite_table_cert_grants_real_codomain() {
    let verdict = solve_one(
        r#"
        (set-logic AUFLIRA)
        (declare-fun f (Int) Real)
        (assert (forall ((x Int)) (>= (f x) 0.0)))
        (assert (= (f 3) 5.0))
        (check-sat)
    "#,
    );
    assert_eq!(verdict, "sat");
}

/// Real point conflict: `f(3) = -5.0` violates the forall at the table point.
/// The pointwise leg must catch it exactly — never `sat`.
#[test]
fn finite_table_cert_refuses_real_point_conflict() {
    let verdict = solve_one(
        r#"
        (set-logic AUFLIRA)
        (declare-fun f (Int) Real)
        (assert (forall ((x Int)) (>= (f x) 0.0)))
        (assert (= (f 3) (- 5.0)))
        (check-sat)
    "#,
    );
    assert_ne!(verdict, "sat", "Real point conflict certified");
}

/// A Real BINDER is in class: the pointwise + residual totality argument is
/// domain-agnostic (see the Real-binder section of the certificate doc).
/// Table {3.0 -> 5.0} + default 0 (residual `0 >= 0` is ground-true).
#[test]
fn finite_table_cert_grants_real_binder() {
    let verdict = solve_one(
        r#"
        (set-logic AUFLIRA)
        (declare-fun f (Real) Real)
        (assert (forall ((x Real)) (>= (f x) 0.0)))
        (assert (= (f 3.0) 5.0))
        (check-sat)
    "#,
    );
    assert_eq!(verdict, "sat");
}

/// Real-binder point conflict: `f(3.0) = -5.0` violates the forall at the
/// table point — genuinely UNSAT, and the pointwise leg must never grant.
#[test]
fn finite_table_cert_refuses_real_binder_point_conflict() {
    let verdict = solve_one(
        r#"
        (set-logic AUFLIRA)
        (declare-fun f (Real) Real)
        (assert (forall ((x Real)) (>= (f x) 0.0)))
        (assert (= (f 3.0) (- 5.0)))
        (check-sat)
    "#,
    );
    assert_eq!(verdict, "unsat", "Real-binder point conflict must refute");
}

/// Non-integer rational table point: the key 0.5 has no integer
/// representation, so this exercises the exact-BigRational point path.
#[test]
fn finite_table_cert_grants_real_binder_rational_point() {
    let verdict = solve_one(
        r#"
        (set-logic AUFLIRA)
        (declare-fun f (Real) Real)
        (assert (forall ((x Real)) (>= (f x) 0.25)))
        (assert (= (f 0.5) 0.75))
        (check-sat)
    "#,
    );
    assert_eq!(verdict, "sat");
}

/// Real-binder residual solver leg: the residual `(or (< x 0.0) (>= d 0.0))`
/// still mentions x, so the isolated REAL-sorted ground refutation must
/// discharge it (fresh k of sort Real, point-exclusion disequality on 3.0).
#[test]
fn finite_table_cert_grants_real_binder_residual_solver_leg() {
    let verdict = solve_one(
        r#"
        (set-logic AUFLIRA)
        (declare-fun f (Real) Real)
        (assert (forall ((x Real)) (or (< x 0.0) (>= (f x) 0.0))))
        (assert (= (f 3.0) 5.0))
        (check-sat)
    "#,
    );
    assert_eq!(verdict, "sat");
}

/// Strict-inequality half-open boundary: the pinned point 3.0 sits exactly ON
/// the open border of `(3, 4)`, so the pointwise leg passes vacuously and the
/// residual leg must exclude k = 3.0 while covering the open interval with
/// the default d = 1 (hinted by the body constant).
#[test]
fn finite_table_cert_grants_real_binder_open_interval_boundary() {
    let verdict = solve_one(
        r#"
        (set-logic AUFLIRA)
        (declare-fun f (Real) Real)
        (assert (forall ((x Real)) (=> (and (< 3.0 x) (< x 4.0)) (>= (f x) 1.0))))
        (assert (= (f 3.0) 0.0))
        (check-sat)
    "#,
    );
    assert_eq!(verdict, "sat");
}

/// FOOLING VECTOR (strict-inequality boundary): `forall x:Real. f(x) > 0`
/// with the pinned point value EXACTLY 0 — `0 > 0` is false at the point, so
/// the problem is UNSAT and the exact pointwise comparison must refuse; a
/// certifier sloppy about strictness would grant.
#[test]
fn finite_table_cert_refuses_real_binder_strict_boundary() {
    let verdict = solve_one(
        r#"
        (set-logic AUFLIRA)
        (declare-fun f (Real) Real)
        (assert (forall ((x Real)) (> (f x) 0.0)))
        (assert (= (f 3.0) 0.0))
        (check-sat)
    "#,
    );
    assert_ne!(verdict, "sat", "strict boundary point wrongly certified");
}

/// FOOLING VECTOR (interval density): jointly UNSAT — every x in the OPEN
/// interval (0, 1) forces f(x) = 7, but f <= 6 everywhere. A residual leg
/// that quantified the fresh constant over the INTEGERS would see an empty
/// interval and wrongly certify; the REAL-sorted refutation must refuse.
#[test]
fn finite_table_cert_refuses_real_binder_interval_density() {
    let verdict = solve_one(
        r#"
        (set-logic AUFLIRA)
        (declare-fun f (Real) Real)
        (assert (forall ((x Real)) (or (<= x 0.0) (>= x 1.0) (= (f x) 7.0))))
        (assert (forall ((y Real)) (<= (f y) 6.0)))
        (check-sat)
    "#,
    );
    assert_ne!(
        verdict, "sat",
        "Int-density residual fool wrongly certified"
    );
}

/// FOOLING VECTOR (algebraic table point): the ground part pins c = sqrt(2)
/// — an IRRATIONAL point with no exact BigRational key. Satisfiable, but the
/// collect step must fail closed (`EvalValue::Algebraic` never matches the
/// `Rational`-only key arm); `unsat` would be plain wrong.
#[test]
fn finite_table_cert_fail_closed_real_binder_algebraic_point() {
    let verdict = solve_one(
        r#"
        (set-logic AUFNIRA)
        (declare-fun f (Real) Real)
        (declare-const c Real)
        (assert (= (* c c) 2.0))
        (assert (> c 0.0))
        (assert (= (f c) 5.0))
        (assert (forall ((x Real)) (>= (f x) 0.0)))
        (check-sat)
    "#,
    );
    assert_eq!(
        verdict, "unknown",
        "algebraic (irrational) table point must fail closed"
    );
}

/// FOOLING VECTOR (nonlinear body, x outside f): `x*x` in arithmetic
/// position would push a NONLINEAR real formula into the residual ground
/// solve — out of the Real-binder class (linearity guard). Satisfiable; must
/// fail closed, and `unsat` would be wrong.
#[test]
fn finite_table_cert_fail_closed_real_binder_nonlinear_x() {
    let verdict = solve_one(
        r#"
        (set-logic AUFNIRA)
        (declare-fun f (Real) Real)
        (assert (forall ((x Real)) (>= (+ (f x) (* x x)) 0.0)))
        (assert (= (f 3.0) 5.0))
        (check-sat)
    "#,
    );
    assert_eq!(
        verdict, "unknown",
        "nonlinear-in-x Real-binder body must fail closed"
    );
}

/// FOOLING VECTOR (nonlinear body, table-app product): `f(x)*f(x)` is out of
/// the Real-binder class even though it is semantically nonnegative — the
/// linearity guard rejects any x-dependent product that is not
/// `literal * single-x-dependent-factor`. Satisfiable; must fail closed.
#[test]
fn finite_table_cert_fail_closed_real_binder_table_app_product() {
    let verdict = solve_one(
        r#"
        (set-logic AUFNIRA)
        (declare-fun f (Real) Real)
        (assert (forall ((x Real)) (>= (* (f x) (f x)) 0.0)))
        (assert (= (f 3.0) 5.0))
        (check-sat)
    "#,
    );
    assert_eq!(
        verdict, "unknown",
        "table-app product Real-binder body must fail closed"
    );
}

/// FOOLING VECTOR (compound UF argument): `f(x*x)` reaches the UF through a
/// non-bare argument — out of class for ANY binder sort (the finite table
/// would not cover the image of x*x). Satisfiable; must fail closed.
#[test]
fn finite_table_cert_fail_closed_real_binder_compound_uf_arg() {
    let verdict = solve_one(
        r#"
        (set-logic AUFNIRA)
        (declare-fun f (Real) Real)
        (assert (forall ((x Real)) (>= (f (* x x)) 0.0)))
        (assert (= (f 3.0) 5.0))
        (check-sat)
    "#,
    );
    assert_eq!(
        verdict, "unknown",
        "compound UF argument must fail closed for Real binders too"
    );
}

/// Literal linear coefficient on a table app stays IN class for a Real
/// binder (`literal * x-dependent` is the one admitted product shape).
#[test]
fn finite_table_cert_grants_real_binder_literal_coeff() {
    let verdict = solve_one(
        r#"
        (set-logic AUFLIRA)
        (declare-fun f (Real) Real)
        (assert (forall ((x Real)) (>= (+ (* 2.0 (f x)) 1.0) 0.0)))
        (assert (= (f 3.0) 5.0))
        (check-sat)
    "#,
    );
    assert_eq!(verdict, "sat");
}

/// Mixed binder domains in one problem: an Int-binder forall and a
/// Real-binder forall, one shared interpretation (independent tables).
#[test]
fn finite_table_cert_grants_mixed_int_real_binders() {
    let verdict = solve_one(
        r#"
        (set-logic AUFLIRA)
        (declare-fun f (Int) Int)
        (declare-fun g (Real) Real)
        (assert (forall ((x Int)) (>= (f x) 0)))
        (assert (forall ((y Real)) (>= (g y) 0.0)))
        (assert (= (f 3) 5))
        (assert (= (g 2.5) 1.5))
        (check-sat)
    "#,
    );
    assert_eq!(verdict, "sat");
}

/// Two Real-domain UFs in one Real-binder body: the joint default vector
/// (d_f + d_g >= 0) must be found, with independent tables per symbol.
#[test]
fn finite_table_cert_grants_real_binder_two_ufs() {
    let verdict = solve_one(
        r#"
        (set-logic AUFLIRA)
        (declare-fun f (Real) Real)
        (declare-fun g (Real) Real)
        (assert (forall ((x Real)) (>= (+ (f x) (g x)) 0.0)))
        (assert (= (f 3.0) 1.5))
        (assert (= (g 3.0) 2.5))
        (check-sat)
    "#,
    );
    assert_eq!(verdict, "sat");
}

/// get-model after a Real-BINDER certificate grant: the printed table must
/// honour the pinned point and drop only the quantifier/CE-skolem phantom
/// rows (no command-level error).
#[test]
fn finite_table_cert_real_binder_get_model() {
    let output = solve_one(
        r#"
        (set-logic AUFLIRA)
        (declare-fun f (Real) Real)
        (assert (forall ((x Real)) (>= (f x) 0.0)))
        (assert (= (f 3.0) 5.0))
        (check-sat)
        (get-model)
    "#,
    );
    assert!(
        output.contains("define-fun f"),
        "get-model must print an interpretation for f, got: {output}"
    );
    assert!(
        !output.contains("error"),
        "get-model must not error after a certified Real-binder sat, got: {output}"
    );
}

/// Non-integer rational default: the bound 0.5 sits strictly between the
/// integer default candidates; the body-constant hint (0.5 itself) must be
/// picked up and the comparison done exactly.
#[test]
fn finite_table_cert_grants_rational_default_hint() {
    let verdict = solve_one(
        r#"
        (set-logic AUFLIRA)
        (declare-fun f (Int) Real)
        (assert (forall ((x Int)) (>= (f x) 0.5)))
        (assert (= (f 3) 1.0))
        (check-sat)
    "#,
    );
    assert_eq!(verdict, "sat");
}

/// FOOLING VECTOR (rational rounding): `f(3) = 0.3333333333333333` (sixteen
/// 3s) is strictly LESS than 1/3, so `forall x. f(x) > 1/3` is violated at
/// the table point. A float-rounding evaluator would see both sides as the
/// same f64 and grant; the exact BigRational comparison must refuse.
#[test]
fn finite_table_cert_refuses_rational_rounding_fool() {
    let verdict = solve_one(
        r#"
        (set-logic AUFLIRA)
        (declare-fun f (Int) Real)
        (assert (forall ((x Int)) (> (f x) (/ 1.0 3.0))))
        (assert (= (f 3) 0.3333333333333333))
        (check-sat)
    "#,
    );
    assert_ne!(verdict, "sat", "float rounding fooled the exact evaluator");
}

/// Division by a literal nonzero constant is in class: the body divides the
/// table value by 2 exactly (residual `(/ 0.0 2.0) >= 0.0` is ground-true).
#[test]
fn finite_table_cert_grants_literal_division() {
    let verdict = solve_one(
        r#"
        (set-logic AUFLIRA)
        (declare-fun f (Int) Real)
        (assert (forall ((x Int)) (>= (/ (f x) 2.0) 0.0)))
        (assert (= (f 3) 5.0))
        (check-sat)
    "#,
    );
    assert_eq!(verdict, "sat");
}

/// FOOLING VECTOR (division): a SYMBOLIC divisor (declared const, even one
/// pinned to 2.0) is out of class — only literal nonzero numerals pin the
/// division semantics. Satisfiable; must not be certified by this
/// certificate, and `unsat` would be wrong.
#[test]
fn finite_table_cert_fail_closed_symbolic_divisor() {
    let verdict = solve_one(
        r#"
        (set-logic AUFLIRA)
        (declare-fun f (Int) Real)
        (declare-const k Real)
        (assert (= k 2.0))
        (assert (forall ((x Int)) (>= (/ (f x) k) 0.0)))
        (assert (= (f 3) 5.0))
        (check-sat)
    "#,
    );
    assert_ne!(
        verdict, "unsat",
        "satisfiable symbolic-divisor forall reported unsat"
    );
}

/// FOOLING VECTOR (division by zero): `(/ (f x) 0.0)` has UNPINNED semantics
/// (SMT-LIB leaves x/0 uninterpreted). The scan must reject the shape — a
/// certificate that evaluated it with any fixed convention would be reasoning
/// about a function the model does not pin. z3 says `sat` (choose the /0
/// interpretation); `unsat` is wrong, and `sat` must not come from THIS
/// certificate's evaluator.
#[test]
fn finite_table_cert_fail_closed_division_by_zero() {
    let verdict = solve_one(
        r#"
        (set-logic AUFLIRA)
        (declare-fun f (Int) Real)
        (assert (forall ((x Int)) (>= (/ (f x) 0.0) 0.0)))
        (assert (= (f 3) 5.0))
        (check-sat)
    "#,
    );
    assert_ne!(verdict, "unsat", "satisfiable /0 forall reported unsat");
}

/// Mixed Int/Real coercion: an Int-codomain table symbol under `to_real`,
/// compared against a Real bound. Exact Int -> Rational injection.
#[test]
fn finite_table_cert_grants_to_real_coercion() {
    let verdict = solve_one(
        r#"
        (set-logic AUFLIRA)
        (declare-fun f (Int) Int)
        (assert (forall ((x Int)) (>= (to_real (f x)) 0.0)))
        (assert (= (f 3) 5))
        (check-sat)
    "#,
    );
    assert_eq!(verdict, "sat");
}

/// FOOLING VECTOR (coercion): `to_real(f(x)) = 0.5` is unsatisfiable for an
/// INT-codomain f — no integer maps to one half. The exact rational equality
/// at the table point (5.0 = 0.5 → false) and at every default must refuse;
/// an evaluator that truncated 0.5 to an int would wrongly grant.
#[test]
fn finite_table_cert_refuses_to_real_half_fool() {
    let verdict = solve_one(
        r#"
        (set-logic AUFLIRA)
        (declare-fun f (Int) Int)
        (assert (forall ((x Int)) (= (to_real (f x)) 0.5)))
        (assert (= (f 3) 5))
        (check-sat)
    "#,
    );
    assert_ne!(verdict, "sat", "Int/Real coercion truncation fool");
}

/// Real residual-solver leg: the residual `(or (= x 3) (>= d 1.5))` still
/// mentions x, so the isolated ground solve must prove it valid off the
/// table points for the body-hinted default d = 1.5.
#[test]
fn finite_table_cert_grants_real_residual_solver_leg() {
    let verdict = solve_one(
        r#"
        (set-logic AUFLIRA)
        (declare-fun f (Int) Real)
        (assert (forall ((x Int)) (or (= x 3) (>= (f x) 1.5))))
        (assert (= (f 0) 2.0))
        (check-sat)
    "#,
    );
    assert_eq!(verdict, "sat");
}

/// Joint Int + Real tables in one problem: one forall over an Int-codomain
/// symbol, one over a Real-codomain symbol, one shared interpretation.
#[test]
fn finite_table_cert_grants_mixed_int_real_tables() {
    let verdict = solve_one(
        r#"
        (set-logic AUFLIRA)
        (declare-fun f (Int) Int)
        (declare-fun g (Int) Real)
        (assert (forall ((x Int)) (>= (f x) 0)))
        (assert (forall ((y Int)) (>= (g y) 0.0)))
        (assert (= (f 3) 5))
        (assert (= (g 2) 2.5))
        (check-sat)
    "#,
    );
    assert_eq!(verdict, "sat");
}

/// Conflicting Real foralls with no ground point: `f >= 0.5` and `f <= 0.25`
/// everywhere — jointly unsatisfiable, no default vector may pass the joint
/// check.
#[test]
fn finite_table_cert_refuses_conflicting_real_foralls() {
    let verdict = solve_one(
        r#"
        (set-logic AUFLIRA)
        (declare-fun f (Int) Real)
        (assert (forall ((x Int)) (>= (f x) 0.5)))
        (assert (forall ((y Int)) (<= (f y) 0.25)))
        (check-sat)
    "#,
    );
    assert_ne!(
        verdict, "sat",
        "jointly unsatisfiable Real foralls certified"
    );
}

/// get-model after a Real-codomain certificate grant: the printed table must
/// honour the pinned point (no phantom-row error, #real-codomain model
/// output).
#[test]
fn finite_table_cert_real_codomain_get_model() {
    let output = solve_one(
        r#"
        (set-logic AUFLIRA)
        (declare-fun f (Int) Real)
        (assert (forall ((x Int)) (>= (f x) 0.0)))
        (assert (= (f 3) 5.0))
        (check-sat)
        (get-model)
    "#,
    );
    assert!(
        output.contains("define-fun f"),
        "get-model must print an interpretation for f, got: {output}"
    );
    assert!(
        !output.contains("error"),
        "get-model must not error after a certified sat, got: {output}"
    );
}

// ---------------------------------------------------------------------------
// CCMC M1: curried ground-prefix finite-table certificate.
//
// The certified body shape widens from the bare unary `f(x)` to
// `f(g1..gn, x)` where the TRAILING argument is the bare binder and every
// prefix arg `gi` is binder-free and Int/Real-valued. Tables are keyed by
// (evaluated-prefix-value-vector, point) so coincident prefixes share one row.
// ---------------------------------------------------------------------------

/// GRANT (probe `m1_curried_grant.smt2`): `forall x. f(a, x) >= 0` with a
/// ground Int prefix `a`, pinned `f(a, 3) = 5`, and an off-prefix `f(7, 4) =
/// -2`. Model-satisfiable (choose `a != 7`); certified by the row
/// `([a], 3) -> 5` + default 0. Was `unknown(quantifier-ematching-exists)`
/// before M1 — the curried scan admits the shape and the Phase-2.5 trigger now
/// consults the certificate for that reason.
#[test]
fn finite_table_cert_grants_curried_ground_prefix() {
    let verdict = solve_one(
        r#"
        (set-logic UFLIA)
        (declare-fun f (Int Int) Int)
        (declare-const a Int)
        (assert (forall ((x Int)) (! (>= (f a x) 0) :pattern ((f a x)))))
        (assert (= (f a 3) 5))
        (assert (= (f 7 4) (- 0 2)))
        (check-sat)
    "#,
    );
    // #quantified-model-gate: satisfiable, but the emitted table's `else`
    // row (`-2`, from the `f(7,4)` pin) FALSIFIES `∀x. f(a,x) ≥ 0` at every
    // off-table point; the gate fail-closes to `unknown` rather than print a
    // falsifying witness.
    assert!(
        verdict == "sat" || verdict == "unknown",
        "expected sat (with a valid model) or fail-closed unknown, got {verdict}"
    );
}

/// REFUSE (probe `m1_adv_binder_prefix_unsat.smt2`): the binder sits in a
/// PREFIX position (`f(x, 3)`), not trailing — outside the curried class, so
/// the scan rejects it via the x-under-argument guard. The problem
/// (`forall x. f(x, 3) >= 0` with `f(2, 3) = -1`) is UNSAT; the certificate
/// must NEVER grant `sat`.
#[test]
fn finite_table_cert_refuses_curried_binder_in_prefix() {
    let verdict = solve_one(
        r#"
        (set-logic UFLIA)
        (declare-fun f (Int Int) Int)
        (assert (forall ((x Int)) (! (>= (f x 3) 0) :pattern ((f x 3)))))
        (assert (= (f 2 3) (- 0 1)))
        (check-sat)
    "#,
    );
    assert_ne!(
        verdict, "sat",
        "binder in prefix position wrongly certified"
    );
}

/// REFUSE (probe `m1_adv_shifted_unsat.smt2`): a SHIFTED trailing argument
/// (`f(a, x+1)`) is not the bare binder — outside the curried class. The
/// problem (`forall x. f(a, x+1) >= 0` with `f(a, 0) = -1`) is UNSAT (the
/// forall's image at `x = -1` is `f(a, 0)`); the certificate must NEVER grant.
#[test]
fn finite_table_cert_refuses_curried_shifted_trailing_arg() {
    let verdict = solve_one(
        r#"
        (set-logic UFLIA)
        (declare-fun f (Int Int) Int)
        (declare-const a Int)
        (assert (forall ((x Int)) (! (>= (f a (+ x 1)) 0) :pattern ((f a (+ x 1))))))
        (assert (= (f a 0) (- 0 1)))
        (check-sat)
    "#,
    );
    assert_ne!(
        verdict, "sat",
        "shifted curried trailing arg wrongly certified"
    );
}

/// REFUSE (probe `m1_adv_prefix_eq_unsat.smt2`): the soundness core of
/// VALUE-keying. `a = b`, `forall x. f(a, x) >= 0`, and `f(b, 3) = -1`. Under
/// value-keying the prefixes `[a]` and `[b]` collapse to the SAME row, so
/// `f(b, 3) = -1` becomes a ROW CONFLICT with the forall at point 3 (`-1 >= 0`
/// is false) — never a fresh table that passes vacuously. The problem is
/// UNSAT; the certificate must NEVER grant.
#[test]
fn finite_table_cert_refuses_curried_equal_prefix_row_conflict() {
    let verdict = solve_one(
        r#"
        (set-logic UFLIA)
        (declare-fun f (Int Int) Int)
        (declare-const a Int)
        (declare-const b Int)
        (assert (= a b))
        (assert (forall ((x Int)) (! (>= (f a x) 0) :pattern ((f a x)))))
        (assert (= (f b 3) (- 0 1)))
        (check-sat)
    "#,
    );
    assert_ne!(
        verdict, "sat",
        "coincident-prefix row conflict wrongly certified as separate tables"
    );
}

/// SOUNDNESS PIN for the new `QuantifierEmatchingExistsIncomplete` Phase-2.5
/// trigger: a snapshot whose top level contains an `exists` must be rejected by
/// the certificate partition (it is grant-only and fail-closed on any exists /
/// nested quantifier). Here `forall x. f(x) >= 0` alone would grant, but the
/// `exists y. f(y) < 0` makes the problem UNSAT — the certificate must NEVER
/// turn this into `sat` (whether ay decides it unsat directly or leaves it
/// unknown, `sat` would be a false-accept).
#[test]
fn finite_table_cert_refuses_exists_in_snapshot() {
    let verdict = solve_one(
        r#"
        (set-logic UFLIA)
        (declare-fun f (Int) Int)
        (assert (forall ((x Int)) (>= (f x) 0)))
        (assert (= (f 3) 5))
        (assert (exists ((y Int)) (< (f y) 0)))
        (check-sat)
    "#,
    );
    assert_ne!(
        verdict, "sat",
        "exists-bearing UNSAT snapshot wrongly certified"
    );
}
