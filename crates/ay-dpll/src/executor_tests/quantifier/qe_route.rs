// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! #qe-alternation-route — a quantified problem over `{LIA, LRA}` with no
//! uninterpreted function of arity >= 1 must reach quantifier elimination
//! BEFORE instantiation, on every rigor level.
//!
//! # What these tests pin, and why they are shaped this way
//!
//! The route is fail-closed: every refusal keeps the original quantified
//! assertion, which is byte-identical to the route never running. So a
//! verdict-level assertion CANNOT detect a dead route — the same trap that has
//! already killed thirteen pre-passes in this codebase (see
//! `prepass_reachability.rs`). The tests therefore assert on
//! `PrepassReachability`, a pair of counters the solver itself never reads:
//!
//! * `qe_route_applicable` — the recognizer accepted the problem.
//! * `qe_route_grounded` — QE actually ran and left the problem fully
//!   quantifier-free, so `has_quantified_assertions` was recomputed to false.
//!
//! Every assertion below is UNCONDITIONAL: no `if let`, no early return, no
//! "assert only when the counter is nonzero". Mutating
//! `Executor::adopt_qe_alternation_route` to `false` (a no-op route), or
//! `pure_arithmetic_quantified_problem` to `false` (a route that never
//! recognizes anything), must fail
//! `qe_route_grounds_alternating_lra_before_instantiation`. Deleting the
//! recognizer's guards instead must fail
//! `qe_route_declines_uninterpreted_functions` and
//! `qe_route_declines_nonlinear_arithmetic`, so the barrier cannot be
//! satisfied from either direction.

use super::*;

/// Genuine LRA alternation: one `forall` under two `exists`, linear atoms,
/// declared constants only. This is the `scholl-smt08/RND` shape that makes up
/// the SQ Arith division, reduced to a small input with the same routing.
///
/// Every binder is COUPLED to the others on purpose. `deep_qe` peels binders
/// innermost-out and recovers each bound variable by finding its node in the
/// already-rewritten matrix; a binder whose variable is eliminated away by an
/// inner peel becomes unrecoverable, and `find_bound_var → None` is refused
/// conservatively (it does not prove non-occurrence). A toy formula where the
/// outer `y1` drops out is therefore refused for a reason that has nothing to
/// do with this route — measured, not guessed.
///
/// z3 5.0.0 and cvc5 1.3.0 both answer `sat` for this formula.
const ALTERNATING_LRA: &str = r#"
    (set-logic LRA)
    (declare-fun x1 () Real)
    (assert (exists ((y1 Real)) (exists ((y2 Real))
        (and (forall ((y3 Real))
               (or (<= (+ (* 2 y3) y1) (+ y2 x1))
                   (>= (+ y3 (* 3 y2)) (+ (* 5 y1) 1))))
             (and (> (+ y1 y2) x1) (< (- y1 y2) (* 2 x1)))))))
    (check-sat)
"#;

/// The same shape over `Int`, so the route is pinned on Cooper as well as on
/// Loos-Weispfenning. A route wired only for `Real` would pass the LRA test
/// alone.
const ALTERNATING_LIA: &str = r#"
    (set-logic LIA)
    (declare-fun a () Int)
    (assert (forall ((x Int)) (exists ((y Int))
        (and (> y (+ x a)) (> y 5)))))
    (check-sat)
"#;

/// THE BARRIER. Alternating pure-arithmetic quantifiers must be recognized AND
/// fully eliminated before instantiation runs.
///
/// This is the test that fails when the route is mutated to a no-op. It does
/// not assert a verdict, deliberately: the route is a routing change, and
/// whether the resulting ground residue can be PUBLISHED is a separate question
/// owned by the mandatory certification gates (see the module docs on
/// `executor::qe_route` — the residue is a solving candidate, never authority).
/// Asserting a verdict here would make the barrier hostage to that unrelated
/// policy.
#[test]
fn qe_route_grounds_alternating_lra_before_instantiation() {
    let commands = parse(ALTERNATING_LRA).unwrap();
    let mut exec = Executor::new();
    exec.set_qe_alternation_route(true);
    let _ = exec.execute_all(&commands).unwrap();
    let seen = exec.prepass_reachability();

    assert!(
        seen.qe_route_applicable > 0,
        "an alternating LRA problem over declared constants is exactly the \
         decidable-by-QE class the recognizer exists for; it was not recognized"
    );
    assert!(
        seen.qe_route_grounded > 0,
        "the QE route recognized the problem but did not ground it — either \
         `adopt_qe_alternation_route` is a no-op, or the eliminators refused a \
         formula squarely inside their fragment (#qe-alternation-route)"
    );
}

/// The same barrier on the Cooper (`Int`) side.
#[test]
fn qe_route_grounds_alternating_lia_before_instantiation() {
    let commands = parse(ALTERNATING_LIA).unwrap();
    let mut exec = Executor::new();
    exec.set_qe_alternation_route(true);
    let _ = exec.execute_all(&commands).unwrap();
    let seen = exec.prepass_reachability();

    assert!(
        seen.qe_route_applicable > 0,
        "an alternating LIA problem over declared constants must be recognized"
    );
    assert!(
        seen.qe_route_grounded > 0,
        "Cooper must ground an alternating LIA problem inside its fragment"
    );
}

/// The route must run at the DEFAULT rigor, not only under `--rigor fast`.
///
/// This is the measured bug the route repairs. The pre-existing deep-QE lane
/// sits on the `Unknown` fallback inside `cegar_refine_solve`, and that whole
/// cascade is behind `if self.is_producing_proofs() { return }`. At the default
/// rigor AY emits an Alethe certificate, so `is_producing_proofs()` is TRUE and
/// the fallback — deep-QE retry AND the quantified-trace-arming retry with it —
/// is unreachable. Measured on `LRA/scholl-smt08/RND/RND_3_13.smt2`: with
/// `AY_QE_DIAG` instrumentation the default-rigor run emitted ZERO lane traces,
/// while `--rigor fast` entered the retry, eliminated every binder, and reduced
/// the whole assertion to the constant `true`.
///
/// The posture has to be established EXPLICITLY. An earlier revision of this
/// test used a bare `Executor::new()` and asserted `!is_producing_proofs()`,
/// directly contradicting the paragraph above — `is_producing_proofs()` is
/// `proof_output_requested || :produce-proofs` (`lifecycle.rs:990`), false for
/// a fresh executor. So it pinned the one posture where the deep-QE fallback
/// is still REACHABLE, i.e. the opposite of the claim in its own name. Asking
/// for proofs in the script is what puts the fallback out of reach and makes
/// this test discriminating.
///
/// The compiled-parked route is armed explicitly through its test seam (see
/// `qe_route_is_off_by_default` below). The two claims are separate on
/// purpose: this one is about WHERE the route runs, not about whether it is on.
#[test]
fn qe_route_runs_while_a_certificate_is_being_produced() {
    let commands = parse(&ALTERNATING_LRA.replace(
        "(set-logic LRA)",
        "(set-logic LRA)\n(set-option :produce-proofs true)",
    ))
    .unwrap();
    let mut exec = Executor::new();
    exec.set_qe_alternation_route(true);
    let _ = exec.execute_all(&commands).unwrap();

    assert!(
        exec.is_producing_proofs(),
        "the posture under test is the one where `cegar_refine_solve` returns \
         early, taking the deep-QE fallback with it; if this is false the test \
         is exercising the case where that fallback still works"
    );
    assert!(
        exec.prepass_reachability().qe_route_grounded > 0,
        "the route must fire on the ordinary default-rigor path; the deep-QE \
         `Unknown` fallback it supersedes is unreachable there because \
         `cegar_refine_solve` returns early while the mandatory certificate is \
         being produced"
    );
}

/// The route ships OFF, and a fresh `Executor` must not pay for it.
///
/// This is the honest state of the work, pinned so it cannot drift on by
/// accident. The route grounds real division files and its answers agree with
/// z3 and cvc5 on 15/15 constant-folding cases — but the mandatory independent
/// gate refuses the residue publication authority
/// (`quantified_gate_general_check`: "quantifier-free QE candidate lacks exact
/// equivalence authority"), so it moves ZERO published verdicts while costing
/// measured wall time: +11 s on `LRA/scholl-smt08/RND/RND_3_13.smt2`, which
/// fails closed in under a second without it.
///
/// Flip this test when — and only when — the eliminators can present a
/// checkable equivalence derivation, not a bounded differential screen.
#[test]
fn qe_route_is_off_by_default() {
    let commands = parse(ALTERNATING_LRA).unwrap();
    let mut exec = Executor::new();
    let _ = exec.execute_all(&commands).unwrap();

    assert!(
        !exec.qe_alternation_route_armed(),
        "the QE alternation route must remain compiled parked: it gains no \
         published verdict today (the independent gate refuses the residue) \
         and costs seconds, and a default-on pass that trades wall time for \
         nothing is a regression"
    );
    assert_eq!(
        exec.prepass_reachability().qe_route_applicable,
        0,
        "a disarmed route must not even run its recognizer"
    );
}

/// The recognizer must REFUSE an uninterpreted function of arity >= 1.
///
/// Neither Cooper nor Loos-Weispfenning can eliminate a binder occurring under
/// an uninterpreted application; instantiation owns that class. This is one
/// half of what stops the barrier above from being satisfied by deleting the
/// recognizer's guards.
#[test]
fn qe_route_declines_uninterpreted_functions() {
    let input = r#"
        (set-logic UFLIA)
        (declare-fun f (Int) Int)
        (assert (forall ((x Int)) (> (f x) x)))
        (assert (exists ((y Int)) (< (f y) 0)))
        (check-sat)
    "#;
    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    exec.set_qe_alternation_route(true);
    let _ = exec.execute_all(&commands).unwrap();

    assert_eq!(
        exec.prepass_reachability().qe_route_applicable,
        0,
        "a problem with an uninterpreted function of arity >= 1 is outside the \
         decidable-by-QE class and must not be routed away from instantiation"
    );
}

/// The recognizer must REFUSE nonlinear arithmetic.
///
/// NIA / NRA are NOT decidable by Cooper or Loos-Weispfenning — `x * y` with
/// two non-constant factors is out of both fragments. Declining cleanly (rather
/// than entering and burning the elimination budget to a refusal) is the
/// intended behaviour for the 353 NIA/NRA files of the SQ Arith selection, and
/// it is the other half of the barrier's two-sided guard.
#[test]
fn qe_route_declines_nonlinear_arithmetic() {
    let input = r#"
        (set-logic NRA)
        (declare-fun c () Real)
        (assert (forall ((x Real)) (exists ((y Real)) (> (* x y) c))))
        (check-sat)
    "#;
    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    exec.set_qe_alternation_route(true);
    let _ = exec.execute_all(&commands).unwrap();

    assert_eq!(
        exec.prepass_reachability().qe_route_applicable,
        0,
        "nonlinear multiplication is outside both eliminators' fragments; NIA \
         and NRA must decline the route rather than pay for it"
    );
}

/// A ground problem must not pay for the route at all.
///
/// `has_quantified_assertions` is genuine applicability, not a mode guard, so
/// the barrier must not be satisfiable by removing it.
#[test]
fn qe_route_is_not_applicable_to_a_ground_problem() {
    let input = r#"
        (set-logic LRA)
        (declare-const a Real)
        (assert (> a 5.0))
        (assert (< a 100.0))
        (check-sat)
    "#;
    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    exec.set_qe_alternation_route(true);
    let outputs = exec.execute_all(&commands).unwrap();
    assert_eq!(outputs, vec!["sat"]);

    assert_eq!(
        exec.prepass_reachability().qe_route_applicable,
        0,
        "a problem with no quantified assertion is not route-applicable"
    );
}

/// The route must never publish a verdict the certification gates would refuse.
///
/// A VALID universal sentence over `Real` is a case where QE gets the answer
/// (the residue folds to `true`) and the ordinary lanes may not. Whatever this
/// answers, it must not be `unsat`: the assertion is satisfiable, so an `unsat`
/// here is a wrong answer, not a slow one. Held as a directional guard rather
/// than an equality so the test keeps its meaning if the publication policy
/// ever grants the residue authority.
#[test]
fn qe_route_never_refutes_a_satisfiable_alternation() {
    let commands = parse(ALTERNATING_LRA).unwrap();
    let mut exec = Executor::new();
    exec.set_qe_alternation_route(true);
    let outputs = exec.execute_all(&commands).unwrap();

    assert!(
        outputs == vec!["sat"] || outputs == vec!["unknown"],
        "a satisfiable LRA alternation must never publish unsat through the QE \
         route (got {outputs:?}) — a wrong elimination is a WRONG ANSWER, not a \
         slow one"
    );
}

/// The dual directional guard, on the refutable side: an UNSATISFIABLE
/// pure-arithmetic quantified problem must never come back `sat`.
#[test]
fn qe_route_never_satisfies_an_unsatisfiable_alternation() {
    let input = r#"
        (set-logic LRA)
        (assert (forall ((x Real)) (exists ((y Real)) (and (> y x) (< y x)))))
        (check-sat)
    "#;
    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    exec.set_qe_alternation_route(true);
    let outputs = exec.execute_all(&commands).unwrap();

    assert!(
        outputs == vec!["unsat"] || outputs == vec!["unknown"],
        "`forall x. exists y. y > x and y < x` is unsatisfiable; the QE route \
         must never publish sat for it (got {outputs:?})"
    );
}
