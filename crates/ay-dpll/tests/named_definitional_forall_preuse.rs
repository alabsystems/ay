// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::panic)]

//! Definitional-forall macro adoption of `:named` definitions and of
//! definitions asserted AFTER a use of their head (#defmacro-named-preuse).
//!
//! Both fixtures are queries deductive-checks raised through its embedder posture
//! (unsat cores ON, proofs OFF, a 30 s command deadline; every assertion
//! `:named`), captured verbatim from the solver's own assertion stack, and
//! both have a z3 verdict the pre-fix solver could not reach:
//!
//! * `C_witnessless_choose` (`77585-00004`): the spec function
//!   `f(i) = 5 <= i` is asserted as a `:named` definitional forall FIRST, and
//!   the obligation is `f(choose |i| f(i))` under the guarded choose axiom.
//!   z3: `unsat`. ay answered `unknown (quantifier-unhandled)` because the
//!   parsed-SMT macro finder refused the `:named` wrapper outright; with the
//!   definition adopted the problem is the inlined `77585-00005`, which was
//!   already `unsat` in 0.2 s.
//! * `C_proof_in_spec` (`85014-00027`): `out = successor(i)` is asserted
//!   BEFORE the `:named` definition `successor(x) = x + 1`. z3: `sat`. ay
//!   answered `unknown (quantifier-cegqi)` after 18 s because assert-time
//!   adoption must refuse a head already in use; the first `check-sat` now
//!   adopts and re-elaborates the earlier use, leaving ground LIA.
//!
//! The native API path (what deductive-checks actually drives) is covered separately
//! below: `try_assert_named` adopts exactly like `try_assert_term`, pins the
//! pre-built application, and the definition's core label survives.

use std::time::{Duration, Instant};

use ay_dpll::api::{Logic, SolveResult, Solver, Sort};
use ay_dpll::Executor;
use ay_frontend::{parse, Command};
use ntest::timeout;

const EMBEDDER_WALL: Duration = Duration::from_secs(30);

fn embedder_solver() -> Solver {
    let mut solver = Solver::try_new(Logic::All).expect("solver constructs");
    solver.set_produce_unsat_cores(true);
    solver.set_timeout(Some(EMBEDDER_WALL));
    solver
}

fn assert_inside_wall(name: &str, elapsed: Duration) {
    if !cfg!(debug_assertions) {
        assert!(
            elapsed < EMBEDDER_WALL,
            "{name}: verdict must arrive inside the command deadline, took {elapsed:?}"
        );
    }
}

/// `77585-00004` verbatim: the `:named` definition-first shape certifies
/// `unsat` on the named-core route, and the reported core names the
/// definition it depends on.
#[test]
#[timeout(300_000)]
fn witnessless_choose_named_definition_certifies_unsat() {
    let mut solver = embedder_solver();
    solver
        .parse_smtlib2(include_str!(
            "fixtures/deductive_checks_witnessless_choose_named_core.smt2"
        ))
        .expect("fixture parses");
    let started = Instant::now();
    let details = solver.check_sat_with_details();
    let elapsed = started.elapsed();
    let verdict = details
        .result
        .accept_for_consumer()
        .unwrap_or_else(|error| panic!("consumer acceptance failed: {error:?}"))
        .clone();
    assert!(
        matches!(verdict, SolveResult::Unsat(_)),
        "expected the certified unsat, got {verdict:?} (reason {:?}) after {elapsed:?}",
        details.unknown_reason
    );
    assert!(
        details.verification.unsat_proof_strictly_verified,
        "the published unsat must carry the strict certification: {:?}",
        details.verification
    );
    assert_inside_wall("witnessless_choose", elapsed);
    let core = solver.try_get_unsat_core().expect("core readable");
    assert!(
        core.iter().any(|name| name == "dn0"),
        "the core must name the adopted definition `dn0`: {core:?}"
    );
}

/// `85014-00027` verbatim through the command route (what the CLI runs): the
/// use-before-definition shape decides `sat` (ground LIA after expansion)
/// instead of failing closed through CEGQI, and the model carries the
/// adopted definition plus the entailed `out = 4`.
#[test]
#[timeout(300_000)]
fn proof_in_spec_pre_use_named_definition_decides_sat() {
    let (mut executor, outputs) = run_script(include_str!(
        "fixtures/deductive_checks_proof_in_spec_preuse_named_core.smt2"
    ));
    assert_eq!(outputs, vec!["sat"], "z3 agrees: sat");
    let model = executor
        .execute(&Command::GetModel)
        .expect("get-model executes")
        .expect("get-model prints");
    assert!(
        model.contains("(define-fun proof_in_spec_successor")
            && model.contains("(define-fun out () Int 4)"),
        "the model must carry the adopted definition and the entailed `out = 4`:\n{model}"
    );
}

fn run_script(script: &str) -> (Executor, Vec<String>) {
    let commands = parse(script).expect("script parses");
    let mut executor = Executor::new();
    let started = Instant::now();
    let outputs = executor.execute_all(&commands).expect("script executes");
    assert_inside_wall("script", started.elapsed());
    (executor, outputs)
}

/// Named SAT/UNSAT pair on the parsed-SMT path with the definition asserted
/// AFTER its use. The unsat twin's core must name the definition (`n1`): the
/// remaining members alone are satisfiable in the authored problem.
#[test]
#[timeout(120_000)]
fn order_swapped_named_definition_pair_decides_both_polarities() {
    let prelude = "(set-option :produce-unsat-cores true) \
         (set-logic ALL) \
         (declare-fun f (Int) Int) (declare-const i Int) (declare-const out Int) \
         (assert (! (= i 3) :named n0)) \
         (assert (! (= out (f i)) :named n2)) \
         (assert (! (forall ((x Int)) (= (f x) (+ x 1))) :named n1))";
    let (_, sat_outputs) = run_script(&format!(
        "{prelude} (assert (! (= out 4) :named n3)) (check-sat)"
    ));
    assert_eq!(sat_outputs, vec!["sat"], "out = f(3) = 4 is consistent");

    let (_, unsat_outputs) = run_script(&format!(
        "{prelude} (assert (! (not (= out 4)) :named n3)) (check-sat) (get-unsat-core)"
    ));
    assert_eq!(unsat_outputs.len(), 2, "{unsat_outputs:?}");
    assert_eq!(unsat_outputs[0], "unsat");
    let core = &unsat_outputs[1];
    assert!(
        core.contains("n1") && core.contains("n3"),
        "the core must carry the definition and the negated goal: {core}"
    );
}

/// The native API twin of the pre-use shape (deductive-checks drives this path):
/// the raw application is BUILT and asserted under a core name before the
/// `:named` definition arrives. `try_assert_named` must adopt exactly like
/// `try_assert_term` — pinning the pre-built application — so the goal is
/// decided in both polarities and the definition's label reaches the core.
fn native_pre_use(negate_goal: bool) -> (Solver, ay_dpll::api::VerifiedSolveResult) {
    let mut solver = embedder_solver();
    let succ = solver
        .try_declare_fun("succ", &[Sort::Int], Sort::Int)
        .expect("declare succ");
    let i = solver.try_declare_const("i", Sort::Int).expect("i");
    let out = solver.try_declare_const("out", Sort::Int).expect("out");
    let three = solver.int_const(3);
    let i_is_three = solver.eq(i, three);
    solver.try_assert_named(i_is_three, "i3").expect("assert i");
    let call = solver.try_apply(&succ, &[i]).expect("apply succ");
    let use_ = solver.eq(out, call);
    solver.try_assert_named(use_, "use").expect("assert use");

    let x = solver.try_fresh_var("x", Sort::Int).expect("x");
    let head = solver.try_apply(&succ, &[x]).expect("head");
    let one = solver.int_const(1);
    let rhs = solver.add(x, one);
    let body = solver.eq(head, rhs);
    let definition = solver.try_forall(&[x], body).expect("forall");
    solver
        .try_assert_named(definition, "def")
        .expect("assert definition");

    let four = solver.int_const(4);
    let goal = solver.eq(out, four);
    let goal = if negate_goal { solver.not(goal) } else { goal };
    solver.try_assert_named(goal, "goal").expect("assert goal");
    let details = solver.check_sat_with_details();
    assert!(
        details.unknown_reason.is_none(),
        "native pre-use shape must decide: {:?} / {:?}",
        details.result,
        details.unknown_reason
    );
    (solver, details.result)
}

#[test]
#[timeout(120_000)]
fn native_named_pre_use_definition_is_adopted_with_the_use_pinned() {
    let (solver, sat) = native_pre_use(false);
    assert!(
        sat.result().is_sat(),
        "succ(3) = 4 is consistent with the definition; got {sat:?}"
    );
    let model = solver.try_get_model_str().expect("model after sat");
    assert!(
        model.contains("(define-fun succ") && model.contains("(define-fun out () Int 4)"),
        "the adopted definition and the entailed `out = 4` must be in the model:\n{model}"
    );

    let (solver, unsat) = native_pre_use(true);
    assert!(
        unsat.result().is_unsat(),
        "`not (out = 4)` contradicts the pinned pre-built use; got {unsat:?}"
    );
    let core = solver.try_get_unsat_core().expect("core readable");
    assert!(
        core.iter().any(|name| name == "def"),
        "the core must name the adopted definition: {core:?}"
    );
    assert!(
        core.iter().any(|name| name == "goal"),
        "the core must name the negated goal: {core:?}"
    );
}
