// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The deep-QE `Unknown` retry in the DEFAULT CLI posture (the best-effort
//! Alethe sidecar), and the publication fences it depends on there.
//!
//! The retry used to stand down whenever `is_producing_proofs()` held, which
//! the synthesized best-effort sidecar makes true on every default-posture CLI
//! solve. It now stands down only when a checked certificate is DEMANDED
//! (`checked_certificate_demanded`). These tests pin both halves: the lane runs
//! under the sidecar, and what it can publish there is exactly what it can
//! publish with no proof policy at all.

use super::RetryAllowance;
use crate::executor::qe_prepass::FORCE_WRONG_ELIMINATION;
use crate::executor::Executor;
use crate::SolveResult;
use ay_frontend::parse;

/// The CLI's synthesized-default reconstruction budget is irrelevant to the
/// lane; any budget selects the same best-effort policy.
const BEST_EFFORT_BUDGET: u64 = 1_000_000;

/// `s > r`, `x >= r`, `x >= s`, `forall w. (r > w or s > w or w >= x)`.
/// The universal forces `x <= max(r, s)`, so `x = s` is a model. z3 5.0.0 and
/// cvc5 1.3.0 answer `sat`. The ordinary quantifier lanes leave it `unknown`
/// (CEGQI); the deep-QE retry grounds it and the authored-root SAT gate
/// confirms the model.
const T065_SAT: &str = r"
    (set-logic LRA)
    (declare-const r Real) (declare-const s Real) (declare-const x Real)
    (assert (> s r))
    (assert (and (forall ((w Real)) (or (or (> r w) (> s w)) (>= w x)))
                 (and (>= x r) (>= x s))))
    (check-sat)
";

/// The LOIS `incremental0` #34 shape: two "least upper bound" universals
/// pinning `k` and `l` to `max(a, b, c)`. `k = l = max(a, b, c)` is a model;
/// cvc5 1.3.0 answers `sat`. Unlike `T065_SAT`, whose single universal the
/// and-root SAT certificates decide on the first pass, the legacy first pass
/// answers `unknown` here and only the deep-QE retry decides it. The qlra lane
/// (#qlra-nested-cegqi) decides it on the first pass, so every test that needs
/// the retry to RUN, or to STAND DOWN on an `Unknown`, solves it through
/// `solve_without_qlra`.
const I0_034_SAT: &str = r"
    (set-logic LRA)
    (declare-const b Real) (declare-const a Real) (declare-const c Real)
    (declare-const k Real) (declare-const l Real)
    (assert (and (forall ((g Real)) (or (> b g) (> a g) (> c g) (>= g k)))
                 (and (>= k b) (>= k a) (>= k c))))
    (assert (and (forall ((g Real)) (or (> b g) (> a g) (> c g) (>= g l)))
                 (and (>= l b) (>= l a) (>= l c))))
    (check-sat)
";

/// The LOIS `incremental0` #36 shape: two "least upper bound" universals
/// pinning `k` and `l` to the same maximum, then `l != k`. z3 5.0.0 and cvc5
/// 1.3.0 answer `unsat`. The deep-QE residue is refutable, but no step connects
/// the authored `forall` roots to that residue, so the refutation cannot mint.
const I0_036_UNSAT: &str = r"
    (set-logic LRA)
    (declare-const b Real) (declare-const a Real) (declare-const c Real)
    (declare-const k Real) (declare-const l Real)
    (assert (and (forall ((g Real)) (or (> b g) (> a g) (> c g) (>= g k)))
                 (and (>= k b) (>= k a) (>= k c))))
    (assert (and (forall ((g Real)) (or (> b g) (> a g) (> c g) (>= g l)))
                 (and (>= l b) (>= l a) (>= l c))))
    (assert (not (= l k)))
    (check-sat)
";

#[derive(Clone, Copy, Debug)]
enum Posture {
    /// A bare executor: no proof policy (`--no-proof` / `--z3-mode` analogue).
    NoProof,
    /// `set_best_effort_produce_proofs`: the default CLI posture.
    BestEffortSidecar,
    /// An in-script `:produce-proofs true` demand (`--proof` analogue).
    ProofDemanded,
    /// `set_self_check(true)` with mandatory collection (`--rigor certified`).
    SelfCheck,
}

/// The QSAT route decides these fixtures and the retry stands down behind it
/// (`qsat_route_applied`), so the retry is exercised under `--no-qsat`.
fn solve(source: &str, posture: Posture) -> (Vec<String>, Executor) {
    let _no_qsat = ay_core::misc_test_override::set(ay_core::MiscCliFlags {
        no_qsat: true,
        ..ay_core::misc_cli_flags().clone()
    });
    let source = match posture {
        Posture::ProofDemanded => source.replacen(
            "(set-logic LRA)",
            "(set-logic LRA)\n(set-option :produce-proofs true)",
            1,
        ),
        _ => source.to_string(),
    };
    let commands = parse(&source).unwrap();
    let mut exec = Executor::new();
    match posture {
        Posture::NoProof | Posture::ProofDemanded => {}
        Posture::BestEffortSidecar => exec.set_best_effort_produce_proofs(BEST_EFFORT_BUDGET),
        Posture::SelfCheck => {
            exec.set_self_check(true);
            exec.set_mandatory_proof_collection();
        }
    }
    let outputs = exec.execute_all(&commands).unwrap();
    (outputs, exec)
}

/// `solve` with the qlra lane (#qlra-nested-cegqi) off: the lane decides
/// `I0_034_SAT` on the first pass (under `:produce-proofs` too), and these tests
/// pin the deep-QE retry boundary, which is reached only when the first pass
/// answers `unknown`.
fn solve_without_qlra(source: &str, posture: Posture) -> (Vec<String>, Executor) {
    let _no_qlra = ay_core::misc_test_override::set(ay_core::MiscCliFlags {
        no_qlra_cegqi: true,
        ..ay_core::misc_cli_flags().clone()
    });
    solve(source, posture)
}

/// Clears the wrong-elimination seam even when an assertion unwinds.
struct WrongElimination;

impl WrongElimination {
    fn arm() -> Self {
        FORCE_WRONG_ELIMINATION.with(|flag| flag.set(true));
        Self
    }
}

impl Drop for WrongElimination {
    fn drop(&mut self) {
        FORCE_WRONG_ELIMINATION.with(|flag| flag.set(false));
    }
}

/// THE REPAIR. In the default CLI posture the retry runs and the query that
/// `--no-proof` answers publishes `sat` too.
#[test]
fn deep_qe_retry_publishes_sat_under_the_best_effort_sidecar() {
    let (outputs, exec) = solve_without_qlra(I0_034_SAT, Posture::BestEffortSidecar);
    assert!(
        exec.is_producing_proofs() && !exec.checked_certificate_demanded(),
        "the posture under test is the best-effort sidecar: producing an \
         artifact, demanding none"
    );
    let seen = exec.prepass_reachability();
    assert!(
        seen.deep_qe_unknown_retries > 0 && seen.deep_qe_entered > 0,
        "the deep-QE `Unknown` retry must run under the best-effort sidecar; \
         it was gated off by `is_producing_proofs()` ({seen:?})"
    );
    assert_eq!(outputs, vec!["sat"], "z3 and cvc5 answer sat");
    // Same verdict, same lane, as with no proof policy at all.
    let (plain, plain_exec) = solve_without_qlra(I0_034_SAT, Posture::NoProof);
    assert_eq!(plain, vec!["sat"]);
    assert!(plain_exec.prepass_reachability().deep_qe_unknown_retries > 0);
}

/// A DEMANDED certificate keeps the exact quantified source: the retry stands
/// down under `:produce-proofs` and under self-check (`--rigor certified`).
#[test]
fn deep_qe_retry_stands_down_when_a_certificate_is_demanded() {
    for posture in [Posture::ProofDemanded, Posture::SelfCheck] {
        let (outputs, exec) = solve_without_qlra(I0_034_SAT, posture);
        assert!(exec.checked_certificate_demanded(), "{posture:?}");
        let seen = exec.prepass_reachability();
        assert!(
            seen.deep_qe_demand_stand_downs > 0,
            "{posture:?}: the first pass must answer `unknown` and reach the \
             retry boundary, or the stand-down below is vacuous ({seen:?})"
        );
        assert_eq!(
            (seen.deep_qe_unknown_retries, seen.deep_qe_entered),
            (0, 0),
            "{posture:?}: a demanded certificate must keep the authored \
             quantified source; the retry must not run"
        );
        assert_ne!(
            outputs,
            vec!["unsat"],
            "{posture:?}: z3 and cvc5 answer sat"
        );
    }
}

/// The lane's OWN guard, not the caller's. `cegar_refine_solve` returns before
/// the retry whenever a certificate is demanded, so the end-to-end test above
/// cannot tell whether the lane states the condition itself. Calling the lane
/// directly can: a demanded certificate must leave it untouched.
#[test]
fn deep_qe_retry_lane_guard_holds_without_the_cegar_early_return() {
    for posture in [Posture::ProofDemanded, Posture::SelfCheck] {
        let setup = T065_SAT.replace("(check-sat)", "");
        let (_, mut exec) = solve(&setup, posture);
        assert!(exec.checked_certificate_demanded(), "{posture:?}");
        let authored = exec.ctx.assertions.clone();
        let result = exec
            .deep_qe_unknown_retry(SolveResult::Unknown, &authored, RetryAllowance::UNBOUNDED)
            .unwrap();
        assert!(matches!(result, SolveResult::Unknown), "{posture:?}");
        let seen = exec.prepass_reachability();
        assert_eq!(
            (
                seen.deep_qe_unknown_retries,
                seen.deep_qe_demand_stand_downs
            ),
            (0, 1),
            "{posture:?}: the lane must stand down on a demanded certificate \
             even if the caller's early return moves, and say so itself"
        );
        assert_eq!(exec.ctx.assertions, authored, "{posture:?}");
    }
}

/// THE UNSAT FENCE, adversarially. The eliminator is forced to report the
/// maximally WRONG result — every quantified assertion becomes `false` — on a
/// SATISFIABLE problem, so the retry's residue is trivially refutable. Nothing
/// may publish that refutation: it has no authored `Assume` scope, so the
/// mandatory certificate cannot mint, in the new posture exactly as in the old.
#[test]
fn deep_qe_retry_wrong_elimination_never_publishes_unsat() {
    for posture in [Posture::NoProof, Posture::BestEffortSidecar] {
        let _seam = WrongElimination::arm();
        let (outputs, exec) = solve_without_qlra(I0_034_SAT, posture);
        let seen = exec.prepass_reachability();
        assert!(
            seen.deep_qe_unknown_retries > 0 && seen.deep_qe_entered > 0,
            "{posture:?}: the fence is only exercised if the retry adopts the \
             wrong residue ({seen:?})"
        );
        assert_eq!(
            outputs,
            vec!["unknown"],
            "{posture:?}: a refutation of a wrong QE residue must never publish \
             (the authored problem is satisfiable)"
        );
    }
}

/// A GENUINE retry refutation is still withheld under the sidecar: the
/// residue's `unsat` is correct here, but it carries no derivation from the
/// authored roots, so it publishes `unknown` exactly as with no proof policy.
/// Flip this only with a PRODUCER for the QE step, never by narrowing a gate.
#[test]
fn deep_qe_retry_unsat_is_downgraded_under_the_best_effort_sidecar() {
    for posture in [Posture::NoProof, Posture::BestEffortSidecar] {
        let (outputs, exec) = solve(I0_036_UNSAT, posture);
        let seen = exec.prepass_reachability();
        assert!(
            seen.deep_qe_unknown_retries > 0 && seen.deep_qe_entered > 0,
            "{posture:?}: the retry must run on this shape ({seen:?})"
        );
        assert_eq!(
            outputs,
            vec!["unknown"],
            "{posture:?}: an uncertified residue refutation must be downgraded"
        );
    }
}

/// A panic inside the retry's re-solve disarms the one-shot latch and restores
/// the authored assertions before it continues unwinding, so a later query on
/// the same executor still gets the lane.
#[test]
fn deep_qe_retry_disarms_and_restores_when_the_retry_panics() {
    let source = T065_SAT.replacen("(check-sat)", "", 1);
    let commands = parse(&source).unwrap();
    let mut exec = Executor::new();
    exec.execute_all(&commands).unwrap();
    let authored = exec.ctx.assertions.clone();
    exec.test_panic_in_deep_qe_retry = true;

    let unwound = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        exec.deep_qe_unknown_retry(SolveResult::Unknown, &authored, RetryAllowance::UNBOUNDED)
    }));

    assert!(
        unwound.is_err(),
        "the fixture must reach the retry and panic inside it"
    );
    assert_eq!(exec.prepass_reachability().deep_qe_unknown_retries, 1);
    assert!(
        !exec.deep_qe_retry_armed,
        "the one-shot latch must be disarmed on unwind"
    );
    assert_eq!(exec.ctx.assertions, authored);

    exec.test_panic_in_deep_qe_retry = false;
    let again =
        exec.deep_qe_unknown_retry(SolveResult::Unknown, &authored, RetryAllowance::UNBOUNDED);
    assert!(again.is_ok(), "{again:?}");
    assert_eq!(
        exec.prepass_reachability().deep_qe_unknown_retries,
        2,
        "the lane must run again on the same executor"
    );
    assert_eq!(exec.ctx.assertions, authored);
}

/// A declaration library and one fact, with `declaration` as its only
/// quantified assertion. No `check-sat`: the retry is entered directly.
fn loaded_with(declaration: &str) -> Executor {
    let source = format!(
        "(declare-fun tr (Int Int) Bool)
         (declare-const c Int)
         (assert (> c 0))
         {declaration}"
    );
    let commands = parse(&source).unwrap();
    let mut exec = Executor::new();
    exec.execute_all(&commands).unwrap();
    assert!(
        exec.ctx
            .assertions
            .iter()
            .any(|&a| crate::ematching::contains_quantifier(&exec.ctx.terms, a)),
        "the fixture must keep its quantified assertion"
    );
    exec
}

/// A quantifier whose body mentions none of its binders is collapsed by
/// `simplify_vacuous_quantifiers` before the in-solve pre-pass runs, in the
/// first pass as in the retry. The probe on the authored vector still counts
/// it as an elimination, so the retry runs; it solves the same problem again
/// and must be held to a re-solve's allowance.
#[test]
fn a_vacuous_declaration_makes_the_retry_a_re_solve_of_the_same_problem() {
    let mut exec = loaded_with("(assert (forall ((a Int) (b Int)) (! true :pattern ((tr a b)))))");
    let authored = exec.ctx.assertions.clone();

    let mut probe = authored.clone();
    assert!(
        crate::executor::qe_prepass::deep_qe(&mut exec.ctx.terms, &mut probe, None),
        "the authored probe counts the vacuous declaration as an elimination"
    );
    assert!(
        !exec.deep_qe_prepass_will_rewrite(&authored),
        "the in-solve pre-pass has nothing left to eliminate"
    );
    assert_eq!(
        exec.ctx.assertions, authored,
        "the question mints terms only"
    );
}

/// The twin: the same declaration with a body the eliminators rewrite
/// (`forall a b. a > c => a > 0` is `c >= 0`). The retry solves a different
/// problem and keeps its unbounded allowance.
#[test]
fn a_declaration_the_pre_pass_eliminates_makes_the_retry_a_different_problem() {
    let mut exec = loaded_with(
        "(assert (forall ((a Int) (b Int)) (! (=> (> a c) (> a 0)) :pattern ((tr a b)))))",
    );
    let authored = exec.ctx.assertions.clone();
    assert!(exec.deep_qe_prepass_will_rewrite(&authored));
    assert_eq!(exec.ctx.assertions, authored);
}
