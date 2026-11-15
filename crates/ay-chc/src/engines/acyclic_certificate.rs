// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! The empty-model acyclic certificate: its class, the BMC run that proves
//! it, and its validation. Validation never trusts that BMC alone: an engine
//! agreeing with itself validated a wrong SAFE (MODEL_CHECKER_CONSUMER state report §4-A1),
//! so an empty model is admitted only when `crate::empty_acyclic_safe_check`
//! also confirms it.

use super::*;
use crate::smt::replay_control::ScopedReplayControl;

pub(super) fn validate_empty_scalar_acyclic_bmc_certificate(
    problem: &ChcProblem,
    config: &PdrConfig,
) -> Option<ChcResult<bool>> {
    // INV-S2 (#horn-smt-session §7.2).
    let _verification_pin = crate::smt::lane::ScopedVerificationMode::install();
    let memory = crate::bmc::memory::Budget::capture(config.memory_budget, None);
    let _memory_scope = memory.install();
    if !memory.open() {
        return Some(Ok(false));
    }
    // `None` (not this certificate class) is unchanged: the caller falls
    // through to clause verification, which refuses an empty model.
    let start = ay_core::time::Instant::now();
    scalar_acyclic_certificate_class(problem)?;
    // Under an effort the certificate is closed (`BmcSolver::closed_under_effort`):
    // its BMC is, and so is the executor recheck before it (and its memo), whose
    // answer would come from a wall budget. Not validated: `unknown`.
    if BmcSolver::closed_under_effort() {
        return Some(Ok(false));
    }
    let budget = config.solve_timeout.unwrap_or(PDR_PROOF_VALIDATION_TIMEOUT);
    let Some(deadline) = start.checked_add(budget) else {
        return Some(Ok(false));
    };
    let control = ScopedReplayControl::install_until(deadline, config.cancellation_token.as_ref());
    if !control.open() {
        return Some(Ok(false));
    }
    // BMC alone is the engine agreeing with itself: that validated a wrong
    // SAFE when `BmcSolver::mk_rule_vars` shared head-only clause variables
    // (MODEL_CHECKER_CONSUMER state report §4-A1). Decide the claim WITHOUT the engine
    // first; after an adaptive solve this is a memo hit, because the finalize
    // gate already decided the same script.
    let remaining = control
        .deadline()
        .saturating_duration_since(ay_core::time::Instant::now());
    if !crate::empty_acyclic_safe_check::confirmed(problem, remaining, control.cancellation())
        || !control.open()
    {
        return Some(Ok(false));
    }
    // The exhaustive BMC stays a necessary condition, as before 2026-09-29
    // (after a solve, a hit on the solve lane's memo), inside what is left of
    // the same validation budget.
    let bmc_config = PdrConfig {
        solve_timeout: Some(
            control
                .deadline()
                .saturating_duration_since(ay_core::time::Instant::now()),
        ),
        cancellation_token: control.cancellation().cloned(),
        ..config.clone()
    };
    let (bmc_safe, _depth) = run_scalar_acyclic_bmc_certificate(problem, &bmc_config)?;
    Some(Ok(bmc_safe && control.open()))
}

/// The empty-model acyclic certificate class: `Some((problem, depth))`
/// when `problem`, modulo dead-end cycles (the returned problem), is a
/// multi-predicate acyclic DAG over scalar or finite-datatype sorts;
/// `depth` is its exhaustive unrolling bound. `None` otherwise.
fn scalar_acyclic_certificate_class(
    problem: &ChcProblem,
) -> Option<(std::borrow::Cow<'_, ChcProblem>, usize)> {
    // Dead-end-cycle parity (ay#8578): the SOLVE lane
    // (`AdaptivePortfolio::new`) strips provably-dead-end cycle predicates
    // (a self-loop with no path to any query) so an acyclic-modulo-dead-end
    // CHC routes to the fast bounded-BMC lane, and then ships an EMPTY
    // acyclic-BMC certificate for the now-acyclic DAG. The CLI discharges
    // that certificate against `solver.problem()` (already stripped), but an
    // out-of-crate re-validation caller (e.g. model-checker-consumer's native CHC path)
    // hands us the ORIGINAL, un-stripped problem, whose lone dead-end
    // self-loop makes `has_cycles()` true and would spuriously reject the
    // honest empty certificate below — demoting a genuinely-proved Safe to
    // UNKNOWN. Apply the SAME verdict-preserving strip here so validation
    // classifies and re-checks the identical acyclic-modulo-dead-end problem
    // the solve lane proved. `strip_dead_end_cycle_predicates` is a strict
    // no-op (byte-identical) for every problem outside that class, so this
    // only recovers the lost decision and cannot change any other verdict.
    let problem = if problem.has_cycles() {
        let mut p = problem.clone();
        p.strip_dead_end_cycle_predicates();
        std::borrow::Cow::Owned(p)
    } else {
        std::borrow::Cow::Borrowed(problem)
    };

    // Accept scalar acyclic DAGs over any combination of Bool/Int/BV — NOT just BV.
    // The production path emits these acyclic-BMC Safe certificates for pure Bool/Int
    // scalar DAGs (source_exact_bool_int_dag, adaptive_multi_pred.rs:397), but this
    // validator previously required BV (`!has_bv_sorts()` -> bail), so pure-LIA proofs
    // were emitted then rejected and the genuinely-proved Safe was demoted to unknown.
    // SOUND: the certificate is EXHAUSTIVE acyclic BMC (finalize_bounded_search
    // returns Safe only with no SMT-unknown AND every depth <= dag_depth.max(num_preds)
    // discharged UNSAT in the original theory) — complete for acyclic DAGs over scalar
    // theories AND over FINITE (non-recursive) datatypes. Arrays/reals stay excluded (not
    // complete under bounded unroll). Datatypes: admit NON-recursive ADTs (a struct of
    // bitvectors, `Option<bv64>`, an enum of scalar variants, `CoroutineState`, `Pin<bv64>`)
    // — their value space is finite, so bounded acyclic unrolling is complete for them.
    // RECURSIVE datatypes (unbounded value space) stay excluded: bounded unrolling is not
    // complete for them, so admitting their acyclic-BMC Safe would be a false proof.
    if problem.predicates().is_empty()
        || problem.has_array_sorts()
        || problem.has_real_sorts()
        || problem.has_recursive_datatype_sorts()
    {
        return None;
    }

    let features = ProblemClassifier::classify(&problem);
    if features.has_cycles || features.uses_arrays || features.num_predicates <= 1 {
        return None;
    }

    let depth = features.dag_depth.max(features.num_predicates).max(1);
    Some((problem, depth))
}

/// Run the exact acyclic BMC certificate for a scalar/acyclic/BV
/// multi-predicate problem.
///
/// Returns `None` when the problem is not eligible (has predicates, no
/// arrays, has BV sorts, no cycles, more than one predicate). When
/// eligible, returns `Some((is_safe, depth))` where `is_safe` is `true`
/// only if the exact acyclic path expansion discharged every
/// error-reachability branch as UNSAT in the original theory, and `depth`
/// is the exhaustive DAG depth used (admissible evidence metadata). A zero
/// budget yields `Some((false, depth))`.
pub(super) fn run_scalar_acyclic_bmc_certificate(
    problem: &ChcProblem,
    config: &PdrConfig,
) -> Option<(bool, usize)> {
    // INV-S2 (#horn-smt-session §7.2): the empty-model Safe certificate
    // re-proof (design F15) never routes to a `HornSmt` session.
    let _verification_pin = crate::smt::lane::ScopedVerificationMode::install();
    let memory = crate::bmc::memory::Budget::capture(config.memory_budget, None);
    let _memory_scope = memory.install();
    let started = ay_core::time::Instant::now();
    let (problem, depth) = scalar_acyclic_certificate_class(problem)?;
    let problem: &ChcProblem = &problem;
    let budget = config.solve_timeout.unwrap_or(PDR_PROOF_VALIDATION_TIMEOUT);
    let Some(deadline) = started.checked_add(budget) else {
        return Some((false, depth));
    };
    let control = ScopedReplayControl::install_until(deadline, config.cancellation_token.as_ref());
    if !control.open() || !memory.open() {
        return Some((false, depth));
    }
    // Under an effort the certificate is closed (`BmcSolver::closed_under_effort`),
    // before the process-wide memo below: a hit there would make the run's
    // answer and its ticks depend on what the process solved before it. The
    // proof run's prepass then falls through to the PDR search.
    if BmcSolver::closed_under_effort() {
        return Some((false, depth));
    }

    // Reuse the solve lane's already-computed acyclic-BMC safety proof
    // instead of recomputing the identical exhaustive BMC (the whole point
    // of this optimization; count_zero/loop_with_old: ~8.5 s proved twice →
    // once). This is reached ONLY after the eligibility, zero-budget, and
    // pre-cancellation gates above, so a hit can only ever stand in for the
    // `BmcSolver::solve()` run below — never bypass a gate. The memo records
    // `problem` (the same dead-end-stripped problem classified here) ONLY
    // immediately after complete acyclic BMC genuinely proved it safe.
    // The key is the full structural identity, and the cached bound must
    // cover the freshly recomputed exhaustive depth, so a hit is exactly
    // equivalent to re-running: it yields `Some((true, depth))`, the same
    // Safe verdict the re-run would establish. On any miss (the problem
    // was not proved this session, is not structurally identical, or was
    // proved only to a shallower bound) we fall through to the
    // correct-but-slower re-run. See `crate::acyclic_cert_cache`.
    if crate::acyclic_cert_cache::lookup_acyclic_bmc_safe(problem)
        .is_some_and(|cached_depth| cached_depth >= depth)
    {
        return Some((control.open(), depth));
    }

    let bmc_config = BmcConfig {
        smt_lane: crate::smt::SmtLane::Verification,
        base: ChcEngineConfig {
            verbose: config.verbose,
            cancellation_token: control.cancellation().cloned(),
        },
        max_depth: depth,
        acyclic_safe: true,
        prefer_exact_acyclic_first: true,
        per_depth_timeout: None,
        time_budget: Some(
            control
                .deadline()
                .saturating_duration_since(ay_core::time::Instant::now()),
        ),
        enable_k_induction: false,
        enable_adaptive_stepping: false,
        proof_cross_check: false,
        memory_budget: memory.term_limit(),
        ts_probe_clamp: None,
        soft_time_budget: None,
        probe_extension_deadline: None,
        resume_frontier: None,
        sweep_past_spurious_sat: true,
    };

    Some((
        run_bmc_attempts(bmc_config, &control, |config| {
            BmcSolver::new(problem.clone(), config).solve()
        }),
        depth,
    ))
}

// Both complete decision procedures consume ONE existing certificate wall.
// Definite Unsafe and any observed owner refusal never select another attempt.
fn run_bmc_attempts(
    bmc_config: BmcConfig,
    control: &ScopedReplayControl,
    mut solve: impl FnMut(BmcConfig) -> PortfolioResult,
) -> bool {
    if !control.open() {
        return false;
    }
    let result = solve(bmc_config.clone());
    if !control.open() {
        return false;
    }
    match result {
        PortfolioResult::Safe(_) => true,
        // A definite Unsafe is a hard reject — never fall back to another engine.
        PortfolioResult::Unsafe(_) => false,
        // The streaming exact-acyclic engine (prefer_exact_acyclic_first: true) fails
        // CLOSED to Unknown on a single per-branch SMT-unknown (e.g. intro1/intro2's
        // symbolic-LIA query expansion). Retry once with the EXHAUSTIVE engine
        // (prefer_exact_acyclic_first: false -> solve_acyclic_exhaustive_once), the same
        // complete decision procedure the production probe used to PROVE these Safe: it
        // builds the full level encoding as one combined check-sat. SOUND — still only
        // Safe on a full UNSAT unroll, and this arm is never reached on a definite Unsafe.
        PortfolioResult::Unknown | PortfolioResult::NotApplicable => {
            let exhaustive_config = BmcConfig {
                prefer_exact_acyclic_first: false,
                time_budget: Some(
                    control
                        .deadline()
                        .saturating_duration_since(ay_core::time::Instant::now()),
                ),
                ..bmc_config
            };
            if !control.open() {
                return false;
            }
            let exhaustive = solve(exhaustive_config);
            matches!(exhaustive, PortfolioResult::Safe(_)) && control.open()
        }
    }
}

#[cfg(test)]
mod control_tests;

#[cfg(test)]
mod tests {
    use super::*;

    /// Inside a proof run under an effort the certificate is closed (P4a slice
    /// 8) before the process-wide memo is read: a hit an earlier solve of the
    /// same problem recorded does not decide the run, and the validation of an
    /// empty model does not run its recheck either. Outside one the hit stands.
    #[test]
    fn the_certificate_is_closed_under_an_effort_before_its_memo() {
        let problem = ChcParser::parse(
            r#"(set-logic HORN)
(declare-fun P (Int) Bool)
(declare-fun Q (Int) Bool)
(assert (forall ((x Int)) (=> (= x 7) (P x))))
(assert (forall ((x Int) (y Int)) (=> (and (P x) (= y (+ x 1))) (Q y))))
(assert (forall ((y Int)) (=> (and (Q y) (< y 0)) false)))
(check-sat)
"#,
        )
        .expect("acyclic fixture parses");
        let (_, depth) = scalar_acyclic_certificate_class(&problem).expect("in the class");
        // The problem is safe (y = 8), so the memo records the truth.
        crate::acyclic_cert_cache::record_acyclic_bmc_safe(&problem, depth);
        let config = PdrConfig::default();
        let meter = crate::run_meter::RunMeter::open(Some(1 << 40), None);
        assert_eq!(
            run_scalar_acyclic_bmc_certificate(&problem, &config),
            Some((false, depth)),
            "no memo hit, no BMC: not proved"
        );
        assert!(matches!(
            validate_empty_scalar_acyclic_bmc_certificate(&problem, &config),
            Some(Ok(false))
        ));
        let work = meter.close().expect("the run is metered");
        assert_eq!(work.closed_route_checks, 2);
        assert_eq!(
            run_scalar_acyclic_bmc_certificate(&problem, &config),
            Some((true, depth)),
            "outside a run the memo hit stands"
        );
    }
}
