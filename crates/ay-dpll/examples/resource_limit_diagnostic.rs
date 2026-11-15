//! Native public-API regression: deterministic work is not process memory.
//! Run as an ordinary consumer; this does not require AY libtest.
use ay_dpll::api::{Logic, NativeReplayMetadata, Solver};
use ay_dpll::{LimitKind, SolveDetails, UnknownReason};
use std::error::Error;
use std::time::Duration;

fn solver() -> Result<Solver, Box<dyn Error>> {
    let mut solver = Solver::try_new(Logic::QfUf)?;
    solver.set_produce_proofs(true);
    solver.set_produce_unsat_cores(true);
    solver.set_timeout(Some(Duration::from_secs(120)));
    solver.set_quantifier_deadline_backstop(false);
    Ok(solver)
}

fn require_limit(
    solver: &Solver,
    details: &SolveDetails,
    reason: UnknownReason,
    kind: LimitKind,
    code: &str,
) -> Result<(), Box<dyn Error>> {
    let actual = details.resource_usage.limit_hit.map(|kind| kind.code());
    println!(
        "result={} reason={:?} limit={actual:?} diagnostic={:?}",
        details.result, details.unknown_reason, details.unknown_diagnostic
    );
    if !details.result.is_unknown()
        || details.unknown_reason != Some(reason)
        || details.resource_usage.limit_hit != Some(kind)
        || actual != Some(code)
    {
        return Err(format!("expected Unknown/{reason:?}/{code}").into());
    }
    if solver.last_proof().is_some() || solver.model_for_consumer().is_some() {
        return Err("Unknown retained a proof or consumable model".into());
    }
    let replay =
        solver.export_native_replay_artifact(NativeReplayMetadata::default(), Some(details));
    let replay_limit = replay
        .solve
        .as_ref()
        .and_then(|solve| solve.resources.limit_hit.as_deref());
    let replay_text = match reason {
        UnknownReason::ResourceLimit => "ResourceLimit",
        UnknownReason::MemoryLimit => "MemoryLimit",
        UnknownReason::Timeout => "Timeout",
        UnknownReason::Interrupted => "Interrupted",
        _ => return Err("unexpected control reason".into()),
    };
    if replay_limit != Some(replay_text) {
        return Err("native replay lost the typed limit classification".into());
    }
    let summary = details.decision_profile_summary();
    if summary
        .unknown
        .as_ref()
        .and_then(|unknown| unknown.limit_code.as_deref())
        != Some(code)
    {
        return Err("decision profile lost the typed limit code".into());
    }
    if reason == UnknownReason::ResourceLimit {
        let diagnostic = details
            .unknown_diagnostic
            .as_ref()
            .ok_or("missing resource diagnostic")?;
        if diagnostic.phase.as_deref() != Some("resource-control")
            || diagnostic.cost_center.as_deref() != Some("deterministic-budget")
        {
            return Err("resource refusal has the wrong phase or cost center".into());
        }
    }
    Ok(())
}

fn main() -> Result<(), Box<dyn Error>> {
    let input = include_str!("fixtures/resource_limit_sat.smt2");
    let control = input.replace("(set-option :rlimit 1)", "");
    let mut sat = solver()?;
    sat.parse_smtlib2(&control)?;
    let details = sat.check_sat_with_details();
    if !details.accept_for_consumer()?.is_sat() || !details.result.was_model_validated() {
        return Err("SAT control failed native model validation".into());
    }
    println!("explicit-rlimit-removed: model-validated SAT");

    let mut bounded = solver()?;
    bounded.parse_smtlib2(input)?;
    let details = bounded.check_sat_with_details();
    require_limit(
        &bounded,
        &details,
        UnknownReason::ResourceLimit,
        LimitKind::ResourceLimit,
        "resource_limit",
    )?;

    bounded.parse_smtlib2("(assert false)")?;
    let recovered = bounded.check_sat_with_details();
    if !recovered.accept_for_consumer()?.is_unsat()
        || !recovered.result.was_unsat_strictly_verified()
        || bounded.last_proof().is_none()
        || recovered.unknown_reason.is_some()
        || recovered.resource_usage.limit_hit.is_some()
    {
        return Err("later strict UNSAT retained refusal state or lost its proof".into());
    }
    println!("same-solver after refusal: strict UNSAT with retained proof");

    // Another route may solve within its conflict allowance. Do not demand
    // identical search behavior; any resource refusal must be classified.
    let mut assuming = solver()?;
    assuming.parse_smtlib2(input)?;
    let details = assuming.check_sat_assuming_with_details(&[]).solve;
    if details.unknown_reason == Some(UnknownReason::ResourceLimit) {
        require_limit(
            &assuming,
            &details,
            UnknownReason::ResourceLimit,
            LimitKind::ResourceLimit,
            "resource_limit",
        )?;
    } else if !details.accept_for_consumer()?.is_sat() || !details.result.was_model_validated() {
        return Err("assuming control was neither validated SAT nor a resource refusal".into());
    }

    let mut timed = solver()?;
    timed.parse_smtlib2("(set-logic QF_UF)(declare-const p Bool)(assert p)")?;
    timed.set_timeout(Some(Duration::ZERO));
    let details = timed.check_sat_with_details();
    require_limit(
        &timed,
        &details,
        UnknownReason::Timeout,
        LimitKind::Timeout,
        "timeout",
    )?;

    let mut interrupted = solver()?;
    interrupted.parse_smtlib2("(set-logic QF_UF)(declare-const p Bool)(assert p)")?;
    interrupted.interrupt();
    let details = interrupted.check_sat_with_details();
    require_limit(
        &interrupted,
        &details,
        UnknownReason::Interrupted,
        LimitKind::Interrupted,
        "interrupted",
    )?;

    #[cfg(any(target_os = "macos", target_os = "linux"))]
    {
        let mut memory = solver()?;
        memory.parse_smtlib2("(set-logic QF_UF)(declare-const p Bool)(assert p)")?;
        memory.set_memory_limit(Some(1));
        let details = memory.check_sat_with_details();
        require_limit(
            &memory,
            &details,
            UnknownReason::MemoryLimit,
            LimitKind::MemoryLimit,
            "memory_limit",
        )?;
    }
    Ok(())
}
