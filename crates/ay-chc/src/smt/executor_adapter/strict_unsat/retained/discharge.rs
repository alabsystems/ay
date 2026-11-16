// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::super::{parse_plain_query, phase_probe, solver_config, Phase, Solver};
use super::{BoundRetainedProof, RetainedReplayProgress};
use ay_core::time::Instant;
use std::panic::AssertUnwindSafe;

/// Mint bound authority only from the live solver's exact source capability.
/// No raw snapshot, offline recheck or legacy-v3 fallback enters this path.
pub(crate) fn check_plain_unsat_retained_native_with_progress(
    smt: &str,
    progress: &mut RetainedReplayProgress<'_>,
) -> Result<BoundRetainedProof, String> {
    progress.check()?;
    let proposed =
        ay_core::catch_ay_panics(AssertUnwindSafe(|| discharge(smt, progress)), |reason| {
            Err(format!("retained native discharge panicked: {reason}"))
        });
    // The native solver, parsed body, exact binding and third-check report
    // have all dropped inside discharge BEFORE terminal publication polling.
    let certificate = match proposed {
        Ok(certificate) => certificate,
        Err(reason) => return Err(progress.refuse(&reason)),
    };
    if let Err(error) = progress.check() {
        drop(certificate);
        let _ = progress.check();
        return Err(error);
    }
    Ok(certificate)
}

fn discharge(
    smt: &str,
    progress: &mut RetainedReplayProgress<'_>,
) -> Result<BoundRetainedProof, String> {
    // Declared first, so every solver, binding and replay owner below drops
    // before it on any exit; the returned proof owner carries it onward.
    let settlement = progress.settlement()?;
    let limit = progress.limit();
    let query = progress.copied_query(smt)?;
    if !progress.charge(smt.len(), smt.len()) {
        return Err(progress.refuse("retained borrowed source admission refusal"));
    }
    let plain = phase_probe::result(Phase::ParseShape, limit, || {
        progress.check()?;
        let plain = parse_plain_query(smt, limit)
            .ok_or_else(|| "retained obligation is not a plain hard query".to_string())?;
        progress.check()?;
        Ok::<_, String>(plain)
    })?;
    // The opaque parser's allocations are not term-store allocations. Admit
    // its retained body copy when the authenticated logic split needs one.
    if let std::borrow::Cow::Owned(body) = &plain.body {
        if !progress.charge(body.len(), body.capacity()) {
            return Err(progress.refuse("retained split query allocation refusal"));
        }
    }
    let config = solver_config();
    let memory = progress.memory();
    let mut solver = phase_probe::result(Phase::Setup, limit, || {
        progress.check()?;
        let solver = Solver::try_new_with_config(plain.logic, config)
            .map_err(|error| format!("retained solver setup failed: {error}"))?;
        progress.check()?;
        Ok::<_, String>(solver)
    })?;
    solver.set_produce_proofs(true);
    let binding = phase_probe::result(Phase::ParseBound, limit, || {
        progress.check()?;
        let binding = solver
            .parse_smtlib2_with_exact_query_binding(&plain.body)
            .map_err(|error| format!("retained exact query parse failed: {error}"))?;
        progress.check()?;
        Ok::<_, String>(binding)
    })?;
    let deadline = progress.deadline();
    // This is only the ALREADY remaining original wall, never a new solve
    // budget. The interrupt callback retains the unchanged absolute ceiling.
    let remaining = deadline
        .checked_duration_since(Instant::now())
        .filter(|remaining| !remaining.is_zero())
        .ok_or_else(|| progress.refuse("retained original solve deadline expired"))?;
    solver.set_timeout(Some(remaining));
    let cancellation = limit.cancellation().cloned();
    let unsat = phase_probe::result(Phase::Solve, limit, || {
        progress.check()?;
        let unsat = solver
            .check_sat_interruptible(move || {
                cancellation
                    .as_ref()
                    .is_some_and(super::super::ReplayCancellation::is_cancelled)
                    || Instant::now() >= deadline
                    || memory.check().is_none()
            })
            .is_unsat();
        progress.check()?;
        if !unsat {
            return Err("retained obligation did not establish UNSAT".to_string());
        }
        Ok::<_, String>(())
    });
    unsat?;
    let bundle = exact_export(&solver, &binding, deadline, progress)?;
    #[cfg(test)]
    let census_third = progress.census_stage("walk-3-independent-replay");
    let strict_verdict = verified_third_replay(&bundle, progress)?;
    #[cfg(test)]
    drop(census_third);
    Ok(BoundRetainedProof {
        query,
        bundle,
        request: progress.request()?,
        strict_verdict,
        settlement,
    })
}

fn exact_export(
    solver: &Solver,
    binding: &ay_dpll::api::ExactSmtlibQueryBinding,
    deadline: Instant,
    progress: &mut RetainedReplayProgress<'_>,
) -> Result<super::RetainedProofBundle, String> {
    #[cfg(test)]
    let _census_export = super::fee_census::begin_export(solver);
    phase_probe::result(Phase::ExactExport, progress.limit(), || {
        progress.check()?;
        let artifact = solver
            .export_last_unsat_retained_bundle_for_exact_query_with_resource_control(
                binding,
                deadline,
                &mut |work, bytes| progress.charge(work, bytes),
            )
            .map_err(|error| format!("retained live exact export failed: {error}"))?
            .ok_or_else(|| {
                "retained live exact source authority is missing or stale".to_string()
            })?;
        progress.check()?;
        Ok::<_, String>(artifact)
    })
}

fn verified_third_replay(
    bundle: &super::RetainedProofBundle,
    progress: &mut RetainedReplayProgress<'_>,
) -> Result<ay_dpll::api::StrictProofVerdict, String> {
    let checked = phase_probe::result(Phase::Recheck, progress.limit(), || {
        progress.check()?;
        let checked = bundle
            .replay_exact_with_resource_control(progress.deadline(), &mut |work, bytes| {
                progress.charge(work, bytes)
            })
            .map_err(|error| format!("retained mandatory third replay failed: {error}"))?;
        progress.check()?;
        Ok::<_, String>(checked)
    })?;
    let used = progress.ordered_unique(&checked.assume_terms)?;
    if bundle.schema() != ay_dpll::api::RETAINED_PROOF_BUNDLE_SCHEMA
        || !checked.quality.is_complete()
        || used.is_empty()
        || !progress.equal_ids(&used, bundle.obligation_assertions())
    {
        return Err(progress.refuse("retained third replay lacks complete exact source inventory"));
    }
    Ok(ay_dpll::api::StrictProofVerdict::Verified(checked.quality))
}

#[cfg(test)]
mod tests;
