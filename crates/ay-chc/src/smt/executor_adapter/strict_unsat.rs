// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Exact-query-bound native UNSAT certificates for checked replay.

use super::{
    replay_cancellation::ReplayCancellation, replay_limit::ReplayLimit,
    replay_memory::ReplayMemory, split_leading_set_logic,
};
use crate::proof_metadata::replay_check::phase_probe::{self, Phase};
use ay_core::time::Instant;
use ay_dpll::api::{Logic, Solver, SolverConfig};
use std::borrow::Cow;
use std::panic::AssertUnwindSafe;
#[cfg(test)]
use std::time::Duration;

mod resources;
use resources::ProofProgress;
mod retained;
pub(crate) use retained::{
    check_plain_unsat_retained_native_with_progress, BoundRetainedProofBytes,
    RetainedReplayProgress,
};

#[cfg(test)]
mod tests;

/// Independently rechecked native evidence exposed only to negative-control
/// tests. Production fresh rechecks consume the evidence and return no proof
/// object because they never publish it.
#[cfg(test)]
pub(crate) struct StrictUnsatCert {
    pub bundle: ay_dpll::api::SerializableProofBundle,
    pub strict_verdict: ay_dpll::api::StrictProofVerdict,
}

struct PlainQuery<'a> {
    logic: Logic,
    body: Cow<'a, str>,
}

fn is_plain_prefix(command: &ay_frontend::Command) -> bool {
    matches!(
        command,
        ay_frontend::Command::SetOption(..)
            | ay_frontend::Command::SetOptionAttribute(_)
            | ay_frontend::Command::SetInfo(..)
            | ay_frontend::Command::SetInfoAttribute(_)
            | ay_frontend::Command::DeclareSort(..)
            | ay_frontend::Command::DeclareSortParameter(_)
            | ay_frontend::Command::DefineSort(..)
            | ay_frontend::Command::DeclareDatatype(..)
            | ay_frontend::Command::DeclareDatatypes(..)
            | ay_frontend::Command::DeclareFun(..)
            | ay_frontend::Command::DeclareConst(..)
            | ay_frontend::Command::DefineFun(..)
            | ay_frontend::Command::DefineFunRec(..)
            | ay_frontend::Command::DefineFunsRec(..)
            | ay_frontend::Command::Assert(_)
    )
}

/// Authenticate the textual logic splitter and the one-shot plain-hard query
/// shape before granting the exact parse capability.
fn parse_plain_query<'s>(smt: &'s str, limit: ReplayLimit<'_>) -> Option<PlainQuery<'s>> {
    let original = limit.phase(|| ay_frontend::parse(smt).ok())?;
    if limit.deadline().is_some() && original.iter().any(is_timeout_override) {
        tracing::debug!("executor_adapter: strict bounded obligation contains a timeout override");
        return None;
    }
    let leading_logic = matches!(original.first(), Some(ay_frontend::Command::SetLogic(_)));
    if original.iter().enumerate().any(|(index, command)| {
        matches!(command, ay_frontend::Command::SetLogic(_)) && (!leading_logic || index != 0)
    }) {
        tracing::debug!(
            "executor_adapter: strict-unsat-cert has a non-leading or repeated set-logic"
        );
        return None;
    }

    let (logic, body) = limit.phase(|| {
        Some(if leading_logic {
            split_leading_set_logic(smt, Logic::All)
        } else {
            (Logic::All, Cow::Borrowed(smt))
        })
    })?;
    let commands = limit.phase(|| ay_frontend::parse(&body).ok())?;
    let checks: Vec<_> = commands
        .iter()
        .enumerate()
        .filter(|(_, command)| matches!(command, ay_frontend::Command::CheckSat))
        .map(|(index, _)| index)
        .collect();
    let plain = matches!(checks.as_slice(), [index]
        if commands[..*index].iter().all(is_plain_prefix)
            && matches!(&commands[*index + 1..], [] | [ay_frontend::Command::Exit]));
    if !plain {
        tracing::debug!(
            "executor_adapter: strict-unsat-cert obligation is not a canonical plain hard query"
        );
        return None;
    }
    limit.check()?;
    Some(PlainQuery { logic, body })
}

fn is_timeout_override(command: &ay_frontend::Command) -> bool {
    let keyword = match command {
        ay_frontend::Command::SetOption(keyword, _)
        | ay_frontend::Command::SetOptionAttribute(keyword) => keyword,
        _ => return false,
    };
    keyword.trim_start_matches(':') == "timeout"
}

fn solver_config() -> SolverConfig {
    let config = SolverConfig::default();
    match ReplayMemory::capture(None).term_limit() {
        Some(limit) => config.with_term_memory_limit(limit),
        None => config,
    }
}

#[cfg(test)]
pub(super) fn ordered_unique_assumes(terms: &[ay_core::TermId]) -> Vec<ay_core::TermId> {
    let mut unique = Vec::new();
    for term in terms {
        if !unique.contains(term) {
            unique.push(*term);
        }
    }
    unique
}

fn solve_plain_unsat<T>(
    query: PlainQuery<'_>,
    config: SolverConfig,
    limit: ReplayLimit<'_>,
    finish: impl FnOnce(ay_dpll::api::SerializableProofBundle, ay_dpll::api::StrictProofVerdict) -> T,
) -> Option<T> {
    let memory = ReplayMemory::capture(config.term_memory_limit);
    // #completed-check-accepted: the outer phases ADMIT the executor and never
    // poll after it returns. Every `Some` below is a certificate whose strict
    // recheck and exact binding completed; each phase before that (setup,
    // parse, solve, export) keeps its own exit guard, so an overrun BETWEEN
    // steps still refuses, but solver destruction after a finished check
    // cannot turn it into a refusal.
    phase_probe::option(Phase::Executor, limit, || {
        memory.admit(|| {
            limit.admit(|| {
                let cleanup = phase_probe::SolverCleanup::new(limit);
                let mut solver = phase_probe::option(Phase::Setup, limit, || {
                    limit.phase(|| Solver::try_new_with_config(query.logic, config).ok())
                })?;
                let _cleanup_start = cleanup.start_on_drop();
                memory.check()?;
                limit.phase(|| {
                    // Native bundle replay is mandatory below. Do not
                    // implicitly demand a hole-free wire proof; an explicit
                    // strict-wire option in the source remains intact.
                    solver.set_produce_proofs(true);
                    Some(())
                })?;
                let exact_query = phase_probe::option(Phase::ParseBound, limit, || {
                    limit.phase(|| {
                        solver
                            .parse_smtlib2_with_exact_query_binding(&query.body)
                            .ok()
                    })
                })?;
                memory.check()?;
                let unsat = phase_probe::option(Phase::Solve, limit, || {
                    limit.phase(|| {
                        Some(match limit.deadline() {
                            Some(deadline) => {
                                let cancellation = limit.cancellation().cloned();
                                solver
                                    .check_sat_interruptible(move || {
                                        cancellation
                                            .as_ref()
                                            .is_some_and(ReplayCancellation::is_cancelled)
                                            || Instant::now() >= deadline
                                            || memory.check().is_none()
                                    })
                                    .is_unsat()
                            }
                            None => solver.check_sat().is_unsat(),
                        })
                    })
                })?;
                memory.check()?;
                if !unsat {
                    tracing::debug!("executor_adapter: strict-unsat-cert obligation was not unsat");
                    return None;
                }
                let mut progress = ProofProgress::new(limit, memory);
                let bundle = phase_probe::option(Phase::ExactExport, limit, || {
                    limit.phase(|| {
                        solver
                            .export_last_unsat_bundle_for_exact_query_with_resource_control(
                                &exact_query,
                                &mut |w, b| progress.charge(w, b),
                            )
                            .ok()
                            .flatten()
                    })
                })?;
                checked_certificate_with(bundle, limit, &mut progress, finish)
            })
        })
    })
}

#[cfg(test)]
fn checked_certificate(
    bundle: ay_dpll::api::SerializableProofBundle,
    limit: ReplayLimit<'_>,
    progress: &mut ProofProgress<'_>,
) -> Option<StrictUnsatCert> {
    checked_certificate_with(bundle, limit, progress, |bundle, strict_verdict| {
        StrictUnsatCert {
            bundle,
            strict_verdict,
        }
    })
}

fn checked_certificate_with<T>(
    bundle: ay_dpll::api::SerializableProofBundle,
    limit: ReplayLimit<'_>,
    progress: &mut ProofProgress<'_>,
    finish: impl FnOnce(ay_dpll::api::SerializableProofBundle, ay_dpll::api::StrictProofVerdict) -> T,
) -> Option<T> {
    // #completed-check-accepted: the recheck is admitted at entry; its stop
    // polls happen between its steps (the callback below), never after its
    // last step, and nothing after the exact binding consults the limit.
    let checked = phase_probe::option(Phase::Recheck, limit, || {
        limit.admit(|| {
            ay_dpll::api::re_check_bundle_strict_with_resource_control(&bundle, &mut |w, b| {
                progress.charge(w, b)
            })
            .ok()
        })
    })?;
    let used_assumes = phase_probe::option(Phase::AssumeBinding, limit, || {
        limit.phase(|| progress.ordered_unique(&checked.assume_terms))
    })?;
    if !checked.quality.is_complete()
        || used_assumes.is_empty()
        || !progress.equal_ids(&used_assumes, &bundle.obligation_assertions)
    {
        tracing::debug!("executor_adapter: exact-query bundle failed the consumer strict recheck");
        return None;
    }
    Some(finish(
        bundle,
        ay_dpll::api::StrictProofVerdict::Verified(checked.quality),
    ))
}

fn run_strict_unsat<T>(
    smt: &str,
    limit: ReplayLimit<'_>,
    finish: impl FnOnce(ay_dpll::api::SerializableProofBundle, ay_dpll::api::StrictProofVerdict) -> T,
) -> Option<T> {
    let memory = ReplayMemory::capture(None);
    // #completed-check-accepted: entry admission only; see `solve_plain_unsat`.
    memory.admit(|| {
        limit.admit(|| {
            ay_core::catch_ay_panics(
                AssertUnwindSafe(|| {
                    let query = phase_probe::option(Phase::ParseShape, limit, || {
                        limit.phase(|| parse_plain_query(smt, limit))
                    })?;
                    let config = limit.phase(|| Some(solver_config()))?;
                    solve_plain_unsat(query, config, limit, finish)
                }),
                |reason| {
                    tracing::debug!("executor_adapter: strict-unsat-cert ay panic: {reason}");
                    None
                },
            )
        })
    })
}

/// Test-only access to the exact bundle retained by the production check.
#[cfg(test)]
pub(crate) fn smtlib_strict_unsat_cert_via_executor_until(
    smt: &str,
    deadline: Instant,
) -> Option<StrictUnsatCert> {
    smtlib_strict_unsat_cert_via_executor_with_limit(smt, ReplayLimit::Until(deadline))
}

#[cfg(test)]
pub(crate) fn smtlib_strict_unsat_cert_via_executor_with_limit(
    smt: &str,
    limit: ReplayLimit<'_>,
) -> Option<StrictUnsatCert> {
    run_strict_unsat(smt, limit, |bundle, strict_verdict| StrictUnsatCert {
        bundle,
        strict_verdict,
    })
}

/// Freshly solve and independently recheck one exact plain UNSAT query without
/// publishing or retaining its proof object.
pub(crate) fn check_plain_unsat_native_with_limit(smt: &str, limit: ReplayLimit<'_>) -> Option<()> {
    run_strict_unsat(smt, limit, |_, _| ())
}
