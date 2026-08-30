// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Exact-query-bound native UNSAT certificates for checked replay.

use super::split_leading_set_logic;
use ay_dpll::api::{Logic, Solver, SolverConfig};
use std::borrow::Cow;
use std::panic::AssertUnwindSafe;
use std::time::Duration;

/// An independently rechecked native UNSAT proof bundle for one CHC replay
/// obligation, plus optional Alethe diagnostic text.
///
/// No external process is invoked. The serialized bundle is authoritative only
/// after a fresh complete `re_check_bundle_strict` pass and exact rebinding to
/// the hard assertions parsed for this call. Alethe is optional presentation.
pub(crate) struct StrictUnsatCert {
    pub bundle: ay_dpll::api::SerializableProofBundle,
    pub alethe: Option<String>,
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
fn parse_plain_query(smt: &str) -> Option<PlainQuery<'_>> {
    let original = ay_frontend::parse(smt).ok()?;
    let leading_logic = matches!(original.first(), Some(ay_frontend::Command::SetLogic(_)));
    if original.iter().enumerate().any(|(index, command)| {
        matches!(command, ay_frontend::Command::SetLogic(_)) && (!leading_logic || index != 0)
    }) {
        tracing::debug!(
            "executor_adapter: strict-unsat-cert has a non-leading or repeated set-logic"
        );
        return None;
    }

    let (logic, body) = if leading_logic {
        split_leading_set_logic(smt, Logic::All)
    } else {
        (Logic::All, Cow::Borrowed(smt))
    };
    let commands = ay_frontend::parse(&body).ok()?;
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
    Some(PlainQuery { logic, body })
}

fn solver_config(timeout: Option<Duration>) -> SolverConfig {
    match timeout {
        Some(timeout) if !timeout.is_zero() => SolverConfig::default().with_timeout(timeout),
        _ => SolverConfig::default(),
    }
}

pub(super) fn ordered_unique_assumes(terms: &[ay_core::TermId]) -> Vec<ay_core::TermId> {
    let mut unique = Vec::new();
    for term in terms {
        if !unique.contains(term) {
            unique.push(*term);
        }
    }
    unique
}

fn solve_plain_unsat(query: PlainQuery<'_>, config: SolverConfig) -> Option<StrictUnsatCert> {
    let mut solver = Solver::try_new_with_config(query.logic, config).ok()?;
    solver.set_produce_proofs(true);
    solver.try_set_option(":check-proofs-strict", "true").ok()?;
    let exact_query = solver
        .parse_smtlib2_with_exact_query_binding(&query.body)
        .ok()?;
    if !solver.check_sat().is_unsat() {
        tracing::debug!("executor_adapter: strict-unsat-cert obligation was not unsat");
        return None;
    }

    let bundle = solver.export_last_unsat_bundle_for_exact_query(&exact_query)?;
    let checked = ay_dpll::api::re_check_bundle_strict(&bundle).ok()?;
    let used_assumes = ordered_unique_assumes(&checked.assume_terms);
    if !checked.quality.is_complete()
        || used_assumes.is_empty()
        || used_assumes != bundle.obligation_assertions
    {
        tracing::debug!("executor_adapter: exact-query bundle failed the consumer strict recheck");
        return None;
    }

    let quality = checked.quality;
    let alethe = ay_core::catch_ay_panics(
        AssertUnwindSafe(|| solver.export_last_proof_alethe()),
        |reason| {
            tracing::debug!("executor_adapter: optional Alethe diagnostic declined: {reason}");
            None
        },
    );
    Some(StrictUnsatCert {
        bundle,
        alethe,
        strict_verdict: ay_dpll::api::StrictProofVerdict::Verified(quality),
    })
}

/// Discharge one canonical plain UNSAT replay obligation with AY's native
/// proof producer and independent strict bundle checker.
///
/// Any parse/shape error, panic, non-UNSAT result, missing proof, incomplete
/// quality, or exact-query authority mismatch returns `None` and must be
/// treated by callers as metadata-only. Repeated proof `Assume` steps are
/// compared after ordered deduplication because the exported authority
/// inventory is deliberately unique in first-use order.
pub(crate) fn smtlib_strict_unsat_cert_via_executor(
    smt: &str,
    timeout: Option<Duration>,
) -> Option<StrictUnsatCert> {
    ay_core::catch_ay_panics(
        AssertUnwindSafe(|| {
            let query = parse_plain_query(smt)?;
            solve_plain_unsat(query, solver_config(timeout))
        }),
        |reason| {
            tracing::debug!("executor_adapter: strict-unsat-cert ay panic: {reason}");
            None
        },
    )
}
