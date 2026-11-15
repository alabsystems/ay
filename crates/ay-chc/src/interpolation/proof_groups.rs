// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Multi-group proof substrate: ONE proof-producing solve per query, many
//! interpolants (binary masks and path interpolants) from its proof.
//!
//! CHC-COMP 2026 Workstream D, Rung 1 (the development design notes
//! DESIGN_lra_interp_tpa.md` §4.1, interface contract **C-P1**).
//! **Owner: WP-D1-P** (proof substrate).
//!
//! Soundness covenant (INV-1..INV-6): interpolants are candidates, never
//! verdicts; extraction is fail-closed (`InterpolantMode::Explicit` in
//! ay-dpll: a Trust step, a missing premise, an unclassified literal or
//! pivot, an uncertified/undecodable theory leaf or an unrepresentable Real
//! constant is an [`ItpFail`], never a degraded `true`/`false`); locality
//! `vars(I) ⊆ shared` is a release check (in ay-dpll against the groups'
//! shared variables and here against the caller's `shared`); the Craig check
//! runs on the exact (A-groups, B-groups, shared) triple that was extracted,
//! on the Verification lane (`SmtContext::new()`).

use super::proof_script::{
    self, build_group_script, dpll_term_to_chc_expr, GroupScript, ProofLogic,
};
use super::stats::{self, EngineTag, ItpOutcome, Source};
use crate::interpolant_validation::is_unsat_result;
use crate::smt::dag_smtlib::DagCaps;
use crate::smt::{SmtContext, SmtResult};
use crate::{ChcExpr, ChcSort};
use ay_core::kani_compat::{DetHashMap as FxHashMap, DetHashSet as FxHashSet};
use ay_core::time::Instant;
use ay_dpll::api::{InterpolantFailure, InterpolantMode, InterpolantStrength, Solver, Term};
use std::panic::{catch_unwind, AssertUnwindSafe};
use std::sync::atomic::{AtomicUsize, Ordering};
use std::time::Duration;

/// Default caps of a proof-solve script: the old proof-path scan cap
/// (200 k), now counted in UNIQUE nodes, and a generous nesting depth.
pub(crate) const DEFAULT_DAG_CAPS: DagCaps = DagCaps {
    max_unique_nodes: 200_000,
    max_depth: 1_000_000,
};

/// Distinct ay-dpll nodes one interpolant may convert back to `ChcExpr`.
const MAX_CONVERT_NODES: usize = 200_000;

/// Reconstruction step budget of a proof-groups solve.
const PROOF_STEP_BUDGET: u64 = 50_000_000;

/// Ask the proof solve for its refutation.
///
/// QF_LRA solves also keep the solver's own refutation for Explicit
/// extraction (`set_interpolation_proofs`), with the lane's preprocessed
/// `assume` leaves attributed to the groups: the best-effort artifact proof
/// alone was poisoned or demoted on most of the LRA-Lin IMC corpus. QF_LIA
/// reads the best-effort artifact proof: its preprocessing records no leaf
/// sources, and the extractor relies on the authored-root derivations that
/// pipeline adds. Verdicts are those of best-effort production either way.
fn enable_proofs(solver: &mut Solver, logic: ProofLogic) {
    match logic {
        ProofLogic::QfLra => solver.set_interpolation_proofs(PROOF_STEP_BUDGET),
        ProofLogic::QfLia => solver.set_best_effort_produce_proofs(PROOF_STEP_BUDGET),
    }
}

/// A-side group selection: bit `g` set = group `g` is in A (≤ 128 groups;
/// k→1 at k = 64 needs 65).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub(crate) struct GroupMask(pub(crate) u128);

/// Interpolation recipe (resolution-level labelling). `Decomposed` arrives in
/// Rung 5.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub(crate) enum ItpRecipe {
    /// Pudlák (balanced; `InterpolantStrength::Default`).
    Pudlak,
    /// McMillan (strongest; `InterpolantStrength::Strongest`).
    McMillan,
    /// McMillan′ (weakest; `InterpolantStrength::Weakest`).
    McMillanPrime,
}

impl ItpRecipe {
    /// Stable board name.
    pub(crate) const fn name(self) -> &'static str {
        match self {
            Self::Pudlak => "pudlak",
            Self::McMillan => "mcmillan",
            Self::McMillanPrime => "mcmillan_prime",
        }
    }

    const fn strength(self) -> InterpolantStrength {
        match self {
            Self::Pudlak => InterpolantStrength::Default,
            Self::McMillan => InterpolantStrength::Strongest,
            Self::McMillanPrime => InterpolantStrength::Weakest,
        }
    }
}

/// Why the proof source did not produce a refutation.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum ItpUnknown {
    /// Outside QF_LIA+Bool / QF_LRA+Bool (or an Int+Real mix).
    Fragment,
    /// Over the DAG or constraint caps.
    Size,
    /// The time budget ran out.
    Budget,
    /// The proof solve returned `unknown`.
    SolverUnknown,
    /// The solver panicked (caught).
    Panic,
    /// The parsed script's assert count does not match the groups.
    ParseMismatch,
}

impl ItpUnknown {
    /// Stable board name.
    pub(crate) const fn name(self) -> &'static str {
        match self {
            Self::Fragment => "fragment",
            Self::Size => "size",
            Self::Budget => "budget",
            Self::SolverUnknown => "solver_unknown",
            Self::Panic => "panic",
            Self::ParseMismatch => "parse_mismatch",
        }
    }
}

/// Fail-closed extraction/validation failure (INV-4, INV-5, INV-6).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum ItpFail {
    TrustStep,
    UncertifiedLeaf,
    UndecodableLeaf,
    UnclassifiedLiteral,
    MissingPremise,
    NonLocal,
    CoefficientOverflow,
    Conversion,
    Budget,
    Panic,
    CraigInvalid,
    CraigUnknown,
    /// A reachable proof step the extractor has no rule for (subproof
    /// anchor, DRUP step, unrecoverable resolution chain, unsupported
    /// inference or certificate shape). Added by WP-D1-P with the extractor;
    /// the frozen variants above keep their meaning.
    UnsupportedStep,
}

impl ItpFail {
    /// Stable board name.
    pub(crate) const fn name(self) -> &'static str {
        match self {
            Self::TrustStep => "trust_step",
            Self::UncertifiedLeaf => "uncertified_leaf",
            Self::UndecodableLeaf => "undecodable_leaf",
            Self::UnclassifiedLiteral => "unclassified_literal",
            Self::MissingPremise => "missing_premise",
            Self::NonLocal => "non_local",
            Self::CoefficientOverflow => "coefficient_overflow",
            Self::Conversion => "conversion",
            Self::Budget => "budget",
            Self::Panic => "panic",
            Self::CraigInvalid => "craig_invalid",
            Self::CraigUnknown => "craig_unknown",
            Self::UnsupportedStep => "unsupported_step",
        }
    }

    /// Map an ay-dpll fail-closed extraction failure.
    fn from_extraction(failure: &InterpolantFailure) -> Self {
        match failure {
            InterpolantFailure::TrustStep { .. } => Self::TrustStep,
            InterpolantFailure::UncertifiedLeaf { .. } => Self::UncertifiedLeaf,
            InterpolantFailure::UndecodableLeaf { .. } => Self::UndecodableLeaf,
            InterpolantFailure::UnclassifiedLiteral { .. } => Self::UnclassifiedLiteral,
            // No proof at all is the limit case of a missing premise.
            InterpolantFailure::MissingPremise { .. } | InterpolantFailure::NoProof => {
                Self::MissingPremise
            }
            InterpolantFailure::UnsupportedStep { .. } => Self::UnsupportedStep,
            InterpolantFailure::NonLocal { .. } => Self::NonLocal,
            // Malformed groups/masks are a caller defect; fail closed.
            _ => Self::Conversion,
        }
    }
}

/// How served candidates are Craig-checked.
#[derive(Clone, Copy, Debug)]
#[cfg_attr(
    not(test),
    expect(
        dead_code,
        reason = "Full/Sampled are the WP-D1-E engine policies (Rung 1 / Rung 5b)"
    )
)]
pub(crate) enum ValidatePolicy {
    /// Every candidate (Rungs 1–3).
    Full,
    /// One in `n` (Rung 5b only, per recipe, after two clean full-track runs).
    Sampled(u32),
    /// The caller validates the consequence itself (e.g. `Hyp::Inductive`).
    OracleGuarded,
}

/// Verdict of one proof-producing solve over the groups.
pub(crate) enum ProofCheck {
    Sat,
    Unsat(ProofRefutation),
    Unknown(ItpUnknown),
}

/// A proof-carrying refutation of the groups' conjunction.
pub(crate) struct ProofRefutation {
    solver: Solver,
    group_terms: Vec<Vec<Term>>,
    groups: Vec<Vec<ChcExpr>>,
    var_sorts: FxHashMap<String, ChcSort>,
    deadline: Instant,
    trust_steps: usize,
    /// Candidates seen by `ValidatePolicy::Sampled`.
    sampled: u32,
}

/// Sequence number of `--chc-proof-itp-dump` group scripts.
static DUMP_SEQ: AtomicUsize = AtomicUsize::new(0);

fn stats_enabled() -> bool {
    ay_core::misc_cli_flags().chc_proof_itp_stats
}

/// Attribution side channel: `--chc-proof-itp-dump=<dir>` writes each proof
/// script (with its logic and a `; groups:` header) for offline replay
/// (`interpolation_replay --groups …`). Never affects the solve.
fn dump_script(script: &GroupScript) {
    let Some(dir) = ay_core::misc_cli_flags().chc_proof_itp_dump.as_deref() else {
        return;
    };
    if dir.is_empty() {
        return;
    }
    let n = DUMP_SEQ.fetch_add(1, Ordering::Relaxed);
    let sizes: Vec<String> = script.group_sizes.iter().map(ToString::to_string).collect();
    let path = std::path::Path::new(dir).join(format!(
        "proof_groups_{n}_{}_g{}.smt2",
        script.logic.name(),
        script.group_sizes.len()
    ));
    let text = format!(
        "; groups: {}\n(set-logic {})\n{}(check-sat)\n",
        sizes.join(","),
        script.logic.name(),
        script.text
    );
    let _ = std::fs::write(path, text);
}

/// The solve deadline: `now + budget`, clamped to the thread's SMT deadline.
/// A cancelled portfolio lane (`ScopedLaneCancellation`) has no time left.
fn solve_deadline(budget: Duration) -> Instant {
    if crate::smt::deadline::lane_cancelled() {
        return Instant::now();
    }
    let own = Instant::now() + budget;
    match crate::smt::deadline::effective_thread_deadline() {
        Some(thread) if thread < own => thread,
        _ => own,
    }
}

/// ONE proof-producing solve over the groups in order (`Solver::try_new(logic)`,
/// proof production, `:ay-proof-no-varsubst`,
/// `set_timeout(min(budget, thread deadline))`, `catch_unwind`).
pub(crate) fn proof_check_groups(
    groups: &[&[ChcExpr]],
    budget: Duration,
    caps: DagCaps,
) -> ProofCheck {
    let engine = stats::current_engine();
    if groups.len() < 2 || groups.len() > 128 {
        return ProofCheck::Unknown(ItpUnknown::Size);
    }
    let deadline = solve_deadline(budget);
    let script = match build_group_script(groups, caps) {
        Ok(script) => script,
        Err(unknown) => return ProofCheck::Unknown(unknown),
    };
    dump_script(&script);
    let remaining = deadline.saturating_duration_since(Instant::now());
    if remaining.is_zero() {
        return ProofCheck::Unknown(ItpUnknown::Budget);
    }
    let started = Instant::now();
    let outcome = catch_unwind(AssertUnwindSafe(|| run_proof_solve(&script, remaining)));
    let solve = started.elapsed();
    stats::record_proof_solve(solve, Duration::ZERO, script.dag);
    let check = match outcome {
        Ok(Ok((solver, group_terms, verdict))) => match verdict {
            Verdict::Unsat => {
                let trust_steps = solver.last_proof_trust_steps().unwrap_or(0);
                stats::record_trust_steps(engine, Source::ProofGroups, trust_steps);
                ProofCheck::Unsat(ProofRefutation {
                    solver,
                    group_terms,
                    groups: groups.iter().map(|g| g.to_vec()).collect(),
                    var_sorts: script.var_sorts.clone(),
                    deadline,
                    trust_steps,
                    sampled: 0,
                })
            }
            Verdict::Sat => {
                stats::record_request_on_sat_pair(engine.name());
                ProofCheck::Sat
            }
            Verdict::Unknown => ProofCheck::Unknown(if Instant::now() >= deadline {
                ItpUnknown::Budget
            } else {
                ItpUnknown::SolverUnknown
            }),
        },
        Ok(Err(unknown)) => ProofCheck::Unknown(unknown),
        Err(_) => ProofCheck::Unknown(ItpUnknown::Panic),
    };
    if stats_enabled() {
        let what = match &check {
            ProofCheck::Sat => "sat".to_string(),
            ProofCheck::Unsat(r) => format!("unsat trust_steps={}", r.trust_steps),
            ProofCheck::Unknown(u) => format!("unknown:{}", u.name()),
        };
        safe_eprintln!(
            "[PROOF-GROUPS] engine={} logic={} groups={} unique_nodes={} solve={:.3}s -> {what}",
            engine.name(),
            script.logic.name(),
            script.group_sizes.len(),
            script.dag.unique_nodes,
            solve.as_secs_f64()
        );
    }
    check
}

enum Verdict {
    Sat,
    Unsat,
    Unknown,
}

fn run_proof_solve(
    script: &GroupScript,
    remaining: Duration,
) -> Result<(Solver, Vec<Vec<Term>>, Verdict), ItpUnknown> {
    let mut solver =
        Solver::try_new(script.logic.dpll_logic()).map_err(|_| ItpUnknown::Fragment)?;
    // Proof mode is scoped to THIS solver instance / THIS query only.
    enable_proofs(&mut solver, script.logic);
    // Preprocessing variable substitution detaches proof leaves from the
    // original assertions (everything collapses to Trust steps).
    solver.set_option(":ay-proof-no-varsubst", "true");
    solver.set_timeout(Some(remaining));
    let asserts = solver
        .parse_smtlib2(&script.text)
        .map_err(|_| ItpUnknown::ParseMismatch)?;
    let total: usize = script.group_sizes.iter().sum();
    if asserts.len() != total {
        return Err(ItpUnknown::ParseMismatch);
    }
    let mut group_terms = Vec::with_capacity(script.group_sizes.len());
    let mut at = 0;
    for &n in &script.group_sizes {
        group_terms.push(asserts[at..at + n].to_vec());
        at += n;
    }
    let result = solver.check_sat_internal_query();
    let verdict = if result.is_unsat() {
        Verdict::Unsat
    } else if result.is_sat() {
        Verdict::Sat
    } else {
        Verdict::Unknown
    };
    Ok((solver, group_terms, verdict))
}

/// `ChcExpr` conjunction without the dedup hashing of `and_all` (a tree walk
/// on DAG-shaped groups).
fn conjoin(parts: Vec<ChcExpr>) -> ChcExpr {
    ChcExpr::and_vec(parts)
}

impl ProofRefutation {
    fn full_mask(&self) -> u128 {
        if self.groups.len() >= 128 {
            u128::MAX
        } else {
            (1u128 << self.groups.len()) - 1
        }
    }

    fn mask_is_proper(&self, a: GroupMask) -> bool {
        a.0 != 0 && a.0 & !self.full_mask() == 0 && a.0 != self.full_mask()
    }

    /// Fail-closed extraction of one interpolant per mask (one proof clone).
    fn extract(&mut self, masks: &[u128], r: ItpRecipe) -> Result<Vec<ChcExpr>, ItpFail> {
        if Instant::now() >= self.deadline || crate::smt::deadline::lane_cancelled() {
            return Err(ItpFail::Budget);
        }
        let solver = &mut self.solver;
        let group_slices: Vec<&[Term]> = self.group_terms.iter().map(Vec::as_slice).collect();
        let terms = catch_unwind(AssertUnwindSafe(|| {
            solver.get_interpolants_for_masks(
                &group_slices,
                masks,
                r.strength(),
                InterpolantMode::Explicit,
            )
        }))
        .map_err(|_| ItpFail::Panic)?;
        let terms = match terms {
            Ok(terms) => terms,
            Err(failure) => {
                if stats_enabled() {
                    let detail = failure
                        .step()
                        .and_then(|s| self.solver.describe_last_proof_step(s))
                        .unwrap_or_default();
                    safe_eprintln!(
                        "[PROOF-GROUPS] extract {}: {} {detail}",
                        r.name(),
                        failure.kind_name()
                    );
                }
                return Err(ItpFail::from_extraction(&failure));
            }
        };
        let mut out = Vec::with_capacity(terms.len());
        for t in terms {
            let mut budget = MAX_CONVERT_NODES;
            let solver = &self.solver;
            let sorts = &self.var_sorts;
            let converted = catch_unwind(AssertUnwindSafe(|| {
                dpll_term_to_chc_expr(solver, t, sorts, &mut budget)
            }))
            .map_err(|_| ItpFail::Panic)??;
            out.push(converted);
        }
        Ok(out)
    }

    fn check_locality(itp: &ChcExpr, shared: &FxHashSet<String>) -> Result<(), ItpFail> {
        if proof_script::dag_var_names(itp)
            .iter()
            .all(|v| shared.contains(v))
        {
            Ok(())
        } else {
            Err(ItpFail::NonLocal)
        }
    }

    /// Validate `itp` for mask `a` per `v`; returns the number of solves.
    fn validate(
        &mut self,
        a: GroupMask,
        itp: &ChcExpr,
        shared: &FxHashSet<String>,
        v: ValidatePolicy,
        r: ItpRecipe,
    ) -> Result<u32, ItpFail> {
        let check = match v {
            ValidatePolicy::Full => true,
            ValidatePolicy::Sampled(n) => {
                self.sampled = self.sampled.wrapping_add(1);
                n <= 1 || self.sampled % n == 1
            }
            ValidatePolicy::OracleGuarded => false,
        };
        if !check {
            return Ok(0);
        }
        match self.craig_valid(a, itp, shared) {
            Ok(()) => Ok(2),
            Err(fail) => {
                if fail == ItpFail::CraigInvalid {
                    stats::record_pre_validation_invalid(
                        stats::current_engine(),
                        Source::ProofGroups,
                        Some(r),
                    );
                }
                Err(fail)
            }
        }
    }

    /// A = groups in `a`; shared = caller-given set (must ⊇ vars(A) ∩ vars(B));
    /// explicit (fail-closed) mode.
    pub(crate) fn interpolant(
        &mut self,
        a: GroupMask,
        r: ItpRecipe,
        shared: &FxHashSet<String>,
        v: ValidatePolicy,
    ) -> Result<ChcExpr, ItpFail> {
        let engine = stats::current_engine();
        stats::record_request(engine, Source::ProofGroups, Some(r));
        let started = Instant::now();
        let result = self.interpolant_inner(a, r, shared, v);
        record(engine, r, &result, started.elapsed());
        result.map(|(itp, _)| itp)
    }

    fn interpolant_inner(
        &mut self,
        a: GroupMask,
        r: ItpRecipe,
        shared: &FxHashSet<String>,
        v: ValidatePolicy,
    ) -> Result<(ChcExpr, u32), ItpFail> {
        if !self.mask_is_proper(a) {
            return Err(ItpFail::Conversion);
        }
        let itp = self
            .extract(&[a.0], r)?
            .into_iter()
            .next()
            .ok_or(ItpFail::Conversion)?;
        Self::check_locality(&itp, shared)?;
        let solves = self.validate(a, &itp, shared, v, r)?;
        Ok((itp, solves))
    }

    /// Cut i = groups[0..=i]; Farkas leaf only (D-6); one proof clone for all
    /// cuts. `shared[i]` is the shared set of cut `i` (`groups.len() - 1`
    /// entries).
    pub(crate) fn path_interpolants(
        &mut self,
        r: ItpRecipe,
        shared: &[FxHashSet<String>],
        v: ValidatePolicy,
    ) -> Result<Vec<ChcExpr>, ItpFail> {
        let engine = stats::current_engine();
        stats::record_request(engine, Source::ProofGroups, Some(r));
        let started = Instant::now();
        let result = self.path_inner(r, shared, v);
        let outcome = match &result {
            Ok((_, solves)) => ItpOutcome::Served { solves: 1 + solves },
            Err(fail) => ItpOutcome::Failed(*fail),
        };
        stats::record_outcome(
            engine,
            Source::ProofGroups,
            Some(r),
            outcome,
            started.elapsed(),
        );
        result.map(|(itps, _)| itps)
    }

    fn path_inner(
        &mut self,
        r: ItpRecipe,
        shared: &[FxHashSet<String>],
        v: ValidatePolicy,
    ) -> Result<(Vec<ChcExpr>, u32), ItpFail> {
        let n = self.groups.len();
        if n < 2 || shared.len() != n - 1 {
            return Err(ItpFail::Conversion);
        }
        let masks: Vec<u128> = (1..n).map(|i| (1u128 << i) - 1).collect();
        let itps = self.extract(&masks, r)?;
        let mut solves = 0u32;
        for (i, itp) in itps.iter().enumerate() {
            Self::check_locality(itp, &shared[i])?;
            solves += self.validate(GroupMask(masks[i]), itp, &shared[i], v, r)?;
        }
        Ok((itps, solves))
    }

    /// Craig check on the exact triple extracted (A-groups, B-groups,
    /// shared), on `SmtContext::new()` (Verification lane): `A ∧ ¬I` and
    /// `I ∧ B` UNSAT, `vars(I) ⊆ shared`.
    pub(crate) fn craig_valid(
        &self,
        a: GroupMask,
        itp: &ChcExpr,
        shared: &FxHashSet<String>,
    ) -> Result<(), ItpFail> {
        if !self.mask_is_proper(a) {
            return Err(ItpFail::Conversion);
        }
        Self::check_locality(itp, shared)?;
        let mut a_parts = Vec::new();
        let mut b_parts = Vec::new();
        for (g, exprs) in self.groups.iter().enumerate() {
            if a.0 & (1u128 << g) != 0 {
                a_parts.extend(exprs.iter().cloned());
            } else {
                b_parts.extend(exprs.iter().cloned());
            }
        }
        a_parts.push(ChcExpr::not(itp.clone()));
        b_parts.push(itp.clone());
        for query in [conjoin(a_parts), conjoin(b_parts)] {
            let remaining = self.deadline.saturating_duration_since(Instant::now());
            if remaining.is_zero() {
                return Err(ItpFail::CraigUnknown);
            }
            let mut ctx = SmtContext::new();
            let result = ctx.check_sat_with_timeout(&query, remaining);
            if is_unsat_result(&result) {
                continue;
            }
            return Err(match result {
                SmtResult::Sat(_) => ItpFail::CraigInvalid,
                _ => ItpFail::CraigUnknown,
            });
        }
        Ok(())
    }

    /// Trust-rule steps in the refutation proof (reachable from its root).
    pub(crate) fn trust_steps(&self) -> usize {
        self.trust_steps
    }
}

fn record(
    engine: EngineTag,
    r: ItpRecipe,
    result: &Result<(ChcExpr, u32), ItpFail>,
    elapsed: Duration,
) {
    let outcome = match result {
        Ok((_, solves)) => ItpOutcome::Served { solves: 1 + solves },
        Err(fail) => ItpOutcome::Failed(*fail),
    };
    stats::record_outcome(engine, Source::ProofGroups, Some(r), outcome, elapsed);
}

#[allow(clippy::unwrap_used, clippy::panic)]
#[cfg(test)]
#[path = "proof_groups_tests.rs"]
mod tests;
