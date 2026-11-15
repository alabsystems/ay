// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The strict checker's bit-blast producer, swept (`crate::sat_sweep`) when
//! its monolithic refutation stops on a counted SEARCH or PROOF-SIZE cap.
//!
//! Measured 2026-09-29 on external-codegen's strict gate: the IDIV lowerings spelled
//! by `bvsdiv`'s definition, the `SMULL`, `BFM`, `UdotV` and `LDP` rows all
//! found a monolithic refutation too large to surface (`resolution hints`,
//! `resolution proof output bytes`), although each is an equivalence of two
//! circuits whose internal signals line up.
//!
//! Nothing here is trusted. The CNF's own typed bit lemmas give every gate's
//! function; the disequality clauses are the roots; the sweep returns a
//! candidate refutation, and the caller replays it against the same CNF under
//! the same validation limits (`ExprRefutation::validate`) before anything is
//! admitted. A sweep that does not close leaves the monolithic refusal as it
//! was.
//!
//! ## The envelope
//!
//! The sweep is a SECOND counted attempt inside the caller's envelope, never
//! an escape from it. It runs only when the caller opts in
//! (`BvExprProofLimits::sweep`) and after the monolithic attempt stopped on a
//! counted search or proof-size cap: a cancellation, a deadline, an input
//! limit or any other refusal ends the attempt as before. Its solver calls
//! together spend at most the envelope's `max_conflicts`, each charged what
//! it spent, and its candidates read at most [`SWEEP_WORK`] literals, a
//! ceiling that also counts the candidates propagation decides without a
//! conflict; it stops at the envelope's deadline and polls `keep_going`.
//!
//! A monolithic attempt that stopped on the CONFLICT cap itself leaves
//! nothing to sweep: the search the envelope pays for is spent. One that
//! stopped on a proof-size or decision cap is not charged against the sweep.
//! Its conflicts say how far the search got before its proof outgrew what can
//! surface, and that is the case the sweep exists for. 562aac51de charged
//! them (the sweep had the envelope minus the attempt's conflicts), and
//! external-codegen's strict gate lost a row it had verified:
//! `NEON UdotV.4S lanewise-intent == D-pair per-lane u8-dot-accumulate`
//! (corpus9 0644). Its monolithic attempt stops on the 4,000,000-hint cap
//! after 121,520 conflicts. Charged, the sweep had 78,480 conflicts and did
//! not close at any of the query's three asks, so the row answered `unknown
//! (incomplete self-check-rejected)`. Handed the whole 200,000, it closes in
//! 4.6 s, and the row verifies in 18.7 CPU-s (measured 2026-10-09 on ay
//! 43c531aead). The charge was made for `bv_circuit_source`'s coroutine row,
//! whose doomed sweep (after a 32 MiB proof-output stop at 61,838 conflicts)
//! ran 39.5 s fresh and 29.2 s charged. Since the offset-equality encoding
//! (DR-30) that row no longer reaches this sweep; it passes in 0.9 s either
//! way.
//!
//! Within one proof build, an exact-division attempt whose divider
//! obligation another spelling already swept to the end of the envelope
//! without closing does not sweep it again (`crate::exact_division_sweeps`):
//! the first sweep of each obligation has the whole envelope.
//!
//! The case split (`crate::sat_sweep::split`) goes first, under the same
//! envelope, and what it spends the sweep may not. It declines at once for a
//! root that leaves no guarded fact open; where one is open, a lemma that
//! holds case by case is what it closes. Measured 2026-09-30 on
//! proof_gate_strict row 1257 (`i64 → f64 → i64`, 29,064 variables): the
//! monolithic attempt stops on the 32 MiB proof output cap, and the sweep
//! alone spent the whole envelope without closing; split, the lemma is
//! admitted about 4 s after the monolithic attempt stops.
//!
//! ## Why only a clause over no array
//!
//! The one caller that opts in, the checker's lemma validation, does so only
//! for a clause that mentions no array. A checker newly able to admit a JOINT
//! array lemma (`closed_spelling_chain`'s `(= lo (concat #x0 #x4))` with its
//! two `select`s) let the head of the authored cascade install a repair that
//! prints a `hole` ahead of a later member's complete EUF proof (measured
//! 2026-09-29). Every row this sweep was built for is a pure bit-vector
//! circuit.

use super::cnf::BvExprCnf;
use super::{map_bounded_resolution_error, BvExprExportError, BvExprProofLimits};
use crate::bv_blast_export::{BitLemmaKind, ClauseProvenance};
use crate::sat_sweep::{literal, Gate, SweepLimits};
use ay_sat::{
    prove_unsat_resolution_dag_counted_work, Literal, ResolutionDag, ResolutionProofError,
    ResolutionProofLimits, ResolutionProofResource,
};

/// Conflicts one candidate lemma may spend inside the checker's envelope.
/// Most lemmas close by unit propagation and never reach the solver; one
/// that needs more than this is left unmerged rather than paid for. Measured
/// 2026-09-29 on the 64-bit `127 * x == (x << 7) - x`: at 1,000, the 155
/// lemmas left undecided spent 154,000 of the 200,000 conflicts and the close
/// ran out; at 100 the whole sweep and its close spent about 126,000.
const LEMMA_CONFLICTS: u64 = 100;

/// Literals the case split and the sweep together may read
/// (`crate::sat_sweep`'s `work.rs`): each candidate's local problem and its
/// unit propagation, which a candidate that propagation decides spends
/// instead of a conflict.
///
/// The count is deterministic and the same in every build profile. Measured
/// 2026-10-07 through `recognize_bv_bitblast` on reconstructions of
/// external-codegen's rows (no local BV-family or external-codegen corpus document reaches a
/// checker sweep that closes): the most an ADMITTED sweep read is 10.52G
/// literals, the 64-bit division guarded by `b = -1`, `udiv(|a|, |b|) =
/// |a|` (the IDIV shape of 6571be1b9; 99 s without debug assertions), then
/// 10.08G and 5.62G for its other spellings, 0.62G at 32 bits and 2.5-2.7M
/// for 64-bit products over commuted operands. The commuted SMULL sweeps
/// that cannot close read less, 0.29-0.57G, and already end on a count:
/// their conflicts, or their one pass over the gates. No cap ends them
/// sooner without refusing the division rows, which do more of the same
/// work.
///
/// 32G: after a split that spent nothing the sweep may read 3.0x the most an
/// admitted sweep read, and 1.5x after one that spent its whole half. It is
/// a host-independent CEILING, not a fast decline. At the fastest rate
/// measured, the admitted divisions' 106-115M literals a second without
/// debug assertions, 32G takes about as long as `PRODUCER_HANG_GUARD`, and
/// the SMULL sweeps, whose time goes to their solver calls, read 6-10M a
/// second in the test profile: on the measured host the clock still ends a
/// sweep that neither closes nor runs out of conflicts or candidates, as it
/// ended the one measured, the split of the commuted SMULL `bvult` row (a
/// true claim), at its half of the hang guard after 1.51G and three of its
/// four leaf core sweeps closed. A solver call is charged its conflicts
/// only: its propagations and its refutation's validation are not work here.
const SWEEP_WORK: u64 = 32_000_000_000;

/// The bounded producer's refutation of `cnf`: one monolithic CDCL attempt
/// under `limits` and, past a counted cap, the sweep (see "The envelope").
/// The optional count is the monolithic producer's existing independent DAG
/// validation, not search or construction. A swept candidate has unreported
/// local validation work, so it returns None, never fictitious zero credit.
/// The compatibility caller still performs its required final graph/DAG replay;
/// a metered retained caller must refuse that missing aggregate measurement.
pub(super) fn bounded_refutation(
    cnf: &BvExprCnf,
    sat_clauses: &[Vec<Literal>],
    limits: &BvExprProofLimits,
    keep_going: &mut dyn FnMut() -> bool,
) -> Result<(ResolutionDag, Option<u64>), BvExprExportError> {
    let resolution = &limits.resolution;
    let (monolithic, _conflicts) = prove_unsat_resolution_dag_counted_work(
        cnf.vars.len(),
        sat_clauses,
        resolution,
        keep_going,
    );
    match monolithic {
        Ok((dag, work)) => Ok((dag, Some(work))),
        Err(ResolutionProofError::Satisfiable) => Err(BvExprExportError::NoRefutation),
        Err(other) => limits
            .sweep
            .then(|| after_counted_cap(cnf, sat_clauses, &other, resolution, keep_going))
            .flatten()
            .map(|dag| (dag, None))
            .ok_or_else(|| map_bounded_resolution_error(other, resolution)),
    }
}

/// A swept refutation after the monolithic attempt stopped on `error`, or
/// `None` (see "The envelope" above). A stop on the conflict cap itself is
/// not listed: it spent every conflict the envelope had.
fn after_counted_cap(
    cnf: &BvExprCnf,
    sat_clauses: &[Vec<Literal>],
    error: &ResolutionProofError,
    limits: &ResolutionProofLimits,
    keep_going: &mut dyn FnMut() -> bool,
) -> Option<ResolutionDag> {
    use ResolutionProofResource as R;
    let ResolutionProofError::LimitExceeded { resource, .. } = error else {
        return None;
    };
    let counted = matches!(
        resource,
        R::Decisions
            | R::ProofOutputBytes
            | R::DerivedSteps
            | R::DerivedLiterals
            | R::Hints
            | R::PendingDeletions
            | R::CodecBytes
            | R::BackwardReconstructionBytes
    );
    if !counted || sat_clauses.len() != cnf.clauses.len() {
        return None;
    }
    let limits = SweepLimits {
        lemma_conflicts: LEMMA_CONFLICTS,
        total_conflicts: limits.max_conflicts?,
        total_work: SWEEP_WORK,
        deadline: limits.deadline?,
    };
    // An exact-division attempt whose divider obligation another spelling
    // already swept to the end of the envelope without closing, in this
    // proof build, does not sweep it again; the first sweep of each has the
    // whole envelope (`crate::exact_division_sweeps`).
    if crate::exact_division_sweeps::skips_sweep() {
        return None;
    }
    let (refutation, spent) = split_then_sweep(cnf, sat_clauses, limits, keep_going);
    if refutation.is_none()
        && crate::exact_division_sweeps::remembers_sweep()
        && spent.exhausts(&limits)
        && std::time::Instant::now() < limits.deadline
        && keep_going()
    {
        crate::exact_division_sweeps::sweep_failed();
    }
    refutation
}

/// What a split and the sweep after it spent together.
#[derive(Clone, Copy, Debug, Default)]
struct Spent {
    conflicts: u64,
    work: u64,
}

impl Spent {
    /// Whether this spent all the conflicts or all the work of `limits`.
    fn exhausts(self, limits: &SweepLimits) -> bool {
        self.conflicts >= limits.total_conflicts || self.work >= limits.total_work
    }
}

/// The case split first: it declines at once when the root leaves no guard
/// open, and where one is open it is the route that closes
/// (`crate::sat_sweep::split`). It may spend half of `limits`
/// ([`split_share`]), and whatever it spends, the sweep may not
/// ([`left_after`]). Also returns what both spent.
fn split_then_sweep(
    cnf: &BvExprCnf,
    sat_clauses: &[Vec<Literal>],
    limits: SweepLimits,
    keep_going: &mut dyn FnMut() -> bool,
) -> (Option<ResolutionDag>, Spent) {
    let Some(gates) = sweep_gates(cnf) else {
        return (None, Spent::default());
    };
    let split = crate::sat_sweep::split::refute(
        gates,
        sat_clauses,
        &disequality_roots(cnf),
        false,
        &[],
        &[],
        crate::sat_sweep::split::Leaves::All,
        split_share(limits, std::time::Instant::now()),
        keep_going,
    );
    let spent = Spent {
        conflicts: split.spent,
        work: split.worked,
    };
    if split.refutation.is_some() {
        return (split.refutation, spent);
    }
    let Some(left) = left_after(limits, &split) else {
        return (None, spent);
    };
    let (refutation, swept) = swept_refutation(cnf, sat_clauses, left, keep_going);
    let spent = Spent {
        conflicts: spent.conflicts.saturating_add(swept.conflicts),
        work: spent.work.saturating_add(swept.work),
    };
    (refutation, spent)
}

/// The split's share of `limits`: half its conflicts, its work and the time
/// it has left at `now` (row 1257's split spends 11,292 conflicts in 2.7 s).
fn split_share(limits: SweepLimits, now: std::time::Instant) -> SweepLimits {
    SweepLimits {
        total_conflicts: limits.total_conflicts / 2,
        total_work: limits.total_work / 2,
        deadline: now + limits.deadline.saturating_duration_since(now) / 2,
        ..limits
    }
}

/// What `limits` leaves the sweep after a split that spent `split`, or
/// `None` once its conflicts or its work are spent.
fn left_after(
    mut limits: SweepLimits,
    split: &crate::sat_sweep::split::Outcome,
) -> Option<SweepLimits> {
    limits.total_conflicts = limits.total_conflicts.saturating_sub(split.spent);
    limits.total_work = limits.total_work.saturating_sub(split.worked);
    (limits.total_conflicts > 0 && limits.total_work > 0).then_some(limits)
}

/// Each variable's gate, from the CNF's own typed bit lemmas.
fn sweep_gates(cnf: &BvExprCnf) -> Option<Vec<Gate>> {
    let count = cnf.vars.len();
    let mut gates: Vec<Gate> = (0..count).map(|_| Gate::Input).collect();
    for lemma in &cnf.bit_lemmas {
        let input = |index: usize| -> Option<Literal> {
            Some(literal(
                usize::try_from(*lemma.ins.get(index)?).ok()?,
                false,
            ))
        };
        let gate = match lemma.kind {
            BitLemmaKind::ConstTrue => Gate::Const(true),
            BitLemmaKind::ConstFalse => Gate::Const(false),
            BitLemmaKind::Not => Gate::Alias(input(0)?.negated()),
            BitLemmaKind::And2 => Gate::And(vec![input(0)?, input(1)?]),
            BitLemmaKind::Or2 => Gate::Or(vec![input(0)?, input(1)?]),
            BitLemmaKind::Xor2 => Gate::Xor(vec![input(0)?, input(1)?]),
            BitLemmaKind::Xor3 => Gate::Xor(vec![input(0)?, input(1)?, input(2)?]),
            BitLemmaKind::FullAdderCarry => Gate::Majority(input(0)?, input(1)?, input(2)?),
            BitLemmaKind::XnorEq => Gate::Iff(input(0)?, input(1)?),
        };
        *gates.get_mut(usize::try_from(lemma.out).ok()?)? = gate;
    }
    Some(gates)
}

/// The disequality clauses: the roots only a closing refutation may use.
fn disequality_roots(cnf: &BvExprCnf) -> Vec<usize> {
    cnf.clauses
        .iter()
        .enumerate()
        .filter(|(_, clause)| matches!(clause.provenance, ClauseProvenance::Disequality))
        .map(|(index, _)| index)
        .collect()
}

/// A swept refutation of `cnf` (its clauses as `sat_clauses`), or `None`,
/// and what the sweep spent.
fn swept_refutation(
    cnf: &BvExprCnf,
    sat_clauses: &[Vec<Literal>],
    limits: SweepLimits,
    keep_going: &mut dyn FnMut() -> bool,
) -> (Option<ResolutionDag>, Spent) {
    let roots = disequality_roots(cnf);
    let Some(gates) = sweep_gates(cnf) else {
        return (None, Spent::default());
    };
    let (refutation, spent) =
        crate::sat_sweep::refute_counted(gates, sat_clauses, &roots, false, limits, keep_going);
    let spent = Spent {
        conflicts: spent.conflicts,
        work: spent.work,
    };
    (refutation, spent)
}

#[cfg(test)]
#[path = "sweep_tests.rs"]
mod tests;
