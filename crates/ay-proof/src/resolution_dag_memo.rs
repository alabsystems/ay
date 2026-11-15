// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! One refutation per CNF, instead of one refutation per ask.
//!
//! # The duplication this removes
//!
//! `checked_bv_bitblast_lowering_supported` answers a SUPPORT question — "can
//! the Alethe printer spell this bit-vector lemma?" — by BUILDING THE ANSWER
//! and throwing it away. It constructs a printer, bit-blasts the lemma, runs a
//! resolution-DAG SAT refutation, and then discards the document to return a
//! `bool`. The real export runs the identical dispatch again to keep the text.
//!
//! That is already two refutations of one lemma. The publication funnel then
//! multiplies it: `proof_has_known_wire_gap` asks the support question once per
//! `TheoryLemma` step, and one publication asks THAT about the same unchanged
//! document several times over — the cascade's entry guard, the strict-wire-gap
//! retry guard and its inter-repair re-asks, the post-fallback ask, and the
//! public policy entries in `unsat_cert`.
//!
//! Measured on a Trust termination obligation whose normalized CHC is minimal
//! (1 relation, 2 clauses, 3 atoms over QF_BV(64)), ~71% of the wall clock sat
//! in proof assembly for publication, AFTER the query had already been decided.
//! The loop-invariant shape in the same function cost 1.81 s; the termination
//! shape differs from it only by two 64-bit `bvsub` and cost 6.37 s. A bigger
//! circuit means a bigger per-lemma refutation fan, and the fan was paid in
//! full on every ask.
//!
//! # Why the fix belongs here and not at the screen
//!
//! An earlier repair memoized the SCREEN's whole-document verdict. It could
//! only ever be deny-only, because the screen is not clock-free: a wall-clock
//! deadline inside the circuit refutation can flip a step from supported to
//! unsupported, so replaying an ADMIT would let timing decide publication. A
//! deny-only memo buys exactly nothing on the path that matters — a document
//! with NO wire gap, which is the shape that publishes — and it charges the
//! admitting path a deep clone of both override maps per ask to build a key
//! that can never hit.
//!
//! The duplicated work is not the verdict. It is the refutation. Every
//! expensive arm of the printer's dispatch bottoms out in one of the two
//! `ay_sat` entry points below, over a CNF that is a pure function of the
//! lemma and the term store — the `ProofId` reaches the blaster only as a name
//! prefix and a step-name stem, never as circuit structure — so the support
//! call's `ProofId(0)` and the exporter's real id produce the SAME CNF.
//! Keying on that CNF collapses every repeat, in both directions, at once.
//!
//! # Why replaying a hit is sound
//!
//! * The key is the COMPLETE input. `num_vars`, every clause in order, every
//!   literal in it, and — for the bounded entry point — every resource bound
//!   except the wall-clock deadline. `LimitsKey::of` destructures its source
//!   struct exhaustively with no `..` rest pattern, so adding a limit field
//!   fails the build here instead of silently weakening the key.
//! * Only SUCCESS is stored, but for a counted envelope's refusal (`within`).
//!   A refusal caused by a deadline, a stop, any other bound or a satisfiable
//!   formula is never made sticky; the next ask re-derives it as before.
//!   Only the asking solve's screen keeps its declines (`bv_support_memo/within_solve.rs`).
//! * A stored value is a CERTIFICATE, not a verdict. A [`ResolutionDag`] is a
//!   pure-RUP refutation of the very CNF that keys it; the consumer prints it
//!   and Carcara re-checks the printed document. Replaying it asserts nothing
//!   that re-deriving it would not have asserted.
//! * Dropping the deadline from the key is the one deliberate inexactness, and
//!   it runs in the honest direction. A hit means this exact CNF under these
//!   exact bounds ALREADY produced this refutation. Serving it converts a
//!   timing-dependent decline into the answer the same input already gave, so
//!   it removes a clock-dependent flip rather than introducing one. It cannot
//!   manufacture a refutation for a formula that has none: nothing is stored
//!   unless the solver refuted it.
//!
//! The memo is therefore observationally transparent wherever the solver is
//! deterministic, and strictly more decisive — never less — where it is not.

use ay_core::kani_compat::DetHashMap;
use ay_sat::{
    prove_unsat_resolution_dag, prove_unsat_resolution_dag_until,
    prove_unsat_resolution_dag_with_limits_and_cancellation, Literal, ResolutionDag,
    ResolutionDagError, ResolutionProofError, ResolutionProofLimits,
};
use std::cell::RefCell;
use std::sync::OnceLock;

mod limits;
use limits::LimitsKey;

mod ordinary_controlled;
pub use ordinary_controlled::prove_unsat_resolution_dag_with_cancellation_memoized;

#[cfg(test)]
#[path = "resolution_dag_memo_tests.rs"]
mod tests;
mod within;
pub use within::{prove_unsat_resolution_dag_memoized_within, resolution_dag_refusals_served};

/// Entries retained before the table is dropped wholesale.
const MAX_ENTRIES: usize = 512;

/// Literals retained across keys and stored refutations before the table is
/// dropped wholesale. A refutation fan is the thing being cached, so the bound
/// that matters is literals, not entries.
///
/// Sized for headroom over a repeated lemma, not over a whole benchmark: a
/// literal is 4 bytes and each clause carries its own `Vec`, so this bounds the
/// table at roughly 100 MB against the 256 MB a single bounded refutation is
/// already allowed to retain.
///
/// Raised from 2,000,000 on 2026-09-30, measured: the swept 64-bit divider
/// lemmas of external-codegen's `SDIV`/`IDIV` definitional rows cost 3,890,035 and
/// 4,078,222 literals (CNF plus DAG), so none was retained, and each of the
/// eight renders one publication asks for re-ran its 15 to 30 s sweep: the
/// rows answered `unknown` at their 120 s budget.
const MAX_RETAINED_LITERALS: usize = 8_000_000;

#[derive(Clone, PartialEq, Eq, Hash)]
struct MemoKey {
    num_vars: usize,
    clauses: Vec<Vec<Literal>>,
    /// `None` is the ungated entry point; the two are never confused.
    limits: Option<LimitsKey>,
    /// The producer of an entry stored by [`resolution_dag_memoized_by`];
    /// `None` for the SAT entry points, so the two never share a key.
    strategy: Option<&'static str>,
}

/// A stored refutation. Its original clauses are, as every producer here
/// makes them, the key's clauses numbered from 1, so they are not kept twice:
/// a hit restores them from the key.
struct Stored {
    dag: ResolutionDag,
}

#[derive(Default)]
struct Memo {
    entries: DetHashMap<MemoKey, Stored>,
    retained_literals: usize,
    hits: u64,
    misses: u64,
}

thread_local! {
    static MEMO: RefCell<Memo> = RefCell::new(Memo::default());
}

/// `AY_RESOLUTION_DAG_MEMO=off` derives every refutation for real. This is the
/// control for measuring the memo, and the escape hatch if one is ever needed;
/// it also renders every support question (`alethe_printer/bv_support_memo.rs`)
/// and decides every strict producer input (`bv_blast_solver/compact/refusal_memo.rs`) for real.
pub(crate) fn memo_disabled() -> bool {
    static DISABLED: OnceLock<bool> = OnceLock::new();
    *DISABLED.get_or_init(|| {
        std::env::var("AY_RESOLUTION_DAG_MEMO")
            .map(|value| {
                let value = value.trim().to_ascii_lowercase();
                value == "off" || value == "0" || value == "false"
            })
            .unwrap_or(false)
    })
}

fn literal_count(clauses: &[Vec<Literal>]) -> usize {
    clauses.iter().map(Vec::len).sum()
}

fn dag_literal_count(dag: &ResolutionDag) -> usize {
    dag.original_clauses
        .iter()
        .map(|(_, clause)| clause.len())
        .sum::<usize>()
        + dag
            .derived
            .iter()
            .map(|step| step.clause.len() + step.rup_hints.len())
            .sum::<usize>()
}

fn lookup(key: &MemoKey) -> Option<ResolutionDag> {
    MEMO.with(|memo| {
        let mut memo = memo.borrow_mut();
        let hit = memo.entries.get(key).map(|stored| ResolutionDag {
            num_vars: stored.dag.num_vars,
            original_clauses: numbered(&key.clauses),
            derived: stored.dag.derived.clone(),
            empty_clause_id: stored.dag.empty_clause_id,
        });
        if hit.is_some() {
            memo.hits += 1;
        } else {
            memo.misses += 1;
        }
        hit
    })
}

/// `clauses` as a DAG's original clauses: numbered from 1, in order.
fn numbered(clauses: &[Vec<Literal>]) -> Vec<(u64, Vec<Literal>)> {
    clauses
        .iter()
        .enumerate()
        .map(|(index, clause)| (index as u64 + 1, clause.clone()))
        .collect()
}

fn store(key: MemoKey, dag: &ResolutionDag) {
    // A refutation whose original clauses are not exactly the key's,
    // numbered from 1, is not one this memo can restore: it is not kept.
    if dag.original_clauses.len() != key.clauses.len()
        || dag
            .original_clauses
            .iter()
            .zip(&key.clauses)
            .enumerate()
            .any(|(index, ((id, stored), clause))| *id != index as u64 + 1 || stored != clause)
    {
        return;
    }
    let stored = Stored {
        dag: ResolutionDag {
            num_vars: dag.num_vars,
            original_clauses: Vec::new(),
            derived: dag.derived.clone(),
            empty_clause_id: dag.empty_clause_id,
        },
    };
    let cost = literal_count(&key.clauses) + dag_literal_count(&stored.dag);
    // A single refutation larger than the whole budget is never retained: it
    // would evict the table on every store and cache nothing.
    if cost > MAX_RETAINED_LITERALS {
        return;
    }
    MEMO.with(|memo| {
        let mut memo = memo.borrow_mut();
        if memo.entries.len() >= MAX_ENTRIES
            || memo.retained_literals + cost > MAX_RETAINED_LITERALS
        {
            memo.entries.clear();
            memo.retained_literals = 0;
        }
        if memo.entries.insert(key, stored).is_none() {
            memo.retained_literals += cost;
        }
    });
}

/// A refutation of `clauses` produced by `derive`, served from the same
/// per-thread memo under a key tagged with `strategy`.
///
/// `derive` must return only a refutation that [`ResolutionDag::validate`]
/// accepts for exactly `(num_vars, clauses)`: a stored value is a certificate
/// for that CNF, whoever produced it. As with the SAT entry points, only a
/// success is stored, so a budget or deadline refusal is never made sticky.
pub fn resolution_dag_memoized_by(
    num_vars: usize,
    clauses: &[Vec<Literal>],
    strategy: &'static str,
    derive: impl FnOnce() -> Option<ResolutionDag>,
) -> Option<ResolutionDag> {
    if memo_disabled() {
        return derive();
    }
    let key = MemoKey {
        num_vars,
        clauses: clauses.to_vec(),
        limits: None,
        strategy: Some(strategy),
    };
    if let Some(dag) = lookup(&key) {
        return Some(dag);
    }
    let dag = derive()?;
    if dag.num_vars != num_vars
        || dag.original_clauses.len() != clauses.len()
        || dag
            .original_clauses
            .iter()
            .zip(clauses)
            .any(|((_, stored), clause)| stored != clause)
    {
        return None;
    }
    store(key, &dag);
    Some(dag)
}

/// Whether this thread retains a refutation of `clauses` that `strategy`
/// produced, without deriving one or counting a hit or a miss.
#[must_use]
pub fn resolution_dag_is_memoized_by(
    num_vars: usize,
    clauses: &[Vec<Literal>],
    strategy: &'static str,
) -> bool {
    if memo_disabled() {
        return false;
    }
    let key = MemoKey {
        num_vars,
        clauses: clauses.to_vec(),
        limits: None,
        strategy: Some(strategy),
    };
    MEMO.with(|memo| memo.borrow().entries.contains_key(&key))
}

/// Hits and misses on this thread, for tests and measurement.
#[must_use]
pub fn resolution_dag_memo_counters() -> (u64, u64) {
    MEMO.with(|memo| {
        let memo = memo.borrow();
        (memo.hits, memo.misses)
    })
}

/// Drop every retained refutation and refusal on this thread. Tests use it
/// to measure a cold lane; production never needs it, as a key is exact.
pub fn reset_resolution_dag_memo() {
    MEMO.with(|memo| *memo.borrow_mut() = Memo::default());
    within::reset_refusals();
}

/// [`prove_unsat_resolution_dag`], served from the per-thread refutation memo.
///
/// # Errors
/// Exactly [`prove_unsat_resolution_dag`]'s errors; none of them is cached.
pub fn prove_unsat_resolution_dag_memoized(
    num_vars: usize,
    clauses: &[Vec<Literal>],
) -> Result<ResolutionDag, ResolutionDagError> {
    monolithic_memoized(num_vars, clauses, None)
}

/// [`prove_unsat_resolution_dag_until`], served under the key of
/// [`prove_unsat_resolution_dag_memoized`]: the stop only polls, so what it
/// lets finish is the refutation the unpolled solve finds. `should_stop` is
/// consulted BEFORE a hit is served: a stopped caller observes a stop, never a
/// refutation.
///
/// # Errors
/// Exactly [`prove_unsat_resolution_dag_until`]'s; none is cached.
pub fn prove_unsat_resolution_dag_memoized_until(
    num_vars: usize,
    clauses: &[Vec<Literal>],
    should_stop: &dyn Fn() -> bool,
) -> Result<ResolutionDag, ResolutionDagError> {
    monolithic_memoized(num_vars, clauses, Some(should_stop))
}

fn monolithic_memoized(
    num_vars: usize,
    clauses: &[Vec<Literal>],
    should_stop: Option<&dyn Fn() -> bool>,
) -> Result<ResolutionDag, ResolutionDagError> {
    let derive = || match should_stop {
        None => prove_unsat_resolution_dag(num_vars, clauses),
        Some(should_stop) => prove_unsat_resolution_dag_until(num_vars, clauses, should_stop),
    };
    if memo_disabled() {
        return derive();
    }
    let key = MemoKey {
        num_vars,
        clauses: clauses.to_vec(),
        limits: None,
        strategy: None,
    };
    if let Some(dag) = lookup(&key) {
        if should_stop.is_some_and(|should_stop| should_stop()) {
            return Err(ResolutionDagError::Unknown);
        }
        return Ok(dag);
    }
    let dag = derive()?;
    store(key, &dag);
    Ok(dag)
}

/// [`prove_unsat_resolution_dag_with_limits_and_cancellation`], served from the
/// per-thread refutation memo.
///
/// `keep_going` is consulted BEFORE a hit is served, so a caller that has
/// already refused to continue observes exactly what it observed without the
/// memo: a cancellation, never a refutation.
///
/// # Errors
/// Exactly the wrapped function's errors, plus
/// [`ResolutionProofError::Cancelled`] when `keep_going` refuses before a hit.
/// None of them is cached.
pub fn prove_unsat_resolution_dag_with_limits_and_cancellation_memoized(
    num_vars: usize,
    clauses: &[Vec<Literal>],
    limits: &ResolutionProofLimits,
    keep_going: &mut dyn FnMut() -> bool,
) -> Result<ResolutionDag, ResolutionProofError> {
    if memo_disabled() {
        return prove_unsat_resolution_dag_with_limits_and_cancellation(
            num_vars, clauses, limits, keep_going,
        );
    }
    let key = MemoKey {
        num_vars,
        clauses: clauses.to_vec(),
        limits: Some(LimitsKey::of(limits)),
        strategy: None,
    };
    if let Some(dag) = lookup(&key) {
        if !keep_going() {
            return Err(ResolutionProofError::Cancelled);
        }
        return Ok(dag);
    }
    let dag = prove_unsat_resolution_dag_with_limits_and_cancellation(
        num_vars, clauses, limits, keep_going,
    )?;
    store(key, &dag);
    Ok(dag)
}
