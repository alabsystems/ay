// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! The strict producer's counted refusals, keyed by its exact input: the
//! CNF it would refute and the counted caps it would refute it under.
//!
//! ## Why
//!
//! One proof build, and the certification's nested solves after it, ask the
//! strict checker about one obligation in many spellings: the solver's
//! lemma, the guarded collapse's roots, the raw-root lane's roots, the same
//! lemma again in a fresh executor over a cloned store, and one copy of each
//! for every isomorphic assertion. The checker's memos are keyed by the
//! clause's `TermId`s (`checker/bv_bitblast/semantic_decision.rs`) or by its
//! division terms read by name (`crate::exact_division_sweeps`), so none of
//! those spellings sees another's refusal, although every one of them hands
//! this producer the SAME input. Measured 2026-10-15 on ay 086779f02 (model-checker-consumer
//! R30 review probes, release): `fac28` decides one 4,260-variable CNF three
//! times at 5.6 s each; `f3_padb`, three copies of one 32-bit factoring
//! constraint, decides one 5,506-variable CNF three times at 14.5 s each;
//! `urem128` re-sweeps one 82,948-variable CNF in a fresh executor (13.9 s).
//!
//! ## What is remembered
//!
//! A refusal of the input, recorded only when ALL of these hold:
//!
//! * it is the producer's own verdict: "no refutation" (the CNF has a model)
//!   or a cap of the SAT producer or of its replay (a `resolution ...`
//!   resource), never a deadline, a cancellation or anything else;
//! * no failure the producer met during it can have been its environment's
//!   rather than its input's ([`note_uncounted_failure`]): an allocation it
//!   could not make, which ay-sat reports as a `resolution ...` resource
//!   indistinguishable from a cap, or a SAT sweep's solver call that ended
//!   on neither its counts, a stop nor its deadline, such as ay-sat's
//!   process-memory interrupt, which the sweep passes over and after which
//!   the decision reports the monolithic attempt's cap;
//! * no exact-division sweep was withheld during it
//!   (`crate::exact_division_sweeps`), so the whole envelope ran;
//! * no poll of the caller refused during it, so no stop can have ended a
//!   search early and come back as a cap (`semantic_decision.rs` says how),
//!   and one poll after it confirms the caller is still going;
//! * it ended so far inside every wall it could meet that none can have
//!   touched it: in less than a tenth of the time then left to its deadline,
//!   and in less than [`WALL_SHARE_CAP`]. The producer's walls are that
//!   deadline itself, the case split's half of what is left to it
//!   (`bv_blast_solver/sweep.rs`), and the head start ay-sat's parked
//!   support enumeration waits for (a tenth of what is left, at most 30 s);
//!   an attempt shorter than all of them was decided by its counts alone.
//!   The strict checker's deadline is its 300 s hang guard, so a decision
//!   is recorded only if it took less than about 27 s: a slower or busier
//!   host records fewer, which costs time, never correctness.
//!
//! The key is the whole CNF — width, variable roles, bit lemmas, clauses
//! and provenance, written out field by field and compared exactly, never by
//! a hash alone — and the counted caps with their deadlines cleared.
//! Variable NAMES are not in it, because the CNF has none: leaves are
//! numbered in first-seen order. So the same obligation over other variables
//! is the same input, as it is to the producer, which reads nothing else.
//!
//! ## What it changes
//!
//! A later decision of an identical input under identical caps returns the
//! remembered refusal instead of searching again. That is the refusal the
//! search would return: its outcome is a function of exactly this input,
//! and the recording conditions exclude every outcome a clock, a stop or a
//! withheld sweep could have shaped. A decision that remembered a failed
//! exact-division sweep is repeated with it: the hit remembers that sweep
//! again in the attempt in progress, as the search would
//! (`crate::exact_division_sweeps::failing`), so a build whose own memo
//! starts afresh learns the divider from the hit too.
//!
//! Nothing is ever ACCEPTED from here: the memo can only refuse, and every
//! refutation is still found and replayed in full. The memo lives on the
//! thread for its life and holds at most [`MAX_ENTRIES`] inputs and
//! [`MAX_BYTES`], dropping the oldest to make room; a dropped or unrecorded
//! refusal costs time, never correctness.
//!
//! It is the strict checker's counterpart of the printer's memo of
//! refutations and counted refusals per CNF (`crate::resolution_dag_memo`),
//! and the same control turns both off: under `AY_RESOLUTION_DAG_MEMO=off`
//! every input is decided for real. Unlike that memo's refusals, these are
//! matched by the whole input, never by a fingerprint alone.

use std::cell::{Cell, RefCell};
use std::collections::VecDeque;
use std::mem::size_of;
use std::time::Duration;

use super::super::cnf::BvExprCnf;
use super::super::{poll_export, BvExprExportError, BvExprProofLimits};
use crate::bv_blast_export::{BitLemmaKind, BvBlastValidateLimits, ClauseProvenance, VarRole};
use ay_core::time::Instant;

/// Inputs one thread remembers at most; the oldest is dropped first.
const MAX_ENTRIES: usize = 64;
/// Bytes of remembered inputs one thread keeps at most, and the most one
/// input may take. An input is kept as about one `u32` per role field, lemma
/// field and literal: the largest measured, `urem128`'s 128-bit division
/// (82,948 variables, 462,855 clauses), takes about 13 MB.
const MAX_BYTES: usize = 32 * 1024 * 1024;
/// The longest attempt that is recorded, whatever its deadline: ay-sat's
/// parked support enumeration may start after 30 s of search.
const WALL_SHARE_CAP: Duration = Duration::from_secs(30);

struct Entry {
    shape: Shape,
    caps: String,
    input: Vec<u32>,
    refusal: BvExprExportError,
    /// Its decision remembered a failed exact-division sweep.
    swept_out: bool,
}

/// An input's sizes: a decision whose input matches no remembered shape
/// costs nothing more than this.
#[derive(Clone, Copy, PartialEq, Eq)]
struct Shape {
    width: u32,
    roles: usize,
    lemmas: usize,
    clauses: usize,
}

impl Shape {
    fn of(input: &BvExprCnf) -> Self {
        Self {
            width: input.width(),
            roles: input.vars.roles.len(),
            lemmas: input.bit_lemmas.len(),
            clauses: input.clauses.len(),
        }
    }
}

impl Entry {
    fn bytes(&self) -> usize {
        size_of::<Self>() + self.caps.len() + self.input.len() * size_of::<u32>()
    }
}

#[derive(Default)]
struct Memo {
    entries: VecDeque<Entry>,
    bytes: usize,
}

thread_local! {
    static MEMO: RefCell<Memo> = RefCell::new(Memo::default());
    /// Failures this thread's producer met that its environment, not its
    /// input, may have decided ([`note_uncounted_failure`]).
    static UNCOUNTED: Cell<u64> = const { Cell::new(0) };
}

/// Note a failure the producer met that its environment, not its input, may
/// have decided: an allocation it could not make, or a SAT sweep's solver
/// call that ended on neither its counts, a stop nor its deadline. No
/// refusal of a decision during which one was noted is remembered.
pub(crate) fn note_uncounted_failure() {
    UNCOUNTED.with(|noted| noted.set(noted.get().wrapping_add(1)));
}

fn uncounted_failures() -> u64 {
    UNCOUNTED.with(Cell::get)
}

/// Decide `input` under `limits` and `replay` with `decide`, unless this
/// thread already holds a refusal of exactly this input under exactly these
/// caps. `decide` hands the input back with a refusal it may be remembered
/// by; an input is written out only to be compared with a remembered one of
/// its shape, or to be remembered.
///
/// `keep_going` must be STICKY, as `cancellation::run` makes the producer's
/// poll: once it refuses, it refuses for good. Then one poll after the
/// decision says both that no poll during it refused and that the caller is
/// still going, and the decision's own polls pass through untouched.
pub(super) fn deciding(
    input: BvExprCnf,
    limits: &BvExprProofLimits,
    replay: &BvBlastValidateLimits,
    keep_going: &mut dyn FnMut() -> bool,
    decide: impl FnOnce(
        BvExprCnf,
        &mut dyn FnMut() -> bool,
    ) -> (Result<(), BvExprExportError>, Option<BvExprCnf>),
) -> Result<(), BvExprExportError> {
    if crate::resolution_dag_memo::memo_disabled() {
        return decide(input, keep_going).0;
    }
    let shape = Shape::of(&input);
    if let Some((refusal, swept_out)) = refused(shape, &input, || caps(limits, replay)) {
        poll_export(keep_going)?;
        if swept_out {
            crate::exact_division_sweeps::sweep_failed();
        }
        return Err(refusal);
    }
    let deadline = deadline(limits);
    let uncounted = uncounted_failures();
    let start = Instant::now();
    let (((outcome, returned), swept_out), withheld) =
        crate::exact_division_sweeps::deciding(|| {
            crate::exact_division_sweeps::failing(|| decide(input, &mut *keep_going))
        });
    if let (Err(refusal), Some(input), Some(deadline)) = (&outcome, returned, deadline) {
        if !withheld
            && counted(refusal)
            && uncounted_failures() == uncounted
            && clear_of_every_wall(start, Instant::now(), deadline)
            && keep_going()
        {
            if let Some(encoded) = encode(&input) {
                remember(Entry {
                    shape,
                    caps: caps(limits, replay),
                    input: encoded,
                    refusal: refusal.clone(),
                    swept_out,
                });
            }
        }
    }
    outcome
}

/// The producer's own verdict on its input: no refutation, or a cap of the
/// SAT producer or of its replay (never their deadline).
fn counted(refusal: &BvExprExportError) -> bool {
    match refusal {
        BvExprExportError::NoRefutation => true,
        BvExprExportError::ResourceLimit { resource, .. } => {
            resource.starts_with("resolution ") && !resource.ends_with("deadline")
        }
        _ => false,
    }
}

/// Whether an attempt from `start` to `end` stayed so far inside `deadline`
/// that no wall it could meet can have touched it (see the module docs).
fn clear_of_every_wall(start: Instant, end: Instant, deadline: Instant) -> bool {
    let spent = end.saturating_duration_since(start);
    let left = deadline.saturating_duration_since(end);
    spent < (left / 10).min(WALL_SHARE_CAP)
}

fn deadline(limits: &BvExprProofLimits) -> Option<Instant> {
    let resolution = &limits.resolution;
    match (resolution.deadline, resolution.validation.deadline) {
        (Some(a), Some(b)) => Some(a.min(b)),
        (a, b) => a.or(b),
    }
}

/// Every counted cap of `limits` and `replay`, their deadlines cleared.
fn caps(limits: &BvExprProofLimits, replay: &BvBlastValidateLimits) -> String {
    let mut limits = limits.clone();
    limits.resolution.deadline = None;
    limits.resolution.validation.deadline = None;
    let mut replay = *replay;
    replay.deadline = None;
    format!("{limits:?}\n{replay:?}")
}

/// `input` written out field by field, every list after its length, so two
/// inputs are equal exactly when their encodings are: the width, each role,
/// each bit lemma (kind, output, inputs) and each clause (provenance,
/// literals). Lemma and clause ids are their positions, which is checked,
/// not assumed. `None` past [`MAX_BYTES`], or for a field a `u32` cannot
/// hold or an id that is not its position.
fn encode(input: &BvExprCnf) -> Option<Vec<u32>> {
    let words = |count: usize| u32::try_from(count).ok();
    let size = 3 * input.vars.roles.len()
        + input
            .bit_lemmas
            .iter()
            .map(|lemma| 3 + lemma.ins.len())
            .sum::<usize>()
        + input
            .clauses
            .iter()
            .map(|clause| 2 + clause.lits.len())
            .sum::<usize>()
        + 4;
    if size.checked_mul(size_of::<u32>())? > MAX_BYTES {
        return None;
    }
    let mut out = Vec::with_capacity(size);
    out.extend([input.width(), words(input.vars.roles.len())?]);
    for role in &input.vars.roles {
        out.extend(role_words(*role));
    }
    out.push(words(input.bit_lemmas.len())?);
    for (position, lemma) in input.bit_lemmas.iter().enumerate() {
        if usize::try_from(lemma.id).ok()? != position {
            return None;
        }
        out.extend([kind_word(lemma.kind), lemma.out, words(lemma.ins.len())?]);
        out.extend(&lemma.ins);
    }
    out.push(words(input.clauses.len())?);
    for (position, clause) in input.clauses.iter().enumerate() {
        if usize::try_from(clause.id).ok()? != position {
            return None;
        }
        let provenance = match clause.provenance {
            ClauseProvenance::BitLemmaCnf { lemma } => lemma.checked_mul(2)?,
            ClauseProvenance::Disequality => 1,
        };
        out.extend([provenance, words(clause.lits.len())?]);
        for lit in &clause.lits {
            out.push(lit.var.checked_mul(2)?.checked_add(u32::from(lit.neg))?);
        }
    }
    Some(out)
}

fn role_words(role: VarRole) -> [u32; 3] {
    match role {
        VarRole::InputA { bit } => [0, bit, 0],
        VarRole::InputB { bit } => [1, bit, 0],
        VarRole::Out { bit } => [2, bit, 0],
        VarRole::BitEq { bit } => [3, bit, 0],
        VarRole::Aux { bit } => [4, bit, 0],
        VarRole::CarryIn => [5, 0, 0],
        VarRole::NotB { bit } => [6, bit, 0],
        VarRole::LhsOut { bit } => [7, bit, 0],
        VarRole::RhsOut { bit } => [8, bit, 0],
        VarRole::LhsAux { bit } => [9, bit, 0],
        VarRole::RhsAux { bit } => [10, bit, 0],
        VarRole::RhsCarryIn => [11, 0, 0],
        VarRole::RhsNotB { bit } => [12, bit, 0],
        VarRole::InputLeaf { leaf, bit } => [13, leaf, bit],
    }
}

fn kind_word(kind: BitLemmaKind) -> u32 {
    match kind {
        BitLemmaKind::Xor2 => 0,
        BitLemmaKind::And2 => 1,
        BitLemmaKind::Or2 => 2,
        BitLemmaKind::Xor3 => 3,
        BitLemmaKind::FullAdderCarry => 4,
        BitLemmaKind::Not => 5,
        BitLemmaKind::ConstTrue => 6,
        BitLemmaKind::ConstFalse => 7,
        BitLemmaKind::XnorEq => 8,
    }
}

/// The remembered refusal of exactly `input` under exactly the caps
/// `caps` builds, if any, and whether its decision remembered a failed
/// exact-division sweep.
fn refused(
    shape: Shape,
    input: &BvExprCnf,
    caps: impl FnOnce() -> String,
) -> Option<(BvExprExportError, bool)> {
    MEMO.with(|memo| {
        let memo = memo.borrow();
        if !memo.entries.iter().any(|entry| entry.shape == shape) {
            return None;
        }
        let (caps, encoded) = (caps(), encode(input)?);
        memo.entries
            .iter()
            .find(|entry| entry.shape == shape && entry.caps == caps && entry.input == encoded)
            .map(|entry| (entry.refusal.clone(), entry.swept_out))
    })
}

fn remember(entry: Entry) {
    let bytes = entry.bytes();
    if bytes > MAX_BYTES {
        return;
    }
    MEMO.with(|memo| {
        let mut memo = memo.borrow_mut();
        while memo.entries.len() >= MAX_ENTRIES || memo.bytes + bytes > MAX_BYTES {
            let Some(oldest) = memo.entries.pop_front() else {
                break;
            };
            memo.bytes -= oldest.bytes();
        }
        memo.bytes += bytes;
        memo.entries.push_back(entry);
    });
}

/// Inputs this thread remembers.
#[cfg(test)]
pub(super) fn remembered() -> usize {
    MEMO.with(|memo| memo.borrow().entries.len())
}

#[cfg(test)]
#[path = "refusal_memo_tests.rs"]
mod tests;
