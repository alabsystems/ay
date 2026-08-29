// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! #strict-walk-memo — replay a strict-check verdict for a byte-identical
//! document instead of re-walking it.
//!
//! WHY. The certification pipeline re-asks `check_proof_strict_with_datatypes`
//! about the SAME finished document many times per solve: every authored
//! replacement cascade member opens with a defensive `is_ok()` entry guard, and
//! the surgery/commit gates around them ask again. Measured with a per-walk
//! attribution probe (`ay solve --no-proof`, QF_IDL, 2026-08-28):
//!
//!  * `sal/bakery/inf-bakery-mutex-18`: 74 strict-chokepoint walks, of which
//!    TWO 30-walk fans each walk one unchanged document (identical structural
//!    digest AND identical term-store snapshot stamp across the fan) for
//!    1.02G + 0.78G metered work units;
//!  * `sal/bakery/inf-bakery-mutex-8`: the same two fans at 109M work per walk
//!    — 6.53G of the solve's 7.07G total — the measured 0.58s -> 3.4s wall
//!    regression of its committed `EqDiffVar` splice;
//!  * `DTP/DTP_k2_n35_c245_s4`: ONE document walked 66 times at 350M work each
//!    (23.1G total), the walk cost that pushed its correct `unsat` over
//!    `-T:10`.
//!
//! Every fan outcome is a deterministic verdict on an unchanged input; the
//! walks re-derive a fact the checker has already established. This memo makes
//! the chokepoint answer such repeats from a stored verdict. It decides WHEN
//! the checker walks, never WHAT passes: the checker itself (`ay-proof`) is
//! untouched, a memo hit replays the checker's own verdict for an input proven
//! identical, and any doubt about identity is a MISS and a real walk.
//!
//! ## Currency argument (why a hit cannot be stale)
//!
//! A stored verdict is replayed only when EVERY input the checker read is
//! proven unchanged:
//!
//!  * **Document identity** — the memo stores a full clone of the checked
//!    `Proof` and compares it LITERALLY (`Proof: PartialEq`, structural over
//!    every step, clause, premise, annotation and named-step entry). No hash
//!    is trusted anywhere: a collision cannot produce a hit, only inequality
//!    can produce a miss.
//!  * **Term universe** — [`TermStoreSnapshotStamp`] equality, the store's own
//!    authority token for read-only derived state: same physical store
//!    (identity `Arc`), same structural generation (any rollback or compaction
//!    retires the stamp) and same length (any interning retires it). Term
//!    entries are immutable, so stamp equality proves every `TermId` the
//!    checker resolved still denotes byte-identical term data. This is the
//!    same idiom `CheckedGroundScope` / the quantified-SAT authority grants
//!    use to re-verify "the snapshot is current".
//!  * **Checker-visible TermStore metadata** —
//!    `TermStore::checker_visible_metadata_generation` equality. The stamp
//!    proves the term ARENA unchanged, but the checker also reads four
//!    TermStore metadata families that mutate WITHOUT appending a term or
//!    advancing the structural generation: the `to_real_shadowed` /
//!    `is_int_shadowed` latches (ground evaluation stands down for a
//!    shadowed builtin) and the `skolem_symbols` / `skolem_choice`
//!    registries (Skolem witness authority — where `register_skolem_choice`
//!    OVERWRITES on re-registration, changing the table at unchanged size).
//!    Their mutators bump the dedicated generation on every actual state
//!    change (#checker-visible-metadata-generation, `ay-core`), so equality
//!    here proves all four families are exactly what the stored walk read.
//!    A dedicated counter rather than literal table comparison: O(1) per
//!    probe regardless of table size, one conjunct covers any FUTURE family
//!    (a new checker-side read must join the counter's families — enforced
//!    by the audited read-surface contract below), and the
//!    [`TermStoreSnapshotStamp`] keeps its arena-only meaning for its other
//!    consumers, which tolerate no metadata-driven retirement. The price —
//!    a mutator re-recording an identical value would miss — is bounded by
//!    bumping only on actual change, and a spurious miss is the fail-closed
//!    direction (a re-walk, never a stale verdict).
//!  * **Datatype registries** — the constructor-distinctness declarations,
//!    constructor→selector table and exact member signatures passed to the
//!    checker are stored and compared literally.
//!  * **Authored problem scope** — the exact assertion window handed to the
//!    checker (freshness/authorization authority) is stored and compared
//!    literally; it is recomputed from executor state on every call, so any
//!    scope drift (new obligation extension, changed authored window) is an
//!    inequality and therefore a miss.
//!  * **Route identity** — the finite-enum capability check runs BEFORE the
//!    memo probe on every call; a proof with a capability takes the capability
//!    route and never consults the memo, so a stored general-route verdict can
//!    never answer for the capability route or vice versa.
//!
//! The executor's stop/deadline state is handled OUTSIDE the key, in both
//! directions: `ProofCheckError::Cancelled` is NEVER stored (a cancellation
//! says nothing about the document), and a STOPPING caller never receives a
//! cached answer — the lookup polls the same stop signals a real walk's first
//! charge polls and misses when they are asserted, so the stop surfaces as the
//! walk's own `Cancelled` with its calibrated downstream meaning (revert,
//! nothing learned, nothing latched — the commit gate's tier 4). Every stored
//! outcome — `Ok(quality)` or a typed/budget rejection — is a deterministic
//! function of the keyed inputs: the checker walks the document in step order
//! with deterministic containers, and the work meter's budget limbs are
//! compile-time constants.
//!
//! The replayed WORK figure is the original walk's metered aggregate, so any
//! consumer that prices the verdict by cost makes byte-identical decisions on
//! a hit and on a walk. (This memo is also what RETIRED the one such consumer
//! the campaign had: the `EqDiffVar` commit gate's 125M second price existed
//! to bound repetition, and repetition is what this memo removed — see
//! #eqdv-second-price-retired.)
//!
//! ## The checker-read TermStore surface is a CONTRACT, not an inference
//! (#strict-memo-term-metadata-contract)
//!
//! The key above is complete only if we KNOW everything the checker reads
//! from the `TermStore`. That enumeration is pinned — audited rather than
//! inferred — by `the_checker_read_term_store_surface_is_audited` in
//! `check/strict_memo_tests.rs`, a grep-style inventory of every
//! term-module accessor name called from `ay-proof`'s strict-walk source
//! (`checker/**`, `quality/**` and the entry files), compared EXACTLY
//! against the allowlist in that test. Today the checker-read state is:
//!
//!  * the immutable term entries and sorts (`get`, `sort`, `children`,
//!    `len`, `entry_stamp`, …) — covered by the SNAPSHOT-STAMP conjunct;
//!  * the four metadata families above — covered by the
//!    CHECKER-VISIBLE-METADATA-GENERATION conjunct;
//!  * `strict_bv_semantics_ok` (via `strict_bv_semantics_validated` /
//!    `record_strict_bv_semantics_validated`) — deliberately NOT keyed: it
//!    is the checker's own accept-only memo of COMPLETED `bv_bitblast`
//!    decisions, keyed by `(store, clause)`; no failure is ever recorded,
//!    so growth is monotone toward accepting recorded semantic FACTS, and
//!    its only clearing writers (`rollback_to`, `mark_and_compact`, clone)
//!    all retire the snapshot stamp. A stored verdict can therefore differ
//!    from a fresh walk only as an uncached checker run differs from a
//!    cached one — the fresh walk may ACCEPT a fact whose re-derivation the
//!    stored walk's budget rejected, never the reverse — and replaying the
//!    older, at-most-more-conservative verdict is the fail-closed side.
//!
//! Any NEW `TermStore` read appearing in that source fails the audit test
//! loudly until the key (or the counter's family set) is re-audited, and a
//! row VANISHING from the surface fails it too, so the allowlist cannot rot
//! into fiction. The write side is the counter's own contract
//! (#checker-visible-metadata-generation): every mutation of the four
//! families either bumps the generation or retires the stamp.
//!
//! ## Bounds
//!
//! At most [`STRICT_WALK_MEMO_CAPACITY`] entries, and only for documents whose
//! payload size fits [`STRICT_WALK_MEMO_MAX_PAYLOAD`] (a clone of a
//! multi-hundred-million-literal DT proof would cost more memory than the
//! walks it saves; such documents were measured walking at most twice per
//! solve). The memo is cleared when a public solve begins, alongside the M0(a)
//! counter reset.

use std::collections::VecDeque;

use ay_core::term::TermStoreSnapshotStamp;
use ay_core::{Proof, TermId};
use ay_proof::{DatatypeMemberSignature, ProofCheckError, ProofQuality};

use crate::executor::Executor;

/// Retained verdicts. The measured repeat pattern is one large document per
/// assembly phase plus an occasional small candidate/probe document
/// interleaved (`inf-bakery-mutex-8`: main fan split 2/26/2 by a 149-step
/// candidate); four slots cover that with room to spare while keeping the
/// worst-case retained memory small.
const STRICT_WALK_MEMO_CAPACITY: usize = 4;

/// Upper bound on a memoized document's payload (steps plus every clause
/// literal, premise and argument across the proof). Documents past it are
/// walked normally and simply not stored.
pub(in crate::executor) const STRICT_WALK_MEMO_MAX_PAYLOAD: usize = 16_000_000;

/// One stored strict-check verdict together with EVERY input that produced it.
pub(in crate::executor) struct StrictWalkMemoEntry {
    /// Full clone of the checked document — compared literally on probe.
    proof: Proof,
    /// Term-universe currency token captured at walk time.
    term_snapshot: TermStoreSnapshotStamp,
    /// Checker-visible TermStore metadata generation captured at walk time
    /// (the shadow latches and Skolem registries the checker reads; see
    /// #checker-visible-metadata-generation in `ay-core`).
    checker_metadata_generation: u64,
    /// Constructor-distinctness registry passed to the checker.
    datatype_decls: Vec<(String, Vec<String>)>,
    /// Constructor→selector registry passed to the checker.
    selector_decls: Vec<(String, Vec<String>)>,
    /// Exact sticky member signatures passed to the checker.
    member_signatures: Vec<DatatypeMemberSignature>,
    /// Exact authored premise scope passed to the checker.
    problem: Vec<TermId>,
    /// The checker's verdict. Never `Err(Cancelled)`.
    outcome: Result<ProofQuality, ProofCheckError>,
    /// The original walk's metered aggregate work.
    work: usize,
}

/// The executor-owned store: a tiny FIFO ring probed linearly.
#[derive(Default)]
pub(in crate::executor) struct StrictWalkMemo {
    entries: VecDeque<StrictWalkMemoEntry>,
}

impl StrictWalkMemo {
    /// Forget everything (public-solve boundary).
    pub(in crate::executor) fn clear(&mut self) {
        self.entries.clear();
    }
}

/// The exact non-document inputs of one strict-chokepoint walk.
pub(in crate::executor) struct StrictWalkKey<'a> {
    pub(in crate::executor) datatype_decls: &'a [(String, Vec<String>)],
    pub(in crate::executor) selector_decls: &'a [(String, Vec<String>)],
    pub(in crate::executor) member_signatures: &'a [DatatypeMemberSignature],
    pub(in crate::executor) problem: &'a [TermId],
}

/// Whether `entry` proves the pending walk would see byte-identical inputs.
///
/// Every conjunct is an independent currency authority; deleting any one of
/// them re-opens a stale-hit direction and is pinned RED by the adversarial
/// invalidation tests in `check/strict_memo_tests.rs`.
fn entry_is_current(
    entry: &StrictWalkMemoEntry,
    executor: &Executor,
    proof: &Proof,
    key: &StrictWalkKey<'_>,
) -> bool {
    // TERM-UNIVERSE CURRENCY: strict equality — any interning, rollback,
    // compaction or store replacement since the stored walk is a miss.
    entry.term_snapshot == executor.ctx.terms.snapshot_stamp()
        // CHECKER-READ METADATA CURRENCY: the shadow latches and Skolem
        // registries mutate WITHOUT retiring the stamp; any registration,
        // latch flip or same-size `skolem_choice` overwrite since the
        // stored walk is a miss (#checker-visible-metadata-generation).
        && entry.checker_metadata_generation
            == executor.ctx.terms.checker_visible_metadata_generation()
        // REGISTRY CURRENCY.
        && entry.datatype_decls == key.datatype_decls
        && entry.selector_decls == key.selector_decls
        && entry.member_signatures == key.member_signatures
        // AUTHORED-SCOPE CURRENCY.
        && entry.problem == key.problem
        // DOCUMENT IDENTITY: literal structural equality, compared last
        // because it is the widest conjunct.
        && entry.proof == *proof
}

/// Structural payload of `proof`: steps plus every stored id/literal. Linear,
/// and only computed when a walk finished and might be stored.
fn document_payload(proof: &Proof) -> usize {
    let mut payload = proof.steps.len();
    for step in &proof.steps {
        payload = payload.saturating_add(match step {
            ay_core::ProofStep::Assume(_) => 1,
            ay_core::ProofStep::Resolution { clause, .. } => clause.len().saturating_add(3),
            ay_core::ProofStep::TheoryLemma { clause, farkas, .. } => clause
                .len()
                .saturating_add(farkas.as_ref().map_or(0, |f| f.coefficients.len())),
            ay_core::ProofStep::Step {
                clause,
                premises,
                args,
                ..
            } => clause
                .len()
                .saturating_add(premises.len())
                .saturating_add(args.len()),
            ay_core::ProofStep::Anchor { variables, .. } => variables.len().saturating_add(1),
            // `ProofStep` is non-exhaustive: an unknown future variant has an
            // unknown payload, so refuse to memoize documents containing one
            // (fail closed towards re-walking).
            _ => STRICT_WALK_MEMO_MAX_PAYLOAD,
        });
    }
    payload
}

/// Diagnostic kill switch (`AY_NO_STRICT_WALK_MEMO=1`): every probe misses and
/// every store is skipped, restoring the walk-every-time behavior byte for
/// byte. Read once per process (repo precedent: `AY_MILP_NO_LATTICE`).
fn strict_walk_memo_disabled() -> bool {
    static DISABLED: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *DISABLED.get_or_init(|| std::env::var_os("AY_NO_STRICT_WALK_MEMO").is_some())
}

impl Executor {
    /// Probe the memo for a stored verdict whose complete input context is
    /// proven current. `None` means: walk for real.
    pub(in crate::executor) fn strict_walk_memo_lookup(
        &self,
        proof: &Proof,
        key: &StrictWalkKey<'_>,
    ) -> Option<(Result<ProofQuality, ProofCheckError>, usize)> {
        if strict_walk_memo_disabled() {
            return None;
        }
        // A STOPPING caller never gets a cached answer: a real walk's first
        // charge poll cancels it, and `Cancelled` has calibrated downstream
        // meaning (revert, nothing learned, nothing latched — see the
        // commit gate's tier 4). Miss and walk, so the stop is observed
        // exactly as it always was.
        if super::strict_check_progress::executor_stop_signals_asserted(self) {
            return None;
        }
        let memo = self.strict_walk_memo.borrow();
        for entry in memo.entries.iter() {
            if entry_is_current(entry, self, proof, key) {
                return Some((entry.outcome.clone(), entry.work));
            }
        }
        None
    }

    /// Store a finished walk's verdict, unless it is ineligible:
    /// a cancellation (not a fact about the document), or a document too
    /// large to retain.
    pub(in crate::executor) fn strict_walk_memo_store(
        &self,
        proof: &Proof,
        key: &StrictWalkKey<'_>,
        outcome: &Result<ProofQuality, ProofCheckError>,
        work: usize,
    ) {
        if strict_walk_memo_disabled() {
            return;
        }
        if matches!(outcome, Err(ProofCheckError::Cancelled)) {
            return;
        }
        if document_payload(proof) > STRICT_WALK_MEMO_MAX_PAYLOAD {
            return;
        }
        let entry = StrictWalkMemoEntry {
            proof: proof.clone(),
            term_snapshot: self.ctx.terms.snapshot_stamp(),
            checker_metadata_generation: self.ctx.terms.checker_visible_metadata_generation(),
            datatype_decls: key.datatype_decls.to_vec(),
            selector_decls: key.selector_decls.to_vec(),
            member_signatures: key.member_signatures.to_vec(),
            problem: key.problem.to_vec(),
            outcome: outcome.clone(),
            work,
        };
        let mut memo = self.strict_walk_memo.borrow_mut();
        // Replace a superseded verdict for the SAME document identity rather
        // than duplicating it (the document text is the entry's dominant
        // memory cost, and the reason for a re-walk was a context change that
        // retired the old entry anyway).
        memo.entries.retain(|existing| existing.proof != *proof);
        while memo.entries.len() >= STRICT_WALK_MEMO_CAPACITY {
            memo.entries.pop_front();
        }
        memo.entries.push_back(entry);
    }
}
