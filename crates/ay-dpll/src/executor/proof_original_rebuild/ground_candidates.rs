// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The arithmetic ground-evaluate leg's authored value candidates, memoized
//! for one planning run.
//!
//! `plan_ground_form` asks for the authored ground values of a term at EVERY
//! planner node it visits, and the node budget (`EQ_PLAN_BUDGET`) counts nodes,
//! not the work inside one. Recomputed per node, that work is a scan of every
//! authored equality plus one strict ground evaluation per side, so a bridge
//! that spends its budget pays (nodes x sides) evaluations. On the 100-step
//! `mod` BMC script in `group_lia::lia_incremental_bmc_stress`, whose 34
//! `unsat` certificates each run a bridge that never closes, that was 5.1
//! million evaluations and 1.08 s for the bridge at step 65 alone, and 44.7 s
//! for the script on an idle X925 core (84 s on an A725), of which 7.6 s
//! remain with this leg switched off. Memoized, a run evaluates each term,
//! and computes each term's candidate list, at most once, and the script
//! takes 8.1 s on the X925 core (15.1 s on the A725).
//!
//! Every answer is pure within a run. The side list is a function of the
//! authored set alone, and a term's candidate list is a function of the term,
//! the side list and evaluability. Evaluability is a function of the term,
//! whose entry is immutable while the store keeps its identity and structural
//! generation (rollback and compaction advance it), and of the `to_real` /
//! `is_int` shadow latches the strict evaluator also reads, which flip
//! without retiring the snapshot and so are covered by the store's
//! checker-visible metadata generation
//! (#checker-visible-metadata-generation). The memo is keyed on all three
//! and returns exactly what the recomputation returns, in the same order. On
//! a miss it evaluates sides in the same order, and the recognizer only reads
//! the store, so plans, budget consumption and the terms interned along the
//! way are unchanged.

use super::*;
use ay_core::term::TermStoreSnapshotStamp;

/// Planning-run memo behind [`Executor::authored_ground_candidates`] and
/// [`Executor::term_is_ground_evaluable`].
///
/// Boxed and empty between runs: `rebuild_trust_leaf_proof_from_original_assertions`
/// clears it around the substitution bridge, the only production caller, so
/// no `TermId` outlives the run that recorded it. Every read also checks the
/// store snapshot and the checker-visible metadata generation (and a side or
/// candidate read checks the authored set), so a direct caller (the planner
/// unit tests) never reads an entry recorded against another store, latch
/// state or set.
#[derive(Default)]
pub(in crate::executor) struct GroundCandidateMemo {
    state: Option<Box<GroundCandidateMemoState>>,
    /// Strict ground evaluations run since the last `clear`, across state
    /// resets, for the counted unit tests.
    #[cfg(test)]
    evaluations: usize,
    /// Candidate lists computed (not answered from the memo) since the last
    /// `clear`, across state resets, for the counted unit tests.
    #[cfg(test)]
    scans: usize,
}

struct GroundCandidateMemoState {
    /// The store the entries below were recorded against. Append-only growth
    /// keeps them valid; a replaced, rolled-back or compacted store does not.
    store: TermStoreSnapshotStamp,
    /// The store's checker-visible metadata generation at the same moment:
    /// the strict evaluator reads the `to_real` / `is_int` shadow latches,
    /// which flip without retiring `store`.
    metadata: u64,
    /// Strict ground evaluability per term.
    evaluable: HashMap<TermId, bool>,
    /// The authored set `sides` and `candidates` were collected from.
    originals: Vec<TermId>,
    /// Every side of an authored binary `=` in `originals`, first occurrence
    /// first, without repeats.
    sides: Vec<TermId>,
    /// The authored ground candidates per term over `originals`.
    candidates: HashMap<TermId, Vec<TermId>>,
}

impl GroundCandidateMemo {
    /// Forget every entry (and the `TermId`s they hold).
    pub(in crate::executor) fn clear(&mut self) {
        *self = Self::default();
    }

    /// The state for `terms`, emptied first when it was recorded against
    /// another store snapshot or metadata generation.
    fn state_for(&mut self, terms: &TermStore) -> &mut GroundCandidateMemoState {
        let metadata = terms.checker_visible_metadata_generation();
        if !self.state.as_ref().is_some_and(|state| {
            state.metadata == metadata && state.store.is_append_only_prefix_of(terms)
        }) {
            self.state = None;
        }
        self.state.get_or_insert_with(|| {
            Box::new(GroundCandidateMemoState {
                store: terms.snapshot_stamp(),
                metadata,
                evaluable: HashMap::default(),
                originals: Vec::new(),
                sides: Vec::new(),
                candidates: HashMap::default(),
            })
        })
    }
}

impl GroundCandidateMemoState {
    /// Re-collect `sides`, and forget `candidates`, unless they were collected
    /// from `original_terms`.
    fn follow_authored_set(&mut self, terms: &TermStore, original_terms: &[TermId]) {
        if self.originals.as_slice() == original_terms {
            return;
        }
        self.sides.clear();
        self.candidates.clear();
        let mut seen: HashSet<TermId> = HashSet::default();
        for &original in original_terms {
            let TermData::App(Symbol::Named(name), args) = terms.get(original) else {
                continue;
            };
            if name != "=" || args.len() != 2 {
                continue;
            }
            for side in [args[0], args[1]] {
                if seen.insert(side) {
                    self.sides.push(side);
                }
            }
        }
        self.originals.clear();
        self.originals.extend_from_slice(original_terms);
    }
}

impl Executor {
    /// Whether the strict ground evaluator closes `x` on its own.
    ///
    /// Asked by running the recognizer on `(= x x)`: the evaluator descends
    /// `x` exactly as it would inside a real conclusion, so this agrees with
    /// the checker by construction (including its work, depth and value-size
    /// envelopes) instead of re-implementing a groundness predicate that could
    /// drift from it. The cheap shape pre-filter keeps the common variable /
    /// uninterpreted case from interning a term at all. Memoized per planning
    /// run (module docs).
    pub(super) fn term_is_ground_evaluable(&mut self, x: TermId) -> bool {
        let memo = self.ground_candidate_memo.state_for(&self.ctx.terms);
        if let Some(&known) = memo.evaluable.get(&x) {
            return known;
        }
        let evaluable = self.term_is_ground_evaluable_uncached(x);
        #[cfg(test)]
        {
            self.ground_candidate_memo.evaluations += 1;
        }
        let memo = self.ground_candidate_memo.state_for(&self.ctx.terms);
        memo.evaluable.insert(x, evaluable);
        evaluable
    }

    fn term_is_ground_evaluable_uncached(&mut self, x: TermId) -> bool {
        if !matches!(self.ctx.terms.sort(x), Sort::Bool | Sort::Int | Sort::Real) {
            return false;
        }
        match self.ctx.terms.get(x) {
            TermData::Const(Constant::Bool(_) | Constant::Int(_) | Constant::Rational(_))
            | TermData::Not(_)
            | TermData::Ite(_, _, _) => {}
            TermData::App(Symbol::Named(_), args) if !args.is_empty() => {}
            _ => return false,
        }
        let self_eq = self
            .ctx
            .terms
            .mk_app(Symbol::named("="), [x, x], Sort::Bool);
        ay_proof::recognize_ground_evaluate(&self.ctx.terms, self_eq)
    }

    /// Ground terms the ORIGINAL assertions offer as a value for `x`.
    ///
    /// Only sides of authored binary equalities are considered — the same
    /// non-laundering rule the definition leg follows. This does NOT decide
    /// that `x` equals any of them: each candidate is handed to `plan_eq`,
    /// which must derive `(= x c)` from the originals (typically `symm`, or
    /// `trans` along an authored definition chain) or the candidate is dropped.
    /// Memoized per planning run (module docs).
    pub(super) fn authored_ground_candidates(
        &mut self,
        x: TermId,
        original_terms: &[TermId],
    ) -> Vec<TermId> {
        /// Cap the per-argument candidate fan-out. `EQ_PLAN_BUDGET` already
        /// terminates the search; this only keeps a constant-rich problem from
        /// spending most of it on one argument position.
        const MAX_CANDIDATES: usize = 64;
        let memo = self.ground_candidate_memo.state_for(&self.ctx.terms);
        memo.follow_authored_set(&self.ctx.terms, original_terms);
        if let Some(known) = memo.candidates.get(&x) {
            return known.clone();
        }
        let sides = memo.sides.clone();
        #[cfg(test)]
        {
            self.ground_candidate_memo.scans += 1;
        }
        let sort = self.ctx.terms.sort(x).clone();
        let mut candidates = Vec::new();
        for side in sides {
            if candidates.len() >= MAX_CANDIDATES {
                break;
            }
            if side != x
                && *self.ctx.terms.sort(side) == sort
                && self.term_is_ground_evaluable(side)
            {
                candidates.push(side);
            }
        }
        let memo = self.ground_candidate_memo.state_for(&self.ctx.terms);
        if memo.originals.as_slice() == original_terms {
            memo.candidates.insert(x, candidates.clone());
        }
        candidates
    }
}

#[cfg(test)]
mod tests;
