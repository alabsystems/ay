// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Which cached compound BV values go stale when a leaf variable moves.
//!
//! `try_bv_candidates` must drop every cached compound value that depends on
//! the leaf it is about to mutate, or the evaluator's bit-blast cache keeps
//! answering with the pre-mutation value and confirms an invalid candidate
//! (#bv-ite-bool-model). It used to find them by walking the term DAG of EVERY
//! compound term in the BV model, once per candidate leaf, with a fresh visited
//! set each walk: O(attempts x model x DAG) for a relation holding only
//! O(model x DAG). On `inv_Newton` that walk was the minimizer's hottest frame.
//!
//! Dependence is reachability in the TERM STORE, which is immutable while
//! minimization runs (only model VALUES move), and the `bv_model` key set is
//! invariant across a pass (candidates overwrite, remove and restore existing
//! keys, never add one). So one walk per compound term yields the whole
//! relation and each attempt becomes a hash lookup. `try_bv_candidates` keeps a
//! debug-build assertion that the indexed set still equals the original full
//! scan, so a future violation of either invariant fails loudly instead of
//! silently under-invalidating the cache.

use ay_core::kani_compat::{DetHashMap, DetHashSet};
use ay_core::{TermData, TermId};

use super::super::Model;
use super::MinAttempt;
use crate::executor::Executor;

/// `BV leaf variable -> cached COMPOUND bv_model terms derived from it`.
pub(super) type BvDependentIndex = DetHashMap<TermId, Vec<TermId>>;

impl Executor {
    /// One minimization pass's inputs: the candidate attempts and the BV
    /// dependency index they share. `None` when there is no model to minimize.
    /// The index is skipped entirely when no attempt will consult it.
    pub(super) fn collect_min_attempts_and_dependents(
        &self,
    ) -> Option<(Vec<MinAttempt>, BvDependentIndex)> {
        let model = self.last_model.as_ref()?;
        let attempts = self.collect_min_attempts(model);
        let dependents = if attempts.is_empty() {
            BvDependentIndex::default()
        } else {
            self.bv_dependent_compound_index(model)
        };
        Some((attempts, dependents))
    }

    /// Whether `needle` occurs in the subtree rooted at `root`.
    ///
    /// Iterative worklist with a visited set so shared (DAG) subterms are
    /// walked once — the naive recursive version is exponential on DAGs.
    pub(in crate::executor::model) fn term_mentions(
        terms: &ay_core::TermStore,
        root: TermId,
        needle: TermId,
    ) -> bool {
        let mut visited: DetHashSet<TermId> = DetHashSet::default();
        let mut worklist = vec![root];
        while let Some(t) = worklist.pop() {
            if t == needle {
                return true;
            }
            if !visited.insert(t) {
                continue;
            }
            match terms.get(t) {
                TermData::App(_, args) => worklist.extend(args.iter().copied()),
                TermData::Not(inner) => worklist.push(*inner),
                TermData::Ite(c, th, el) => worklist.extend([*c, *th, *el]),
                TermData::Let(bindings, body) => {
                    worklist.extend(bindings.iter().map(|(_, b)| *b));
                    worklist.push(*body);
                }
                TermData::Forall(_, body, _) | TermData::Exists(_, body, _) => {
                    worklist.push(*body);
                }
                _ => {}
            }
        }
        false
    }

    /// Build the pass's [`BvDependentIndex`] from `model`'s BV cache.
    ///
    /// One reachability walk per COMPOUND entry; every VARIABLE entry reached on
    /// that walk records the compound as a dependent. Equivalent by construction
    /// to `term_mentions(compound, variable)` for every pair the old per-attempt
    /// scan tested — that predicate IS reachability, and the walk visits exactly
    /// the reachable set. Lists are sorted by term id so the stale-entry order a
    /// pass observes is stable run to run.
    pub(super) fn bv_dependent_compound_index(&self, model: &Model) -> BvDependentIndex {
        let mut index = BvDependentIndex::default();
        let Some(bv) = model.bv_model.as_ref() else {
            return index;
        };
        let leaves: DetHashSet<TermId> = bv
            .values
            .keys()
            .copied()
            .filter(|&t| matches!(self.ctx.terms.get(t), TermData::Var(_, _)))
            .collect();
        if leaves.is_empty() {
            return index;
        }
        let mut visited: DetHashSet<TermId> = Default::default();
        let mut worklist: Vec<TermId> = Vec::new();
        for &compound in bv.values.keys() {
            if matches!(self.ctx.terms.get(compound), TermData::Var(_, _)) {
                continue;
            }
            visited.clear();
            worklist.clear();
            worklist.push(compound);
            while let Some(t) = worklist.pop() {
                if !visited.insert(t) {
                    continue;
                }
                if t != compound && leaves.contains(&t) {
                    index.entry(t).or_default().push(compound);
                }
                match self.ctx.terms.get(t) {
                    TermData::App(_, args) => worklist.extend(args.iter().copied()),
                    TermData::Not(inner) => worklist.push(*inner),
                    TermData::Ite(c, th, el) => worklist.extend([*c, *th, *el]),
                    TermData::Let(bindings, body) => {
                        worklist.extend(bindings.iter().map(|(_, b)| *b));
                        worklist.push(*body);
                    }
                    TermData::Forall(_, body, _) | TermData::Exists(_, body, _) => {
                        worklist.push(*body);
                    }
                    _ => {}
                }
            }
        }
        for dependents in index.values_mut() {
            dependents.sort_unstable_by_key(|t| t.0);
        }
        index
    }

    /// The cached compound `(term, value)` entries that go stale when `leaf`
    /// moves — the ones `try_bv_candidates` must evict before it re-evaluates.
    /// `None` when there is no BV model at all.
    pub(super) fn stale_bv_cache_entries(
        &self,
        leaf: TermId,
        dependents: &BvDependentIndex,
    ) -> Option<Vec<(TermId, num_bigint::BigInt)>> {
        let compounds: &[TermId] = dependents.get(&leaf).map_or(&[], Vec::as_slice);
        #[cfg(debug_assertions)]
        self.assert_bv_dependents_match_full_scan(leaf, compounds);
        let bv = self.last_model.as_ref()?.bv_model.as_ref()?;
        Some(
            compounds
                .iter()
                .filter_map(|&t| bv.values.get(&t).map(|v| (t, v.clone())))
                .collect(),
        )
    }

    /// Debug-build differential oracle for one lookup: the indexed dependents of
    /// `leaf` must equal what the original full `term_mentions` scan finds.
    #[cfg(debug_assertions)]
    fn assert_bv_dependents_match_full_scan(&self, leaf: TermId, indexed: &[TermId]) {
        let oracle: DetHashSet<TermId> = self
            .last_model
            .as_ref()
            .and_then(|m| m.bv_model.as_ref())
            .map(|bv| {
                bv.values
                    .iter()
                    .filter(|&(&t, _)| {
                        t != leaf
                            && !matches!(self.ctx.terms.get(t), TermData::Var(_, _))
                            && Self::term_mentions(&self.ctx.terms, t, leaf)
                    })
                    .map(|(&t, _)| t)
                    .collect()
            })
            .unwrap_or_default();
        let fast: DetHashSet<TermId> = indexed.iter().copied().collect();
        debug_assert_eq!(
            fast, oracle,
            "BvDependentIndex diverged from the full term_mentions scan \
             (term store mutated mid-minimization, or a bv_model key appeared?)"
        );
    }
}
