// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Invocation-local results of late array-read materialization.
//!
//! `mk_select` can return a scalar value instead of a select node. Preserve
//! that exact result without adding an assertion or pretending the value is a
//! new select for functional-consistency discovery. These associations only
//! fill missing ROW2/ITE lookups; existing raw-read representatives win.

use super::{BvSolver, HashMap, HashSet, Sort, TermData, TermId};
use ay_core::TermStore;

pub(super) const MAX_LATE_ARRAY_READS: usize = 20_000;

/// Empty construction carries no associations. Only `materialize_read` can
/// record a result, directly from the live arena's own `mk_select` operation.
/// The owning solve keeps this value local; it is neither persistent state nor
/// authority for a different arena, invocation, or independently checked proof.
#[derive(Default)]
pub(in crate::executor) struct LateArrayReads {
    added_roots: usize,
    folded: HashMap<(TermId, TermId), TermId>,
}

impl LateArrayReads {
    pub(in crate::executor) fn added_roots(&self) -> usize {
        self.added_roots
    }

    pub(super) fn note_added_root(&mut self) {
        self.added_roots += 1;
    }

    pub(super) fn materialize_read(
        &mut self,
        terms: &mut TermStore,
        array: TermId,
        index: TermId,
    ) -> TermId {
        let read = terms.mk_select(array, index);
        let is_exact_select = matches!(terms.get(read), TermData::App(sym, args)
            if sym.name() == "select" && args.as_slice() == [array, index]);
        // Folded obligations can share ONE result root, so the original root
        // cap alone does not bound their associations. Refusing another entry
        // here must not stop/reorder the legacy root-materialization loop.
        if !is_exact_select
            && self.folded.len() < MAX_LATE_ARRAY_READS
            && matches!(terms.sort(read), Sort::Bool | Sort::BitVec(_))
            && terms.sort(array).array_index() == Some(terms.sort(index))
            && terms.sort(array).array_element() == Some(terms.sort(read))
        {
            self.folded.entry((array, index)).or_insert(read);
        }
        read
    }

    pub(super) fn get(&self, array: TermId, index: TermId) -> Option<TermId> {
        self.folded.get(&(array, index)).copied()
    }

    /// Include dependencies beneath Boolean predicates/ITE conditions too:
    /// `BvSolver::collect_bv_subterms` stops at a non-BV root. Otherwise a
    /// folded default's arithmetic can acquire delayed, unconstrained bits
    /// before ROW2 or an ITE branch equates the read with those bits.
    pub(in crate::executor) fn extend_eager_terms(
        &self,
        terms: &TermStore,
        eager: &mut HashSet<TermId>,
    ) {
        let mut visited = HashSet::default();
        let mut pending = Vec::new();
        for &read in self.folded.values() {
            if visited.insert(read) {
                pending.push(read);
            }
        }
        while let Some(term) = pending.pop() {
            // Scalar dependencies only: following an opaque array argument
            // would eagerly blast unrelated store payloads. Their semantics
            // remain owned by the existing array/UF/other-theory routes.
            if !matches!(terms.sort(term), Sort::Bool | Sort::BitVec(_)) {
                continue;
            }
            if matches!(terms.sort(term), Sort::BitVec(_)) {
                eager.insert(term);
            }
            let mut enqueue = |child| {
                if visited.insert(child) {
                    pending.push(child);
                }
            };
            match terms.get(term) {
                TermData::App(_, args) => {
                    for &arg in args {
                        enqueue(arg);
                    }
                }
                TermData::Not(inner) => enqueue(*inner),
                TermData::Ite(c, t, e) => {
                    for child in [*c, *t, *e] {
                        enqueue(child);
                    }
                }
                _ => {}
            }
        }
    }

    /// Called before the non-incremental route's atom-linking phase. Bool
    /// predicates must use their real encoding, not a fresh placeholder atom;
    /// `ensure_bool_literal` also records predicate literals in `bool_to_var`.
    /// This does not complete residual UF/lambda or other unsupported theories.
    pub(super) fn materialize_bits(&self, bv: &mut BvSolver<'_>, terms: &TermStore) {
        for &read in self.folded.values() {
            match terms.sort(read) {
                Sort::BitVec(_) if bv.get_term_bits(read).is_none() => {
                    let _ = bv.ensure_term_bits(read);
                }
                Sort::Bool if !bv.bool_to_var().contains_key(&read) => {
                    let _ = bv.ensure_bool_literal(read);
                }
                _ => {}
            }
        }
    }
}

#[cfg(test)]
mod storage_tests;
