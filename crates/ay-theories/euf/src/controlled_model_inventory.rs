// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Controlled preparation of the legacy EUF model-term inventory.
//!
//! The iterative reachability walk uses a fixed source-sized bitmap instead
//! of allocating TermStore::children vectors or an unpriced hash table.

use ay_core::original_query::{QueryError, WorkBudget};
use ay_core::term::{TermData, TermId};

use crate::solver::EufSolver;

struct InventoryScratch {
    marked: Vec<u8>,
    pending: Vec<TermId>,
    ordered: Vec<TermId>,
}

fn priced_vec<T>(entries: usize, work: &mut WorkBudget<'_>) -> Result<Vec<T>, QueryError> {
    let bytes = entries
        .checked_mul(std::mem::size_of::<T>())
        .and_then(|bytes| bytes.checked_mul(8))
        .and_then(|bytes| bytes.checked_add(4 * std::mem::size_of::<Vec<T>>()))
        .ok_or_else(|| work.refuse_exhaustion())?;
    let units = entries
        .checked_mul(8)
        .and_then(|units| units.checked_add(1))
        .ok_or_else(|| work.refuse_exhaustion())?;
    work.admit(units, bytes)?;
    let mut values = Vec::new();
    values
        .try_reserve_exact(entries)
        .map_err(|_| work.refuse_exhaustion())?;
    Ok(values)
}

impl InventoryScratch {
    fn new(entries: usize, work: &mut WorkBudget<'_>) -> Result<Self, QueryError> {
        let mut marked = priced_vec(entries, work)?;
        let pending = priced_vec(entries, work)?;
        let ordered = priced_vec(entries, work)?;
        marked.resize(entries, 0);
        Ok(Self {
            marked,
            pending,
            ordered,
        })
    }

    // Each raw occurrence is charged, including duplicates and shared edges.
    // Mark BEFORE queueing, so neither queue nor result can exceed source len.
    fn record(&mut self, term: TermId, work: &mut WorkBudget<'_>) -> Result<(), QueryError> {
        work.charge(8)?;
        let Some(mark) = self.marked.get_mut(term.0 as usize) else {
            return Err(QueryError::Invalid("EUF model inventory has a dead term"));
        };
        if *mark == 0 {
            *mark = 1;
            self.pending.push(term);
        }
        Ok(())
    }

    fn children(&mut self, term: &TermData, work: &mut WorkBudget<'_>) -> Result<(), QueryError> {
        match term {
            TermData::Const(_) | TermData::Var(_, _) => Ok(()),
            TermData::App(_, children) => {
                for &child in children {
                    self.record(child, work)?;
                }
                Ok(())
            }
            TermData::Let(bindings, body) => {
                for (_, child) in bindings {
                    self.record(*child, work)?;
                }
                self.record(*body, work)
            }
            TermData::Not(child)
            | TermData::Forall(_, child, _)
            | TermData::Exists(_, child, _) => self.record(*child, work),
            TermData::Ite(condition, then_term, else_term) => {
                self.record(*condition, work)?;
                self.record(*then_term, work)?;
                self.record(*else_term, work)
            }
            // TermData is non-exhaustive across this crate boundary. A future
            // variant must refuse, never masquerade as a childless model leaf.
            _ => Err(QueryError::Invalid(
                "EUF model inventory has an unsupported term",
            )),
        }
    }

    fn finish(
        mut self,
        result: Result<(), QueryError>,
        work: &mut WorkBudget<'_>,
    ) -> Result<Vec<TermId>, QueryError> {
        let result = result.and_then(|()| {
            for (index, &marked) in self.marked.iter().enumerate() {
                work.charge(4)?;
                if marked != 0 {
                    let id = u32::try_from(index).map_err(|_| work.refuse_exhaustion())?;
                    self.ordered.push(TermId(id));
                }
            }
            Ok(())
        });
        drop(self.pending);
        drop(self.marked);
        match result.and_then(|()| work.charge(0)) {
            Ok(()) => Ok(self.ordered),
            Err(error) => {
                drop(self.ordered);
                let _ = work.charge(0);
                Err(error)
            }
        }
    }
}

impl EufSolver<'_> {
    /// Prepare the same sorted reachable inventory as scope_model_to_roots.
    ///
    /// Borrows the caller's SAME work/copy ledger; no grant or deadline is
    /// created. All raw children (including repeated/unchosen ITE arms) count.
    /// Quantifier triggers are not model children, exactly as in the legacy
    /// TermStore::children walk. This is structural DATA, not source/proof
    /// authority, a model, or a controlled congruence-closure operation.
    ///
    /// This method never changes the installed scope or any solver/cache
    /// state, on success or refusal. It is not wired to extraction yet. The
    /// future caller must retain source/entry stamps, original minimum memory
    /// controls and publication gates, price subsequent work, and poll after
    /// its own cleanup. Returned vector storage/disposal was prepaid here;
    /// later caller growth/copying is not covered.
    pub fn try_model_terms_from_roots(
        &self,
        roots: &[TermId],
        work: &mut WorkBudget<'_>,
    ) -> Result<Vec<TermId>, QueryError> {
        let mut scratch = InventoryScratch::new(self.terms.len(), work)?;
        let result = (|| {
            for &root in roots {
                scratch.record(root, work)?;
            }
            while let Some(term) = scratch.pending.pop() {
                work.charge(4)?;
                // record checked this ID before it could enter the queue.
                scratch.children(self.terms.get(term), work)?;
            }
            Ok(())
        })();
        scratch.finish(result, work)
    }

    /// Copy the current legacy scope's sorted term inventory under one ledger.
    ///
    /// An absent scope still means ALL source entries, including unreachable
    /// entries, exactly as scoped_model_terms. A sparse hash scope pays its
    /// full capacity scan before iteration; there is no average-O(1) claim.
    /// This neither constructs a model nor makes prior unpriced scope/cache
    /// preparation controlled. State and legacy APIs remain untouched.
    pub fn try_scoped_model_terms(
        &self,
        work: &mut WorkBudget<'_>,
    ) -> Result<Vec<TermId>, QueryError> {
        let mut scratch = InventoryScratch::new(self.terms.len(), work)?;
        let result = (|| {
            if let Some(scope) = &self.model_term_scope {
                let scan = scope
                    .capacity()
                    .checked_mul(32)
                    .and_then(|units| units.checked_add(256))
                    .ok_or_else(|| work.refuse_exhaustion())?;
                work.charge(scan)?;
                for &term in scope {
                    scratch.record(term, work)?;
                }
            } else {
                for index in 0..self.terms.len() {
                    let id = u32::try_from(index).map_err(|_| work.refuse_exhaustion())?;
                    scratch.record(TermId(id), work)?;
                }
            }
            // This inventory copies scope membership only: it MUST NOT close
            // children again and change the meaning of the installed scope.
            Ok(())
        })();
        scratch.finish(result, work)
    }
}

#[cfg(test)]
mod tests;
