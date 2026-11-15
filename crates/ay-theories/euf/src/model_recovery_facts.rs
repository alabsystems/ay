// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Borrowed data for a model-only transaction while the live graph still exists.

use crate::EufSolver;
use ay_core::{TermId, TermStore};

/// A readonly fact from this solver's CURRENT graph/assignment state. It is not
/// a certificate and cannot justify adding equalities to the solving context.
#[derive(Clone, Copy)]
pub enum ModelRecoveryFact<'a> {
    /// Admit the original backing-store scan before visiting its live entries.
    ScanSlots(usize),
    /// One valid graph node and its immediate union-find parent. Consumers must
    /// bound/check their traversal; no missing node is claimed a singleton.
    Parent { term: TermId, parent: TermId },
    /// An active Boolean assignment (also a current kernel-inventory root).
    Boolean { term: TermId, value: bool },
    /// An active decoded equality/biconditional, with its actual truth value.
    Equality {
        left: TermId,
        right: TermId,
        equal: bool,
    },
    /// An active TRUE distinct atom. Every pair, not only a false equality,
    /// constrains the candidate interpretation.
    Distinct(&'a [TermId]),
    /// A scoped live disequality communicated by another theory (including
    /// arithmetic). Its endpoints are current kernel occurrences, not guesses
    /// from the absence of an explicit false equality.
    SharedDisequality { left: TermId, right: TermId },
}

impl EufSolver<'_> {
    /// Visit without allocation, model mutation, class walks or BigInt clones.
    /// Each callback is invoked BEFORE proceeding to the next bounded item and
    /// is responsible for admission/stop checking. Returning false means the
    /// graph was unavailable/malformed; no fallback singleton fact is minted.
    pub fn visit_model_recovery_facts<E>(
        &self,
        terms: &TermStore,
        mut visit: impl FnMut(ModelRecoveryFact<'_>) -> Result<(), E>,
    ) -> Result<bool, E> {
        if !std::ptr::eq(self.terms, terms)
            || !self.enodes_init
            || self.dirty
            || self.poisoned
            || self.pending_conflict.is_some()
            || self.pending_shared_diseq_conflict.is_some()
            || self.enodes.len() > self.terms.len()
        {
            return Ok(false);
        }
        visit(ModelRecoveryFact::ScanSlots(self.enodes.len()))?;
        visit(ModelRecoveryFact::ScanSlots(self.assigns.capacity()))?;
        for (index, node) in self.enodes.iter().enumerate() {
            if node.root as usize >= self.enodes.len() {
                return Ok(false);
            }
            visit(ModelRecoveryFact::Parent {
                term: TermId(match u32::try_from(index) {
                    Ok(index) => index,
                    Err(_) => return Ok(false),
                }),
                parent: TermId(node.root),
            })?;
        }
        visit(ModelRecoveryFact::ScanSlots(
            self.shared_disequalities.capacity(),
        ))?;
        for &(left, right) in self.shared_disequalities.keys() {
            if left as usize >= self.terms.len() || right as usize >= self.terms.len() {
                return Ok(false);
            }
            visit(ModelRecoveryFact::SharedDisequality {
                left: TermId(left),
                right: TermId(right),
            })?;
        }
        for (&term, &value) in &self.assigns {
            if term.index() >= self.terms.len() {
                return Ok(false);
            }
            visit(ModelRecoveryFact::Boolean { term, value })?;
            if let Some((left, right)) = self.decode_eq(term) {
                visit(ModelRecoveryFact::Equality {
                    left,
                    right,
                    equal: value,
                })?;
            } else if value {
                if let Some(arguments) = self.decode_distinct(term) {
                    visit(ModelRecoveryFact::Distinct(arguments))?;
                }
            }
        }
        Ok(true)
    }
}
