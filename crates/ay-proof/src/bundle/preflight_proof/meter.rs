// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use std::collections::BTreeSet;
use std::mem::size_of;

use super::*;

pub(super) struct ProofMeter<'a> {
    pub(super) progress: &'a mut dyn FnMut(usize, usize) -> bool,
}

pub(super) fn add(left: usize, right: usize) -> Result<usize, ProofCheckError> {
    left.checked_add(right)
        .ok_or(ProofCheckError::ResourceLimit)
}

pub(super) fn mul(left: usize, right: usize) -> Result<usize, ProofCheckError> {
    left.checked_mul(right)
        .ok_or(ProofCheckError::ResourceLimit)
}

impl<'a> ProofMeter<'a> {
    pub(super) fn new(progress: &'a mut dyn FnMut(usize, usize) -> bool) -> Self {
        Self { progress }
    }

    pub(super) fn charge(&mut self, work: usize, bytes: usize) -> Result<(), ProofCheckError> {
        if (self.progress)(work, bytes) {
            Ok(())
        } else {
            Err(ProofCheckError::ResourceLimit)
        }
    }

    pub(super) fn invalid<T>(
        &mut self,
        step: usize,
        message: &'static str,
    ) -> Result<T, ProofCheckError> {
        // Static text plus at most 20 decimal digits. Fourfold slack covers
        // formatting and geometric String growth before the first allocation.
        let bound = mul(add(message.len(), 64)?, 4)?;
        self.charge(bound, bound)?;
        Err(malformed_bundle(format!("proof step t{step} {message}")))
    }

    pub(super) fn term<'e>(
        &mut self,
        entries: &'e [(TermData, Sort)],
        id: TermId,
        step: usize,
        role: &'static str,
    ) -> Result<&'e (TermData, Sort), ProofCheckError> {
        self.charge(1, 0)?;
        match entries.get(id.index()) {
            Some(entry) => Ok(entry),
            None => self.root_error(step, role, "references term outside the snapshot"),
        }
    }

    fn root_error<T>(
        &mut self,
        step: usize,
        role: &'static str,
        message: &'static str,
    ) -> Result<T, ProofCheckError> {
        let bound = mul(add(add(role.len(), message.len())?, 64)?, 4)?;
        self.charge(bound, bound)?;
        // Never display an unvalidated recursive sort in an error path.
        Err(malformed_bundle(format!(
            "proof step t{step} {role} {message}"
        )))
    }

    pub(super) fn boolean(
        &mut self,
        entries: &[(TermData, Sort)],
        id: TermId,
        step: usize,
        role: &'static str,
    ) -> Result<(), ProofCheckError> {
        if !matches!(self.term(entries, id, step, role)?.1, Sort::Bool) {
            return self.root_error(step, role, "references non-Boolean term");
        }
        Ok(())
    }

    pub(super) fn clause(
        &mut self,
        entries: &[(TermData, Sort)],
        clause: &[TermId],
        step: usize,
        role: &'static str,
    ) -> Result<(), ProofCheckError> {
        for &literal in clause {
            self.boolean(entries, literal, step, role)?;
        }
        Ok(())
    }

    pub(super) fn seen(
        &mut self,
        seen: &mut BTreeSet<TermId>,
        term: TermId,
    ) -> Result<bool, ProofCheckError> {
        let levels = add(seen.len().bit_width() as usize, 1)?;
        let comparisons = add(seen.len(), 1)?.min(mul(levels, 12)?);
        let lookup = add(comparisons, levels)?;
        self.charge(lookup, 0)?;
        if seen.contains(&term) {
            return Ok(false);
        }
        // A second search occurs inside insert. alloc's B=6 tree has <=11
        // keys/12 edges per node. One split sibling per level plus a new root
        // fits in 32 (key,pointer) slots per node, including headers/padding.
        let slots = mul(add(levels, 1)?, 32)?;
        let bytes = mul(slots, add(size_of::<TermId>(), size_of::<usize>())?)?;
        // Also reserve linear drop/edge traversal work for each inserted node.
        self.charge(add(add(lookup, slots)?, 4)?, bytes)?;
        Ok(seen.insert(term))
    }

    pub(super) fn push(
        &mut self,
        stack: &mut Vec<TermId>,
        term: TermId,
    ) -> Result<(), ProofCheckError> {
        self.charge(1, 0)?;
        if stack.len() == stack.capacity() {
            let capacity = add(stack.capacity(), stack.capacity().max(1))?;
            let bytes = mul(capacity, size_of::<TermId>())?;
            // Price the entire replacement allocation and moved old elements,
            // not only its net growth. Refusal leaves the existing queue intact.
            self.charge(add(stack.len(), capacity)?, bytes)?;
            stack
                .try_reserve_exact(capacity - stack.len())
                .map_err(|_| ProofCheckError::ResourceLimit)?;
        }
        stack.push(term);
        Ok(())
    }
}
