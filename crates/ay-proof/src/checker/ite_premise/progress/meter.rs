// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

pub(super) struct Meter<'terms, 'progress> {
    pub(super) terms: &'terms TermStore,
    pub(super) progress: &'progress mut dyn FnMut(usize, usize) -> bool,
}

impl<'terms> Meter<'terms, '_> {
    pub(super) fn charge(&mut self, work: usize, bytes: usize) -> Result<(), ProofCheckError> {
        if (self.progress)(work, bytes) {
            Ok(())
        } else {
            Err(ProofCheckError::ResourceLimit)
        }
    }

    pub(super) fn root(&mut self, id: TermId) -> Result<(), ProofCheckError> {
        self.charge(1, 0)?;
        if id.index() < self.terms.len() {
            return Ok(());
        }
        let reason = "authored-ITE premise references a term outside the term store";
        self.charge(reason.len(), reason.len())?;
        Err(ProofCheckError::MalformedProofBundle {
            reason: reason.to_owned(),
        })
    }

    pub(super) fn roots(&mut self, ids: &[TermId]) -> Result<(), ProofCheckError> {
        for &id in ids {
            self.root(id)?;
        }
        Ok(())
    }

    pub(super) fn term(&mut self, id: TermId) -> Result<&'terms TermData, ProofCheckError> {
        self.root(id)?;
        Ok(self.terms.get(id))
    }

    pub(super) fn is_boolean(&mut self, id: TermId) -> Result<bool, ProofCheckError> {
        self.root(id)?;
        Ok(matches!(self.terms.sort(id), Sort::Bool))
    }

    pub(super) fn named(&mut self, left: &str, right: &str) -> Result<bool, ProofCheckError> {
        let work = left.len().min(right.len()).checked_add(1);
        self.charge(work.ok_or(ProofCheckError::ResourceLimit)?, 0)?;
        Ok(left == right)
    }

    pub(super) fn push<T>(&mut self, values: &mut Vec<T>, value: T) -> Result<(), ProofCheckError> {
        self.charge(1, 0)?;
        if values.len() == values.capacity() {
            let capacity = values
                .capacity()
                .max(1)
                .checked_mul(2)
                .ok_or(ProofCheckError::ResourceLimit)?;
            let bytes = capacity
                .checked_mul(size_of::<T>())
                .ok_or(ProofCheckError::ResourceLimit)?;
            // Charge the entire replacement allocation and old-element copy,
            // not merely the extra slot. Existing storage remains paid for.
            self.charge(values.len(), bytes)?;
            values
                .try_reserve_exact(capacity - values.len())
                .map_err(|_| ProofCheckError::ResourceLimit)?;
        }
        values.push(value);
        Ok(())
    }

    pub(super) fn flags(&mut self, len: usize) -> Result<Vec<bool>, ProofCheckError> {
        let bytes = len
            .checked_mul(size_of::<bool>())
            .ok_or(ProofCheckError::ResourceLimit)?;
        self.charge(len, bytes)?;
        let mut flags = Vec::new();
        flags
            .try_reserve_exact(len)
            .map_err(|_| ProofCheckError::ResourceLimit)?;
        flags.resize(len, false);
        Ok(flags)
    }
}
