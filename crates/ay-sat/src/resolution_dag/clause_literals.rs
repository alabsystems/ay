// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Preflight's per-clause literal pass: every literal names a variable in
//! range, none repeats in its clause, and the scratch of the repeat check is
//! charged before the clause is read.
//!
//! ## Why a scan, and a stride over the whole input
//!
//! The repeat check was a fresh SipHash `HashMap<u32, usize>` per clause,
//! and the clock was read at the first literal of every clause (the literal
//! stride `literal_index % 1024` is 0 there). Every solve preflights its
//! whole input, and the strict producer's SAT sweep makes thousands of
//! solves, mostly over one candidate's cone. On `qb44`, the 44-bit
//! `(bvudiv x 1000003) < 17592134` under `:produce-proofs` (release CLI):
//! about 10,600 solves preflighting about 67 M clauses and 214 M literals in
//! all, only 7 of them over 53,000 clauses (counted 2026-11-04 on
//! 491ef52fb). This pass took 8.5 s of the 50.6 s of CPU (SIGPROF samples,
//! 2026-11-03, 7d56ca109), 1.9 s of it reading the clock and 4.4 s building,
//! probing and freeing the per-clause maps.
//!
//! ## What changed, and what did not
//!
//! * A clause of at most [`SCANNED_LITERALS`] literals is checked by
//!   comparing each literal with the ones before it. That finds the same
//!   first repeat, at the same index and with the same first index, as the
//!   map did.
//! * The scratch it is charged for is unchanged: the capacity a fresh map
//!   reserves for that many literals, read from such a map, once per length
//!   and pass. A longer clause still gets a fresh map of its own.
//! * The clock is read at every 1,024th literal of the input, as well as at
//!   every 1,024th clause, so a passed deadline is still seen within 1,024
//!   clauses and 1,024 literals.
//! * Every poll is where it was: the caller's callback sees the same
//!   sequence, and every error comes at the same poll with the same fields.

use std::collections::HashMap;

use super::{
    check_deadline, enforce_proof_limit, Literal, ProofControl, ResolutionProofError,
    ResolutionProofLimits, ResolutionProofPhase, ResolutionProofResource,
};

/// The longest clause whose repeat check is a scan of its earlier literals.
pub(super) const SCANNED_LITERALS: usize = 16;

/// Bytes charged per reserved slot of a clause's repeat check: a
/// conservative estimate covering `(u32, usize)`, control bytes and
/// alignment. Only one clause's check is live at a time.
const SLOT_BYTES: usize = 32;

/// Literals between two clock reads of the pass.
const CLOCK_LITERALS: usize = 1024;

/// One preflight's literal pass over its clauses, in order.
pub(super) struct ClauseLiterals<'a, 'c> {
    num_vars: usize,
    input_bytes: usize,
    limits: &'a ResolutionProofLimits,
    control: &'a ProofControl<'c>,
    /// The capacity a fresh map reserves for each scanned length, once read.
    capacities: [Option<usize>; SCANNED_LITERALS + 1],
    /// Literals the pass has read, across all clauses.
    walked: usize,
    /// Clock reads the pass made.
    #[cfg(test)]
    clock_reads: usize,
    /// Repeat-check maps the pass built.
    #[cfg(test)]
    maps_built: usize,
}

impl<'a, 'c> ClauseLiterals<'a, 'c> {
    /// A pass over clauses of a `num_vars`-variable input whose records and
    /// literals take `input_bytes`.
    pub(super) fn new(
        num_vars: usize,
        input_bytes: usize,
        limits: &'a ResolutionProofLimits,
        control: &'a ProofControl<'c>,
    ) -> Self {
        Self {
            num_vars,
            input_bytes,
            limits,
            control,
            capacities: [None; SCANNED_LITERALS + 1],
            walked: 0,
            #[cfg(test)]
            clock_reads: 0,
            #[cfg(test)]
            maps_built: 0,
        }
    }

    /// Check clause `clause_index`: poll, charge its repeat check's scratch,
    /// then read each literal.
    pub(super) fn check(
        &mut self,
        clause_index: usize,
        clause: &[Literal],
    ) -> Result<(), ResolutionProofError> {
        self.control.poll()?;
        if clause_index.is_multiple_of(1024) {
            self.read_clock()?;
        }
        self.charge(clause.len().checked_mul(SLOT_BYTES))?;
        self.control.poll()?;
        let mut seen = (clause.len() > SCANNED_LITERALS).then(HashMap::<u32, usize>::new);
        #[cfg(test)]
        {
            self.maps_built += usize::from(seen.is_some());
        }
        let capacity = match seen.as_mut() {
            Some(map) => reserve(map, clause.len())?,
            None => self.scanned_capacity(clause.len())?,
        };
        self.charge(capacity.checked_mul(SLOT_BYTES))?;
        for (literal_index, literal) in clause.iter().enumerate() {
            self.control.poll()?;
            if self.walked.is_multiple_of(CLOCK_LITERALS) {
                self.read_clock()?;
            }
            self.walked += 1;
            let var = literal.variable().index();
            if var >= self.num_vars {
                return Err(ResolutionProofError::InputLiteralOutOfRange {
                    clause_index,
                    literal_index,
                    var,
                    num_vars: self.num_vars,
                });
            }
            let first = match seen.as_mut() {
                Some(map) => map.insert(literal.raw(), literal_index),
                None => clause[..literal_index]
                    .iter()
                    .position(|earlier| earlier.raw() == literal.raw()),
            };
            if let Some(first_index) = first {
                return Err(ResolutionProofError::DuplicateInputLiteral {
                    clause_index,
                    literal_index,
                    first_index,
                });
            }
        }
        Ok(())
    }

    fn read_clock(&mut self) -> Result<(), ResolutionProofError> {
        #[cfg(test)]
        {
            self.clock_reads += 1;
        }
        check_deadline(self.limits.deadline, ResolutionProofPhase::Preflight)
    }

    /// Refuse an input whose bytes and `scratch` exceed the input-byte limit.
    fn charge(&self, scratch: Option<usize>) -> Result<(), ResolutionProofError> {
        let overflow = ResolutionProofError::AccountingOverflow {
            resource: ResolutionProofResource::InputBytes,
        };
        let peak = scratch
            .and_then(|scratch| self.input_bytes.checked_add(scratch))
            .ok_or(overflow)?;
        enforce_proof_limit(
            ResolutionProofResource::InputBytes,
            peak,
            self.limits.max_input_bytes,
        )
    }

    /// The capacity a fresh map reserves for `len` literals, read from one
    /// the first time this pass meets the length.
    fn scanned_capacity(&mut self, len: usize) -> Result<usize, ResolutionProofError> {
        if let Some(capacity) = self.capacities[len] {
            return Ok(capacity);
        }
        #[cfg(test)]
        {
            self.maps_built += 1;
        }
        let capacity = reserve(&mut HashMap::new(), len)?;
        self.capacities[len] = Some(capacity);
        Ok(capacity)
    }
}

/// Reserve `map` for `len` literals and return its capacity.
fn reserve(map: &mut HashMap<u32, usize>, len: usize) -> Result<usize, ResolutionProofError> {
    map.try_reserve(len)
        .map_err(|_| ResolutionProofError::AllocationFailed {
            resource: ResolutionProofResource::InputLiterals,
        })?;
    Ok(map.capacity())
}

#[cfg(test)]
mod tests;
