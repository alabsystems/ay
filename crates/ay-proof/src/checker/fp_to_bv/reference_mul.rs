// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Independent word-level references for WHOLE IEEE Mul/Add/Sub operations.
//! `matching` checks a COMPLETE unit equality against this universally
//! symbolic word recipe. This is not a native gate/CNF or original-input
//! certificate. Native circuits still need independently replayed equivalence
//! and exact producer/export/root inventories on the original allowance.
//!
//! Exact-product/direct-quantum rounding follows BTRW15:
//! <https://smt-lib.org/papers/BTRW15.pdf>. Unlike a producer circuit descriptor,
//! this recipe is derived from the live source operation and independent
//! integer arithmetic. It never calls `ay-fp` or a native float operation.

use ay_core::{TermId, TermStore};

mod addition;
mod canonical;

mod canonical_clause;

pub(super) fn validate_canonical_clause(
    terms: &TermStore,
    step: ay_core::ProofId,
    clause: &[TermId],
    operation: ay_core::FpOp,
    limits: &ay_sat::ResolutionProofLimits,
    work: &mut ay_core::original_query::WorkBudget<'_>,
) -> std::result::Result<(), super::ProofCheckError> {
    canonical_clause::validate(terms, step, clause, operation, limits, work)
}
mod graph;
mod matching;
mod product;
mod rounding;
mod source;

#[cfg(test)]
mod tests;

use graph::{Node, RefId};
use source::Fields;

// Same logical construction envelope as the existing conservative BV route.
// This is a REFUSAL ceiling, never credit supplied to an original owner or a
// compatibility bit-width rule; all requested storage is still debited there.
const MAX_REFERENCE_BYTES: usize = 128 * 1024 * 1024;

#[cfg(test)]
pub(super) fn recognizes(
    terms: &TermStore,
    clause: &[TermId],
    progress: Progress<'_>,
) -> Result<bool> {
    recognizes_arithmetic(terms, clause, Arithmetic::Mul, progress)
}

pub(super) fn recognizes_arithmetic(
    terms: &TermStore,
    clause: &[TermId],
    operation: Arithmetic,
    progress: Progress<'_>,
) -> Result<bool> {
    let mut refused = false;
    let mut original = |work, bytes| {
        if refused {
            return false;
        }
        refused = true;
        let live = progress(work, bytes);
        if live {
            refused = false;
        }
        live
    };
    if !original(0, 0) {
        return Err(ReferenceError::Resource);
    }
    let result = matching::unit(terms, clause, operation, &mut original);
    // Both orientation attempts and their temporary programs are dropped
    // BEFORE the complete unit check's final original-owner observation.
    if !original(0, 0) {
        return Err(ReferenceError::Resource);
    }
    result
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, thiserror::Error)]
pub(super) enum ReferenceError {
    #[error("original FP reference owner refused")]
    Resource,
    #[error("FP reference source or operand is unsupported or malformed")]
    Source,
    #[error("FP reference width arithmetic overflowed")]
    Width,
    #[error("FP reference allocation refused")]
    Allocation,
}

type Result<T> = std::result::Result<T, ReferenceError>;
type Progress<'a> = &'a mut dyn FnMut(usize, usize) -> bool;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum Arithmetic {
    Mul,
    Add,
    Sub,
}

impl Arithmetic {
    fn name(self) -> &'static str {
        match self {
            Self::Mul => "fp.mul",
            Self::Add => "fp.add",
            Self::Sub => "fp.sub",
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct Format {
    eb: u32,
    p: u32,
    product_width: u32,
    exponent_width: u32,
}

impl Format {
    #[cfg(test)]
    fn checked(eb: u32, p: u32) -> Result<Self> {
        Self::checked_for(Arithmetic::Mul, eb, p)
    }

    fn checked_for(operation: Arithmetic, eb: u32, p: u32) -> Result<Self> {
        if eb < 2 || p < 2 {
            return Err(ReferenceError::Source);
        }
        eb.checked_add(p).ok_or(ReferenceError::Width)?;
        let product_width = match operation {
            Arithmetic::Mul => p.checked_mul(2).and_then(|n| n.checked_add(1)),
            Arithmetic::Add | Arithmetic::Sub => p.checked_add(4),
        }
        .ok_or(ReferenceError::Width)?;
        let count = u64::from(p) * 4;
        let count_bits = u64::BITS - count.leading_zeros();
        let exponent_width = eb
            .checked_add(4)
            .ok_or(ReferenceError::Width)?
            .max(count_bits + 3);
        Ok(Self {
            eb,
            p,
            product_width,
            exponent_width,
        })
    }
}

#[derive(Clone, Copy)]
struct Output {
    sign: RefId,
    exponent: RefId,
    fraction: RefId,
    // Required for a future fresh BV-carrier clause translation. The current
    // word matcher instead checks ACTUAL RM equalities and the exact five-way
    // source code, never treating this Boolean as a caller-provided premise.
    rm_domain: RefId,
}

/// Opaque, context-borrowed program retaining the SAME original owner. No
/// public root/permit/caller-selected source binding is exposed here.
pub(super) struct Reference<'terms, 'owner> {
    terms: &'terms TermStore,
    source: TermId,
    operation: Arithmetic,
    format: Format,
    progress: Progress<'owner>,
    refused: bool,
    nodes: Vec<Node>,
    node_limit: usize,
    allocated_bytes: usize,
    output: Option<Output>,
}

impl<'terms, 'owner> Reference<'terms, 'owner> {
    #[cfg(test)]
    pub(super) fn build(
        terms: &'terms TermStore,
        source: TermId,
        progress: Progress<'owner>,
    ) -> Result<Self> {
        Self::build_operation(terms, source, Arithmetic::Mul, progress)
    }

    pub(super) fn build_operation(
        terms: &'terms TermStore,
        source: TermId,
        operation: Arithmetic,
        progress: Progress<'owner>,
    ) -> Result<Self> {
        // A provisional format cannot authorize an operand; read_source
        // derives and checks the actual result and BOTH operand formats first.
        let mut reference = Self {
            terms,
            source,
            operation,
            format: Format {
                eb: 0,
                p: 0,
                product_width: 0,
                exponent_width: 0,
            },
            progress,
            refused: false,
            nodes: Vec::new(),
            node_limit: 0,
            allocated_bytes: 0,
            output: None,
        };
        reference.charge(0, 0)?;
        let result = reference.construct();
        // Normal source refusal also observes the original terminal stop.
        reference.charge(0, 0)?;
        result?;
        Ok(reference)
    }

    fn construct(&mut self) -> Result<()> {
        let (rm, x, y, format) = self.read_source()?;
        self.format = format;
        self.reserve_nodes()?;
        let (rm, rm_domain) = self.rounding_mode(rm)?;
        let x = self.input_fields(x)?;
        let y = self.input_fields(y)?;
        let output = match self.operation {
            Arithmetic::Mul => {
                let finite = self.product(x, y, rm)?;
                self.specials(x, y, finite, rm_domain)?
            }
            Arithmetic::Add | Arithmetic::Sub => self.addition(x, y, rm, rm_domain)?,
        };
        self.output = Some(output);
        Ok(())
    }

    fn charge(&mut self, work: usize, bytes: usize) -> Result<()> {
        if self.refused {
            return Err(ReferenceError::Resource);
        }
        // Keep refusal set during a panic or a swallowed nested owner error.
        self.refused = true;
        if !(self.progress)(work, bytes) {
            return Err(ReferenceError::Resource);
        }
        self.refused = false;
        Ok(())
    }

    fn stop<T>(&mut self, error: ReferenceError) -> Result<T> {
        self.refused = true;
        Err(error)
    }

    fn storage(&mut self, work: usize, bytes: usize) -> Result<()> {
        let total = self
            .allocated_bytes
            .checked_add(bytes)
            .ok_or(ReferenceError::Resource)?;
        if total > MAX_REFERENCE_BYTES {
            return self.stop(ReferenceError::Resource);
        }
        // Exact requested logical layouts are charged BEFORE owned reserve,
        // initialization or copying. Allocator bookkeeping remains outside it.
        self.charge(work, bytes)?;
        self.allocated_bytes = total;
        Ok(())
    }

    fn reserve_nodes(&mut self) -> Result<()> {
        let width =
            usize::try_from(self.format.product_width).map_err(|_| ReferenceError::Width)?;
        // The single leading-index loop emits three nodes per product bit;
        // the fixed recipe is <1024 nodes. Conservative extra slack is NOT
        // reusable work or storage credit; exceeding it refuses before growth.
        let limit = width
            .checked_mul(6)
            .and_then(|n| n.checked_add(1024))
            .ok_or(ReferenceError::Width)?;
        let bytes = limit
            .checked_mul(std::mem::size_of::<Node>())
            .ok_or(ReferenceError::Width)?;
        self.storage(limit, bytes)?;
        if self.nodes.try_reserve_exact(limit).is_err() {
            return self.stop(ReferenceError::Allocation);
        }
        self.node_limit = limit;
        Ok(())
    }

    fn input_fields(&mut self, fields: Fields) -> Result<graph::Bits> {
        let sign = self.input(fields.sign, 1)?;
        let exponent = self.input(fields.exponent, self.format.eb)?;
        let fraction = self.input(fields.fraction, self.format.p - 1)?;
        Ok(graph::Bits {
            sign,
            exponent,
            fraction,
        })
    }

    // The canonical child independently rederives supported complete source
    // roots and their total gate CNF. Native publication/source journals remain
    // separate; this word object itself is no valid-lemma permit.
}
