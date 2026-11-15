// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Closed snapshot DAG construction, not source identity or model authority.

use ay_core::term::ControlledTermInternError;
use ay_core::{Constant, Sort, Symbol, TermData, TermId, TermStore};
use num_bigint::BigInt;

use super::{SnapshotKind, SnapshotTopology};
use crate::{ArrayValue, ModelValue};

mod range;
#[cfg(test)]
mod tests;
mod validate;

/// Refusal of whole-function MODEL DATA construction; never a solver verdict.
#[derive(Debug, Clone, Copy, PartialEq, Eq, thiserror::Error)]
pub enum SnapshotTermError {
    #[error("snapshot term original owner refused construction")]
    ResourceLimit,
    #[error("snapshot term requires a complete backwards DAG")]
    InvalidTopology,
    #[error("snapshot term admits only BV64 arrays of Bool or BV1..128")]
    UnsupportedSort,
    #[error("snapshot term producer refused: {0}")]
    Producer(ControlledTermInternError),
}

type Result<T> = std::result::Result<T, SnapshotTermError>;

struct Admission<'a> {
    progress: &'a mut dyn FnMut(usize, usize) -> bool,
    refused: bool,
}

impl Admission<'_> {
    fn pay(&mut self, work: usize, bytes: usize) -> Result<()> {
        if self.refused {
            return Err(SnapshotTermError::ResourceLimit);
        }
        self.refused = true;
        if !(self.progress)(work, bytes) {
            return Err(SnapshotTermError::ResourceLimit);
        }
        self.refused = false;
        Ok(())
    }

    fn reserve<T>(&mut self, values: &mut Vec<T>, count: usize) -> Result<()> {
        let bytes = count
            .checked_mul(std::mem::size_of::<T>())
            .and_then(|n| n.checked_mul(2))
            .ok_or(SnapshotTermError::ResourceLimit)?;
        self.pay(
            bytes
                .checked_add(count)
                .ok_or(SnapshotTermError::ResourceLimit)?,
            bytes,
        )?;
        values
            .try_reserve_exact(count)
            .map_err(|_| SnapshotTermError::ResourceLimit)
    }
}

impl SnapshotTopology<'_> {
    /// Construct this complete closed function in the SAME producer arena.
    ///
    /// Export this topology with `topology_with_progress` under the SAME sink.
    /// All rows, ordered overrides, shared edges and even empty-range captures
    /// are admitted before construction. Index arithmetic is unsigned BV64;
    /// Range source indexing is `(i - lo + source_lo) mod 2^64`.
    ///
    /// The sink retains the original finite work/storage/end/stop across every
    /// call and must latch typed ResourceLimit (including allocation/overflow)
    /// before retry. No grant, timer, model choice, sampled read or proof seal is
    /// created. BRAY controlled producer interning and controlled fresh BV64
    /// binders are prerequisites. Scratch drops precede the final zero poll;
    /// committed inert arena entries can remain on refusal, with no rollback or
    /// refund. Existing caller-owned topology/arena disposal remains its owner.
    pub fn try_to_term_with_progress(
        &self,
        terms: &mut TermStore,
        progress: &mut dyn FnMut(usize, usize) -> bool,
    ) -> std::result::Result<TermId, SnapshotTermError> {
        let mut builder = Builder {
            terms,
            admission: Admission {
                progress,
                refused: false,
            },
        };
        let result = builder.build(self);
        let final_poll = builder.admission.pay(0, 0);
        match (result, final_poll) {
            (Ok(id), Ok(())) => Ok(id),
            (Err(error), _) | (_, Err(error)) => Err(error),
        }
    }
}

struct Builder<'t, 'p> {
    terms: &'t mut TermStore,
    admission: Admission<'p>,
}

impl Builder<'_, '_> {
    fn build(&mut self, topology: &SnapshotTopology<'_>) -> Result<TermId> {
        validate::complete(topology, &mut self.admission)?;
        self.admission.pay(0, 0)?;
        let mut built = Vec::new();
        self.admission.reserve(&mut built, topology.nodes().len())?;
        for node in topology.nodes() {
            self.admission.pay(1, 0)?;
            let id = match node.kind {
                SnapshotKind::Finite(value) => self.finite(value, node.sort)?,
                SnapshotKind::Store { base, index, value } => {
                    let base = *built.get(base).ok_or(SnapshotTermError::InvalidTopology)?;
                    self.store(base, index, value, node.sort)?
                }
                SnapshotKind::Range {
                    destination,
                    source,
                    lo,
                    hi,
                    source_lo,
                } => {
                    let destination = *built
                        .get(destination)
                        .ok_or(SnapshotTermError::InvalidTopology)?;
                    let source = *built
                        .get(source)
                        .ok_or(SnapshotTermError::InvalidTopology)?;
                    self.range(destination, source, lo, hi, source_lo, node.sort)?
                }
            };
            built.push(id);
        }
        built
            .get(topology.root())
            .copied()
            .ok_or(SnapshotTermError::InvalidTopology)
    }

    fn finite(&mut self, value: &ArrayValue, sort: &Sort) -> Result<TermId> {
        let element = validate::element(sort)?;
        let default = self.scalar(&value.default, element)?;
        let mut id = self.app("const-array", &[default], sort)?;
        for (index, datum) in &value.store {
            self.admission.pay(1, 0)?;
            id = self.store(id, index, datum, sort)?;
        }
        Ok(id)
    }

    fn store(
        &mut self,
        base: TermId,
        index: &ModelValue,
        value: &ModelValue,
        sort: &Sort,
    ) -> Result<TermId> {
        let index = self.scalar(index, &Sort::bitvec(64))?;
        let value = self.scalar(value, validate::element(sort)?)?;
        self.app("store", &[base, index, value], sort)
    }

    fn scalar(&mut self, value: &ModelValue, sort: &Sort) -> Result<TermId> {
        // The complete pass bounded the payload before this prepaid clone.
        self.admission.pay(512, 4096)?;
        let constant = match value {
            ModelValue::Bool(value) => Constant::Bool(*value),
            ModelValue::BitVec { value, width } => Constant::BitVec {
                value: value.clone(),
                width: *width,
            },
            _ => return Err(SnapshotTermError::InvalidTopology),
        };
        self.intern(&TermData::Const(constant), sort)
    }

    fn bound(&mut self, value: &BigInt) -> Result<TermId> {
        self.admission.pay(512, 4096)?;
        self.intern(
            &TermData::Const(Constant::BitVec {
                value: value.clone(),
                width: 64,
            }),
            &Sort::bitvec(64),
        )
    }

    fn app(&mut self, name: &'static str, args: &[TermId], sort: &Sort) -> Result<TermId> {
        self.admission.pay(512, 4096)?;
        let mut owned = Vec::new();
        owned
            .try_reserve_exact(args.len())
            .map_err(|_| SnapshotTermError::ResourceLimit)?;
        owned.extend_from_slice(args);
        self.intern(&TermData::App(Symbol::named(name), owned), sort)
    }

    fn intern(&mut self, data: &TermData, sort: &Sort) -> Result<TermId> {
        let admission = &mut self.admission;
        self.terms
            .try_intern_with_progress(data, sort, &mut |work, bytes| {
                admission.pay(work, bytes).is_ok()
            })
            .map_err(map_intern)
    }
}

fn map_intern(error: ControlledTermInternError) -> SnapshotTermError {
    match error {
        ControlledTermInternError::ResourceLimit => SnapshotTermError::ResourceLimit,
        error => SnapshotTermError::Producer(error),
    }
}
