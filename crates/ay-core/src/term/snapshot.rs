// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Caller-metered copies and private metadata restoration for checker snapshots.

use std::mem::size_of;

use super::{
    fresh_term_entry_stamp, Constant, Sort, Symbol, TermData, TermEntry, TermId, TermStore,
};
use crate::sort::{ArraySort, DatatypeConstructor, DatatypeField};

mod comparison;
mod skolem;

/// Failure to copy a term snapshot or restore names within the caller's envelope.
#[derive(Debug, Clone, Copy, PartialEq, Eq, thiserror::Error)]
pub enum TermSnapshotError {
    /// The callback refused, checked accounting overflowed, the sort nesting
    /// bound was exceeded, metadata generation would overflow, or an output
    /// vector or private registry could not be reserved.
    #[error("term snapshot resource limit exceeded")]
    ResourceLimit,
}

// Bound the recursive Sort::clone implementation BEFORE entering it. The
// serialized proof bundle admits at most this same nesting depth. This is a
// copy-safety bound, not an assertion that the snapshot is well typed.
const MAX_SNAPSHOT_SORT_DEPTH: usize = 256;
// A reconstructed store owns one fresh Arc-backed rollback identity. The
// existing diagnostic clone accountant reserves the same conservative size.
const SNAPSHOT_ROLLBACK_IDENTITY_BYTES: usize = 64;

type Progress<'a> = &'a mut dyn FnMut(usize, usize) -> bool;
type SnapshotResult<T> = Result<T, TermSnapshotError>;

impl TermStore {
    /// Inspect a borrowed native sort through the established owned-copy
    /// safety walk. Callback bytes describe payload inspected, not a grant.
    pub fn inspect_sort_with_progress(
        sort: &Sort,
        progress: &mut dyn FnMut(usize, usize) -> bool,
    ) -> Result<(), TermSnapshotError> {
        meter_sort(sort, 0, progress)
    }
    /// Return the stored Boolean-constant IDs without assuming they exist or
    /// authenticating their contents. Positional snapshot readers must retain
    /// these options exactly and validate them independently.
    #[must_use]
    pub fn boolean_constant_ids(&self) -> (Option<TermId>, Option<TermId>) {
        (self.true_term, self.false_term)
    }

    /// Copy every entry, preserving its positional [`TermId`], under one
    /// caller-owned work/byte/cancellation envelope.
    ///
    /// Charges include unused entries and recursively owned sort/binder
    /// payloads, independently of this store's memory ledgers. Each payload is
    /// inspected and charged before cloning; no term is hashed or interned.
    /// A refusal produces no snapshot. The callback must retain its cumulative
    /// allowance across this operation and subsequent reconstruction/checking.
    pub fn entries_snapshot_with_progress(
        &self,
        progress: &mut dyn FnMut(usize, usize) -> bool,
    ) -> Result<Vec<(TermData, Sort)>, TermSnapshotError> {
        charge(progress, 1, size_of::<Vec<(TermData, Sort)>>())?;
        let mut entries = reserve_output::<(TermData, Sort)>(self.terms.len(), progress)?;
        for entry in &self.terms {
            meter_entry(&entry.term, &entry.sort, progress)?;
            charge(progress, 0, 0)?;
            entries.push((entry.term.clone(), entry.sort.clone()));
        }
        charge(progress, 0, 0)?;
        Ok(entries)
    }

    /// Copy a borrowed positional snapshot without constructing a term store.
    ///
    /// This is the raw-snapshot counterpart of [`Self::entries_snapshot_with_progress`].
    /// Every entry, including unused or malformed entries, is preserved exactly
    /// and its owned payload is charged before copying. No interning, semantic
    /// validation, fresh entry identity, or proof authority is introduced. The
    /// caller must keep the same cumulative callback for later replay phases.
    pub fn copy_snapshot_entries_with_progress(
        source: &[(TermData, Sort)],
        progress: &mut dyn FnMut(usize, usize) -> bool,
    ) -> Result<Vec<(TermData, Sort)>, TermSnapshotError> {
        charge(progress, 1, size_of::<Vec<(TermData, Sort)>>())?;
        let mut entries = reserve_output::<(TermData, Sort)>(source.len(), progress)?;
        for (term, sort) in source {
            meter_entry(term, sort, progress)?;
            charge(progress, 0, 0)?;
            entries.push((term.clone(), sort.clone()));
        }
        charge(progress, 0, 0)?;
        Ok(entries)
    }

    /// Copy a borrowed positional snapshot into a fresh CHECKER-ONLY store
    /// under the supplied aggregate envelope, without an intermediate snapshot
    /// vector. See [`Self::from_entries`] for the read-only store contract.
    ///
    /// This is allocation/resource preflight, NOT semantic validation: all
    /// supplied term IDs, sorts, and constants remain exactly as supplied. The
    /// independent reader must still authenticate the snapshot before use.
    /// Producer-side metadata and the interner remain empty, and the memory
    /// ledgers remain zero, as with the existing unmetered constructor.
    pub fn from_entries_with_progress(
        entries: &[(TermData, Sort)],
        true_term: Option<TermId>,
        false_term: Option<TermId>,
        var_counter: u32,
        progress: &mut dyn FnMut(usize, usize) -> bool,
    ) -> Result<Self, TermSnapshotError> {
        charge(
            progress,
            1,
            checked_add(size_of::<Self>(), SNAPSHOT_ROLLBACK_IDENTITY_BYTES)?,
        )?;
        let mut terms = reserve_output::<TermEntry>(entries.len(), progress)?;
        for (term, sort) in entries {
            meter_entry(term, sort, progress)?;
            charge(progress, 0, 0)?;
            // Scalar sorts need no private walk/allocation. Complex descriptor
            // reachability remains unchecked in this checker-only snapshot.
            let own = match sort {
                Sort::FiniteField(_) => Some(true),
                Sort::Array(_) | Sort::Seq(_) | Sort::Datatype(_) => None,
                _ => Some(false),
            };
            let visits = match term {
                TermData::App(_, args) => args.len(),
                TermData::Ite(..) => 3,
                TermData::Not(_) => 1,
                TermData::Const(_) | TermData::Var(..) => 0,
                _ => 0,
            };
            charge(progress, checked_add(visits, 1)?, 0)?;
            let field_presence = if matches!(
                term,
                TermData::Let(..) | TermData::Forall(..) | TermData::Exists(..)
            ) {
                None
            } else {
                super::finite_field::entry_from_sort(&terms, term, own)
            };
            terms.push(TermEntry {
                term: term.clone(),
                sort: sort.clone(),
                stamp: fresh_term_entry_stamp(),
                field_presence,
            });
        }
        charge(progress, 0, 0)?;
        let store = Self::from_snapshot_entries(terms, true_term, false_term, var_counter);
        charge(progress, 0, 0)?;
        Ok(store)
    }
}

fn charge(progress: Progress<'_>, work: usize, bytes: usize) -> SnapshotResult<()> {
    if progress(work, bytes) {
        Ok(())
    } else {
        Err(TermSnapshotError::ResourceLimit)
    }
}

fn checked_add(left: usize, right: usize) -> SnapshotResult<usize> {
    left.checked_add(right)
        .ok_or(TermSnapshotError::ResourceLimit)
}

fn checked_mul(left: usize, right: usize) -> SnapshotResult<usize> {
    left.checked_mul(right)
        .ok_or(TermSnapshotError::ResourceLimit)
}

fn reserve_output<T>(len: usize, progress: Progress<'_>) -> SnapshotResult<Vec<T>> {
    if len > u32::MAX as usize {
        return Err(TermSnapshotError::ResourceLimit);
    }
    charge(
        progress,
        checked_add(len, 1)?,
        checked_mul(len, size_of::<T>())?,
    )?;
    let mut output = Vec::new();
    output
        .try_reserve_exact(len)
        .map_err(|_| TermSnapshotError::ResourceLimit)?;
    Ok(output)
}

#[allow(clippy::ptr_arg)] // Source allocation capacity is part of the conservative charge.
fn meter_vec<T>(values: &Vec<T>, progress: Progress<'_>) -> SnapshotResult<()> {
    // Vec::clone copies its elements, not its spare capacity. Charging the
    // source capacity is deliberately conservative and uses checked products.
    charge(
        progress,
        checked_add(values.len(), 1)?,
        checked_mul(values.capacity(), size_of::<T>())?,
    )
}

#[allow(clippy::ptr_arg)] // Preserve the source String capacity in the allocation charge.
fn meter_string(value: &String, progress: Progress<'_>) -> SnapshotResult<()> {
    charge(progress, checked_add(value.len(), 1)?, value.capacity())
}

fn meter_bigint(value: &num_bigint::BigInt, progress: Progress<'_>) -> SnapshotResult<()> {
    let bits = usize::try_from(value.bits()).map_err(|_| TermSnapshotError::ResourceLimit)?;
    // BigUint::clone copies its normalized digit Vec. Rounding to 64-bit
    // limbs also covers 32-bit digits and avoids pricing only partial bytes.
    // The one-limb floor conservatively covers zero and small magnitudes.
    let limbs = (checked_add(bits, 63)? / 64).max(1);
    charge(
        progress,
        checked_add(limbs, 1)?,
        checked_mul(limbs, size_of::<u64>())?,
    )
}

fn meter_constant(value: &Constant, progress: Progress<'_>) -> SnapshotResult<()> {
    match value {
        Constant::Bool(_) => charge(progress, 1, 0),
        Constant::String(value) => meter_string(value, progress),
        Constant::FiniteField { .. } => charge(progress, 1, 0),
        Constant::Int(value) | Constant::BitVec { value, .. } => meter_bigint(value, progress),
        Constant::Rational(value) => {
            meter_bigint(value.0.numer(), progress)?;
            meter_bigint(value.0.denom(), progress)
        }
    }
}

fn meter_symbol(symbol: &Symbol, progress: Progress<'_>) -> SnapshotResult<()> {
    // Symbol names share an Arc<str> when cloned. Charging the retained text
    // anyway is a conservative payload reserve; no symbol is hashed here.
    let name = symbol.name();
    charge(progress, checked_add(name.len(), 1)?, name.len())?;
    if let Symbol::Indexed(_, indices) = symbol {
        meter_vec(indices, progress)?;
    }
    Ok(())
}

pub(in crate::term) fn meter_entry(
    term: &TermData,
    sort: &Sort,
    progress: Progress<'_>,
) -> SnapshotResult<()> {
    charge(progress, 2, 0)?;
    meter_sort(sort, 0, progress)?;
    match term {
        TermData::Const(value) => meter_constant(value, progress),
        TermData::Var(name, _) => meter_string(name, progress),
        TermData::App(symbol, args) => {
            meter_symbol(symbol, progress)?;
            meter_vec(args, progress)
        }
        TermData::Let(bindings, _) => {
            meter_vec(bindings, progress)?;
            for (name, _) in bindings {
                meter_string(name, progress)?;
            }
            Ok(())
        }
        TermData::Forall(binders, _, triggers) | TermData::Exists(binders, _, triggers) => {
            meter_vec(binders, progress)?;
            for (name, sort) in binders {
                meter_string(name, progress)?;
                meter_sort(sort, 0, progress)?;
            }
            meter_vec(triggers, progress)?;
            for trigger in triggers {
                meter_vec(trigger, progress)?;
            }
            Ok(())
        }
        TermData::Not(_) | TermData::Ite(_, _, _) => Ok(()),
    }
}

pub(in crate::term) fn meter_sort(
    sort: &Sort,
    depth: usize,
    progress: Progress<'_>,
) -> SnapshotResult<()> {
    charge(progress, 2, 0)?;
    if depth > MAX_SNAPSHOT_SORT_DEPTH {
        return Err(TermSnapshotError::ResourceLimit);
    }
    match sort {
        Sort::Array(array) => {
            charge(progress, 1, size_of::<ArraySort>())?;
            meter_sort(&array.index_sort, depth + 1, progress)?;
            meter_sort(&array.element_sort, depth + 1, progress)
        }
        Sort::Seq(element) => {
            charge(progress, 1, size_of::<Sort>())?;
            meter_sort(element, depth + 1, progress)
        }
        Sort::Uninterpreted(name) | Sort::TypeVar(name) | Sort::FiniteDomain(name, _) => {
            meter_string(name, progress)
        }
        Sort::Datatype(datatype) => {
            meter_string(&datatype.name, progress)?;
            meter_vec::<DatatypeConstructor>(&datatype.constructors, progress)?;
            for constructor in &datatype.constructors {
                meter_string(&constructor.name, progress)?;
                meter_vec::<DatatypeField>(&constructor.fields, progress)?;
                for field in &constructor.fields {
                    meter_string(&field.name, progress)?;
                    meter_sort(&field.sort, depth + 1, progress)?;
                }
            }
            Ok(())
        }
        Sort::Bool
        | Sort::Int
        | Sort::Real
        | Sort::Complex
        | Sort::BitVec(_)
        | Sort::String
        | Sort::RegLan
        | Sort::FloatingPoint(_, _)
        | Sort::FiniteField(_)
        | Sort::Char => Ok(()),
    }
}

#[cfg(test)]
#[allow(clippy::panic)]
mod tests;

#[cfg(test)]
mod clone_tests;
