// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::encoding_control::EncodingControl;
use std::hash::Hash;
use std::mem::size_of;

pub(crate) fn storage(control: &EncodingControl) -> bool {
    control.counted_refuse(CountedAdmissionError::StorageExhausted);
    false
}

pub(crate) fn reserve<T>(values: &mut Vec<T>, extra: usize, control: &EncodingControl) -> bool {
    if !control.is_counted() {
        return true;
    }
    let Some(required) = values.len().checked_add(extra) else {
        return storage(control);
    };
    if required <= values.capacity() {
        return control.counted_admit(1, 0);
    }
    let Some(doubled) = values.capacity().checked_mul(2) else {
        return storage(control);
    };
    let target = required.max(doubled).max(4);
    let Some(bytes) = target.checked_mul(size_of::<T>()) else {
        return storage(control);
    };
    let Some(work) = target
        .checked_mul(2)
        .and_then(|n| n.checked_add(values.len()))
    else {
        return storage(control);
    };
    control.counted_admit(work, bytes)
        && values
            .try_reserve_exact(target - values.len())
            .map_or_else(|_| storage(control), |()| true)
}

pub(crate) fn map<K: Eq + Hash, V>(values: &mut HashMap<K, V>, control: &EncodingControl) -> bool {
    if !control.is_counted() {
        return true;
    }
    if !control.counted_admit(1, 0) {
        return false;
    }
    if values.len() < values.capacity() {
        return true;
    }
    let Some(target) = values.capacity().checked_mul(2).map(|n| n.max(4)) else {
        return storage(control);
    };
    let Some((work, bytes)) = table_growth::<(K, V)>(target, values.len()) else {
        return storage(control);
    };
    control.counted_admit(work, bytes)
        && values
            .try_reserve(target - values.len())
            .map_or_else(|_| storage(control), |()| true)
}

pub(crate) fn set<K: Eq + Hash>(values: &mut HashSet<K>, control: &EncodingControl) -> bool {
    if !control.is_counted() {
        return true;
    }
    if !control.counted_admit(1, 0) {
        return false;
    }
    if values.len() < values.capacity() {
        return true;
    }
    let Some(target) = values.capacity().checked_mul(2).map(|n| n.max(4)) else {
        return storage(control);
    };
    let Some((work, bytes)) = table_growth::<K>(target, values.len()) else {
        return storage(control);
    };
    control.counted_admit(work, bytes)
        && values
            .try_reserve(target - values.len())
            .map_or_else(|_| storage(control), |()| true)
}

fn table_growth<T>(target: usize, old_len: usize) -> Option<(usize, usize)> {
    // hashbrown's 7/8 load factor, power-of-two buckets, control bytes and
    // alignment slack. Charge all new buckets and old entries before rehash.
    let buckets = target
        .checked_mul(8)?
        .checked_div(7)?
        .checked_add(1)?
        .checked_next_power_of_two()?;
    let bytes = buckets
        .checked_mul(size_of::<T>().checked_add(1)?)?
        .checked_add(64)?;
    Some((buckets.checked_mul(2)?.checked_add(old_len)?, bytes))
}

impl BvSolver<'_> {
    pub(crate) fn counted_vec<T>(&self, len: usize) -> Option<Vec<T>> {
        if !self.encoding.is_counted() {
            return Some(Vec::with_capacity(len));
        }
        let bytes = len.checked_mul(size_of::<T>()).or_else(|| {
            storage(&self.encoding);
            None
        })?;
        let work = len.checked_add(1).or_else(|| {
            storage(&self.encoding);
            None
        })?;
        if !self.encoding.counted_admit(work, bytes) {
            return None;
        }
        let mut values = Vec::new();
        if values.try_reserve_exact(len).is_err() {
            storage(&self.encoding);
            return None;
        }
        Some(values)
    }

    pub(crate) fn counted_bits(&self, len: usize) -> Option<BvBits> {
        if !self.encoding.is_counted() {
            return Some(bits_with_capacity(len));
        }
        self.counted_vec(len)
    }

    pub(crate) fn counted_copy_bits(&self, bits: &[CnfLit]) -> Option<BvBits> {
        let mut copied = self.counted_bits(bits.len())?;
        copied.extend_from_slice(bits);
        Some(copied)
    }

    pub(crate) fn emit_clause(&mut self, literals: &[CnfLit]) {
        if !self.encoding.is_counted() {
            self.add_clause(CnfClause::new(literals.to_vec()));
            return;
        }
        if !self.encoding_complete() || !reserve(&mut self.clauses, 1, &self.encoding) {
            return;
        }
        let Some(copied) = self.counted_copy_bits(literals) else {
            return;
        };
        self.clauses.push(CnfClause::new(copied));
    }

    pub(crate) fn counted_fresh_range(&mut self, count: usize) -> BvFreshVarRange {
        let range = u32::try_from(count)
            .ok()
            .and_then(|count| self.next_var.checked_add(count).map(|end| (count, end)))
            .filter(|(_, end)| *end <= i32::MAX as u32 + 1);
        let Some((count, end)) = range else {
            self.encoding
                .counted_refuse(CountedAdmissionError::WorkExhausted);
            return BvFreshVarRange::new(1, 0);
        };
        if !self.encoding.counted_admit(count as usize + 1, 0) {
            return BvFreshVarRange::new(1, 0);
        }
        let first = self.next_var;
        self.next_var = end;
        BvFreshVarRange::new(first as CnfLit, count)
    }

    pub(crate) fn counted_fresh_bits(&mut self, width: usize) -> BvBits {
        let Some(mut bits) = self.counted_bits(width) else {
            return Vec::new();
        };
        let range = self.batch_fresh_vars(width);
        if !self.encoding_complete() {
            return Vec::new();
        }
        bits.extend(range.iter());
        bits
    }

    pub(crate) fn counted_unsupported(&self, why: &'static str) {
        self.encoding
            .counted_refuse(CountedAdmissionError::Original(
                ay_core::original_query::OriginalAdmissionError::Query(
                    ay_core::original_query::QueryError::Invalid(why),
                ),
            ));
    }

    pub(crate) fn counted_term_data(&self, term: TermId) -> Option<TermData> {
        let data = self.terms.get(term);
        if !self.encoding.is_counted() {
            return Some(data.clone());
        }
        let Some((work, bytes)) = self.counted_clone_fee(data) else {
            storage(&self.encoding);
            return None;
        };
        if !self.encoding.counted_admit(work, bytes) {
            return None;
        }
        Some(data.clone())
    }

    fn counted_clone_fee(&self, data: &TermData) -> Option<(usize, usize)> {
        Some(match data {
            TermData::Var(name, _) => (name.len(), name.len()),
            TermData::App(symbol, args) => {
                let indices = match symbol {
                    Symbol::Indexed(_, ids) => ids.len(),
                    _ => 0,
                };
                let entries = args.len().checked_add(indices)?;
                (
                    entries.checked_add(symbol.name().len())?,
                    args.len()
                        .checked_mul(size_of::<TermId>())?
                        .checked_add(indices.checked_mul(size_of::<u32>())?)?,
                )
            }
            TermData::Const(Constant::BitVec { value, .. }) => {
                let limbs = usize::try_from(value.bits().div_ceil(32)).ok()?;
                (limbs.checked_add(1)?, limbs.max(4).checked_mul(8)?)
            }
            TermData::Const(Constant::Bool(_)) | TermData::Not(_) | TermData::Ite(..) => (1, 0),
            _ => {
                self.counted_unsupported("unaccounted term clone");
                return None;
            }
        })
    }
}
