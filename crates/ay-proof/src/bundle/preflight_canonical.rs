// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Borrowed canonical-entry index for the caller-metered snapshot preflight.
//!
//! Structural validation must precede insertion. This index grants no proof
//! authority, follows no term handles, and never rewrites an input entry.

use std::collections::hash_map::DefaultHasher;
use std::collections::{btree_map, BTreeMap};
use std::hash::{Hash, Hasher};

use super::*;

mod meter;
mod payload;
mod rational;
#[cfg(test)]
mod tests;

use meter::CanonicalMeter;

type Progress<'a> = &'a mut dyn FnMut(usize, usize) -> bool;

struct CanonicalEntry<'a> {
    data: &'a TermData,
    sort: &'a Sort,
    data_work: usize,
    sort_work: usize,
}

pub(super) struct CanonicalEntries<'a> {
    buckets: BTreeMap<u64, Vec<CanonicalEntry<'a>>>,
    // RationalWrapper hashes raw numerator/denominator but compares numeric
    // values. Keeping ALL rationals together avoids assuming reduced encoding
    // or calling Ratio's recursively dividing Eq/Hash implementations.
    rationals: Vec<CanonicalEntry<'a>>,
}

impl<'a> CanonicalEntries<'a> {
    pub(super) fn new() -> Self {
        Self {
            buckets: BTreeMap::new(),
            rationals: Vec::new(),
        }
    }

    /// Return false for an equal complete `(TermData, Sort)` entry. Every
    /// refusal precedes publication of the candidate into this index; scratch
    /// capacity may grow, but cancellation never creates a duplicate record.
    pub(super) fn insert(
        &mut self,
        data: &'a TermData,
        sort: &'a Sort,
        progress: Progress<'_>,
    ) -> Result<bool, ProofCheckError> {
        let mut meter = CanonicalMeter::new(progress);
        meter.charge(0, 0)?;
        let data_work = payload::data(data, &mut meter)?;
        let sort_work = payload::sort(sort, &mut meter, 0)?;
        let candidate = CanonicalEntry {
            data,
            sort,
            data_work,
            sort_work,
        };
        if let TermData::Const(Constant::Rational(value)) = data {
            meter.charge(1, 0)?;
            if value.0.denom().sign() == Sign::NoSign {
                meter.charge(64, 64)?;
                return Err(malformed_bundle(
                    "rational canonical entry has a zero denominator",
                ));
            }
            return insert_bucket(&mut self.rationals, candidate, &mut meter);
        }

        meter.charge(meter::add(data_work, sort_work)?, 0)?;
        let mut hasher = DefaultHasher::new();
        data.hash(&mut hasher);
        sort.hash(&mut hasher);
        let fingerprint = hasher.finish();
        let entries = self.buckets.len();
        meter.map_lookup(entries)?;
        match self.buckets.entry(fingerprint) {
            btree_map::Entry::Occupied(mut bucket) => {
                insert_bucket(bucket.get_mut(), candidate, &mut meter)
            }
            btree_map::Entry::Vacant(bucket) => {
                let mut values = Vec::new();
                meter.vector_room(&mut values)?;
                values.push(candidate);
                meter.map_entry::<(u64, Vec<CanonicalEntry<'a>>)>(entries)?;
                meter.charge(0, 0)?;
                bucket.insert(values);
                Ok(true)
            }
        }
    }
}

fn insert_bucket<'a>(
    bucket: &mut Vec<CanonicalEntry<'a>>,
    candidate: CanonicalEntry<'a>,
    meter: &mut CanonicalMeter<'_>,
) -> Result<bool, ProofCheckError> {
    for existing in bucket.iter() {
        meter.charge(1, 0)?;
        if entries_equal(existing, &candidate, meter)? {
            meter.charge(0, 0)?;
            return Ok(false);
        }
    }
    meter.vector_room(bucket)?;
    meter.charge(0, 0)?;
    bucket.push(candidate);
    Ok(true)
}

fn entries_equal(
    left: &CanonicalEntry<'_>,
    right: &CanonicalEntry<'_>,
    meter: &mut CanonicalMeter<'_>,
) -> Result<bool, ProofCheckError> {
    meter.charge(meter::add(left.sort_work, right.sort_work)?, 0)?;
    if left.sort != right.sort {
        return Ok(false);
    }
    match (left.data, right.data) {
        (TermData::Const(Constant::Rational(left)), TermData::Const(Constant::Rational(right))) => {
            rational::equal(&left.0, &right.0, meter)
        }
        // Defensive separation: never dispatch a rational into derived Eq,
        // even if a future bucket change introduces mixed collision entries.
        (TermData::Const(Constant::Rational(_)), _)
        | (_, TermData::Const(Constant::Rational(_))) => Ok(false),
        _ => {
            meter.charge(meter::add(left.data_work, right.data_work)?, 0)?;
            Ok(left.data == right.data)
        }
    }
}

/// Compare borrowed complete entries under the same payload/rational pricing
/// used by snapshot canonicalization. This follows no term handles and cannot
/// turn serialized ids into source authority.
pub(super) fn borrowed_entries_equal(
    left: (&TermData, &Sort),
    right: (&TermData, &Sort),
    progress: Progress<'_>,
) -> Result<bool, ProofCheckError> {
    let mut meter = CanonicalMeter::new(progress);
    let left = CanonicalEntry {
        data: left.0,
        sort: left.1,
        data_work: payload::data(left.0, &mut meter)?,
        sort_work: payload::sort(left.1, &mut meter, 0)?,
    };
    let right = CanonicalEntry {
        data: right.0,
        sort: right.1,
        data_work: payload::data(right.0, &mut meter)?,
        sort_work: payload::sort(right.1, &mut meter, 0)?,
    };
    entries_equal(&left, &right, &mut meter)
}
