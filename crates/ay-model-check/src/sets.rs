// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! SMT-LIB finite-set operations, computed from the membership carrier.
//!
//! # Why this exists
//!
//! `set.card` and `set.subset` were the last two INTERPRETED operators the
//! gate's audit found reaching the uninterpreted-function path, where the
//! solver's own answer is adopted. `(= (set.card s) 3)` was confirmed because
//! the solver said so, without counting anything.
//!
//! # The representation
//!
//! A set of sort `(Set T)` is modelled on the membership carrier
//! `(Array T Bool)`, and `(set.member e s)` elaborates to `(select s e)`. So a
//! set value arrives here as [`ArrayValue`]: a default plus a finite list of
//! `index -> Bool` overrides, newest winning.
//!
//! That representation is exactly decidable for both operations as long as the
//! reasoning about the indices NOT in either store is kept honest — outside the
//! stores every index takes the default, so the defaults decide that whole
//! region in one step. Where that region's SIZE matters, the caller supplies it
//! as a [`DomainSize`]: `a ⊄ b` when `a` defaults to member and `b` does not
//! holds exactly when an index outside both stores exists, which is a fact
//! about the element sort rather than about either value. An unknown domain
//! (an uninterpreted element sort) is refused rather than guessed.

use num_bigint::BigInt;

use crate::{array_select, value_eq, ArrayValue, ModelValue};

/// How many values the set's ELEMENT sort has.
///
/// Both operations need it in exactly one place each: to decide whether an
/// index outside every override exists. The value alone cannot say — a
/// `(default, finite-store)` array is the same shape over `Int` as over
/// `(_ BitVec 1)` — so the caller, which has the term and therefore its sort,
/// supplies it.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum DomainSize {
    /// Infinitely many elements, so an unoverridden index always exists.
    Infinite,
    /// Exactly this many elements.
    Finite(BigInt),
    /// Not determined by the sort — an uninterpreted sort has whatever
    /// cardinality the model gives it. Fails closed.
    Unknown,
}

impl DomainSize {
    /// Whether some index is overridden by NEITHER store, given how many
    /// distinct indices between them are.
    fn has_index_beyond(&self, overridden: usize) -> Option<bool> {
        match self {
            Self::Infinite => Some(true),
            Self::Finite(n) => Some(*n > BigInt::from(overridden)),
            Self::Unknown => None,
        }
    }
}

fn as_set(value: &ModelValue) -> Result<&ArrayValue, String> {
    match value {
        ModelValue::Array(a) => Ok(a.as_ref()),
        _ => Err("expected a set value".to_string()),
    }
}

fn as_bool(value: &ModelValue) -> Result<bool, String> {
    value
        .as_bool()
        .ok_or_else(|| "set membership must be boolean".to_string())
}

/// The distinct indices either store overrides.
///
/// Deduplicated with [`value_eq`], the same equality the reads use, so an index
/// written twice is counted once. An incomparable pair is an error, never a
/// silent "different" — two indices wrongly treated as distinct would inflate a
/// cardinality.
fn overridden_indices(sets: &[&ArrayValue]) -> Result<Vec<ModelValue>, String> {
    let mut out: Vec<ModelValue> = Vec::new();
    for set in sets {
        for (index, _) in &set.store {
            let mut seen = false;
            for known in &out {
                if value_eq(known, index)? {
                    seen = true;
                    break;
                }
            }
            if !seen {
                out.push(index.clone());
            }
        }
    }
    Ok(out)
}

/// `(set.card s)`: how many elements `s` has.
///
/// A set whose DEFAULT is membership holds every index the store does not
/// exclude. Over an infinite element sort that is not a natural number and the
/// count is refused; over a finite one it is the domain size less the
/// exclusions. Returning the override count there would be a confidently wrong
/// small number.
pub fn card(value: &ModelValue, domain: &DomainSize) -> Result<ModelValue, String> {
    let set = as_set(value)?;
    let overridden = overridden_indices(&[set])?;
    if as_bool(&set.default)? {
        let DomainSize::Finite(size) = domain else {
            return Err("set.card of a set with a membership default is not finite".to_string());
        };
        let mut excluded = BigInt::from(0u8);
        for index in &overridden {
            if !as_bool(&array_select(set, index)?)? {
                excluded += 1u8;
            }
        }
        return Ok(ModelValue::Int(size - excluded));
    }
    let mut count = 0u64;
    for index in overridden {
        if as_bool(&array_select(set, &index)?)? {
            count += 1;
        }
    }
    Ok(ModelValue::Int(BigInt::from(count)))
}

/// `(set.subset a b)`: is every element of `a` an element of `b`?
pub fn subset(a: &ModelValue, b: &ModelValue, domain: &DomainSize) -> Result<ModelValue, String> {
    let (a, b) = (as_set(a)?, as_set(b)?);
    let (a_default, b_default) = (as_bool(&a.default)?, as_bool(&b.default)?);
    let overridden = overridden_indices(&[a, b])?;
    if a_default && !b_default {
        // Outside both stores every index is in `a` and in neither `b`, so any
        // such index refutes the subset. Whether one exists is a fact about the
        // element sort, not about either value.
        let Some(beyond) = domain.has_index_beyond(overridden.len()) else {
            return Err("set.subset over a domain of unknown size is undecided".to_string());
        };
        if beyond {
            return Ok(ModelValue::Bool(false));
        }
    }
    // Everywhere outside the stores, membership in `a` now implies membership
    // in `b`, so only the overridden indices are left to check.
    for index in overridden {
        if as_bool(&array_select(a, &index)?)? && !as_bool(&array_select(b, &index)?)? {
            return Ok(ModelValue::Bool(false));
        }
    }
    Ok(ModelValue::Bool(true))
}

/// Evaluate a set operation over already-evaluated operands.
pub fn eval(name: &str, args: &[ModelValue], domain: &DomainSize) -> Result<ModelValue, String> {
    match (name, args) {
        ("set.card", [s]) => card(s, domain),
        ("set.subset", [a, b]) => subset(a, b, domain),
        _ => Err(format!("unsupported set operation {name}")),
    }
}

/// Whether [`eval`] handles `name` at this arity.
#[must_use]
pub fn handles(name: &str, arity: usize) -> bool {
    matches!((name, arity), ("set.card", 1) | ("set.subset", 2))
}

#[cfg(test)]
#[path = "sets_tests.rs"]
mod tests;
