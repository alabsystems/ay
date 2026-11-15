// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Optional witnesses only: native clause/query authority is never replaced.

use ay_core::term::TermData;
use ay_core::{FarkasAnnotation, Proof, ProofStep, TermId, TermStore, TheoryLemmaKind, TheoryLit};
use num_rational::Rational64;
use num_traits::CheckedAdd;
use std::mem::size_of;

/// Work and cumulative scratch words spend the SAME enclosing assembly count.
/// The callback still checks cancellation/deadline/memory share. No local
/// allowance is opened, and neither failed work nor scratch is refunded.
fn charge(stopped: &dyn Fn() -> bool, work: usize, bytes: usize) -> bool {
    let word = size_of::<usize>();
    let Some(words) = bytes.checked_add(word - 1).map(|n| n / word) else {
        return false;
    };
    let Some(visits) = work.checked_add(words) else {
        return false;
    };
    if visits == 0 {
        return !stopped();
    }
    (0..visits).all(|_| !stopped())
}

fn reserve_vec<T>(values: &mut Vec<T>, additional: usize, stopped: &dyn Fn() -> bool) -> bool {
    let Some(required) = values.len().checked_add(additional) else {
        return false;
    };
    if required <= values.capacity() {
        return charge(stopped, 0, 0);
    }
    let Some(bytes) = required.checked_mul(size_of::<T>()) else {
        return false;
    };
    if !charge(stopped, values.len(), bytes) || values.try_reserve_exact(additional).is_err() {
        return false;
    }
    let Some(excess) = values
        .capacity()
        .checked_sub(required)
        .and_then(|n| n.checked_mul(size_of::<T>()))
    else {
        return false;
    };
    charge(stopped, 0, excess)
}

fn multiset_key(clause: &[TermId], stopped: &dyn Fn() -> bool) -> Option<Vec<TermId>> {
    let count = clause.len();
    let work = count
        .checked_mul(count)?
        .checked_add(count.checked_mul(3)?)?;
    if !charge(stopped, work, 0) {
        return None;
    }
    let mut key = Vec::new();
    if !reserve_vec(&mut key, count, stopped) {
        return None;
    }
    key.extend_from_slice(clause);
    key.sort_unstable();
    Some(key)
}

/// Fixed-width arithmetic and fallible vectors replace the unmetered
/// clone/BTreeMap/Vec rebind. Duplicate weights are summed with CheckedAdd;
/// overflow or a refused allocation simply supplies no metadata.
fn rebind_fallible(
    source: &[TermId],
    target: &[TermId],
    annotation: &FarkasAnnotation,
    stopped: &dyn Fn() -> bool,
) -> Option<FarkasAnnotation> {
    if source.len() != annotation.coefficients.len() {
        return None;
    }
    for coefficient in &annotation.coefficients {
        if !charge(stopped, 1, 0) || *coefficient.denom() <= 0 {
            return None;
        }
    }
    let mut rebound = Vec::new();
    if !reserve_vec(&mut rebound, target.len(), stopped) {
        return None;
    }
    if !charge(stopped, source.len(), 0) {
        return None;
    }
    if source == target {
        for coefficient in &annotation.coefficients {
            if !charge(stopped, 1, 0) {
                return None;
            }
            rebound.push(*coefficient);
        }
        return Some(FarkasAnnotation::new(rebound));
    }
    for (index, target_literal) in target.iter().enumerate() {
        if !charge(stopped, index, 0) {
            return None;
        }
        let mut value = Rational64::from_integer(0);
        if !target[..index].contains(target_literal) {
            for (source_literal, coefficient) in source.iter().zip(&annotation.coefficients) {
                if !charge(stopped, 1, 0) {
                    return None;
                }
                if source_literal == target_literal {
                    // Ratio<i64> checked addition is allocation-free; fund
                    // its bounded integer/GCD scratch before performing it.
                    if !charge(stopped, 128, 4 * size_of::<Rational64>()) {
                        return None;
                    }
                    value = value.checked_add(coefficient)?;
                }
            }
        }
        if !charge(stopped, 1, 0) {
            return None;
        }
        rebound.push(value);
    }
    Some(FarkasAnnotation::new(rebound))
}

fn valid_full_annotation(
    terms: &TermStore,
    clause: &[TermId],
    annotation: &FarkasAnnotation,
    stopped: &dyn Fn() -> bool,
) -> bool {
    if annotation.coefficients.len() != clause.len() {
        return false;
    }
    let mut conflict = Vec::new();
    if !reserve_vec(&mut conflict, clause.len(), stopped) {
        return false;
    }
    for &literal in clause {
        if !charge(stopped, 1, 0) || literal.index() >= terms.len() {
            return false;
        }
        conflict.push(match terms.get(literal) {
            TermData::Not(inner) => TheoryLit::new(*inner, true),
            _ => TheoryLit::new(literal, false),
        });
    }
    ay_core::proof_validation::farkas_conflict_lits_full_holds_with_progress(
        terms,
        &conflict,
        annotation,
        &mut |work, bytes| charge(stopped, work, bytes),
    )
    .unwrap_or(false)
}

/// A separate constructive producer, not a relaxed interpretation of a hint.
/// It uses the exact CURRENT ordered whole clause and returns only after the
/// Core path has replayed its explicit positional branch coefficients. The
/// same enclosing assembly owner pays all work/scratch and the final publish
/// check below remains mandatory. Native clause/query authority is untouched.
fn derive_current_affine_annotation(
    terms: &TermStore,
    clause: &[TermId],
    stopped: &dyn Fn() -> bool,
) -> Option<FarkasAnnotation> {
    let mut conflict = Vec::new();
    if !reserve_vec(&mut conflict, clause.len(), stopped) {
        return None;
    }
    for &literal in clause {
        if !charge(stopped, 1, 0) || literal.index() >= terms.len() {
            return None;
        }
        conflict.push(match terms.get(literal) {
            TermData::Not(inner) => TheoryLit::new(*inner, true),
            _ => TheoryLit::new(literal, false),
        });
    }
    ay_core::proof_validation::derive_affine_equality_farkas_with_progress(
        terms,
        &conflict,
        &mut |work, bytes| charge(stopped, work, bytes),
    )
    .ok()
    .flatten()
}

struct Hint<'a> {
    key: Vec<TermId>,
    clause: &'a [TermId],
    annotation: &'a FarkasAnnotation,
}

fn collect_hints<'a>(
    terms: &TermStore,
    source: &'a Proof,
    stopped: &dyn Fn() -> bool,
) -> Option<Vec<Hint<'a>>> {
    let mut rows = 0;
    for step in &source.steps {
        if !charge(stopped, 1, 0) {
            return None;
        }
        if matches!(
            step,
            ProofStep::TheoryLemma {
                farkas: Some(_),
                lia: None,
                ..
            }
        ) {
            rows += 1;
        }
    }
    if rows == 0 {
        return None;
    }
    let mut hints = Vec::new();
    if !reserve_vec(&mut hints, rows, stopped) {
        return None;
    }
    for step in &source.steps {
        if !charge(stopped, 1, 0) {
            return None;
        }
        let ProofStep::TheoryLemma {
            clause,
            farkas: Some(annotation),
            lia: None,
            ..
        } = step
        else {
            continue;
        };
        if annotation.coefficients.len() != clause.len() {
            continue;
        }
        let mut valid = true;
        for (&literal, coefficient) in clause.iter().zip(&annotation.coefficients) {
            if !charge(stopped, 1, 0) {
                return None;
            }
            valid &= literal.index() < terms.len() && *coefficient.denom() > 0;
        }
        if !valid {
            continue;
        }
        let key = multiset_key(clause, stopped)?;
        if !charge(stopped, 1, 0) {
            return None;
        }
        hints.push(Hint {
            key,
            clause,
            annotation,
        });
    }
    if hints.is_empty() {
        None
    } else {
        Some(hints)
    }
}

pub(super) fn retain_verified_farkas_annotations(
    terms: &TermStore,
    source: &Proof,
    target: &mut Proof,
    stopped: &dyn Fn() -> bool,
) -> usize {
    let mut eligible = false;
    for step in &target.steps {
        if !charge(stopped, 1, 0) {
            return 0;
        }
        if matches!(
            step,
            ProofStep::TheoryLemma {
                kind: TheoryLemmaKind::ArithClauseTautology,
                farkas: None,
                lia: None,
                ..
            }
        ) {
            eligible = true;
            break;
        }
    }
    if !eligible {
        return 0;
    }
    let Some(hints) = collect_hints(terms, source, stopped) else {
        return 0;
    };
    let mut retained = 0;
    for step in &mut target.steps {
        if !charge(stopped, 1, 0) {
            return retained;
        }
        let ProofStep::TheoryLemma {
            kind: TheoryLemmaKind::ArithClauseTautology,
            clause,
            farkas,
            lia: None,
            ..
        } = step
        else {
            continue;
        };
        if farkas.is_some() {
            continue;
        }
        let Some(key) = multiset_key(clause, stopped) else {
            return retained;
        };
        for hint in &hints {
            let Some(comparison_work) = key.len().checked_add(1) else {
                return retained;
            };
            if !charge(stopped, comparison_work, 0) {
                return retained;
            }
            if hint.key != key {
                continue;
            }
            let Some(rebound) = rebind_fallible(hint.clause, clause, hint.annotation, stopped)
            else {
                continue;
            };
            let checked = if valid_full_annotation(terms, clause, &rebound, stopped) {
                Some(rebound)
            } else {
                derive_current_affine_annotation(terms, clause, stopped)
            };
            if let Some(checked) = checked.filter(|_| charge(stopped, 0, 0)) {
                *farkas = Some(checked);
                retained += 1;
                break;
            }
        }
    }
    retained
}

#[cfg(test)]
#[path = "farkas_metadata_tests.rs"]
mod tests;
