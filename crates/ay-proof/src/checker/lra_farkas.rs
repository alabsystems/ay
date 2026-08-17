// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Strict-mode semantic validation for `TheoryLemmaKind::LraFarkas` proof steps.
//!
//! Converts proof-clause (blocking clause) polarity into theory-conflict polarity,
//! then delegates to the shared full or progress-metered Farkas validator.

use std::mem::size_of;

use ay_core::{FarkasAnnotation, ProofId, TermData, TermId, TermStore, TheoryLit};
use num_traits::Zero;

use super::ProofCheckError;

#[derive(Clone, Copy, PartialEq, Eq)]
enum ProgressPath {
    PureInequality,
    AffineEqualityDisequality,
}

pub(crate) fn uses_progress_metered_path(
    terms: &TermStore,
    clause: &[TermId],
    farkas: Option<&FarkasAnnotation>,
) -> bool {
    progress_path(terms, clause, farkas).is_some()
}

fn progress_path(
    terms: &TermStore,
    clause: &[TermId],
    farkas: Option<&FarkasAnnotation>,
) -> Option<ProgressPath> {
    let Some(farkas) = farkas else {
        return None;
    };
    if farkas.coefficients.len() != clause.len() {
        return None;
    }
    if clause.iter().all(|&literal| {
        ay_core::proof_validation::farkas_conflict_literal_is_single_inequality(
            terms,
            &blocking_lit_to_conflict_lit(terms, literal),
        )
    }) {
        return Some(ProgressPath::PureInequality);
    }

    let (mut equalities, mut disequalities) = (0usize, 0usize);
    for (&literal, coefficient) in clause.iter().zip(&farkas.coefficients) {
        let conflict = blocking_lit_to_conflict_lit(terms, literal);
        if coefficient.is_zero() {
            if !ay_core::proof_validation::farkas_conflict_literal_is_single_inequality(
                terms, &conflict,
            ) {
                return None;
            }
            continue;
        }
        match ay_core::proof_validation::farkas_progress_row_kind(terms, &conflict)? {
            ay_core::proof_validation::FarkasProgressRowKind::PositiveEquality => {
                equalities = equalities.checked_add(1)?;
            }
            ay_core::proof_validation::FarkasProgressRowKind::Disequality => {
                disequalities = disequalities.checked_add(1)?;
            }
            ay_core::proof_validation::FarkasProgressRowKind::Inequality => return None,
        }
    }
    if equalities > 0 && disequalities == 1 {
        Some(ProgressPath::AffineEqualityDisequality)
    } else {
        None
    }
}

fn capacity_excess_bytes<T>(requested: usize, actual: usize) -> Result<usize, ProofCheckError> {
    actual
        .checked_sub(requested)
        .and_then(|excess| excess.checked_mul(size_of::<T>()))
        .ok_or(ProofCheckError::ResourceLimit)
}

fn reserve_conflict_vec(
    requested: usize,
    metered: bool,
    progress: &mut dyn FnMut(usize, usize) -> bool,
) -> Result<Vec<TheoryLit>, ProofCheckError> {
    let mut conflict = Vec::new();
    if metered {
        let bytes = requested
            .checked_mul(size_of::<TheoryLit>())
            .ok_or(ProofCheckError::ResourceLimit)?;
        if !progress(requested, bytes) {
            return Err(ProofCheckError::ResourceLimit);
        }
    }
    conflict
        .try_reserve_exact(requested)
        .map_err(|_| ProofCheckError::ResourceLimit)?;
    let excess = if metered {
        capacity_excess_bytes::<TheoryLit>(requested, conflict.capacity())?
    } else {
        0
    };
    if !progress(0, excess) {
        return Err(ProofCheckError::ResourceLimit);
    }
    Ok(conflict)
}

/// Validate a blocking-clause Farkas lemma under a caller-owned envelope.
pub(crate) fn validate_metered(
    terms: &TermStore,
    step_id: ProofId,
    clause: &[TermId],
    farkas: Option<&FarkasAnnotation>,
    progress: &mut dyn FnMut(usize, usize) -> bool,
) -> Result<(), ProofCheckError> {
    let farkas = farkas.ok_or_else(|| ProofCheckError::InvalidTheoryLemma {
        step: step_id,
        reason: "LraFarkas in strict mode requires a Farkas annotation".to_string(),
    })?;

    let progress_path = progress_path(terms, clause, Some(farkas));
    let mut conflict = reserve_conflict_vec(clause.len(), progress_path.is_some(), progress)?;
    conflict.extend(
        clause
            .iter()
            .map(|&lit| blocking_lit_to_conflict_lit(terms, lit)),
    );
    if !progress(0, 0) {
        return Err(ProofCheckError::ResourceLimit);
    }

    let result = match progress_path {
        Some(ProgressPath::PureInequality) => {
            ay_core::proof_validation::verify_pure_inequality_farkas_with_progress(
                terms, &conflict, farkas, progress,
            )
        }
        Some(ProgressPath::AffineEqualityDisequality) => {
            ay_core::proof_validation::verify_affine_equality_farkas_with_progress(
                terms, &conflict, farkas, progress,
            )
        }
        None => {
            ay_core::proof_validation::verify_farkas_conflict_lits_full(terms, &conflict, farkas)
        }
    };
    result.map_err(|error| {
        if matches!(
            &error,
            ay_core::proof_validation::FarkasValidationError::ResourceLimit
        ) {
            ProofCheckError::ResourceLimit
        } else {
            ProofCheckError::InvalidTheoryLemma {
                step: step_id,
                reason: error.to_string(),
            }
        }
    })
}

/// Convert a blocking-clause literal to the corresponding conflict `TheoryLit`.
///
/// - `¬(atom)` in the blocking clause → conflict literal `atom = true`
/// - `atom` in the blocking clause → conflict literal `atom = false`
fn blocking_lit_to_conflict_lit(terms: &TermStore, lit: TermId) -> TheoryLit {
    match terms.get(lit) {
        TermData::Not(inner) => TheoryLit {
            term: *inner,
            value: true,
        },
        _ => TheoryLit {
            term: lit,
            value: false,
        },
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use ay_core::{Sort, Symbol};

    fn affine_span_fixture() -> (TermStore, Vec<TermId>, FarkasAnnotation) {
        let mut terms = TermStore::new();
        let zero = terms.mk_int(0.into());
        let x = terms.mk_var("farkas_meter_span_x", Sort::Int);
        let equality = terms.mk_eq(x, zero);
        let not_equality = terms.mk_not_raw(equality);
        (
            terms,
            vec![equality, not_equality],
            FarkasAnnotation::from_ints(&[1, 1]),
        )
    }

    #[test]
    fn conflict_vec_charges_its_actual_capacity_and_post_reserve_poll() {
        let (mut charged_bytes, mut polls) = (0usize, 0usize);
        let conflict = reserve_conflict_vec(3, true, &mut |_, bytes| {
            charged_bytes = charged_bytes.checked_add(bytes).expect("test charge fits");
            polls += 1;
            true
        })
        .expect("small conflict allocation succeeds");
        assert_eq!(charged_bytes, conflict.capacity() * size_of::<TheoryLit>());
        assert!(
            polls >= 2,
            "pre-reserve charge and post-reserve poll are required"
        );
        assert_eq!(
            capacity_excess_bytes::<TheoryLit>(3, 2),
            Err(ProofCheckError::ResourceLimit)
        );
    }

    #[test]
    fn checker_meter_accepts_exact_total_and_refuses_one_unit_short() {
        let (terms, clause, farkas) = affine_span_fixture();
        let (mut total_work, mut total_bytes) = (0usize, 0usize);
        validate_metered(
            &terms,
            ProofId(0),
            &clause,
            Some(&farkas),
            &mut |work, bytes| {
                total_work = total_work.checked_add(work).expect("test work fits");
                total_bytes = total_bytes.checked_add(bytes).expect("test bytes fit");
                true
            },
        )
        .expect("unbounded checker accepts the contradiction");

        let (mut work_left, mut bytes_left) = (total_work, total_bytes);
        validate_metered(
            &terms,
            ProofId(0),
            &clause,
            Some(&farkas),
            &mut |work, bytes| {
                let (Some(work), Some(bytes)) =
                    (work_left.checked_sub(work), bytes_left.checked_sub(bytes))
                else {
                    return false;
                };
                work_left = work;
                bytes_left = bytes;
                true
            },
        )
        .expect("the exact checker envelope accepts");
        assert_eq!((work_left, bytes_left), (0, 0));

        for limit_bytes in [false, true] {
            let limit = if limit_bytes { total_bytes } else { total_work };
            let mut used = 0usize;
            let error = validate_metered(
                &terms,
                ProofId(0),
                &clause,
                Some(&farkas),
                &mut |work, bytes| {
                    let charge = if limit_bytes { bytes } else { work };
                    let Some(next) = used.checked_add(charge) else {
                        return false;
                    };
                    if next >= limit {
                        return false;
                    }
                    used = next;
                    true
                },
            )
            .expect_err("one-unit-short checker envelope must refuse");
            assert_eq!(error, ProofCheckError::ResourceLimit);
        }
    }

    #[test]
    fn progress_path_selects_only_proved_pure_or_affine_span_shapes() {
        let mut terms = TermStore::new();
        let zero = terms.mk_int(0.into());
        let x = terms.mk_var("farkas_meter_x", Sort::Int);
        let y = terms.mk_var("farkas_meter_y", Sort::Int);
        let inequality = terms.mk_le(x, zero);
        let equality = terms.mk_app(Symbol::named("="), [x, y], Sort::Bool);
        let not_inequality = terms.mk_not_raw(inequality);
        let not_equality = terms.mk_not_raw(equality);

        let pure = FarkasAnnotation::from_ints(&[1]);
        assert!(uses_progress_metered_path(
            &terms,
            &[not_inequality],
            Some(&pure)
        ));

        let equality_is_zero_weight = FarkasAnnotation::from_ints(&[1, 0]);
        assert!(!uses_progress_metered_path(
            &terms,
            &[not_inequality, not_equality],
            Some(&equality_is_zero_weight)
        ));

        let affine_span = FarkasAnnotation::from_ints(&[1, 1]);
        assert!(uses_progress_metered_path(
            &terms,
            &[equality, not_equality],
            Some(&affine_span)
        ));
        assert!(!uses_progress_metered_path(
            &terms,
            &[equality, not_equality],
            Some(&FarkasAnnotation::from_ints(&[0, 1]))
        ));
        assert!(!uses_progress_metered_path(
            &terms,
            &[equality, equality],
            Some(&affine_span)
        ));
        let second_disequality = validate_metered(
            &terms,
            ProofId(7),
            &[equality, equality],
            Some(&affine_span),
            &mut |_, _| true,
        )
        .expect_err("the full fallback refuses a second weighted disequality");
        assert!(matches!(
            second_disequality,
            ProofCheckError::InvalidTheoryLemma { reason, .. }
                if reason.contains("disequality literal")
        ));
        assert!(!uses_progress_metered_path(
            &terms,
            &[equality, not_equality, not_inequality],
            Some(&FarkasAnnotation::from_ints(&[1, 1, 1]))
        ));

        let opaque = terms.mk_app(Symbol::named("metered_opaque"), [x], Sort::Int);
        let opaque_equality = terms.mk_eq(opaque, y);
        let not_opaque_equality = terms.mk_not_raw(opaque_equality);
        assert!(!uses_progress_metered_path(
            &terms,
            &[opaque_equality, not_opaque_equality],
            Some(&affine_span)
        ));

        let opaque_inequality = terms.mk_le(opaque, y);
        let not_opaque_inequality = terms.mk_not_raw(opaque_inequality);
        assert!(uses_progress_metered_path(
            &terms,
            &[equality, not_equality, not_opaque_inequality],
            Some(&FarkasAnnotation::from_ints(&[1, 1, 0]))
        ));
    }
}
