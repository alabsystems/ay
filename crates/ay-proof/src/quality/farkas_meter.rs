// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Static complement to the progress-metered Farkas validator.

use super::{
    checked_mul_usize, PayloadStats, ProofCheckError, ProofStep, SemanticChargeClass, TermStore,
    TheoryLemmaKind,
};

pub(super) fn uses_progress_meter(step: &ProofStep, terms: &TermStore) -> bool {
    let ProofStep::TheoryLemma {
        clause,
        farkas,
        kind,
        lia,
        ..
    } = step
    else {
        return false;
    };
    let direct_farkas = *kind == TheoryLemmaKind::LraFarkas
        || (*kind == TheoryLemmaKind::LiaGeneric && lia.is_none());
    direct_farkas && crate::checker::farkas_uses_progress_meter(terms, clause, farkas.as_ref())
}

/// Byte factor for the FULL (non-progress) Farkas validator's a-priori
/// reservation.
///
/// `verify_farkas_conflict_lits_full` takes no progress callback, so this
/// pre-charge is its only meter and must upper-bound the validator's true
/// allocation. That allocation is LINEAR in the payload: the
/// `NormalizedConstraint` alternatives store one `(TermId, BigRational)`
/// monomial per source atom (<= 12x the atom's serialized bytes), the
/// disequality case split clones the alternatives twice (<= 36x), congruence
/// canonicalization rewrites in place, and the combination accumulator plus
/// i64/i64 lambda scaling add at most one more copy with bounded coefficient
/// growth (<= 24x). 128 covers the sum with headroom; nothing in the
/// validator is quadratic in the term DAG (`proof-meter-v3` doctrine: fix the
/// EXPONENT, keep the reservation).
const FARKAS_FULL_VALIDATOR_BYTE_FACTOR: usize = 128;

pub(super) fn polynomial_charge(
    payload: PayloadStats,
    class: SemanticChargeClass,
) -> Result<(usize, usize), ProofCheckError> {
    let square = checked_mul_usize(payload.unfolded_work, payload.unfolded_work)?;
    let cube = checked_mul_usize(square, payload.unfolded_work)?;
    let coefficient_work = checked_mul_usize(square, payload.work)?;
    let bytes = if class != SemanticChargeClass::ProgressFarkas {
        // Capped by the quadratic product it replaces, so no charge is ever
        // larger than before this fix — a proof that fit the envelope still
        // fits. The linear term is the validator's real bound; the quadratic
        // one billed a 28KB AUFLIA lemma 425MB and vetoed provable UNSATs.
        let linear = checked_mul_usize(payload.bytes, FARKAS_FULL_VALIDATOR_BYTE_FACTOR)?;
        let quadratic = checked_mul_usize(payload.bytes, square)?;
        linear.min(quadratic)
    } else {
        0
    };
    Ok((cube.max(coefficient_work), bytes))
}

#[cfg(test)]
mod tests {
    use super::super::authenticate_premise_clauses_strict_with_context_and_progress;
    use super::*;
    use ay_core::{FarkasAnnotation, Proof, Sort};

    fn quality_fixture() -> (TermStore, Proof) {
        let mut terms = TermStore::new();
        let zero = terms.mk_int(0.into());
        let x = terms.mk_var("quality_farkas_meter_x", Sort::Int);
        let equality = terms.mk_eq(x, zero);
        let not_equality = terms.mk_not_raw(equality);
        let mut proof = Proof::new();
        proof.add_theory_lemma_with_farkas_and_kind(
            "LIA",
            // Blocking clause negates the conflict `x != 0 && x = 0`.
            vec![equality, not_equality],
            FarkasAnnotation::from_ints(&[1, 1]),
            TheoryLemmaKind::LiaGeneric,
        );
        (terms, proof)
    }

    #[test]
    fn progress_path_removes_only_the_polynomial_byte_precharge() {
        let payload = PayloadStats {
            work: 1_321,
            bytes: 24_786,
            unfolded_work: 100,
            order_assignments: 46_656,
        };
        assert_eq!(
            polynomial_charge(payload, SemanticChargeClass::ProgressFarkas),
            Ok((13_210_000, 0))
        );
        assert_eq!(
            polynomial_charge(payload, SemanticChargeClass::General),
            // bytes: min(24_786 * 128, 24_786 * 100^2) — the linear
            // full-validator bound, capped by the legacy quadratic product.
            Ok((13_210_000, 3_172_608))
        );
    }

    #[test]
    fn quality_meter_accepts_exact_total_and_refuses_one_unit_short() {
        let (terms, proof) = quality_fixture();
        let (mut total_work, mut total_bytes) = (0usize, 0usize);
        authenticate_premise_clauses_strict_with_context_and_progress(
            &proof,
            &terms,
            None,
            None,
            &[],
            &mut |work, bytes| {
                total_work = total_work.checked_add(work).expect("test work fits");
                total_bytes = total_bytes.checked_add(bytes).expect("test bytes fit");
                true
            },
        )
        .expect("unbounded quality meter accepts the contradiction");

        let (mut work_left, mut bytes_left) = (total_work, total_bytes);
        authenticate_premise_clauses_strict_with_context_and_progress(
            &proof,
            &terms,
            None,
            None,
            &[],
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
        .expect("the exact quality envelope accepts");
        assert_eq!((work_left, bytes_left), (0, 0));

        for limit_bytes in [false, true] {
            let limit = if limit_bytes { total_bytes } else { total_work };
            let mut used = 0usize;
            let error = authenticate_premise_clauses_strict_with_context_and_progress(
                &proof,
                &terms,
                None,
                None,
                &[],
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
            .expect_err("one-unit-short quality envelope must refuse");
            assert_eq!(error, ProofCheckError::ResourceLimit);
        }
    }
}
