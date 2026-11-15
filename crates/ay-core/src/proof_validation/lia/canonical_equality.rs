// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// Textually included by `lia.rs` so the canonical equality helpers remain in
// the validator's private namespace.

fn canonical_int_equality(
    terms: &TermStore,
    lhs: TermId,
    rhs: TermId,
) -> Option<(
    std::collections::BTreeMap<TermId, num_bigint::BigInt>,
    num_bigint::BigInt,
)> {
    use num_traits::Signed;
    let (coeffs, c0) = int_linear_diff(terms, lhs, rhs)?;
    let flip = coeffs
        .values()
        .next()
        .is_some_and(num_bigint::BigInt::is_negative);
    if flip {
        Some((coeffs.into_iter().map(|(v, c)| (v, -c)).collect(), c0))
    } else {
        Some((coeffs, -c0))
    }
}

/// For a guarded arithmetic disequality split whose guard is PRIMITIVE
/// ([`arith_disequality_split_has_primitive_guard`]), whether the guard's own
/// forward order `(<= lhs rhs)` runs AGAINST the branch form; `None` when
/// `clause` is not such a split.
///
/// `canonical_int_equality` normalizes the guard's sign before the primitive
/// test compares it with the branch form `C_b`, so both `(= C_b T_b)` and
/// `(= T_b C_b)` are primitive guards. The guard's RAW difference
/// `lhs - rhs` is then `C_b - T_b` (`Some(false)`: `(<= lhs rhs)` reads
/// `C_b <= T_b`, the integer complement of the SECOND branch
/// `C_b >= T_b + 1`) or `T_b - C_b` (`Some(true)`: it reads `C_b >= T_b`, the
/// complement of the FIRST branch `C_b <= T_b - 1`). An external lowering that
/// pairs each order of the guard's operands with the branch it excludes must
/// read this, never assume the forward reading. A `Real` split is admitted
/// only in the forward order, so it is always `Some(false)`.
#[must_use]
pub fn arith_disequality_split_primitive_guard_is_reversed(
    terms: &TermStore,
    clause: &[TermId],
) -> Option<bool> {
    use crate::term::{Symbol, TermData};
    use crate::Sort;
    if !arith_disequality_split_has_primitive_guard(terms, clause) {
        return None;
    }
    let [first, _, guard] = clause else {
        return None;
    };
    let TermData::App(Symbol::Named(name), args) = terms.get(*guard) else {
        return None;
    };
    let [lhs, rhs] = args.as_slice() else {
        return None;
    };
    if name != "=" {
        return None;
    }
    if matches!(terms.sort(*lhs), Sort::Real) {
        return Some(false);
    }
    let (raw, _) = int_linear_diff(terms, *lhs, *rhs)?;
    let (branch, _, _) = parse_int_comparison(terms, *first, true)?;
    if raw == branch {
        return Some(false);
    }
    let negated: std::collections::BTreeMap<TermId, num_bigint::BigInt> =
        branch.into_iter().map(|(var, c)| (var, -c)).collect();
    (raw == negated).then_some(true)
}
