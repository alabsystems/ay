// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Exact source theorem for guarded `bv2nat` carrier bounds.

use std::collections::HashSet;

use ay_core::{Sort, TermData, TermId, TermStore};
use num_bigint::BigInt;
use num_traits::{One, Zero};

use super::{int_constant, is_int_var, named_app, BvLiaUnsatAuthenticationError, QueryChecker};

impl QueryChecker<'_> {
    /// Prove the exact guarded carrier contradiction emitted for a symbolic
    /// sequence length, without enumerating its (possibly 64-bit) BV witness.
    ///
    /// Accepted source shape, modulo equality/disjunction operand order:
    ///
    /// ```text
    /// A:  0 <= len
    /// B:  len = bv2nat(index) OR not A
    /// C:  not A OR not (len <= limit)
    /// ```
    ///
    /// Here `index : BitVec(w)`, `1 <= w <= 64`, and
    /// `limit >= 2^w - 1`. From A and B, `len = bv2nat(index)`; SMT-LIB's
    /// unsigned conversion semantics gives `len <= 2^w - 1 <= limit`, while A
    /// and C give `not (len <= limit)`. Thus the exact authored conjunction is
    /// inconsistent.
    ///
    /// This is deliberately a source theorem, not a production bridge replay:
    /// every premise must be one of the exact roots supplied to this checker,
    /// the shared guard is matched by TermId, and the carrier maximum is
    /// recomputed from the checked source sort. Missing/mismatched guards,
    /// lengths, pins, widths, bounds, or polarity decline fail-closed.
    pub(super) fn has_guarded_bv2nat_range_contradiction(
        &mut self,
        assertions: &[TermId],
    ) -> Result<bool, BvLiaUnsatAuthenticationError> {
        let mut active_lower_guards = HashSet::new();
        active_lower_guards
            .try_reserve(assertions.len())
            .map_err(|_| BvLiaUnsatAuthenticationError::ResourceLimit {
                resource: "guarded bv2nat lower-guard allocation",
            })?;
        let mut pins = Vec::new();
        pins.try_reserve(assertions.len()).map_err(|_| {
            BvLiaUnsatAuthenticationError::ResourceLimit {
                resource: "guarded bv2nat pin allocation",
            }
        })?;
        let mut exclusions = Vec::new();
        exclusions.try_reserve(assertions.len()).map_err(|_| {
            BvLiaUnsatAuthenticationError::ResourceLimit {
                resource: "guarded bv2nat exclusion allocation",
            }
        })?;

        for &assertion in assertions {
            self.meter.charge(1)?;
            if nonnegative_int_variable(self.terms, assertion).is_some() {
                active_lower_guards.insert(assertion);
            }
            if let Some(pin) = guarded_bv2nat_pin(self.terms, assertion) {
                pins.push(pin);
            }
            if let Some(exclusion) = guarded_int_upper_exclusion(self.terms, assertion) {
                exclusions.push(exclusion);
            }
        }

        for &(lower, len, width) in &pins {
            if !active_lower_guards.contains(&lower) {
                continue;
            }
            for &(excluded_lower, excluded_len, limit_term) in &exclusions {
                self.meter.charge(1)?;
                if lower != excluded_lower || len != excluded_len {
                    continue;
                }
                let Some(limit) = int_constant(self.terms, limit_term) else {
                    continue;
                };
                self.ensure_integer_magnitude(limit)?;
                let carrier_max = (BigInt::one() << width) - BigInt::one();
                self.ensure_integer_magnitude(&carrier_max)?;
                self.charge_integer_comparison(limit, &carrier_max)?;
                if limit >= &carrier_max {
                    return Ok(true);
                }
            }
        }
        Ok(false)
    }
}

/// Match the exact canonical lower guard `0 <= integer_variable`.
fn nonnegative_int_variable(terms: &TermStore, term: TermId) -> Option<TermId> {
    let (name, args) = named_app(terms, term)?;
    if name != "<=" || args.len() != 2 || int_constant(terms, args[0])? != &BigInt::zero() {
        return None;
    }
    is_int_var(terms, args[1]).then_some(args[1])
}

/// Match `(len = bv2nat(index)) OR not (0 <= len)` and return the exact
/// lower-guard root, length variable, and source carrier width.
fn guarded_bv2nat_pin(terms: &TermStore, term: TermId) -> Option<(TermId, TermId, u32)> {
    let (name, args) = named_app(terms, term)?;
    if name != "or" || args.len() != 2 {
        return None;
    }
    for (&guard_literal, &pin_literal) in [(&args[0], &args[1]), (&args[1], &args[0])] {
        let TermData::Not(lower) = terms.get(guard_literal) else {
            continue;
        };
        let Some(len) = nonnegative_int_variable(terms, *lower) else {
            continue;
        };
        let Some((eq_name, eq_args)) = named_app(terms, pin_literal) else {
            continue;
        };
        if eq_name != "=" || eq_args.len() != 2 {
            continue;
        }
        let nat = if eq_args[0] == len {
            eq_args[1]
        } else if eq_args[1] == len {
            eq_args[0]
        } else {
            continue;
        };
        let Some((nat_name, nat_args)) = named_app(terms, nat) else {
            continue;
        };
        if nat_name != "bv2nat" || nat_args.len() != 1 || terms.sort(nat) != &Sort::Int {
            continue;
        }
        let Sort::BitVec(width) = terms.sort(nat_args[0]) else {
            continue;
        };
        if width.width > 0 && width.width <= 64 {
            return Some((*lower, len, width.width));
        }
    }
    None
}

/// Match `not (0 <= len) OR not (len <= integer_constant)` and return the
/// shared lower guard, length variable, and upper-limit term.
fn guarded_int_upper_exclusion(
    terms: &TermStore,
    term: TermId,
) -> Option<(TermId, TermId, TermId)> {
    let (name, args) = named_app(terms, term)?;
    if name != "or" || args.len() != 2 {
        return None;
    }
    for (&guard_literal, &upper_literal) in [(&args[0], &args[1]), (&args[1], &args[0])] {
        let TermData::Not(lower) = terms.get(guard_literal) else {
            continue;
        };
        let Some(len) = nonnegative_int_variable(terms, *lower) else {
            continue;
        };
        let TermData::Not(upper) = terms.get(upper_literal) else {
            continue;
        };
        let Some((upper_name, upper_args)) = named_app(terms, *upper) else {
            continue;
        };
        if upper_name == "<="
            && upper_args.len() == 2
            && upper_args[0] == len
            && int_constant(terms, upper_args[1]).is_some()
        {
            return Some((*lower, len, upper_args[1]));
        }
    }
    None
}

#[cfg(test)]
mod tests {
    use ay_core::{Sort, TermStore};
    use num_bigint::BigInt;
    use num_traits::{One, Zero};

    use super::super::authenticate_bv_lia_unsat_query;

    #[test]
    fn symbolic_carrier_range_authenticates_without_wide_enumeration() {
        for width in [8, 64] {
            let mut terms = TermStore::new();
            let len = terms.mk_var(format!("guarded_carrier_len_{width}"), Sort::Int);
            let index = terms.mk_var(
                format!("guarded_carrier_index_{width}"),
                Sort::bitvec(width),
            );
            let nat = terms.mk_bv2nat(index);
            let zero = terms.mk_int(BigInt::zero());
            let max = terms.mk_int((BigInt::one() << width) - BigInt::one());
            let lower = terms.mk_le(zero, len);
            let equality = terms.mk_eq(nat, len);
            let not_lower = terms.mk_not_raw(lower);
            let guarded_pin = terms.mk_or(vec![not_lower, equality]);
            let upper = terms.mk_le(len, max);
            let not_upper = terms.mk_not_raw(upper);
            let out_of_range = terms.mk_or(vec![not_upper, not_lower]);

            authenticate_bv_lia_unsat_query(&terms, &[lower, guarded_pin, out_of_range], None)
                .unwrap_or_else(|error| {
                    panic!("width-{width} guarded carrier contradiction must authenticate: {error}")
                });
        }
    }

    #[test]
    fn symbolic_carrier_range_schema_rejects_near_misses() {
        let mut terms = TermStore::new();
        let len = terms.mk_var("guarded_near_miss_len", Sort::Int);
        let other_len = terms.mk_var("guarded_near_miss_other_len", Sort::Int);
        let index = terms.mk_var("guarded_near_miss_index", Sort::bitvec(8));
        let nat = terms.mk_bv2nat(index);
        let zero = terms.mk_int(BigInt::zero());
        let below_max = terms.mk_int(BigInt::from(254_u16));

        let lower = terms.mk_le(zero, len);
        let not_lower = terms.mk_not_raw(lower);
        let pin_equality = terms.mk_eq(len, nat);
        let guarded_pin = terms.mk_or(vec![pin_equality, not_lower]);
        let too_tight_upper = terms.mk_le(len, below_max);
        let not_too_tight_upper = terms.mk_not_raw(too_tight_upper);
        let satisfiable_exclusion = terms.mk_or(vec![not_lower, not_too_tight_upper]);
        authenticate_bv_lia_unsat_query(&terms, &[lower, guarded_pin, satisfiable_exclusion], None)
            .expect_err("index=255 witnesses a bound below the carrier maximum");

        let max = terms.mk_int(BigInt::from(255_u16));
        let other_lower = terms.mk_le(zero, other_len);
        let not_other_lower = terms.mk_not_raw(other_lower);
        let other_upper = terms.mk_le(other_len, max);
        let not_other_upper = terms.mk_not_raw(other_upper);
        let unrelated_exclusion = terms.mk_or(vec![not_other_lower, not_other_upper]);
        authenticate_bv_lia_unsat_query(&terms, &[lower, guarded_pin, unrelated_exclusion], None)
            .expect_err("an exclusion for a different integer cannot close the carrier theorem");

        let incorrectly_guarded_pin = terms.mk_or(vec![pin_equality, lower]);
        let upper = terms.mk_le(len, max);
        let not_upper = terms.mk_not_raw(upper);
        let exact_exclusion = terms.mk_or(vec![not_lower, not_upper]);
        authenticate_bv_lia_unsat_query(
            &terms,
            &[lower, incorrectly_guarded_pin, exact_exclusion],
            None,
        )
        .expect_err("the guarded schema must not accept a differently shaped pin");
    }
}
