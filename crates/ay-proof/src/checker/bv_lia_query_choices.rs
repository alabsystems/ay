// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Independent finite-choice covers for the exact original source query.

use ay_core::TermId;
use num_bigint::BigInt;

use super::{
    named_app, two_args, var_const_pair, BvLiaUnsatAuthenticationError, IntClasses, QueryChecker,
    MAX_TERM_NODES,
};

impl<'a> QueryChecker<'a> {
    /// Every leaf of this positive OR must equate the same original Int
    /// variable to a constant. Only after checking the whole disjunction may
    /// its interval hull constrain that variable. Gaps (including zero) stay
    /// in the hull; every assignment still checks the complete original roots.
    pub(super) fn record_int_choice_bound(
        &mut self,
        assertion: TermId,
        classes: &mut IntClasses,
    ) -> Result<(), BvLiaUnsatAuthenticationError> {
        self.meter.charge(1)?;
        let mut pending = Vec::new();
        pending
            .try_reserve_exact(1)
            .map_err(|_| BvLiaUnsatAuthenticationError::ResourceLimit {
                resource: "integer-choice traversal allocation",
            })?;
        pending.push(assertion);
        let mut hull: Option<(TermId, &'a BigInt, &'a BigInt)> = None;
        while let Some(term) = pending.pop() {
            self.meter.charge(1)?;
            let Some((name, args)) = named_app(self.terms, term) else {
                return Ok(());
            };
            if name == "or" {
                let length = pending.len().checked_add(args.len()).ok_or(
                    BvLiaUnsatAuthenticationError::ResourceLimit {
                        resource: "integer-choice traversal nodes",
                    },
                )?;
                if length > MAX_TERM_NODES {
                    return Err(BvLiaUnsatAuthenticationError::ResourceLimit {
                        resource: "integer-choice traversal nodes",
                    });
                }
                // Prepay copied edges and bound this one additional scratch
                // vector within the existing 100k-node/128MiB envelope.
                self.meter
                    .charge(u64::try_from(args.len()).unwrap_or(u64::MAX))?;
                pending.try_reserve_exact(args.len()).map_err(|_| {
                    BvLiaUnsatAuthenticationError::ResourceLimit {
                        resource: "integer-choice traversal allocation",
                    }
                })?;
                pending.extend_from_slice(args);
                continue;
            }
            if name != "=" {
                return Ok(());
            }
            let Some((first, second)) = two_args(args) else {
                return Ok(());
            };
            let Some((var, value)) = var_const_pair(self.terms, first, second) else {
                return Ok(());
            };
            self.ensure_integer_magnitude(value)?;
            hull = Some(match hull {
                None => (var, value, value),
                Some((previous, lo, hi)) if previous == var => {
                    self.charge_integer_comparison(lo, value)?;
                    let lo = if value < lo { value } else { lo };
                    self.charge_integer_comparison(hi, value)?;
                    let hi = if value > hi { value } else { hi };
                    (var, lo, hi)
                }
                Some(_) => return Ok(()),
            });
        }
        let Some((var, lo, hi)) = hull else {
            return Ok(());
        };
        let Some(class) = classes.class_of.get(&var).copied() else {
            return Ok(());
        };
        self.tighten_lower_bound_from_ref(&mut classes.bounds[class], lo)?;
        self.tighten_upper_bound_from_ref(&mut classes.bounds[class], hi)?;
        Ok(())
    }
}

#[cfg(test)]
#[path = "bv_lia_query_choices_tests.rs"]
mod tests;
