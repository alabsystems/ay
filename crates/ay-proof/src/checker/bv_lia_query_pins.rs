// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Exact source-bound `bv2nat(variable) = integer` assignments.

use std::collections::HashMap;

use ay_core::{Constant, Sort, Symbol, TermData, TermId, TermStore};
use num_bigint::BigInt;
use num_traits::{One, Signed, ToPrimitive};

use super::integer_evaluation::integer_limb_units;
use super::{BvLiaUnsatAuthenticationError, QueryChecker};

pub(super) struct PinnedBitVectors {
    pub(super) values: HashMap<TermId, (u64, u32)>,
    pub(super) contradictory: bool,
}

impl QueryChecker<'_> {
    /// Exact BV assignments forced by top-level `bv2nat(variable) = integer`
    /// roots. `bv2nat` is injective on one fixed-width carrier, so an in-range
    /// integer fixes the variable uniquely; an out-of-range or conflicting pin
    /// makes the source conjunction immediately inconsistent.
    pub(super) fn collect_pinned_bitvectors(
        &mut self,
        assertions: &[TermId],
    ) -> Result<PinnedBitVectors, BvLiaUnsatAuthenticationError> {
        let mut values = HashMap::new();
        for &assertion in assertions {
            self.meter.charge(1)?;
            if self.terms.sort(assertion) != &Sort::Bool {
                continue;
            }
            let TermData::App(Symbol::Named(name), args) = self.terms.get(assertion) else {
                continue;
            };
            if name != "=" || args.len() != 2 {
                continue;
            }
            let Some((variable, value, width)) = bv2nat_var_int_pair(self.terms, args) else {
                continue;
            };
            self.ensure_integer_magnitude(value)?;
            self.meter.charge(integer_limb_units(value))?;
            let Some(value) = in_range_bv_value(value, width) else {
                return Ok(PinnedBitVectors {
                    values,
                    contradictory: true,
                });
            };
            match values.get(&variable) {
                Some(&(existing, existing_width))
                    if existing != value || existing_width != width =>
                {
                    return Ok(PinnedBitVectors {
                        values,
                        contradictory: true,
                    });
                }
                Some(_) => {}
                None => {
                    values.insert(variable, (value, width));
                }
            }
        }
        Ok(PinnedBitVectors {
            values,
            contradictory: false,
        })
    }
}

fn bv2nat_variable(terms: &TermStore, term: TermId) -> Option<(TermId, u32)> {
    let TermData::App(Symbol::Named(name), args) = terms.get(term) else {
        return None;
    };
    if name != "bv2nat"
        || args.len() != 1
        || terms.sort(term) != &Sort::Int
        || !matches!(terms.get(args[0]), TermData::Var(..))
    {
        return None;
    }
    let Sort::BitVec(width) = terms.sort(args[0]) else {
        return None;
    };
    (width.width > 0 && width.width <= 64).then_some((args[0], width.width))
}

fn bv2nat_var_int_pair<'a>(
    terms: &'a TermStore,
    args: &[TermId],
) -> Option<(TermId, &'a BigInt, u32)> {
    if let Some((variable, width)) = bv2nat_variable(terms, args[0]) {
        int_constant(terms, args[1]).map(|value| (variable, value, width))
    } else if let Some((variable, width)) = bv2nat_variable(terms, args[1]) {
        int_constant(terms, args[0]).map(|value| (variable, value, width))
    } else {
        None
    }
}

fn int_constant(terms: &TermStore, term: TermId) -> Option<&BigInt> {
    if terms.sort(term) != &Sort::Int {
        return None;
    }
    match terms.get(term) {
        TermData::Const(Constant::Int(value)) => Some(value),
        _ => None,
    }
}

fn in_range_bv_value(value: &BigInt, width: u32) -> Option<u64> {
    if value.is_negative() || value >= &(BigInt::one() << width) {
        return None;
    }
    value.to_u64()
}
