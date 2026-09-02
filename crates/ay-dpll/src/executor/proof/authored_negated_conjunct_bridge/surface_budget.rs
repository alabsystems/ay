// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Iterative admission for terms sent to recursive arithmetic recognizers.

use ay_core::{Constant, TermData, TermId, TermStore};

const MAX_SURFACE_ROOTS: usize = 256;
const MAX_SURFACE_NODES: usize = 8_192;
const MAX_SURFACE_DEPTH: usize = 64;
const MAX_SURFACE_ARITY: usize = 16;
const MAX_NUMERIC_BITS: u64 = 4_096;
const MAX_TOTAL_NUMERIC_BITS: u64 = 16_384;
const MAX_SYMBOL_TOKEN_BYTES: usize = 16 * 1024;
const MAX_TOTAL_SYMBOL_BYTES: usize = 64 * 1024;

pub(super) fn surfaces_admitted(terms: &TermStore, roots: &[TermId]) -> bool {
    if roots.len() > MAX_SURFACE_ROOTS || roots.len() > MAX_SURFACE_NODES {
        return false;
    }
    let mut stack: Vec<(TermId, usize)> = roots.iter().map(|&root| (root, 0)).collect();
    let mut visits = 0usize;
    let mut numeric_bits = 0u64;
    let mut symbol_bytes = 0usize;
    while let Some((term, depth)) = stack.pop() {
        visits += 1;
        if visits > MAX_SURFACE_NODES || depth > MAX_SURFACE_DEPTH {
            return false;
        }
        let remaining = MAX_SURFACE_NODES.saturating_sub(visits.saturating_add(stack.len()));
        match terms.get(term) {
            TermData::Const(constant) => {
                let bits = match constant {
                    Constant::Bool(_) => 1,
                    Constant::Int(value) => value.bits().max(1),
                    Constant::Rational(value) => {
                        let Some(bits) = value.0.numer().bits().checked_add(value.0.denom().bits())
                        else {
                            return false;
                        };
                        bits.max(1)
                    }
                    _ => return false,
                };
                if bits > MAX_NUMERIC_BITS {
                    return false;
                }
                let Some(total) = numeric_bits.checked_add(bits) else {
                    return false;
                };
                if total > MAX_TOTAL_NUMERIC_BITS {
                    return false;
                }
                numeric_bits = total;
            }
            TermData::Var(name, _) => {
                if !spend_symbol_bytes(&mut symbol_bytes, name) {
                    return false;
                }
            }
            TermData::App(symbol, args) => {
                if !spend_symbol_bytes(&mut symbol_bytes, symbol.name()) {
                    return false;
                }
                if args.len() > MAX_SURFACE_ARITY || args.len() > remaining {
                    return false;
                }
                stack.extend(args.iter().map(|&child| (child, depth + 1)));
            }
            TermData::Not(inner) => {
                if remaining == 0 {
                    return false;
                }
                stack.push((*inner, depth + 1));
            }
            // Arithmetic proof planning has no checked authority for binders,
            // local definitions, or conditionals. Reject them before a lower
            // recursive parser can inspect an unmetered surface.
            TermData::Let(..) | TermData::Ite(..) | TermData::Forall(..) | TermData::Exists(..) => {
                return false
            }
            _ => return false,
        }
    }
    true
}

fn spend_symbol_bytes(total: &mut usize, symbol: &str) -> bool {
    if symbol.len() > MAX_SYMBOL_TOKEN_BYTES {
        return false;
    }
    let Some(next) = total.checked_add(symbol.len()) else {
        return false;
    };
    if next > MAX_TOTAL_SYMBOL_BYTES {
        return false;
    }
    *total = next;
    true
}

#[cfg(test)]
mod tests {
    use ay_core::{Sort, Symbol};
    use num_bigint::BigInt;
    use num_rational::BigRational;

    use super::*;

    #[test]
    fn deep_or_wide_arithmetic_surfaces_fail_closed() {
        let mut terms = TermStore::new();
        let zero = terms.mk_int(0.into());
        let mut deep = zero;
        for _ in 0..=MAX_SURFACE_DEPTH {
            deep = terms.mk_app(Symbol::named("+"), [deep, zero], Sort::Int);
        }
        assert!(!surfaces_admitted(&terms, &[deep]));

        let wide = terms.mk_app(
            Symbol::named("+"),
            vec![zero; MAX_SURFACE_ARITY + 1],
            Sort::Int,
        );
        assert!(!surfaces_admitted(&terms, &[wide]));
    }

    #[test]
    fn numeric_payload_bit_boundary_is_exact_for_int_and_rational() {
        let mut terms = TermStore::new();
        let int_at_cap = terms.mk_int(BigInt::from(1) << (MAX_NUMERIC_BITS - 1));
        let int_above_cap = terms.mk_int(BigInt::from(1) << MAX_NUMERIC_BITS);
        assert!(surfaces_admitted(&terms, &[int_at_cap]));
        assert!(!surfaces_admitted(&terms, &[int_above_cap]));

        // Rational payload counts numerator plus denominator bits. A power of
        // two with denominator one makes the exact and +1 boundary explicit.
        let rational_at_cap = terms.mk_rational(BigRational::new(
            BigInt::from(1) << (MAX_NUMERIC_BITS - 2),
            BigInt::from(1),
        ));
        let rational_above_cap = terms.mk_rational(BigRational::new(
            BigInt::from(1) << (MAX_NUMERIC_BITS - 1),
            BigInt::from(1),
        ));
        assert!(surfaces_admitted(&terms, &[rational_at_cap]));
        assert!(!surfaces_admitted(&terms, &[rational_above_cap]));
    }

    #[test]
    fn symbol_payload_boundaries_are_exact_per_token_and_in_aggregate() {
        let mut terms = TermStore::new();
        let at_token_cap = terms.mk_var("v".repeat(MAX_SYMBOL_TOKEN_BYTES), Sort::Int);
        let above_token_cap = terms.mk_var("v".repeat(MAX_SYMBOL_TOKEN_BYTES + 1), Sort::Int);
        assert!(surfaces_admitted(&terms, &[at_token_cap]));
        assert!(!surfaces_admitted(&terms, &[above_token_cap]));

        let exact_root_count = MAX_TOTAL_SYMBOL_BYTES / MAX_SYMBOL_TOKEN_BYTES;
        assert_eq!(
            exact_root_count * MAX_SYMBOL_TOKEN_BYTES,
            MAX_TOTAL_SYMBOL_BYTES
        );
        assert!(surfaces_admitted(
            &terms,
            &vec![at_token_cap; exact_root_count]
        ));
        assert!(!surfaces_admitted(
            &terms,
            &vec![at_token_cap; exact_root_count + 1]
        ));
    }
}
