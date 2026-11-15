// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Exact lowering of native-API `^` applications at the assertion boundary.
//!
//! [`Solver::try_power`] builds a structural `(^ base exponent)` application so
//! the term keeps its public shape (the Z3 C API reports and prints it as a
//! power). The SMT-LIB path never lets such a node reach the executor: the
//! elaborator unfolds a literal integer exponent into a product and rejects
//! every other exponent. The native path must give the engine the same
//! semantics, or the executor would decide `^` as an uninterpreted function
//! (measured through the Z3 C API: `x^2 = 2 ∧ x > 0` answered `sat` with
//! `x = 1/2`, and `xi = 2^xi` answered `sat` with `xi = 0`).
//!
//! This pass rewrites, inside the asserted term only, every `^` whose exponent
//! is a literal integer `n >= 1` into the `n`-fold product of its base — the
//! same unfolding the elaborator performs, and exact under every reading of
//! `^` (SMT-LIB's partial `^` and Z3's agree on positive integer exponents).
//! A symbolic, zero, negative or non-integral exponent is left in place: the
//! executor's capability gate refuses any surviving `^` with `unknown`, so it
//! can never be decided as an uninterpreted function. (`0^0` and `0^-n` are
//! deliberately not lowered: Z3 treats them as unspecified values, not `1`.)

use ay_core::kani_compat::{det_hash_set_new, DetHashSet};
use ay_core::term::Symbol;
use ay_core::{Sort, TermData, TermId};
use num_bigint::BigInt;
use num_traits::{One, ToPrimitive};

use crate::api::Solver;

/// Exponents up to this size unfold into one flat product, so the arithmetic
/// normalizer sees `x * x * ... * x` (the elaborator's threshold).
const FLAT_PRODUCT_LIMIT: u32 = 32;

/// Exponents with more bits than this are left for the capability gate: the
/// squaring chain stays logarithmic, but such a power has no practical use.
const MAX_EXPONENT_BITS: u64 = 64;

/// Upper bound on substitution rounds. Each round removes the innermost
/// remaining layer of nested lowerable powers, so this bounds the nesting depth
/// that is lowered; a deeper residue simply stays for the capability gate.
const MAX_ROUNDS: usize = 64;

impl Solver {
    /// Lower every native `^` with a literal positive integer exponent in
    /// `root` (see the module docs). Returns `root` itself when it contains no
    /// lowerable power, so assertions without `^` are untouched.
    pub(super) fn lower_native_integer_powers(&mut self, root: TermId) -> TermId {
        let mut current = root;
        for _ in 0..MAX_ROUNDS {
            let powers = self.lowerable_powers(current);
            if powers.is_empty() {
                break;
            }
            let mut from = Vec::with_capacity(powers.len());
            let mut to = Vec::with_capacity(powers.len());
            for (power, base, exponent) in powers {
                from.push(power);
                let product = self.positive_power_product(base, &exponent);
                // Z3 types every power as `Real` (see `Solver::try_power`): an
                // `Int` base unfolds to an integer product, lifted to `Real` so
                // the replacement keeps the power's sort.
                let lifted = if self.terms().sort(power) == &Sort::Real
                    && self.terms().sort(base) == &Sort::Int
                {
                    self.terms_mut().mk_to_real(product)
                } else {
                    product
                };
                to.push(lifted);
            }
            current = self.terms_mut().substitute(current, &from, &to);
        }
        current
    }

    /// Every `(^ base n)` in the DAG under `root` with a literal integer
    /// exponent `1 <= n` of at most [`MAX_EXPONENT_BITS`] bits.
    fn lowerable_powers(&self, root: TermId) -> Vec<(TermId, TermId, BigInt)> {
        let terms = self.terms();
        let mut found = Vec::new();
        let mut seen: DetHashSet<TermId> = det_hash_set_new();
        let mut pending = vec![root];
        while let Some(term) = pending.pop() {
            if !seen.insert(term) {
                continue;
            }
            if let TermData::App(Symbol::Named(name), args) = terms.get(term) {
                if name == "^" && args.len() == 2 {
                    if let Some(exponent) = terms.extract_integer_constant(args[1]) {
                        if exponent >= BigInt::one() && exponent.bits() <= MAX_EXPONENT_BITS {
                            found.push((term, args[0], exponent));
                        }
                    }
                }
            }
            pending.extend(terms.children(term));
        }
        found
    }

    /// `base^n` for `n >= 1` as a product: flat for small `n`, otherwise by
    /// repeated squaring (logarithmic term size), mirroring the elaborator.
    fn positive_power_product(&mut self, base: TermId, exponent: &BigInt) -> TermId {
        let terms = self.terms_mut();
        if let Some(n) = exponent.to_u32() {
            if n <= FLAT_PRODUCT_LIMIT {
                return terms.mk_mul(vec![base; n as usize]);
            }
        }
        let mut result: Option<TermId> = None;
        let mut square = base;
        let bits = exponent.bits();
        for i in 0..bits {
            if exponent.bit(i) {
                result = Some(match result {
                    Some(product) => terms.mk_mul(vec![product, square]),
                    None => square,
                });
            }
            if i + 1 < bits {
                square = terms.mk_mul(vec![square, square]);
            }
        }
        // `exponent >= 1` has a set bit, so `result` is always populated.
        result.unwrap_or(base)
    }
}
