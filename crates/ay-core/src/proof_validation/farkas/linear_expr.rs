// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// Textually included by `farkas.rs` to preserve the private linear-expression
// representation used throughout certificate validation.

#[derive(Debug, Clone)]
pub(crate) struct LinearExpr {
    pub(crate) coeffs: BTreeMap<TermId, BigRational>,
    pub(crate) constant: BigRational,
}

impl LinearExpr {
    fn zero() -> Self {
        Self {
            coeffs: BTreeMap::new(),
            constant: BigRational::zero(),
        }
    }

    fn constant(c: BigRational) -> Self {
        Self {
            coeffs: BTreeMap::new(),
            constant: c,
        }
    }

    fn var(v: TermId) -> Self {
        let mut coeffs = BTreeMap::new();
        coeffs.insert(v, BigRational::one());
        Self {
            coeffs,
            constant: BigRational::zero(),
        }
    }

    fn is_constant(&self) -> bool {
        self.coeffs.is_empty()
    }

    pub(crate) fn negate(&mut self) {
        self.constant = -self.constant.clone();
        for coeff in self.coeffs.values_mut() {
            *coeff = -coeff.clone();
        }
    }

    fn scale(&mut self, scale: &BigRational) {
        if scale.is_zero() {
            self.coeffs.clear();
            self.constant = BigRational::zero();
            return;
        }
        if scale.is_one() {
            return;
        }

        self.constant = &self.constant * scale;
        for coeff in self.coeffs.values_mut() {
            *coeff = &*coeff * scale;
        }
    }

    pub(crate) fn add_scaled(&mut self, other: &Self, scale: &BigRational) {
        if scale.is_zero() {
            return;
        }
        // `λ = ±1` is the overwhelmingly common multiplier: every certificate
        // built as `FarkasAnnotation::from_ints(&vec![1; n])` (the producer
        // default across `ay-dpll`) and every `+`/`-` node walked by
        // `parse_linear_expr` lands here. `1·x` and `(-1)·x` are EXACT on
        // `BigRational` — the type is kept in lowest terms with a positive
        // denominator, so the product is bit-for-bit the operand (resp. its
        // negation) — and `add_expr`/`sub_expr` are defined as exactly those
        // two cases. Taking them skips a BigInt gcd plus two divisions per
        // coefficient, which `Ratio::mul` performs to re-reduce a fraction
        // that was already reduced.
        if scale.denom().is_one() {
            if scale.numer().is_one() {
                self.add_expr(other);
                return;
            }
            if scale.numer().is_negative() && scale.numer().magnitude().is_one() {
                // `scale` is exactly `-1`.
                self.sub_expr(other);
                return;
            }
        }

        self.constant += scale * &other.constant;
        for (var, coeff) in &other.coeffs {
            let should_remove = {
                let entry = self.coeffs.entry(*var).or_insert_with(BigRational::zero);
                *entry += scale * coeff;
                entry.is_zero()
            };
            if should_remove {
                self.coeffs.remove(var);
            }
        }
    }

    /// `self += other`, with the scale already folded into `other`.
    ///
    /// Identical to `add_scaled(other, 1)` but without the per-coefficient
    /// `BigRational` multiplication (a bigint gcd + two divisions each). The
    /// orientation search adds the SAME λ-scaled row millions of times, so the
    /// multiplication belongs in the one-time plan build, not the inner loop.
    fn add_expr(&mut self, other: &Self) {
        self.constant += &other.constant;
        for (var, coeff) in &other.coeffs {
            let should_remove = {
                let entry = self.coeffs.entry(*var).or_insert_with(BigRational::zero);
                *entry += coeff;
                entry.is_zero()
            };
            if should_remove {
                self.coeffs.remove(var);
            }
        }
    }

    /// Exact inverse of [`LinearExpr::add_expr`].
    ///
    /// `coeffs` is canonical — a key is present exactly when its running total
    /// is non-zero — so `add_expr(e)` followed by `sub_expr(e)` restores both
    /// the map and the constant bit-for-bit. That is what lets the orientation
    /// search backtrack in place instead of cloning the accumulator per node.
    fn sub_expr(&mut self, other: &Self) {
        self.constant -= &other.constant;
        for (var, coeff) in &other.coeffs {
            let should_remove = {
                let entry = self.coeffs.entry(*var).or_insert_with(BigRational::zero);
                *entry -= coeff;
                entry.is_zero()
            };
            if should_remove {
                self.coeffs.remove(var);
            }
        }
    }
}
