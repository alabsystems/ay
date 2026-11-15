// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Exact typed arithmetic literals. No caller-selected operator, variable or sort
//! enters this path. The existing counted interner owns all dictionary growth.
use super::*;

impl<O: TermConstructionAdmission> CountedTermBuilder<'_, '_, O> {
    /// Build a typed integer product, folding numeric operands only after
    /// charging their occupied inputs, multiplication work and result scratch.
    pub fn integer_product(&mut self, left: TermId, right: TermId) -> Result<TermId> {
        self.owner.admit(1, 0)?;
        if self.store.sort(left) != &Sort::Int || self.store.sort(right) != &Sort::Int {
            return Err(CountedTermError::InvalidInput);
        }
        if let (TermData::Const(Constant::Int(a)), TermData::Const(Constant::Int(b))) =
            (self.store.get(left), self.store.get(right))
        {
            let product = numbers::multiply(a, b, self.owner)?;
            return self.integer(&product);
        }
        // BR_REWRITE_FULL also normalizes arithmetic in a generated power's
        // exponent. Flatten only unshadowed Int multiplication, preserving
        // opaque operands and combining coefficients with the same paid kernel.
        let mut pending = Vec::new();
        storage::reserve(&mut pending, 2, self.owner)?;
        pending.extend([right, left]);
        let mut factors = Vec::new();
        let mut coefficient = None;
        while let Some(id) = pending.pop() {
            self.owner.admit(1, 0)?;
            if self.store.sort(id) != &Sort::Int {
                return Err(CountedTermError::InvalidInput);
            }
            if matches!(self.store.get(id), TermData::Const(Constant::Int(_))) {
                coefficient = Some(match coefficient {
                    None => id,
                    Some(previous) => self.integer_product(previous, id)?,
                });
                continue;
            }
            if let TermData::App(Symbol::Named(head), args) = self.store.get(id) {
                self.owner.admit(head.len(), 0)?;
                if head == "*" && !self.store.is_declared_function(head) {
                    if args.len() < 2 {
                        return Err(CountedTermError::InvalidInput);
                    }
                    storage::reserve(&mut pending, args.len(), self.owner)?;
                    self.owner.admit(args.len(), 0)?;
                    pending.extend(args.iter().rev().copied());
                    continue;
                }
            }
            storage::reserve(&mut factors, 1, self.owner)?;
            factors.push(id);
        }
        if let Some(id) = coefficient {
            use num_traits::{One as _, Zero as _};
            let TermData::Const(Constant::Int(value)) = self.store.get(id) else {
                return Err(CountedTermError::InvalidInput);
            };
            payload::bigint(value, self.owner, PayloadUse::Inspect)?;
            if value.is_zero() || factors.is_empty() {
                self.owner.check()?;
                return Ok(id);
            }
            if !value.is_one() {
                storage::reserve(&mut factors, 1, self.owner)?;
                self.owner.admit(
                    factors
                        .len()
                        .checked_add(1)
                        .ok_or_else(|| storage::work(self.owner))?,
                    0,
                )?;
                factors.push(id);
                factors.rotate_right(1);
            }
        }
        if factors.len() == 1 {
            self.owner.check()?;
            return Ok(factors[0]);
        }
        let term = payload::named("*", &factors, self.owner)?;
        self.check_generated_head(&term)?;
        let result = self.intern_typed_data(term, Sort::Int, Some(false));
        self.owner.check()?;
        result
    }

    /// Copy an exact integer after pricing its complete arbitrary-precision
    /// payload against the original owner. No value-width cap or new allowance.
    pub fn integer(&mut self, value: &num_bigint::BigInt) -> Result<TermId> {
        payload::bigint(value, self.owner, PayloadUse::Copy)?;
        let term = TermData::Const(Constant::Int(value.clone()));
        let result = self.intern_typed_data(term, Sort::Int, Some(false));
        self.owner.check()?;
        result
    }

    /// Normalize an exact rational with Euclid's algorithm under this same
    /// owner. Raw/non-reduced ratios must not reach the numerator/denominator
    /// based native interning hash. Zero denominators refuse before copying.
    pub fn rational(&mut self, value: &num_rational::BigRational) -> Result<TermId> {
        use num_traits::Zero as _;
        self.owner.admit(1, 0)?;
        if value.denom().is_zero() {
            return Err(CountedTermError::InvalidInput);
        }
        payload::bigint(value.numer(), self.owner, PayloadUse::Copy)?;
        payload::bigint(value.denom(), self.owner, PayloadUse::Copy)?;
        let mut left = value.numer().magnitude().clone();
        let mut right = value.denom().magnitude().clone();
        while !right.is_zero() {
            division(left.bits(), right.bits(), self.owner)?;
            let remainder = &left % &right;
            self.owner.check()?;
            left = right;
            right = remainder;
        }
        // Moving the magnitude into a positive BigInt allocates no limb copy.
        let gcd = num_bigint::BigInt::from(left);
        division(value.numer().bits(), gcd.bits(), self.owner)?;
        let mut numerator = value.numer() / &gcd;
        self.owner.check()?;
        division(value.denom().bits(), gcd.bits(), self.owner)?;
        let mut denominator = value.denom() / &gcd;
        self.owner.check()?;
        if denominator.sign() == num_bigint::Sign::Minus {
            numerator = -numerator;
            denominator = -denominator;
        }
        let canonical = num_rational::BigRational::new_raw(numerator, denominator);
        let term = TermData::Const(Constant::Rational(canonical.into()));
        let result = self.intern_typed_data(term, Sort::Real, Some(false));
        self.owner.check()?;
        result
    }
}

fn division(left_bits: u64, right_bits: u64, owner: &dyn TermConstructionAdmission) -> Result<()> {
    let words = |bits: u64| {
        usize::try_from(bits.div_ceil(64))
            .map(|n| n.max(1))
            .map_err(|_| storage::work(owner))
    };
    let left = words(left_bits)?;
    let right = words(right_bits)?;
    // Logical schoolbook limb work and a conservative native quotient,
    // remainder and division-scratch envelope, prepaid before each operation.
    // This is not a claim to count allocator or CPU instructions.
    let work = left
        .checked_mul(right)
        .and_then(|n| n.checked_add(left))
        .and_then(|n| n.checked_add(right))
        .ok_or_else(|| storage::work(owner))?;
    let bytes = left
        .checked_add(right)
        .and_then(|n| n.checked_add(4))
        .and_then(|n| n.checked_mul(4 * size_of::<u64>()))
        .ok_or_else(|| storage::storage(owner))?;
    owner.admit(work, bytes)?;
    Ok(())
}
