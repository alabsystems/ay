//! Implementation of [`PBConstraint`] for cardinality constraints.

use std::cmp::Ordering;

use malachite_bigint::BigInt;
use num_integer::Integer;
use num_traits::{One, Signed, Zero};

use crate::{
    clause::Clause,
    helper::{merge_from_lits, merge_in_situ_lits, quotient_by_oversized_divisor},
    lit::Lit,
    pb_constraint::{
        PBConstraint, PBConstraintEnum, PBConstraintGetter, WEAKEN_ALL_THRESHOLD,
        add_from_merged_terms, constraint_from_terms_and_coeff_sum,
    },
    prelude::*,
    substitution::Substitutable,
    to_pretty_string::ToPrettyString,
};

/// A cardinality is constraint has all cefficients 1 and the right-hand side can be any integer.
#[derive(Debug, Clone, Default, Hash, PartialEq, Eq)]
pub struct Cardinality {
    lits: Vec<Lit>,
    degree: i64,
}

/// `ceil(A / d)` for the degree `A` of a cardinality constraint and a divisor `d` of arbitrary
/// width, shared by all four of `d`, `c`, `n` and `m`.
///
/// The narrow branch is the hot one. The wide branch used to substitute `i64::MAX` for `d` and
/// divide by that, which is faithful only while `|A| < i64::MAX`: at `A == -i64::MAX` and at
/// `A == i64::MIN` it yields `-1` where the rule's quotient is `0`, so the checker stored a
/// strictly weaker constraint than the one the proof wrote down and then rejected the proof for
/// stating the true one. It is computed exactly now — see
/// [`quotient_by_oversized_divisor`], which also documents why the result always narrows back.
#[inline]
fn divide_degree(degree: i64, divisor: &BigInt) -> i64 {
    match TryInto::<i64>::try_into(divisor) {
        Ok(divisor) => Integer::div_ceil(&degree, &divisor),
        Err(_) => quotient_by_oversized_divisor(&degree, divisor),
    }
}

impl Cardinality {
    /// Set the right-hand side of [`Cardinality`] to `degree`.
    #[inline]
    pub fn set_degree(&mut self, degree: i64) {
        self.degree = degree;
    }

    /// Delete the term containing the [`VarIdx`] `var_idx` from the [`Cardinality`] constraint.
    #[inline]
    fn delete_term(&mut self, var_idx: VarIdx) -> i64 {
        if let Ok(index) = self
            .lits
            .binary_search_by(|lit| lit.get_var().cmp(&var_idx))
        {
            self.lits.remove(index);
            1
        } else {
            0
        }
    }

    /// Get the sum of the coefficients for [`Cardinality`].
    #[inline]
    fn get_coeff_sum(&self) -> i64 {
        self.len() as i64
    }

    /// Get the literals stored in [`Cardinality`] as a slice of [`Lit`].
    #[inline]
    pub fn as_slice(&self) -> &[Lit] {
        self.lits.as_slice()
    }

    /// Construct a [`Cardinality`] from [`Vec<Lit>`] terms and the right-hand side `degree`.
    #[inline]
    pub fn from_lits(lits: Vec<Lit>, degree: i64) -> Self {
        Cardinality { lits, degree }
    }

    /// Widen this constraint into the [`BigInt`] general representation, preserving its meaning.
    ///
    /// A [`Cardinality`] stores its degree in an [`i64`], so any rule that lowers the degree can
    /// underflow. Before the release profile enabled overflow checks such an underflow wrapped
    /// silently and turns a trivially true constraint into the empty contradiction, which is a
    /// universal proof forgery. All such rules therefore check the decrement and escalate to this
    /// representation instead.
    #[inline]
    fn widen_to_bigint(&self) -> GeneralPBConstraint<BigInt> {
        GeneralPBConstraint::from(self)
    }

    /// Apply the degree bookkeeping of a weakening step that removed `weaken_count` literals,
    /// escalating to [`BigInt`] if the decrement does not fit into [`i64`].
    #[inline]
    fn finish_weakening(&mut self, weaken_count: i64) -> Option<PBConstraintEnum> {
        match self.degree.checked_sub(weaken_count) {
            Some(degree) => {
                self.degree = degree;
                None
            }
            None => {
                let mut widened = self.widen_to_bigint();
                widened.set_degree(BigInt::from(self.degree) - BigInt::from(weaken_count));
                Some(widened.into_smallest_type())
            }
        }
    }

    /// The number of negated literals in this constraint.
    ///
    /// The variable-form rules move all negated literals to the right-hand side, which subtracts
    /// exactly this many units from the degree.
    #[inline]
    fn negated_lit_count(&self) -> i64 {
        self.lits.iter().filter(|lit| lit.is_negated()).count() as i64
    }
}

impl PBConstraintGetter for Cardinality {
    type CoeffType = i64;
    type TermType = Lit;

    #[inline]
    fn get_coeff_sum(&self) -> Self::CoeffType {
        self.lits.len() as i64
    }

    #[inline]
    fn get_degree(&self) -> &Self::CoeffType {
        &self.degree
    }

    #[inline]
    fn get_terms(&self) -> &Vec<Self::TermType> {
        &self.lits
    }

    #[inline]
    fn get_lits(&self) -> impl Iterator<Item = &Lit> {
        self.lits.iter()
    }
}

impl PBConstraint for Cardinality {
    #[inline]
    fn is_contradicting(&self) -> bool {
        self.degree > self.lits.len() as i64
    }

    #[inline]
    fn is_trivial(&self) -> bool {
        !self.degree.is_positive()
    }

    #[inline]
    fn saturate(&mut self) {
        if self.is_trivial() {
            self.lits.clear();
        }
    }

    #[inline]
    fn weaken(&mut self, var_idx: VarIdx) -> Option<PBConstraintEnum> {
        let weaken_count = self.delete_term(var_idx);
        // The degree decrement is checked and escalates to `BigInt` on underflow.
        self.finish_weakening(weaken_count)
    }

    #[inline]
    fn weaken_all(&mut self, mut var_idxs: Vec<VarIdx>) -> Option<PBConstraintEnum> {
        if var_idxs.len() <= WEAKEN_ALL_THRESHOLD {
            // Weaken all variables in var_idxs by calling the remove function
            let mut weaken_count: i64 = 0;
            for var_idx in var_idxs.into_iter() {
                weaken_count += self.delete_term(var_idx);
            }
            // The degree decrement is checked and escalates to `BigInt` on underflow.
            self.finish_weakening(weaken_count)
        } else {
            // Weaken all variables by calling the remove function.
            var_idxs.sort_unstable();
            let mut weaken_vars = var_idxs.iter();
            let mut cur_var = weaken_vars.next();
            let mut index = 0;
            let mut new_index = 0;

            let mut weaken_count: i64 = 0;
            while let Some(var) = cur_var {
                if index == self.len() {
                    break;
                }
                match self.lits[index].get_var().cmp(var) {
                    Ordering::Equal => {
                        // The current variable is weakened away.
                        weaken_count += 1;
                        cur_var = weaken_vars.next();
                        index += 1;
                    }
                    Ordering::Less => {
                        // The current variable is not weakened, so move it to keep `lits` contiguous.
                        self.lits[new_index] = self.lits[index];
                        new_index += 1;
                        index += 1;
                    }
                    Ordering::Greater => {
                        // The weakened variable is not in the constraint.
                        cur_var = weaken_vars.next();
                    }
                }
            }
            while index < self.len() {
                // Move remaining variables to keep `lits` contiguous.
                self.lits[new_index] = self.lits[index];
                new_index += 1;
                index += 1;
            }
            self.lits.truncate(new_index);
            // The degree decrement is checked and escalates to `BigInt` on underflow.
            self.finish_weakening(weaken_count)
        }
    }

    #[inline]
    fn normalized_form_div(&mut self, divisor: &BigInt) {
        self.degree = divide_degree(self.degree, divisor);
    }

    #[inline]
    fn variable_form_div(&mut self, divisor: &BigInt) -> Option<PBConstraintEnum> {
        if divisor.is_one() {
            return None;
        }

        // Moving the negated literals to the right-hand side subtracts one per negated literal
        // from the degree, which underflows `i64` for a degree close to `i64::MIN`. Escalate
        // instead of wrapping.
        if self.degree.checked_sub(self.negated_lit_count()).is_none() {
            let mut widened = self.widen_to_bigint();
            widened.variable_form_div(divisor);
            return Some(widened.into_smallest_type());
        }

        // Positive literals are retained.
        self.lits.retain(|lit| {
            if lit.is_negated() {
                self.degree -= 1;
            }
            !lit.is_negated()
        });

        self.degree = divide_degree(self.degree, divisor);

        None
    }

    #[inline]
    fn normalized_form_mir(&mut self, divisor: &BigInt) -> Option<PBConstraintEnum> {
        // Compute the remainder of (A mod d).
        let remainder = BigInt::from(self.degree).mod_floor(divisor);
        // Special case is remainder is 0.
        if remainder.is_zero() {
            self.lits.clear();
            self.degree = 0;
            return None;
        }

        // Compute the quotient.
        self.degree = divide_degree(self.degree, divisor);

        // Skipping the multiplication when `r` does not fit an `i64` is exact, not lucky, but only
        // because the quotient above is exact: `r > i64::MAX` forces `d > i64::MAX`, a positive `A`
        // would then give `r == A` (an `i64`), so `A <= 0`; and `A == -d` — the only way to reach
        // quotient `-1` — gives `r == 0`, which returned above. Hence the quotient is `0` here and
        // `q * r == 0 == q`.
        if let Ok(remainder) = TryInto::<i64>::try_into(&remainder) {
            // Compute the new degree. `|ceil(A / d) * r| <= |A|` for `0 < r < d`, so this cannot
            // leave the range of the degree it started from.
            self.degree *= remainder;
        }

        None
    }

    #[inline]
    fn variable_form_mir(&mut self, divisor: &BigInt) -> Option<PBConstraintEnum> {
        // Moving the negated literals to the right-hand side subtracts one per negated literal
        // from the degree, which underflows `i64` for a degree close to `i64::MIN`. Escalate
        // instead of wrapping.
        if self.degree.checked_sub(self.negated_lit_count()).is_none() {
            let mut widened = self.widen_to_bigint();
            widened.variable_form_mir(divisor);
            return Some(widened.into_smallest_type());
        }

        // Positive literals are retained.
        self.lits.retain(|lit| {
            if lit.is_negated() {
                self.degree -= 1;
            }
            !lit.is_negated()
        });

        // Compute the remainder of (A mod d).
        let remainder = BigInt::from(self.degree).mod_floor(divisor);
        // Special case is remainder is 0.
        if remainder.is_zero() {
            self.lits.clear();
            self.degree = 0;
            return None;
        }

        // Compute the quotient.
        self.degree = divide_degree(self.degree, divisor);

        // Skipping the multiplication when `r` does not fit an `i64` is exact, not lucky, but only
        // because the quotient above is exact: `r > i64::MAX` forces `d > i64::MAX`, a positive `A`
        // would then give `r == A` (an `i64`), so `A <= 0`; and `A == -d` — the only way to reach
        // quotient `-1` — gives `r == 0`, which returned above. Hence the quotient is `0` here and
        // `q * r == 0 == q`.
        if let Ok(remainder) = TryInto::<i64>::try_into(&remainder) {
            // Compute the new degree. `|ceil(A / d) * r| <= |A|` for `0 < r < d`, so this cannot
            // leave the range of the degree it started from.
            self.degree *= remainder;
        }

        None
    }

    #[inline]
    fn multiply(&mut self, factor: &BigInt) -> Option<PBConstraintEnum> {
        if factor.is_one() {
            return None;
        }

        let coeff_sum = factor * self.len();
        let degree = factor * self.degree;

        // Try i64 type.
        if let Ok(coeff_sum) = TryInto::<i64>::try_into(&coeff_sum)
            && let Ok(factor) = TryInto::<i64>::try_into(factor)
            && let Ok(degree) = TryInto::<i64>::try_into(&degree)
        {
            let terms = self
                .lits
                .iter()
                .map(|lit| GeneralPBTerm::new(factor, *lit))
                .collect();
            return Some(GeneralPBConstraint::from_terms(terms, coeff_sum, degree).into());
        }

        if let Ok(coeff_sum) = TryInto::<i128>::try_into(&coeff_sum)
            && let Ok(factor) = TryInto::<i128>::try_into(factor)
            && let Ok(degree) = TryInto::<i128>::try_into(&degree)
        {
            let terms = self
                .lits
                .iter()
                .map(|lit| GeneralPBTerm::new(factor, *lit))
                .collect();
            return Some(GeneralPBConstraint::from_terms(terms, coeff_sum, degree).into());
        }

        let terms = self
            .lits
            .iter()
            .map(|lit| GeneralPBTerm::new(factor.clone(), *lit))
            .collect();
        Some(GeneralPBConstraint::from_terms(terms, coeff_sum, degree).into())
    }

    fn add<C: PBConstraintGetter>(&mut self, summand: &C) -> Option<PBConstraintEnum> {
        let mut card_term = self.lits.iter().peekable();
        let mut summand_term = summand.get_terms().iter().peekable();
        let mut cancel = 0;
        let mut resulting_lits = Vec::with_capacity(self.len() + summand.len());

        // Try to keep `Cardinality` type first.
        merge_in_situ_lits(
            &mut card_term,
            &mut summand_term,
            &mut resulting_lits,
            &mut cancel,
        );

        // If all terms where merged then it is either a clause or cardinality constraint.
        if card_term.peek().is_none()
            && summand_term.peek().is_none()
            && let Ok(degree) = TryInto::<i64>::try_into(summand.get_degree().to_owned())
            && let Some(degree) = degree
                .checked_add(self.degree)
                .and_then(|d| d.checked_sub(cancel))
        {
            if degree == 1 {
                return Some(Clause::from_lits(resulting_lits).into());
            } else {
                self.lits = resulting_lits;
                self.degree = degree;
                return None;
            }
        }

        // Change cardinality to general PB constraint.
        let coeff_sum = self.get_coeff_sum() + summand.get_coeff_sum().into();
        let degree_sum = Into::<BigInt>::into(*self.get_degree())
            + Into::<BigInt>::into(summand.get_degree().to_owned());
        if let Ok(narrow_coeff_sum) = TryInto::<i64>::try_into(&coeff_sum)
            && let Ok(narrow_degree_sum) = TryInto::<i64>::try_into(&degree_sum)
        {
            let mut resulting_terms: Vec<GeneralPBTerm<i64>> = resulting_lits
                .into_iter()
                .map(|lit| GeneralPBTerm::new(1, lit))
                .collect();

            merge_from_lits(card_term, summand_term, &mut resulting_terms, &mut cancel);
            // The cancellation lowers the degree further, so it is the *adjusted* degree that has
            // to fit into the narrow type; escalates to `BigInt` otherwise.
            Some(add_from_merged_terms(
                resulting_terms,
                &coeff_sum,
                &degree_sum,
                narrow_coeff_sum,
                narrow_degree_sum,
                cancel,
            ))
        } else if let Ok(narrow_coeff_sum) = TryInto::<i128>::try_into(&coeff_sum)
            && let Ok(narrow_degree_sum) = TryInto::<i128>::try_into(&degree_sum)
        {
            let mut resulting_terms: Vec<GeneralPBTerm<i128>> = resulting_lits
                .into_iter()
                .map(|lit| GeneralPBTerm::new(1, lit))
                .collect();
            let mut cancel = cancel.into();

            merge_from_lits(card_term, summand_term, &mut resulting_terms, &mut cancel);
            Some(add_from_merged_terms(
                resulting_terms,
                &coeff_sum,
                &degree_sum,
                narrow_coeff_sum,
                narrow_degree_sum,
                cancel,
            ))
        } else {
            let mut resulting_terms: Vec<GeneralPBTerm<BigInt>> = resulting_lits
                .into_iter()
                .map(|lit| GeneralPBTerm::new(BigInt::one(), lit))
                .collect();
            let mut cancel = cancel.into();

            merge_from_lits(card_term, summand_term, &mut resulting_terms, &mut cancel);
            let constraint = GeneralPBConstraint::from_terms(
                resulting_terms,
                coeff_sum - (2 * &cancel),
                degree_sum - cancel,
            );

            Some(constraint.into())
        }
    }

    #[inline]
    fn lower_rhs(&mut self, amount: &BigInt) -> Option<PBConstraintEnum> {
        debug_assert!(!amount.is_negative());

        if let Ok(amount) = TryInto::<i64>::try_into(amount)
            && let Some(degree) = self.degree.checked_sub(amount)
        {
            self.degree = degree;
            return None;
        }

        // The escalation has to hand the lowered constraint *back*. Delegating to
        // `GeneralPBConstraint::<BigInt>::lower_rhs` lowered a temporary: a `BigInt` `checked_sub`
        // never fails, so that implementation takes its in situ branch and returns `None`, and
        // `None` is the caller's signal that `self` was mutated — so the lowering was discarded and
        // the stack kept the un-lowered (strictly stronger) constraint. Unlike the clause case this
        // is reachable with an ordinary `i64` amount, because the guard above also fails when
        // `degree - amount` underflows, which is exactly what it was added for.
        let mut widened = self.widen_to_bigint();
        widened.set_degree(BigInt::from(self.degree) - amount);
        Some(widened.into_smallest_type())
    }

    #[inline]
    fn negate(&self) -> PBConstraintEnum {
        let mut negated_lits = self.lits.clone();
        for lit in negated_lits.iter_mut() {
            lit.negate();
        }

        // See `GeneralPBConstraint::negate()`: `coeff_sum - degree + 1` leaves `i64` for a
        // trivially true constraint whose degree is close to `i64::MIN`.
        let Some(degree) = PBConstraintGetter::get_coeff_sum(self)
            .checked_sub(self.degree)
            .and_then(|degree| degree.checked_add(1))
        else {
            let coeff_sum = BigInt::from(PBConstraintGetter::get_coeff_sum(self));
            let degree = coeff_sum.clone() - BigInt::from(self.degree) + BigInt::one();
            let terms = negated_lits
                .into_iter()
                .map(|lit| GeneralPBTerm::new(BigInt::one(), lit))
                .collect();
            return constraint_from_terms_and_coeff_sum::<BigInt>(terms, degree, coeff_sum);
        };

        Cardinality::from_lits(negated_lits, degree).into()
    }

    #[inline]
    fn substitute(&self, substitution: &impl Substitutable) -> PBConstraintEnum {
        // Each literal substituted to true lowers the degree by one, so the total decrement is
        // bounded by the number of literals. See `GeneralPBConstraint::substitute()` for why
        // wrapping here forges `red`/`dom` proof goals.
        if self.degree.checked_sub(self.len() as i64).is_none() {
            return self.widen_to_bigint().substitute(substitution);
        }

        let mut substituted_lits = Vec::new();
        let mut substituted_degree = self.degree;
        for &lit in self.lits.iter() {
            match substitution.get_lit(lit) {
                Some(SubstitutionValue::TRUE) => substituted_degree -= 1,
                Some(SubstitutionValue::FALSE) => {}
                Some(substituted_lit) => {
                    substituted_lits.push(GeneralPBTerm::new(1i64, substituted_lit.get_lit()))
                }
                None => substituted_lits.push(GeneralPBTerm::new(1i64, lit)),
            }
        }

        let coeff_sum = substituted_lits.len() as i64;
        constraint_from_terms_and_coeff_sum(substituted_lits, substituted_degree, coeff_sum)
    }

    #[inline]
    fn get_lit(&self, index: usize) -> Option<&Lit> {
        self.lits.get(index)
    }

    #[inline]
    fn get_term(&self, index: usize) -> Option<GeneralPBTerm<BigInt>> {
        self.lits
            .get(index)
            .map(|lit| GeneralPBTerm::new(1.into(), *lit))
    }

    #[inline]
    fn is_satisfied(&self, assignment: &Assignment<BooleanVar>) -> bool {
        if self.is_trivial() {
            return true;
        }

        let mut counter = 0;
        for &lit in self.lits.iter() {
            if unsafe { assignment.get_lit_value_unchecked(lit) } == BoolValue::Assigned(true) {
                counter += 1;
                if counter >= self.degree {
                    return true;
                }
            }
        }

        false
    }

    #[inline]
    fn is_falsified(&self, assignment: &Assignment<BooleanVar>) -> bool {
        if self.is_contradicting() {
            return true;
        }

        let mut counter = self.lits.len() as i64;
        for &lit in self.lits.iter() {
            if assignment.get_lit_value(lit) == BoolValue::Assigned(false) {
                counter -= 1;
                if counter < self.degree {
                    return true;
                }
            }
        }

        false
    }

    #[inline]
    fn len(&self) -> usize {
        self.lits.len()
    }

    #[inline]
    fn is_empty(&self) -> bool {
        self.lits.is_empty()
    }

    #[inline]
    fn propagate(&self, assignment: &mut Assignment<BooleanVar>) -> ConstraintPropagationResult {
        if self.is_trivial() {
            return ConstraintPropagationResult::NoPropagation;
        }

        let mut unassigned_lits = Vec::new();
        let mut slack = -self.degree;
        for &lit in self.lits.iter() {
            match unsafe { assignment.get_lit_value_unchecked(lit) } {
                BoolValue::Assigned(true) => {
                    slack += 1;
                    if slack > 0 {
                        return ConstraintPropagationResult::NoPropagation;
                    }
                }
                BoolValue::Assigned(false) => {}
                BoolValue::Unassigned => {
                    slack += 1;
                    if slack > 0 {
                        return ConstraintPropagationResult::NoPropagation;
                    }
                    unassigned_lits.push(lit);
                }
            }
        }

        if slack.is_negative() {
            ConstraintPropagationResult::Conflict
        } else if unassigned_lits.is_empty() {
            ConstraintPropagationResult::NoPropagation
        } else {
            for lit in unassigned_lits {
                unsafe { assignment.set_lit_value_unchecked(lit, BoolValue::Assigned(true)) };
            }
            ConstraintPropagationResult::Propagated
        }
    }

    #[inline]
    fn traced_propagate(&self, assignment: &mut Assignment<BooleanVar>) -> Vec<Lit> {
        if self.is_trivial() {
            return vec![];
        }

        let mut unassigned_lits = Vec::new();
        let mut slack = -self.degree;
        for &lit in self.lits.iter() {
            match unsafe { assignment.get_lit_value_unchecked(lit) } {
                BoolValue::Assigned(true) => {
                    slack += 1;
                    if slack > 0 {
                        return vec![];
                    }
                }
                BoolValue::Assigned(false) => {}
                BoolValue::Unassigned => {
                    slack += 1;
                    if slack > 0 {
                        return vec![];
                    }
                    unassigned_lits.push(lit);
                }
            }
        }

        if slack.is_negative() {
            panic!("The propagation did not succeed earlier.")
        } else if unassigned_lits.is_empty() {
            vec![]
        } else {
            let mut lits = Vec::new();
            for lit in unassigned_lits {
                unsafe { assignment.set_lit_value_unchecked(lit, BoolValue::Assigned(true)) };
                lits.push(lit);
            }
            lits
        }
    }

    #[inline]
    fn mark_negated_lits(
        &self,
        assignment: &Assignment<BooleanVar>,
        marking: &mut Assignment<BooleanVar>,
    ) {
        for &lit in self.get_lits() {
            if unsafe { assignment.get_lit_value_unchecked(lit) } == BoolValue::Assigned(false) {
                unsafe { marking.set_lit_value_unchecked(lit, BoolValue::Assigned(false)) };
            }
        }
    }

    #[inline]
    fn into_smallest_type(self) -> PBConstraintEnum {
        if self.degree.is_one() {
            Clause::from_lits(self.lits).into()
        } else {
            self.into()
        }
    }

    fn get_reification(&self, var: VarIdx, direction: ReificationDir) -> PBConstraintEnum {
        // Handle special cases.
        match direction {
            ReificationDir::VarImplIneq => {
                if self.degree == 0 {
                    // Coefficient of reification variable is 0.
                    return self.clone().into();
                }
                if self.degree == -1 {
                    //Cefficient of reification variable is 1.
                    let mut out_constraint = self.clone();
                    out_constraint.lits.push(Lit::from_var(var, false));
                    out_constraint.lits.sort_unstable();
                    out_constraint.degree = 0;
                    return out_constraint.into();
                }
            }
            ReificationDir::IneqImplVar => {
                if self.len() == self.degree as usize {
                    // Degree of negation is 1.
                    let mut lits: Vec<_> = self.lits.iter().map(|l| -l).collect();
                    lits.push(Lit::from_var(var, false));
                    lits.sort_unstable();
                    return Clause::from_lits(lits).into();
                }
                if self.len() + 1 == self.degree as usize {
                    // Degree of negation is 0.
                    let mut out_constraint = self.clone();
                    out_constraint.lits.iter_mut().for_each(|l| l.negate());
                    out_constraint.degree = 0;
                    return out_constraint.into();
                }
                if self.len() + 2 == self.degree as usize {
                    // Degree of negation is -1
                    let mut out_constraint = self.clone();
                    out_constraint.lits.iter_mut().for_each(|l| l.negate());
                    out_constraint.lits.push(Lit::from_var(var, true));
                    out_constraint.lits.sort_unstable();
                    out_constraint.degree = 0;
                    return out_constraint.into();
                }
            }
        }

        GeneralPBConstraint::<i64>::from(self).get_reification(var, direction)
    }
}

impl From<&Clause> for Cardinality {
    fn from(value: &Clause) -> Self {
        Cardinality::from_lits(value.get_lits().copied().collect(), 1)
    }
}

impl ToPrettyString for Cardinality {
    #[inline]
    fn to_pretty_string<V: VarNameLookup>(&self, var_names: &V) -> String {
        let mut out = String::with_capacity(self.len() * 4);
        for lit in self.lits.iter() {
            out.push_str("1 ");
            out.push_str(&lit.to_pretty_string(var_names));
            out.push(' ');
        }
        out.push_str(">= ");
        out.push_str(&self.degree.to_string());
        out
    }
}
