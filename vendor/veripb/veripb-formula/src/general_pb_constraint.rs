//! Implementation of [`PBConstraint`] for general pseudo-Boolean constraints.

use std::fmt::Debug;
use std::panic;
use std::{any::TypeId, cmp::Ordering};

use malachite_bigint::BigInt;
use num_integer::Integer;
use num_traits::{One, Signed, Zero};

use crate::helper::quotient_by_oversized_divisor;
use crate::pb_constraint::{WEAKEN_ALL_THRESHOLD, add_widened, adjusted_add_bookkeeping};
use crate::prelude::*;
use crate::substitution::Substitutable;

/// A general pseudo-Boolean constraint can have any integer as coefficients and and right-hand side.
///
/// For efficiency reasons the constraint has a generic parameter that defines the integer type used. Currently the integer types [`i64`], [`i128`], and [`BigInt`] are supported.
#[derive(Debug, Clone, Default, Hash, PartialEq, Eq)]
pub struct GeneralPBConstraint<N>
where
    N: Int,
{
    terms: Vec<GeneralPBTerm<N>>,
    coeff_sum: N,
    degree: N,
}

impl<N> GeneralPBConstraint<N>
where
    N: Int,
{
    /// Delete the term containing the [`VarIdx`] `var_idx` from the [`GeneralPBConstraint`] constraint.
    #[inline]
    fn delete_term(&mut self, var_idx: VarIdx) -> N {
        if let Ok(index) = self
            .terms
            .binary_search_by(|term| term.get_lit().get_var().cmp(&var_idx))
        {
            self.terms.remove(index).get_coeff().clone()
        } else {
            N::zero()
        }
    }

    /// Get the sum of the coefficients for [`GeneralPBConstraint`].
    #[inline]
    fn set_coeff_sum(&mut self, coeff_sum: N) {
        self.coeff_sum = coeff_sum;
    }

    /// Add the `value` the sum of the coefficients in [`GeneralPBConstraint`].
    #[inline]
    fn add_to_coeff_sum(&mut self, value: &N) {
        self.coeff_sum += value;
    }

    /// Set the right-hand side of [`GeneralPBConstraint`] to `degree`.
    #[inline]
    pub fn set_degree(&mut self, degree: N) {
        self.degree = degree;
    }

    /// Construct a new pseudo-Boolean constraint from terms and degree. The resulting constraint is normalized.
    ///
    /// To get the smallest possible type, this function should only be used in combination with [`into_smallest_type()`](PBConstraint::into_smallest_type()). This is automatically done by using the functions [`constraint_from_terms()`] or [`constraint_from_terms_and_coeff_sum()`].
    #[inline]
    pub fn from_terms(terms: Vec<GeneralPBTerm<N>>, coeff_sum: N, degree: N) -> Self {
        let mut constraint = GeneralPBConstraint {
            terms,
            coeff_sum,
            degree,
        };
        constraint.normalize();
        constraint
    }

    /// Check if the coefficients of all terms are 1.
    ///
    /// The sum of the coefficients equalling the term count is *necessary* for this and is checked
    /// first, in O(1); it is only *sufficient* for a normalized constraint, whose coefficients are
    /// all non-zero, and that invariant is not visible from here. Callers use this to drop the
    /// coefficients entirely and rebuild the constraint from its literals (see
    /// [`into_smallest_type()`](PBConstraint::into_smallest_type())), so a false positive forges a
    /// constraint rather than merely storing it in a wider type. The terms are therefore confirmed
    /// before the answer is `true`; the scan only runs once the O(1) pre-check passes, on a path
    /// that is about to walk every term anyway.
    #[inline]
    pub fn all_coeff_one(&self) -> bool {
        self.coeff_sum
            .to_owned()
            .try_into()
            .is_ok_and(|sum: i64| sum as usize == self.terms.len())
            && self.terms.iter().all(|term| term.get_coeff().is_one())
    }

    /// Add term to pseudo-Boolean constraint. The term is automatically normalized if the term is not normalized.
    #[inline]
    pub fn add_term(&mut self, new_term: GeneralPBTerm<N>) {
        // Check if the variable of the term is already in the constraint.
        for term in self.terms.iter_mut() {
            if term.lit.get_var() == new_term.lit.get_var() {
                term.add_with(new_term);
                return;
            }
        }

        self.terms.push(new_term);
    }

    /// In situ normalizing the constraint.
    #[inline]
    fn normalize(&mut self) {
        if self.terms.is_empty() {
            return;
        }

        // Sort the terms by variable.
        self.terms
            .sort_unstable_by(|a, b| a.lit.partial_cmp(&b.lit).unwrap());

        let mut new = 0;
        for original in 1..self.terms.len() {
            if self.terms[new].lit.get_var() == self.terms[original].lit.get_var() {
                // If both terms have the same variable, just add the literals without and save them at the `new` position.
                let old_term = self.terms[original].clone();
                let cancellation = self.terms[new].add_with(old_term);
                self.degree -= cancellation.clone();
            } else {
                // We are finished with all literals for this variable.
                let finished_term = self.terms.get_mut(new).unwrap();
                // Normalize term, as the term might have negative coefficient.
                if finished_term.coeff.is_negative() {
                    finished_term.change_negation();
                    self.degree += finished_term.coeff.clone();
                }
                // If the coefficient is not 0, i.e., the term exists in the normalized form, then we go to next term.
                if finished_term.coeff != Zero::zero() {
                    new += 1;
                }

                if new != original {
                    self.terms[new] = self.terms[original].clone();
                }
            }
        }

        let last_term = self.terms.get_mut(new).unwrap();
        // Normalize term, as the `last_term` might have negative coefficient.
        if last_term.coeff.is_negative() {
            last_term.change_negation();
            self.degree += last_term.coeff.clone();
        }
        // Final test if the `last_term` has coefficient 0 and can be removed.
        if last_term.coeff.is_zero() {
            self.terms.truncate(new);
        } else {
            self.terms.truncate(new + 1);
        }

        // Recompute the sum of the coefficients.
        self.coeff_sum = Zero::zero();
        for term in self.terms.iter() {
            self.coeff_sum += &term.coeff;
        }
    }

    /// Merge the terms from the constraint given in `summand` into this constraint.
    ///
    /// The returned integer is the cancellation due to merging the terms, i.e., the constant on the left-hand side after normalizing the terms. The cancellation should be subtracted from the degree and subtracted twice from the sum of coefficients.
    #[inline]
    fn merge_terms(&mut self, summand: &impl PBConstraintGetter) -> N {
        let mut cancel = N::zero();
        let mut resulting_terms = Vec::with_capacity(self.terms.len() + summand.len());
        let mut first_term = self.terms.iter();
        let mut second_term = summand.get_terms().iter();
        let mut cur_first = first_term.next();
        let mut cur_second = second_term.next();

        loop {
            match (cur_first, cur_second) {
                (None, None) => break,
                (Some(first), Some(second)) => {
                    match first.lit.get_var().cmp(&second.get_lit().get_var()) {
                        Ordering::Equal => {
                            let second = GeneralPBTerm::new(
                                Into::<BigInt>::into(second.get_coeff().clone())
                                    .try_into()
                                    .ok()
                                    .unwrap(),
                                second.get_lit(),
                            );
                            resulting_terms.push(first.to_owned());
                            cancel += resulting_terms.last_mut().unwrap().add_with(second);
                            if resulting_terms.last().unwrap().coeff.is_zero() {
                                resulting_terms.pop();
                            }

                            cur_first = first_term.next();
                            cur_second = second_term.next();
                        }
                        Ordering::Less => {
                            resulting_terms.push(first.to_owned());
                            cur_first = first_term.next();
                        }
                        Ordering::Greater => {
                            resulting_terms.push(GeneralPBTerm::new(
                                Into::<BigInt>::into(second.get_coeff().clone())
                                    .try_into()
                                    .ok()
                                    .unwrap(),
                                second.get_lit(),
                            ));
                            cur_second = second_term.next();
                        }
                    }
                }
                (None, Some(second)) => {
                    resulting_terms.push(GeneralPBTerm::new(
                        Into::<BigInt>::into(second.get_coeff().clone())
                            .try_into()
                            .ok()
                            .unwrap(),
                        second.get_lit(),
                    ));
                    cur_second = second_term.next();
                }
                (Some(first), None) => {
                    resulting_terms.push(first.to_owned());
                    cur_first = first_term.next();
                }
            }
        }

        self.terms = resulting_terms;

        cancel
    }

    /// Widen this constraint into the [`BigInt`] representation, preserving its meaning exactly.
    ///
    /// This is the escalation target used whenever an operation would overflow the narrow integer
    /// type `N`. It mirrors the `i64 -> i128 -> BigInt` discipline of the parsers, except that it
    /// jumps straight to [`BigInt`]: the callers use it on paths that are already known to be
    /// unrepresentable in `N`, and the result is narrowed again with
    /// [`into_smallest_type()`](PBConstraint::into_smallest_type()).
    ///
    /// The constraint is assumed to be normalized already, so no re-normalization is performed.
    #[inline]
    fn widen_to_bigint(&self) -> GeneralPBConstraint<BigInt> {
        GeneralPBConstraint {
            terms: self
                .terms
                .iter()
                .map(|term| GeneralPBTerm::new(term.coeff.clone().into(), term.lit))
                .collect(),
            coeff_sum: self.coeff_sum.clone().into(),
            degree: self.degree.clone().into(),
        }
    }

    /// The degree of this constraint in *variable form*, computed in [`BigInt`] so that it cannot
    /// overflow: `degree - sum of the coefficients of the negated literals`.
    ///
    /// The `c` (variable-form division) and `m` (variable-form MIR) rules start by moving all
    /// negated literals to the right-hand side, which is a subtraction that can underflow `N` for
    /// a constraint with a very negative degree. Callers use this to decide whether the operation
    /// has to be escalated to [`BigInt`].
    #[inline]
    fn variable_form_degree_bigint(&self) -> BigInt {
        let mut degree: BigInt = self.degree.clone().into();
        for term in self.terms.iter().filter(|term| term.lit.is_negated()) {
            degree -= Into::<BigInt>::into(term.coeff.clone());
        }
        degree
    }

    /// Apply the degree/coefficient-sum bookkeeping of a weakening step that removed terms whose
    /// coefficients sum to `weaken_sum`.
    ///
    /// The degree decrement is done with [`CheckedSub`](num_traits::CheckedSub); if it does not fit
    /// into `N` the whole constraint is escalated to [`BigInt`] instead of wrapping silently. The
    /// release profile now enables overflow checks, but a plain `-=` here would still be wrong: a
    /// constraint with a degree close to `N::MIN` is trivially true, and wrapping turns it into the
    /// empty contradiction.
    #[inline]
    fn finish_weakening(&mut self, weaken_sum: N) -> Option<PBConstraintEnum> {
        if let (Some(degree), Some(negated_sum)) = (
            self.degree.checked_sub(&weaken_sum),
            N::zero().checked_sub(&weaken_sum),
        ) {
            self.degree = degree;
            self.add_to_coeff_sum(&negated_sum);
            return None;
        }

        let mut widened = self.widen_to_bigint();
        let weaken_sum: BigInt = weaken_sum.into();
        widened.degree -= &weaken_sum;
        widened.coeff_sum -= &weaken_sum;
        Some(widened.into_smallest_type())
    }

    /// Get the reification of this constraint with respect to the literals `lits`.
    ///
    /// For [`ReificationDir::VarImplIneq`] the returned constraint states that the conjunction of the literals in `lits` implies this constraint. For [`ReificationDir::IneqImplVar`] the slice `lits` has to contain exactly one literal and the returned constraint states that this constraint implies that literal.
    ///
    /// This generalizes [`PBConstraint::get_reification()`] from a variable to a (possibly negated) literal and, for [`ReificationDir::VarImplIneq`], from a single literal to a conjunction of literals.
    ///
    /// An implication whose truth does not depend on the literals is returned without them: for [`ReificationDir::VarImplIneq`] a trivially satisfied constraint is returned as it is, and for [`ReificationDir::IneqImplVar`] a contradicting constraint is returned as its (trivially satisfied) negation.
    ///
    /// The reified constraint has a coefficient and a degree that are of the order of
    /// `coeff_sum + |degree|`, which routinely exceeds `N` even though both operands fit into it:
    /// `coeff_sum - degree + 1` overflows for any constraint with a large coefficient sum and a
    /// negative degree. Wrapping here silently flips the reification literal and can leave the
    /// resulting proof goal with degree `<= 0`, which the checker auto-discharges as trivial — a
    /// real proof obligation would be skipped. The reification is therefore always built in
    /// [`BigInt`] and narrowed again afterwards; its callers (the `preserved_add`/`preserved_rm`
    /// rules and the OPB reification shorthands) are not on a hot path, so the extra cost does not
    /// matter.
    ///
    /// **Note:** The constraint has to be normalized, which is guaranteed for every constraint created with [`GeneralPBConstraint::from_terms()`]. The literals are added at the degree as coefficient, so a constraint that is not normalized would give a reification that is too strong.
    pub fn get_lit_reification(&self, lits: &[Lit], direction: ReificationDir) -> PBConstraintEnum
    where
        PBConstraintEnum: From<GeneralPBConstraint<N>>,
    {
        let widened = self.widen_to_bigint();
        match direction {
            ReificationDir::VarImplIneq => {
                // A trivially satisfied constraint is implied by anything. Adding the literals at a degree that is not positive would give a constraint that is too strong.
                if widened.is_trivial() {
                    return widened.into_smallest_type();
                }
                let degree = widened.degree.clone();
                let mut out_constraint = widened;
                for lit in lits {
                    out_constraint
                        .terms
                        .push(GeneralPBTerm::new(degree.clone(), -lit));
                    out_constraint.coeff_sum += &degree;
                }
                out_constraint.normalize();
                out_constraint.into_smallest_type()
            }
            ReificationDir::IneqImplVar => {
                debug_assert_eq!(lits.len(), 1);
                // The negation of this constraint, which is what implies the literal.
                let new_degree = widened.coeff_sum.clone() - &widened.degree + BigInt::one();
                let mut terms: Vec<_> = widened
                    .terms
                    .iter()
                    .cloned()
                    .map(|mut term| {
                        term.negate();
                        term
                    })
                    .collect();
                // A contradicting constraint implies anything, so its negation, which is trivially satisfied, is returned as it is. Adding the literal at a degree that is not positive would give a constraint that is too strong.
                if widened.is_contradicting() {
                    return constraint_from_terms_and_coeff_sum::<BigInt>(
                        terms,
                        new_degree,
                        widened.coeff_sum.clone(),
                    );
                }
                terms.push(GeneralPBTerm::new(new_degree.clone(), lits[0]));
                constraint_from_terms_and_coeff_sum::<BigInt>(
                    terms,
                    new_degree.clone(),
                    widened.coeff_sum.clone() + new_degree,
                )
            }
        }
    }

    /// Get the coefficient of a literal in the constraint.
    ///
    /// The coefficient is returned as `Some(coefficient)`. If there is no term in the constraint that contains `lit`, then [`None`] is returned.
    #[inline]
    pub fn get_coeff(&self, lit: Lit) -> Option<&N> {
        if let Ok(index) = self.terms.binary_search_by(|t| t.lit.cmp(&lit)) {
            Some(&self.terms[index].coeff)
        } else {
            None
        }
    }
}

impl<N> PBConstraintGetter for GeneralPBConstraint<N>
where
    N: Int,
    PBConstraintEnum: From<GeneralPBConstraint<N>>,
{
    type CoeffType = N;
    type TermType = GeneralPBTerm<N>;

    #[inline]
    fn get_coeff_sum(&self) -> Self::CoeffType {
        self.coeff_sum.clone()
    }

    #[inline]
    fn get_degree(&self) -> &Self::CoeffType {
        &self.degree
    }

    #[inline]
    fn get_terms(&self) -> &Vec<Self::TermType> {
        &self.terms
    }

    #[inline]
    fn get_lits(&self) -> impl Iterator<Item = &Lit> {
        self.get_terms().iter().map(|term| &term.lit)
    }
}

impl<N> PBConstraint for GeneralPBConstraint<N>
where
    N: Int,
    PBConstraintEnum: From<GeneralPBConstraint<N>>,
{
    #[inline]
    fn is_contradicting(&self) -> bool {
        self.degree > self.coeff_sum
    }

    #[inline]
    fn is_trivial(&self) -> bool {
        !self.degree.is_positive()
    }

    #[inline]
    fn len(&self) -> usize {
        self.terms.len()
    }

    #[inline]
    fn is_empty(&self) -> bool {
        self.terms.is_empty()
    }

    #[inline]
    fn multiply(&mut self, factor: &BigInt) -> Option<PBConstraintEnum> {
        // Scaling by `0` yields `0 >= 0` for every constraint: each coefficient becomes zero, and a
        // zero coefficient is not a term. Dropping the terms here is not an optimization — the
        // stored form must satisfy the "no zero coefficient" normalization invariant that
        // `all_coeff_one()` reads, and the in situ branch below is the only multiplication path
        // that does not rebuild through `normalize()`. Leaving `0 x1 0 x2 >= 0` behind let a later
        // addition make the coefficient sum equal the term count, at which point
        // `into_smallest_type()` rebuilt the constraint from the literals alone and forged a
        // coefficient of 1 for a term whose real coefficient was 0.
        //
        // This is placed before `new_coeff_sum`/`new_degree` are computed so it applies uniformly
        // at all three width tiers and cannot be reached through the escalation paths.
        if factor.is_zero() {
            self.terms.clear();
            self.degree = N::zero();
            self.coeff_sum = N::zero();
            return None;
        }

        // `0 >= 0` scaled by any factor is still `0 >= 0`: there is no coefficient to scale, so
        // this stays in situ no matter how large the factor is. Without this, an arbitrarily large
        // factor would needlessly widen the stored constraint to the [`BigInt`] representation.
        if self.terms.is_empty() && self.degree.is_zero() && self.coeff_sum.is_zero() {
            return None;
        }

        let new_coeff_sum = self.get_coeff_sum() * factor.clone();
        let new_degree = self.get_degree().clone() * factor.clone();

        // Try to do multiplication in situ.
        //
        // The factor itself has to be representable in the target type, because it is what every
        // coefficient is scaled by: the two products fitting is *not* sufficient. For a constraint
        // whose coefficient sum and degree are both zero, both products are zero for every factor,
        // so the old `try_into().ok().unwrap()` on the factor aborted the checker on a well-formed
        // `pol` line.
        if let Ok(coeff_sum) = TryInto::<N>::try_into(new_coeff_sum.clone())
            && let Ok(degree) = TryInto::<N>::try_into(new_degree.clone())
            && let Ok(factor) = TryInto::<N>::try_into(factor.clone())
        {
            self.degree = degree;
            self.coeff_sum = coeff_sum;
            for term in self.terms.iter_mut() {
                term.set_coeff(term.get_coeff().clone() * factor.clone())
            }
            return None;
        }

        // Multiply into new constraint.
        // As above, the factor itself has to fit into the target type, not just the two products.
        if let Ok(coeff_sum) = TryInto::<i128>::try_into(&new_coeff_sum)
            && let Ok(degree) = TryInto::<i128>::try_into(&new_degree)
            && let Ok(factor) = TryInto::<i128>::try_into(factor)
        {
            let terms = self
                .terms
                .iter()
                .map(|t| t.multiply_to_i128(factor))
                .collect();

            Some(GeneralPBConstraint::<i128>::from_terms(terms, coeff_sum, degree).into())
        } else {
            let terms = self
                .terms
                .iter()
                .map(|t| t.multiply_to_bigint(factor))
                .collect();

            Some(GeneralPBConstraint::<BigInt>::from_terms(terms, new_coeff_sum, new_degree).into())
        }
    }

    fn add<C: PBConstraintGetter>(&mut self, summand: &C) -> Option<PBConstraintEnum> {
        let coeff_sum = self.get_coeff_sum().into() + summand.get_coeff_sum().into();
        let degree_sum = self.get_degree().clone().into() + summand.get_degree().clone().into();

        // Add second constraint into first constraint in situ.
        if let Ok(narrow_coeff_sum) = TryInto::<N>::try_into(coeff_sum.clone())
            && let Ok(narrow_degree_sum) = TryInto::<N>::try_into(degree_sum.clone())
        {
            // Mergesort for the terms, adjusting the coeff_sum and degree if there is cancellation.
            // Merging itself cannot overflow — every resulting coefficient is bounded by the
            // (checked) coefficient sum — but the bookkeeping below can, so it is guarded.
            let cancellation = self.merge_terms(summand);
            let Some((coeff_sum_adjusted, degree)) =
                adjusted_add_bookkeeping(&narrow_coeff_sum, &narrow_degree_sum, &cancellation)
            else {
                // `self` now holds the merged terms but a stale degree and coefficient sum, so the
                // replacement is built from those terms rather than from `self` as a whole.
                return Some(add_widened(
                    &self.terms,
                    &coeff_sum,
                    &degree_sum,
                    &cancellation,
                ));
            };
            self.set_degree(degree);
            self.set_coeff_sum(coeff_sum_adjusted);

            return None;
        }

        // Add second constraint to first constraint which has been cast to `i128`.
        // The operands' own degree and coefficient sum have to fit into `i128` as well; only their
        // sums are known to, and a very negative degree can cancel against a very positive one.
        if let Ok(narrow_coeff_sum) = TryInto::<i128>::try_into(&coeff_sum)
            && let Ok(narrow_degree_sum) = TryInto::<i128>::try_into(&degree_sum)
            && let Ok(own_coeff_sum) = TryInto::<i128>::try_into(self.coeff_sum.to_owned())
            && let Ok(own_degree) = TryInto::<i128>::try_into(self.degree.to_owned())
        {
            let terms = self
                .terms
                .iter()
                .map(|t| {
                    GeneralPBTerm::<i128>::new(t.coeff.to_owned().try_into().ok().unwrap(), t.lit)
                })
                .collect();
            let mut first_constraint =
                GeneralPBConstraint::<i128>::from_terms(terms, own_coeff_sum, own_degree);
            let cancellation = first_constraint.merge_terms(summand);
            let Some((coeff_sum_adjusted, degree)) =
                adjusted_add_bookkeeping(&narrow_coeff_sum, &narrow_degree_sum, &cancellation)
            else {
                return Some(add_widened(
                    &first_constraint.terms,
                    &coeff_sum,
                    &degree_sum,
                    &cancellation,
                ));
            };
            first_constraint.set_degree(degree);
            first_constraint.set_coeff_sum(coeff_sum_adjusted);

            Some(first_constraint.into())
        } else {
            let terms = self
                .terms
                .iter()
                .map(|t| GeneralPBTerm::<BigInt>::new(t.coeff.to_owned().into(), t.lit))
                .collect();
            let mut first_constraint = GeneralPBConstraint::<BigInt>::from_terms(
                terms,
                self.coeff_sum.to_owned().into(),
                self.degree.to_owned().into(),
            );
            let cancellation = first_constraint.merge_terms(summand);
            first_constraint.set_degree(degree_sum - &cancellation);
            first_constraint.set_coeff_sum(coeff_sum - (2 * cancellation));

            Some(first_constraint.into())
        }
    }

    /// Lower the right-hand side by `amount`.
    ///
    /// At `N = BigInt` the in situ branch below always succeeds, so this returns [`None`]
    /// unconditionally. See the trait documentation: [`None`] means "the receiver was mutated", so
    /// the narrower implementations must not escalate *into* this method — they have to build the
    /// widened constraint themselves and hand it back.
    #[inline]
    fn lower_rhs(&mut self, amount: &BigInt) -> Option<PBConstraintEnum> {
        debug_assert!(!amount.is_negative());

        if let Ok(amount) = TryInto::<N>::try_into(amount.to_owned())
            && let Some(degree) = self.degree.checked_sub(&amount)
        {
            self.degree = degree;
            return None;
        }

        let new_degree = self.degree.to_owned().into() - amount;
        let coeff_sum = self.coeff_sum.to_owned().into();
        let terms = std::mem::take(&mut self.terms)
            .into_iter()
            .map(|t| GeneralPBTerm::new(t.coeff.into(), t.lit))
            .collect();
        let new_constraint =
            GeneralPBConstraint::<BigInt>::from_terms(terms, coeff_sum, new_degree);

        // Re-narrow: hand back the canonical smallest representation, as the other escalation
        // paths added alongside this one do (`finish_weakening`, `variable_form_div`,
        // `variable_form_mir`, `Clause::lower_rhs`, `Cardinality::lower_rhs`). This is a
        // representation choice, not a correctness one, and the rationale this comment used to
        // give -- that the `e` rule would otherwise report a mismatch, since `PBConstraintEnum`'s
        // derived `PartialEq`/`Hash` compare by variant -- describes a situation no in-tree caller
        // can reach: the only caller (`PolRule::compute`) re-narrows its final stack top at
        // `cutting_planes.rs`'s `into_smallest_type()`, which is also why `add` and `multiply` can
        // hand back un-narrowed `i128`/`BigInt` forms there without harm. What the re-narrow does
        // buy today is that the remaining steps of the pol line run on machine integers rather
        // than `BigInt`; the variant it produces is pinned by
        // `general_lower_rhs_escalation_hands_back_the_smallest_representation` in
        // `tests/unchecked_arithmetic.rs`, since every degree-only assertion survives its removal.
        Some(new_constraint.into_smallest_type())
    }

    #[inline]
    fn negate(&self) -> PBConstraintEnum {
        let mut negate_terms = self.terms.clone();
        for term in negate_terms.iter_mut() {
            term.negate();
        }

        // The negated degree is `coeff_sum - degree + 1`, which leaves `N` exactly when the degree
        // is non-positive and the coefficient sum is large — i.e. for a trivially true constraint,
        // whose negation is the contradiction. Wrapping turns that contradiction back into a
        // weaker constraint, so the `~C` premise of a `rup`/`red`/`dom`/`delc` check would silently
        // carry less information than it should (in a debug build it aborts outright).
        let Some(degree) = self
            .coeff_sum
            .checked_sub(&self.degree)
            .and_then(|degree| degree.checked_add(&N::one()))
        else {
            let coeff_sum: BigInt = self.coeff_sum.clone().into();
            let degree =
                coeff_sum.clone() - Into::<BigInt>::into(self.degree.clone()) + BigInt::one();
            let terms = negate_terms
                .into_iter()
                .map(|term| {
                    GeneralPBTerm::new(
                        Into::<BigInt>::into(term.get_coeff().clone()),
                        term.get_lit(),
                    )
                })
                .collect();
            return constraint_from_terms_and_coeff_sum::<BigInt>(terms, degree, coeff_sum);
        };

        GeneralPBConstraint::from_terms(negate_terms, self.coeff_sum.to_owned(), degree).into()
    }

    #[inline]
    fn substitute(&self, substitution: &impl Substitutable) -> PBConstraintEnum {
        // Substituting a literal to true subtracts its coefficient from the degree. The total
        // decrement is bounded by the coefficient sum and every intermediate degree lies between
        // `degree - coeff_sum` and `degree`, so this single check covers all of them. Without it a
        // trivially true constraint with a very negative degree wraps into the empty contradiction,
        // and a contradicting source implies *every* target
        // ([`PBConstraintGetter::implies()`]), so `red`/`dom`/`delc` proof goals get auto-
        // discharged with no proof at all.
        if self.degree.checked_sub(&self.coeff_sum).is_none() {
            return self.widen_to_bigint().substitute(substitution);
        }

        let mut substituted_terms = Vec::new();
        let mut substituted_degree = self.degree.clone();
        let mut substituted_coeff_sum = self.coeff_sum.clone();
        for term in self.terms.iter() {
            match substitution.get_lit(term.lit) {
                Some(SubstitutionValue::TRUE) => {
                    substituted_degree -= &term.coeff;
                    substituted_coeff_sum -= &term.coeff;
                }
                Some(SubstitutionValue::FALSE) => substituted_coeff_sum -= &term.coeff,
                Some(substituted_lit) => substituted_terms.push(GeneralPBTerm::new(
                    term.coeff.clone(),
                    substituted_lit.get_lit(),
                )),
                None => substituted_terms.push(term.clone()),
            }
        }

        constraint_from_terms_and_coeff_sum(
            substituted_terms,
            substituted_degree,
            substituted_coeff_sum,
        )
    }

    #[inline]
    fn get_max_coeff(&self) -> BigInt {
        if let Some(min) = self.terms.iter().max_by(|s, t| s.coeff.cmp(&t.coeff)) {
            min.coeff.clone().into()
        } else {
            BigInt::zero()
        }
    }

    #[inline]
    fn get_lit(&self, index: usize) -> Option<&Lit> {
        self.terms.get(index).map(|term| &term.lit)
    }

    #[inline]
    fn get_term(&self, index: usize) -> Option<GeneralPBTerm<BigInt>> {
        self.terms
            .get(index)
            .map(|term| GeneralPBTerm::new(term.coeff.clone().into(), term.lit))
    }

    #[inline]
    fn is_satisfied(&self, assignment: &Assignment<BooleanVar>) -> bool {
        if self.is_trivial() {
            return true;
        }

        let mut counter = N::zero();
        for term in self.terms.iter() {
            if unsafe { assignment.get_lit_value_unchecked(term.lit) } == BoolValue::Assigned(true)
            {
                counter += &term.coeff;
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

        let mut counter = self.coeff_sum.clone();
        for term in self.terms.iter() {
            if assignment.get_lit_value(term.lit) == BoolValue::Assigned(false) {
                counter -= &term.coeff;
                if counter < self.degree {
                    return true;
                }
            }
        }

        false
    }

    #[inline]
    fn saturate(&mut self) {
        if self.is_trivial() {
            self.terms.clear();
            self.set_coeff_sum(N::zero());
            return;
        }

        let mut coeff_sum_change = N::zero();
        for term in self.terms.iter_mut() {
            if term.get_coeff() > &self.degree {
                coeff_sum_change -= term.get_coeff().abs_sub(&self.degree);
                term.set_coeff(self.degree.clone());
            }
        }
        self.add_to_coeff_sum(&coeff_sum_change);
    }

    #[inline]
    fn weaken(&mut self, var_idx: VarIdx) -> Option<PBConstraintEnum> {
        let coeff = self.delete_term(var_idx);
        // The degree decrement is checked and escalates to `BigInt` on underflow.
        self.finish_weakening(coeff)
    }

    #[inline]
    fn weaken_all(&mut self, mut var_idxs: Vec<VarIdx>) -> Option<PBConstraintEnum> {
        if var_idxs.len() <= WEAKEN_ALL_THRESHOLD {
            // Weaken all variables in var_idxs by calling the remove function.
            let mut weaken_sum = N::zero();
            for var_idx in var_idxs.into_iter() {
                weaken_sum += self.delete_term(var_idx);
            }
            // The degree decrement is checked and escalates to `BigInt` on underflow.
            self.finish_weakening(weaken_sum)
        } else {
            // Weaken all variables by calling the remove function.
            var_idxs.sort_unstable();
            let mut weaken_vars = var_idxs.iter();
            let mut cur_var = weaken_vars.next();
            let mut weaken_sum = N::zero();
            let mut index = 0;
            let mut new_index = 0;

            while let Some(var) = cur_var {
                if index == self.len() {
                    break;
                }
                match self.terms[index].lit.get_var().cmp(var) {
                    Ordering::Equal => {
                        // The current variable is weakened away.
                        weaken_sum += self.terms[index].get_coeff();
                        cur_var = weaken_vars.next();
                        index += 1;
                    }
                    Ordering::Less => {
                        // The current variable is not weakened, so move it to keep `terms` contiguous.
                        self.terms[new_index] = self.terms[index].clone();
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
                // Move remaining variables to keep `terms` contiguous.
                self.terms[new_index] = self.terms[index].clone();
                new_index += 1;
                index += 1;
            }
            self.terms.truncate(new_index);
            // The degree decrement is checked and escalates to `BigInt` on underflow.
            self.finish_weakening(weaken_sum)
        }
    }

    #[inline]
    fn normalized_form_div(&mut self, divisor: &BigInt) {
        match divisor.clone().try_into() {
            Ok(divisor) => {
                let mut new_coeff_sum = N::zero();
                for term in self.terms.iter_mut() {
                    term.divide_round_up(&divisor);
                    new_coeff_sum += term.get_coeff();
                }
                self.set_coeff_sum(new_coeff_sum);
                self.set_degree(self.get_degree().div_ceil(&divisor));
            }
            Err(_) => {
                // `d` does not fit into `N`, so it is at least `N::MAX + 1` and every coefficient
                // divides to `1`. The quotient `ceil(A / d)` is then one of `-1`, `0`, `1` — but
                // *which* one is not decided by the sign of `A` alone: `A == N::MIN` with
                // `d == N::MAX + 1` divides to exactly `-1`, and clamping non-positive degrees to
                // `0` stored a strictly stronger constraint than the rule defines there.
                for term in self.terms.iter_mut() {
                    term.set_coeff(N::one());
                }
                self.set_coeff_sum((self.len() as i64).into());
                let quotient = quotient_by_oversized_divisor(self.get_degree(), divisor);
                self.set_degree(quotient);
            }
        };
    }

    #[inline]
    fn variable_form_div(&mut self, divisor: &BigInt) -> Option<PBConstraintEnum> {
        // Moving the negated literals to the right-hand side subtracts their coefficients from the
        // degree. For a constraint whose degree is close to `N::MIN` that underflows, which the
        // release profile would now abort on rather than accept, so check it in `BigInt` first
        // and escalate the whole constraint if the variable-form degree does not fit into `N`.
        // Every intermediate degree of the loops below lies between the variable-form degree and
        // the original degree, so this single check covers all of them.
        if TryInto::<N>::try_into(self.variable_form_degree_bigint()).is_err() {
            let mut widened = self.widen_to_bigint();
            widened.variable_form_div(divisor);
            return Some(widened.into_smallest_type());
        }

        let mut new_neg_coeff_sum = N::zero();
        match divisor.clone().try_into() {
            Ok(divisor) => {
                let mut new_coeff_sum = N::zero();
                self.terms.retain_mut(|term| {
                    if term.lit.is_negated() {
                        self.degree -= &term.coeff;
                        term.coeff /= &divisor;
                        new_neg_coeff_sum += &term.coeff;
                    } else {
                        term.divide_round_up(&divisor);
                    }
                    new_coeff_sum += &term.coeff;
                    !term.coeff.is_zero()
                });
                self.set_coeff_sum(new_coeff_sum);
                self.degree =
                    num_integer::Integer::div_ceil(&self.degree, &divisor) + new_neg_coeff_sum;
            }
            Err(_) => {
                // As in `normalized_form_div`: `d >= N::MAX + 1` collapses every coefficient to
                // `1`, and the quotient of the variable-form degree is one of `-1`, `0`, `1`. The
                // `-1` case is real — the variable-form degree reaches `N::MIN`, and `d` can be
                // exactly `N::MAX + 1` — so it is computed rather than guessed from the sign.
                self.terms.retain_mut(|term| {
                    if term.lit.is_negated() {
                        self.degree -= &term.coeff;
                        false
                    } else {
                        term.coeff = N::one();
                        true
                    }
                });
                self.set_coeff_sum((self.terms.len() as i64).into());
                self.degree = quotient_by_oversized_divisor(&self.degree, divisor);
            }
        };

        None
    }

    #[inline]
    fn normalized_form_mir(&mut self, divisor: &BigInt) -> Option<PBConstraintEnum> {
        // Compute the remainder of (A mod d).
        let remainder = self.degree.clone().into().mod_floor(divisor);
        // Special case if remainder is zero.
        if remainder.is_zero() {
            self.terms.clear();
            self.coeff_sum = N::zero();
            self.degree = N::zero();
            return None;
        }

        let mut new_coeff_sum = N::zero();
        // Try if we can perform the MIR cut in situ.
        if let Ok(divisor) = TryInto::<N>::try_into(divisor.clone()) {
            // `0 <= r < d` and `d` fits into `N`, so `r` fits into `N` as well.
            let remainder: N = remainder
                .try_into()
                .unwrap_or_else(|_| panic!("(A mod d) < d must fit into the constraint type"));
            for term in self.terms.iter_mut() {
                term.coeff = (term.coeff.div_floor(&divisor) * &remainder)
                    + (&term.coeff.mod_floor(&divisor)).min(&remainder);
                new_coeff_sum += &term.coeff;
            }
            self.degree = self.degree.div_ceil(&divisor) * remainder;
        } else {
            // The divisor does not fit into `N`, so `d >= N::MAX + 1`: it is strictly larger than
            // every coefficient, and at least `|A|`. Therefore `floor(a_i / d) == 0` and
            // `a_i mod d == a_i`, i.e. every coefficient becomes `min(a_i, r)`.
            //
            // For the quotient, `d >= |A|` is *not* strict — `A == N::MIN` with `d == N::MAX + 1`
            // divides to exactly `-1`, which is what makes the same clamp wrong in
            // `normalized_form_div`. Here it is safe for a reason that is easy to lose: `A == -d`
            // is the only way to reach quotient `-1`, and it makes `r == 0`, so the zero-remainder
            // early return above has already fired. Everything that reaches this point therefore
            // has quotient `1` for `A > 0` and `0` for `A < 0` (`A == 0` also implies `r == 0`).
            //
            // Hard-coding the quotient to `1` (as this fallback used to do) turns the trivially
            // true constraint `A <= 0` into one with degree `r == A + d`, which is a huge positive
            // number: MIR of a trivially true constraint would yield a contradiction.
            let quotient_is_one = self.degree.is_positive();
            let remainder_in_n = TryInto::<N>::try_into(remainder).ok();
            match remainder_in_n.as_ref() {
                Some(remainder) => {
                    for term in self.terms.iter_mut() {
                        if term.coeff > *remainder {
                            term.coeff = remainder.clone();
                        }
                        new_coeff_sum += &term.coeff;
                    }
                }
                None => {
                    // `r` exceeds `N::MAX` and therefore every coefficient: `min(a_i, r) == a_i`.
                    new_coeff_sum = self.coeff_sum.clone();
                }
            }
            self.degree = if quotient_is_one {
                // `0 < A < d` implies `r == A`, which is stored in `N`, so this cannot fail.
                remainder_in_n
                    .unwrap_or_else(|| panic!("(A mod d) == A for 0 < A < d must fit into `N`"))
            } else {
                N::zero()
            };
        }
        self.coeff_sum = new_coeff_sum;

        None
    }

    #[inline]
    fn variable_form_mir(&mut self, divisor: &BigInt) -> Option<PBConstraintEnum> {
        // Moving the negated literals to the right-hand side can underflow `N` (see
        // `variable_form_div`). The `remainder is larger than the coefficient sum` branch below
        // additionally negates the variable-form degree, so also require that `-A` is
        // representable; otherwise escalate the whole constraint to `BigInt`.
        let variable_form_degree = self.variable_form_degree_bigint();
        if TryInto::<N>::try_into(-variable_form_degree.clone()).is_err()
            || TryInto::<N>::try_into(variable_form_degree).is_err()
        {
            let mut widened = self.widen_to_bigint();
            widened.variable_form_mir(divisor);
            return Some(widened.into_smallest_type());
        }

        self.degree -= self
            .terms
            .iter()
            .filter(|t| t.lit.is_negated())
            .fold(N::zero(), |sum, t| sum + &t.coeff);

        // Compute the remainder of (A mod d).
        let remainder = self.degree.clone().into().mod_floor(divisor);
        // Special case if remainder is zero.
        if remainder.is_zero() {
            self.terms.clear();
            self.coeff_sum = N::zero();
            self.degree = N::zero();
            return None;
        }

        let mut new_coeff_sum = N::zero();
        let mut new_neg_coeff_sum = N::zero();
        // Try if we can perform the MIR cut in situ.
        if let Ok(divisor) = TryInto::<N>::try_into(divisor.clone()) {
            let remainder = remainder
                .try_into()
                .unwrap_or_else(|_| panic!("remainder should be small enough"));
            self.terms.retain_mut(|term| {
                if term.lit.is_negated() {
                    // The rule's expression is `ceil(a / d) * r - min((-a) mod d, r)`, and its
                    // result is bounded by `a` — but the leading product is not: it is the one
                    // product in either MIR routine whose factors come from different numbers
                    // (the quotient from the coefficient `a`, the remainder `r` from the degree),
                    // and for `a = f*d + s` with `s > 0` it reaches `f*r + r`, i.e. up to
                    // `a + d - 2`. That overflows `N` for a coefficient near `N::MAX`, which the
                    // release profile aborts on rather than silently wrapping back to the correct
                    // result. Reassociating into `f*r + (r - min(d - s, r))` is the same integer
                    // for every `a` (the `s == 0` case has to be split off, or the correction adds
                    // a spurious `r`), with both addends non-negative and their sum at most `a`,
                    // so no intermediate can leave the range of a value already known to fit `N`.
                    let negated_remainder = (-term.coeff.clone()).mod_floor(&divisor);
                    let quotient_part = term.coeff.div_floor(&divisor) * &remainder;
                    term.coeff = if negated_remainder.is_zero() {
                        quotient_part
                    } else {
                        quotient_part
                            + (remainder.clone() - negated_remainder.min(remainder.clone()))
                    };
                    new_neg_coeff_sum += &term.coeff;
                } else {
                    term.coeff = (term.coeff.div_floor(&divisor) * &remainder)
                        + (&term.coeff.mod_floor(&divisor)).min(&remainder);
                }
                new_coeff_sum += &term.coeff;
                !term.coeff.is_zero()
            });
            self.degree = self.degree.div_ceil(&divisor) * remainder + new_neg_coeff_sum;
        } else {
            // The divisor does not fit into `N`, so `d >= N::MAX + 1`: it is strictly larger than
            // every coefficient, and at least `|A|`. As in `normalized_form_mir`, `d >= |A|` is
            // not strict — but quotient `-1` needs `A == -d`, which makes `r == 0` and returned
            // above — so the quotient `ceil(A / d)` here is `1` for `A > 0` and `0` for `A < 0`
            // (`A == 0` implies `r == 0` and was handled above). Hard-coding it to `1` turns a
            // trivially true variable-form constraint into a strictly stronger one.
            let quotient_is_one = self.degree.is_positive();
            // Divisor is larger than coeff sum, then positive coefficients are min of remainders and negative coefficients are 1 - remainder.
            if let Ok(remainder_small_type) = TryInto::<N>::try_into(remainder.clone()) {
                // Remainder can still be represented correctly.
                self.terms.retain_mut(|term| {
                    if term.lit.is_negated() {
                        // Compute remainder of coefficient correctly in `BigInt`.
                        let coeff_remainder = -term.coeff.clone().into() + divisor;
                        if coeff_remainder >= remainder {
                            return false;
                        } else {
                            // The resulting (a_i mod d) - (A mod d) is negative, hence (A mod d) - (a_i mod d) is positive.
                            term.coeff = (-coeff_remainder + &remainder)
                                .try_into()
                                .unwrap_or_else(|_| panic!("sum should be small enough"))
                        }
                        new_neg_coeff_sum += &term.coeff;
                    } else if term.coeff > remainder_small_type {
                        term.coeff = remainder_small_type.clone();
                    }
                    new_coeff_sum += &term.coeff;
                    true
                });
                // Degree becomes `ceil(A / d) * r`, shifted back into normalized form by adding
                // the (new) coefficients of the negated literals.
                self.degree = if quotient_is_one {
                    remainder_small_type
                } else {
                    N::zero()
                } + new_neg_coeff_sum;
            } else {
                // Remainder is larger than coeff sum, hence A <= 0.
                let neg_degree = -self.degree.clone();
                self.terms.retain_mut(|term| {
                    if term.lit.is_negated() {
                        // If term is negated and a_i < A, then coeff is a_i - A, but a_i is stored negated, so -a_i < -A and then -a_i - -A.
                        if term.coeff > neg_degree {
                            term.coeff -= &neg_degree;
                        } else {
                            return false;
                        }
                        new_neg_coeff_sum += &term.coeff;
                    }
                    new_coeff_sum += &term.coeff;
                    true
                });
                self.degree = N::zero() + new_neg_coeff_sum;
            }
        }
        self.coeff_sum = new_coeff_sum;

        None
    }

    #[inline]
    fn propagate(&self, assignment: &mut Assignment<BooleanVar>) -> ConstraintPropagationResult {
        if self.is_trivial() {
            return ConstraintPropagationResult::NoPropagation;
        }

        let mut slack = -self.degree.clone();
        for term in self.terms.iter() {
            if unsafe { assignment.get_lit_value_unchecked(term.lit) } != BoolValue::Assigned(false)
            {
                slack += term.coeff.to_owned();
            }
        }

        if slack.is_negative() {
            return ConstraintPropagationResult::Conflict;
        }

        let mut propagated = false;
        for term in self.terms.iter() {
            if unsafe { assignment.get_lit_value_unchecked(term.lit) } == BoolValue::Unassigned
                && term.coeff > slack
            {
                propagated = true;
                unsafe { assignment.set_lit_value_unchecked(term.lit, BoolValue::Assigned(true)) };
            }
        }

        if propagated {
            ConstraintPropagationResult::Propagated
        } else {
            ConstraintPropagationResult::NoPropagation
        }
    }

    #[inline]
    fn traced_propagate(&self, assignment: &mut Assignment<BooleanVar>) -> Vec<Lit> {
        if self.is_trivial() {
            return vec![];
        }

        let mut slack = -self.degree.clone();
        for term in self.terms.iter() {
            if unsafe { assignment.get_lit_value_unchecked(term.lit) } != BoolValue::Assigned(false)
            {
                slack += term.coeff.to_owned();
            }
        }

        if slack.is_negative() {
            panic!("This did not propagate to conflict earlier!")
        }

        let mut lits = Vec::new();
        for term in self.terms.iter() {
            if unsafe { assignment.get_lit_value_unchecked(term.lit) } == BoolValue::Unassigned
                && term.coeff > slack
            {
                lits.push(term.lit);
                unsafe { assignment.set_lit_value_unchecked(term.lit, BoolValue::Assigned(true)) };
            }
        }

        lits
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

    fn into_smallest_type(self) -> PBConstraintEnum {
        // Check if we can use Clause or cardinality constraint.
        if self.all_coeff_one() {
            if self.degree.is_one() {
                return Clause::from_lits(self.terms.iter().map(|t| t.lit).collect()).into();
            } else if let Ok(degree) = self.degree.to_owned().try_into() {
                return Cardinality::from_lits(self.terms.iter().map(|t| t.lit).collect(), degree)
                    .into();
            };
        }

        // General PB constraint. Check for smallest possible type.
        if let Ok(coeff_sum) = TryInto::<i64>::try_into(self.coeff_sum.clone())
            && let Ok(degree) = TryInto::<i64>::try_into(self.degree.clone())
        {
            if TypeId::of::<N>() == TypeId::of::<i64>() {
                return self.into();
            }
            GeneralPBConstraint::from_terms(
                self.terms
                    .into_iter()
                    .map(|t| {
                        GeneralPBTerm::new(
                            unsafe { TryInto::<i64>::try_into(t.coeff).unwrap_unchecked() },
                            t.lit,
                        )
                    })
                    .collect(),
                coeff_sum,
                degree,
            )
            .into()
        } else if let Ok(coeff_sum) = TryInto::<i128>::try_into(self.coeff_sum.clone())
            && let Ok(degree) = TryInto::<i128>::try_into(self.degree.clone())
        {
            if TypeId::of::<N>() == TypeId::of::<i128>() {
                return self.into();
            }
            GeneralPBConstraint::from_terms(
                self.terms
                    .into_iter()
                    .map(|t| {
                        GeneralPBTerm::new(
                            unsafe { TryInto::<i128>::try_into(t.coeff).unwrap_unchecked() },
                            t.lit,
                        )
                    })
                    .collect(),
                coeff_sum,
                degree,
            )
            .into()
        } else {
            self.into()
        }
    }

    fn get_reification(&self, var: VarIdx, direction: ReificationDir) -> PBConstraintEnum {
        // The reification of a variable is the reification of the positive literal on that
        // variable; [`GeneralPBConstraint::get_lit_reification()`] is where the overflow guard
        // lives, so both entry points build the reification in `BigInt` and narrow again.
        self.get_lit_reification(&[Lit::from_var(var, false)], direction)
    }
}

impl<N: Int> From<&Clause> for GeneralPBConstraint<N> {
    #[inline]
    fn from(value: &Clause) -> Self {
        let terms: Vec<_> = value
            .get_lits()
            .map(|&l| GeneralPBTerm::new(N::one(), l))
            .collect();
        GeneralPBConstraint {
            terms,
            coeff_sum: N::from(value.len() as i64),
            degree: N::one(),
        }
    }
}

impl<N: Int> From<&Cardinality> for GeneralPBConstraint<N> {
    #[inline]
    fn from(value: &Cardinality) -> Self {
        let terms: Vec<_> = value
            .get_lits()
            .map(|&l| GeneralPBTerm::new(N::one(), l))
            .collect();
        GeneralPBConstraint {
            terms,
            coeff_sum: N::from(value.len() as i64),
            degree: N::from(*value.get_degree()),
        }
    }
}

impl<N: Int> ToPrettyString for GeneralPBConstraint<N> {
    #[inline]
    fn to_pretty_string<V: VarNameLookup>(&self, var_names: &V) -> String {
        let mut out = String::with_capacity(self.terms.len() * 4);
        for term in self.terms.iter() {
            out.push_str(&term.coeff.to_string());
            out.push(' ');
            out.push_str(&term.lit.to_pretty_string(var_names));
            out.push(' ');
        }
        out.push_str(">= ");
        out.push_str(&self.degree.to_string());
        out
    }
}
