//! Representation of the terms of a pseudo-Boolean constraint while it is being parsed.
//!
//! Both the OPB parser (see [`crate::opb_parser`]) and the proof parser (see
//! [`crate::pbp_parser`]) accept the same constraint syntax, including the reification
//! shorthands `==>`, `<==` and, in the formula file only, `<==>`. They collect the terms into a
//! [`GenericTerms`] and hand it, together with the [`Reification`] the constraint is written with,
//! to [`generate_constraints`], which turns the parsed constraint into the pseudo-Boolean
//! constraints it stands for.

use malachite_bigint::BigInt;
use veripb_formula::general_pb_term::GeneralPBTerm;
use veripb_formula::lit::Lit;
use veripb_formula::pb_constraint::{Int, constraint_from_terms_and_coeff_sum};
use veripb_formula::prelude::{GeneralPBConstraint, PBConstraintEnum, ReificationDir};

/// A pair of constraints in the order in which they are loaded. A constraint that stands for one
/// pseudo-Boolean constraint only has the first entry; an equality has its `>=` direction followed
/// by its `<=` direction, and an equivalence its `==>` direction followed by its `<==` direction.
pub type OptionalConstraintPair = (Option<PBConstraintEnum>, Option<PBConstraintEnum>);

/// The reification shorthand a constraint is written with, if any.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Reification {
    /// A plain constraint, written without a reification shorthand.
    None,
    /// `<literals> ==> <constraint>`: the conjunction of the literals implies the constraint.
    LitsImplIneq(Vec<Lit>),
    /// `<literal> <== <constraint>`: the constraint implies the literal.
    IneqImplLit(Lit),
    /// `<literal> <==> <constraint>`: both of the above, as two constraints.
    Equivalence(Lit),
}

/// Supported comparison operators used for parsing pseudo-Boolean constraints.
#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum Comparator {
    GreaterEqual,
    LessEqual,
    Equal,
}

/// The terms of a pseudo-Boolean constraint as they are written, together with its degree and the
/// sum of the absolute values of its coefficients.
///
/// The terms are kept as they are parsed, so a coefficient can be negative and a variable can
/// occur more than once. Normalizing them is left to [`GeneralPBConstraint::from_terms()`], which
/// every constraint constructed from these terms goes through.
#[derive(Debug, Clone, Default)]
pub struct GenericTerms<N: Int> {
    terms: Vec<GeneralPBTerm<N>>,
    degree: N,
    sum: N,
}

impl<N: Int> GenericTerms<N> {
    /// Add a non-negative `coefficient` to the sum of the absolute values of the coefficients.
    ///
    /// A negative coefficient contributes its absolute value to the sum, so it goes to
    /// [`Self::checked_sub_coefficient`] instead.
    ///
    /// This function returns false if the addition would overflow and only adds `coefficient` if
    /// the addition does not overflow.
    pub fn checked_add_coefficient(&mut self, coefficient: &N) -> bool {
        debug_assert!(!coefficient.is_negative());
        match self.sum.checked_add(coefficient) {
            Some(sum) => {
                self.sum = sum;
                true
            }
            None => false,
        }
    }

    /// Add the absolute value of a negative `coefficient` to the sum of the absolute values of the
    /// coefficients, by subtracting the coefficient itself.
    ///
    /// This is the counterpart of [`Self::checked_add_coefficient`], and lets a caller that has
    /// the coefficient with its sign maintain the sum without materializing the absolute value.
    ///
    /// This function returns false if the subtraction would overflow and only subtracts
    /// `coefficient` if the subtraction does not overflow.
    pub fn checked_sub_coefficient(&mut self, coefficient: &N) -> bool {
        debug_assert!(coefficient.is_negative());
        match self.sum.checked_sub(coefficient) {
            Some(sum) => {
                self.sum = sum;
                true
            }
            None => false,
        }
    }

    /// Add a new term to the recorded terms with `coefficient`, which carries its own sign, and
    /// `literal`.
    pub fn add_term(&mut self, coefficient: N, literal: Lit) {
        self.terms.push(GeneralPBTerm::new(coefficient, literal));
    }

    /// Add `degree` to the currently tracked degree.
    ///
    /// This function returns false if the addition would overflow and only adds `degree` if the
    /// addition does not overflow.
    pub fn checked_add_degree(&mut self, degree: &N) -> bool {
        match self.degree.checked_add(degree) {
            Some(degree) => {
                self.degree = degree;
                true
            }
            None => false,
        }
    }

    /// Check that [`generate_constraints`] can be run for these terms without overflowing `N`.
    ///
    /// The comparator does not matter: `... <= degree` is turned into `... >= -degree` with every
    /// coefficient negated, which changes neither the magnitude of the degree nor the sum of the
    /// absolute coefficients. The [`Reification`] does matter, since it decides what is added to
    /// the constraint once it is normalized.
    pub fn is_overflow_safe(&self, reification: &Reification) -> bool {
        // Normalizing moves at most the sum of the absolute coefficients from one side of the
        // constraint to the other, in either direction, so this bounds the degree the normalized
        // constraint can have.
        let Some(max_degree) = self
            .abs_degree()
            .and_then(|degree| degree.checked_add(&self.sum))
        else {
            return false;
        };
        match reification {
            // A constraint without a reification is not touched after it is normalized.
            Reification::None => true,
            Reification::LitsImplIneq(literals) => {
                self.is_lits_impl_ineq_safe(&max_degree, literals.len())
            }
            Reification::IneqImplLit(_) => self.is_ineq_impl_lit_safe(&max_degree),
            // An equivalence reifies the same constraint in both directions.
            Reification::Equivalence(_) => {
                self.is_lits_impl_ineq_safe(&max_degree, 1)
                    && self.is_ineq_impl_lit_safe(&max_degree)
            }
        }
    }

    /// Check that reifying with a right implication over `num_literals` literals fits into `N`,
    /// which adds one term per literal, at the degree as coefficient.
    fn is_lits_impl_ineq_safe(&self, max_degree: &N, num_literals: usize) -> bool {
        max_degree
            .checked_mul(&N::from(num_literals as i64))
            .is_some_and(|temp| temp.checked_add(&self.sum).is_some())
    }

    /// Check that reifying with a left implication fits into `N`, which adds the consequent at the
    /// degree of the negated constraint as coefficient.
    fn is_ineq_impl_lit_safe(&self, max_degree: &N) -> bool {
        self.sum
            .checked_add(max_degree)
            .and_then(|temp| temp.checked_add(&N::from(1)))
            .is_some_and(|new_degree| new_degree.checked_add(&self.sum).is_some())
    }

    /// The absolute value of the degree, or [`None`] if it is not representable in `N`.
    fn abs_degree(&self) -> Option<N> {
        if self.degree.is_negative() {
            N::zero().checked_sub(&self.degree)
        } else {
            Some(self.degree.clone())
        }
    }

    /// Take this structure and return the internal fields of this structure.
    pub fn destruct(self) -> (Vec<GeneralPBTerm<N>>, N, N) {
        (self.terms, self.degree, self.sum)
    }
}

impl From<GenericTerms<i64>> for GenericTerms<i128> {
    fn from(terms: GenericTerms<i64>) -> Self {
        GenericTerms::<i128> {
            terms: terms.terms.into_iter().map(|t| t.into()).collect(),
            degree: i128::from(terms.degree),
            sum: i128::from(terms.sum),
        }
    }
}

impl From<GenericTerms<i64>> for GenericTerms<BigInt> {
    fn from(terms: GenericTerms<i64>) -> Self {
        GenericTerms::<BigInt> {
            terms: terms.terms.into_iter().map(|t| t.into()).collect(),
            degree: BigInt::from(terms.degree),
            sum: BigInt::from(terms.sum),
        }
    }
}

impl From<GenericTerms<i128>> for GenericTerms<BigInt> {
    fn from(terms: GenericTerms<i128>) -> Self {
        GenericTerms::<BigInt> {
            terms: terms.terms.into_iter().map(|t| t.into()).collect(),
            degree: BigInt::from(terms.degree),
            sum: BigInt::from(terms.sum),
        }
    }
}

/// Turn a parsed constraint into the pseudo-Boolean constraints it stands for.
///
/// A right implication (`==>`) reifies on the conjunction of its literals and can be combined with
/// an equality, which is split into two constraints; a left implication (`<==`) and an equivalence
/// (`<==>`) have exactly one literal and can not. The entries of the returned pair are in the order
/// in which the constraints are loaded, see [`OptionalConstraintPair`].
///
/// **Note:** The caller has to check with [`GenericTerms::is_overflow_safe`] that the arithmetic
/// below fits into `N`.
pub fn generate_constraints<N: Int>(
    terms: GenericTerms<N>,
    comparator: Comparator,
    reification: &Reification,
) -> OptionalConstraintPair
where
    PBConstraintEnum: From<GeneralPBConstraint<N>>,
{
    if let Reification::Equivalence(literal) = reification {
        // An equivalence can not be combined with an equality, so there is a single constraint to
        // reify, and the pair holds its two directions rather than a `>=` and a `<=` direction.
        let (terms, degree, coeff_sum) = match comparator {
            Comparator::LessEqual => into_greater_equal(terms),
            _ => terms.destruct(),
        };
        // Reifying carries the literal at the degree as coefficient, so the constraint has to be
        // normalized first: terms that cancel each other change the degree.
        let constraint = GeneralPBConstraint::from_terms(terms, coeff_sum, degree);
        let literals = std::slice::from_ref(literal);
        return (
            Some(constraint.get_lit_reification(literals, ReificationDir::VarImplIneq)),
            Some(constraint.get_lit_reification(literals, ReificationDir::IneqImplVar)),
        );
    }
    let (geq_terms, leq_terms) = match comparator {
        Comparator::GreaterEqual => (Some(terms), None),
        Comparator::LessEqual => (None, Some(terms)),
        Comparator::Equal => (Some(terms.clone()), Some(terms)),
    };
    let geq_constraint = geq_terms.map(|terms| {
        let (terms, degree, coeff_sum) = terms.destruct();
        generate_constraint(terms, degree, coeff_sum, reification)
    });
    let leq_constraint = leq_terms.map(|terms| {
        let (terms, degree, coeff_sum) = into_greater_equal(terms);
        generate_constraint(terms, degree, coeff_sum, reification)
    });
    (geq_constraint, leq_constraint)
}

/// Turn `... <= degree` into the same constraint written as `... >= -degree`, with every
/// coefficient negated.
fn into_greater_equal<N: Int>(terms: GenericTerms<N>) -> (Vec<GeneralPBTerm<N>>, N, N) {
    let (mut terms, degree, coeff_sum) = terms.destruct();
    for term in &mut terms {
        term.coeff = -term.coeff.clone();
    }
    (terms, -degree, coeff_sum)
}

/// Turn the terms and degree of a single `>=` constraint into the pseudo-Boolean constraint it
/// stands for, reified as `reification` says.
fn generate_constraint<N: Int>(
    terms: Vec<GeneralPBTerm<N>>,
    degree: N,
    coeff_sum: N,
    reification: &Reification,
) -> PBConstraintEnum
where
    PBConstraintEnum: From<GeneralPBConstraint<N>>,
{
    let (literals, direction) = match reification {
        Reification::None => {
            return constraint_from_terms_and_coeff_sum(terms, degree, coeff_sum);
        }
        Reification::LitsImplIneq(literals) => (literals.as_slice(), ReificationDir::VarImplIneq),
        Reification::IneqImplLit(literal) => {
            (std::slice::from_ref(literal), ReificationDir::IneqImplVar)
        }
        Reification::Equivalence(_) => {
            unreachable!("an equivalence is handled by generate_constraints")
        }
    };
    // The literals are carried at the degree as coefficient, so the constraint has to be
    // normalized before it is reified: terms that cancel each other change the degree.
    GeneralPBConstraint::from_terms(terms, coeff_sum, degree)
        .get_lit_reification(literals, direction)
}
