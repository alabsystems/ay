// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Exact checker for Alethe's premise-free `poly_simp` rule.
//!
//! Carcara accepts `(cl (= lhs rhs))` under `poly_simp` when distributing
//! arithmetic `+`, `-`, and `*` makes both sides the same polynomial.  This
//! module independently implements a bounded subset of that rule for Int and
//! Real terms.  Unsupported syntax and every resource-cap trip decline; no
//! solver result or producer annotation is trusted.

use std::collections::BTreeMap;
use std::mem::size_of;

use ay_core::{Constant, Sort, Symbol, TermData, TermId, TermStore};
use num_bigint::BigInt;
use num_rational::BigRational;
use num_traits::{One, Zero};

const MAX_NODES: usize = 100_000;
const MAX_DEPTH: usize = 256;
const MAX_MONOMIALS: usize = 16_384;
const MAX_DEGREE: usize = 256;
const MAX_COEFFICIENT_BITS: u64 = 4_096;
/// Cumulative factor slots copied/created while normalizing one equality.
const MAX_AGGREGATE_FACTORS: usize = 1_048_576;
/// Conservative cumulative allocation estimate for produced map entries.
const MAX_ESTIMATED_ALLOCATION_BYTES: usize = 64 * 1024 * 1024;
/// Meter scalar arithmetic plus monomial-copy work independently of node count.
const MAX_NORMALIZATION_WORK: usize = 2_000_000;

type Monomial = Vec<TermId>;

#[derive(Clone, Default, PartialEq, Eq)]
struct Polynomial {
    terms: BTreeMap<Monomial, BigRational>,
}

impl Polynomial {
    fn constant(value: BigRational, budget: &mut ParseBudget) -> Option<Self> {
        check_rational(&value)?;
        let mut result = Self::default();
        if !value.is_zero() {
            budget.charge_entry(&[], &value)?;
            result.terms.insert(Vec::new(), value);
        }
        Some(result)
    }

    fn atom(term: TermId, budget: &mut ParseBudget) -> Option<Self> {
        let coefficient = BigRational::one();
        budget.charge_entry(&[term], &coefficient)?;
        Some(Self {
            terms: BTreeMap::from([(vec![term], BigRational::one())]),
        })
    }

    fn add_scaled(
        &mut self,
        other: &Self,
        scale: &BigRational,
        budget: &mut ParseBudget,
    ) -> Option<()> {
        check_rational(scale)?;
        for (monomial, coefficient) in &other.terms {
            let scaled = coefficient * scale;
            check_rational(&scaled)?;
            let next = self
                .terms
                .get(monomial)
                .map_or_else(|| scaled.clone(), |old| old + &scaled);
            check_rational(&next)?;
            budget.charge_entry(monomial, &next)?;
            if next.is_zero() {
                self.terms.remove(monomial);
            } else {
                self.terms.insert(monomial.clone(), next);
            }
            if self.terms.len() > MAX_MONOMIALS {
                return None;
            }
        }
        Some(())
    }

    fn multiply(&self, other: &Self, budget: &mut ParseBudget) -> Option<Self> {
        let products = self.terms.len().checked_mul(other.terms.len())?;
        if products > MAX_MONOMIALS {
            return None;
        }
        budget.charge_work(products)?;
        let mut result = Self::default();
        for (left_monomial, left_coefficient) in &self.terms {
            for (right_monomial, right_coefficient) in &other.terms {
                let mut monomial =
                    Vec::with_capacity(left_monomial.len().checked_add(right_monomial.len())?);
                monomial.extend_from_slice(left_monomial);
                monomial.extend_from_slice(right_monomial);
                if monomial.len() > MAX_DEGREE {
                    return None;
                }
                monomial.sort_unstable();
                let coefficient = left_coefficient * right_coefficient;
                check_rational(&coefficient)?;
                result.add_scaled(
                    &Self {
                        terms: BTreeMap::from([(monomial, coefficient)]),
                    },
                    &BigRational::one(),
                    budget,
                )?;
            }
        }
        Some(result)
    }
}

struct ParseBudget {
    nodes_left: usize,
    normalization_work: usize,
    aggregate_factors: usize,
    estimated_allocation_bytes: usize,
}

impl ParseBudget {
    fn new() -> Self {
        Self {
            nodes_left: MAX_NODES,
            normalization_work: 0,
            aggregate_factors: 0,
            estimated_allocation_bytes: 0,
        }
    }

    fn visit(&mut self, depth: usize) -> Option<()> {
        if depth > MAX_DEPTH {
            return None;
        }
        self.nodes_left = self.nodes_left.checked_sub(1)?;
        Some(())
    }

    fn charge_work(&mut self, amount: usize) -> Option<()> {
        self.normalization_work = self.normalization_work.checked_add(amount)?;
        (self.normalization_work <= MAX_NORMALIZATION_WORK).then_some(())
    }

    fn charge_entry(&mut self, monomial: &[TermId], coefficient: &BigRational) -> Option<()> {
        self.charge_work(monomial.len().checked_add(1)?)?;
        self.aggregate_factors = self.aggregate_factors.checked_add(monomial.len())?;
        if self.aggregate_factors > MAX_AGGREGATE_FACTORS {
            return None;
        }
        let coefficient_bits =
            bigint_bits(coefficient.numer()).checked_add(bigint_bits(coefficient.denom()))?;
        let coefficient_bytes = usize::try_from(coefficient_bits.checked_add(7)? / 8).ok()?;
        let factor_bytes = monomial.len().checked_mul(size_of::<TermId>())?;
        let estimated = 64usize
            .checked_add(factor_bytes)?
            .checked_add(coefficient_bytes)?;
        self.estimated_allocation_bytes = self.estimated_allocation_bytes.checked_add(estimated)?;
        (self.estimated_allocation_bytes <= MAX_ESTIMATED_ALLOCATION_BYTES).then_some(())
    }
}

fn bigint_bits(value: &BigInt) -> u64 {
    value.bits()
}

fn check_rational(value: &BigRational) -> Option<()> {
    let bits = bigint_bits(value.numer()).checked_add(bigint_bits(value.denom()))?;
    (bits <= MAX_COEFFICIENT_BITS).then_some(())
}

fn check_integer(value: &BigInt) -> Option<()> {
    // Converting an integer to a rational adds the canonical denominator 1.
    // Check the eventual coefficient size while the stored integer is still
    // borrowed, before cloning its heap allocation.
    let bits = bigint_bits(value).checked_add(1)?;
    (bits <= MAX_COEFFICIENT_BITS).then_some(())
}

fn parse_polynomial(
    terms: &TermStore,
    term: TermId,
    budget: &mut ParseBudget,
    depth: usize,
) -> Option<Polynomial> {
    budget.visit(depth)?;
    let term_sort = terms.sort(term);
    if !matches!(term_sort, Sort::Int | Sort::Real) {
        return None;
    }
    match terms.get(term) {
        TermData::Const(Constant::Int(value)) if term_sort == &Sort::Int => {
            check_integer(value)?;
            Polynomial::constant(BigRational::from(value.clone()), budget)
        }
        TermData::Const(Constant::Rational(value)) if term_sort == &Sort::Real => {
            check_rational(&value.0)?;
            Polynomial::constant(value.0.clone(), budget)
        }
        // A numeric constant must use the canonical constant variant for its
        // sort. Do not let malformed constant/sort pairs fall through as
        // opaque atoms merely because normal `TermStore` builders cannot
        // construct them today.
        TermData::Const(_) => None,
        TermData::App(Symbol::Named(name), args)
            if name == "+"
                && args.len() >= 2
                && args.len() <= budget.nodes_left
                && args.iter().all(|&arg| terms.sort(arg) == term_sort) =>
        {
            let mut result = Polynomial::default();
            for &arg in args {
                let parsed = parse_polynomial(terms, arg, budget, depth + 1)?;
                result.add_scaled(&parsed, &BigRational::one(), budget)?;
            }
            Some(result)
        }
        TermData::App(Symbol::Named(name), args)
            if name == "-"
                && !args.is_empty()
                && args.len() <= budget.nodes_left
                && args.iter().all(|&arg| terms.sort(arg) == term_sort) =>
        {
            let mut result = if args.len() == 1 {
                Polynomial::default()
            } else {
                parse_polynomial(terms, args[0], budget, depth + 1)?
            };
            let start = usize::from(args.len() != 1);
            for &arg in &args[start..] {
                let parsed = parse_polynomial(terms, arg, budget, depth + 1)?;
                result.add_scaled(&parsed, &-BigRational::one(), budget)?;
            }
            Some(result)
        }
        TermData::App(Symbol::Named(name), args)
            if name == "*"
                && args.len() >= 2
                && args.len() <= budget.nodes_left
                && args.iter().all(|&arg| terms.sort(arg) == term_sort) =>
        {
            let mut result = Polynomial::constant(BigRational::one(), budget)?;
            for &arg in args {
                let parsed = parse_polynomial(terms, arg, budget, depth + 1)?;
                result = result.multiply(&parsed, budget)?;
            }
            Some(result)
        }
        TermData::App(Symbol::Named(name), args)
            if name == "to_real"
                && !terms.to_real_is_shadowed()
                && term_sort == &Sort::Real
                && args.len() == 1
                && terms.sort(args[0]) == &Sort::Int =>
        {
            parse_polynomial(terms, args[0], budget, depth + 1)
        }
        // These spellings are reserved arithmetic operators, not opaque
        // polynomial atoms. A malformed arity or sort must fail closed rather
        // than acquire an uninterpreted meaning that the wire checker will not
        // share.
        TermData::App(Symbol::Named(name), _)
            if matches!(name.as_str(), "+" | "-" | "*" | "to_real") =>
        {
            None
        }
        _ => Polynomial::atom(term, budget),
    }
}

fn polynomial_identity(terms: &TermStore, clause: &[TermId]) -> Result<(), String> {
    let [literal] = clause else {
        return Err("poly_simp requires one equality literal".to_string());
    };
    let TermData::App(Symbol::Named(name), args) = terms.get(*literal) else {
        return Err("poly_simp conclusion is not an equality".to_string());
    };
    if name != "=" || args.len() != 2 {
        return Err("poly_simp conclusion is not a binary equality".to_string());
    }
    if terms.sort(*literal) != &Sort::Bool {
        return Err("poly_simp conclusion equality must have Bool sort".to_string());
    }
    let sort = terms.sort(args[0]);
    if !matches!(sort, Sort::Int | Sort::Real) || terms.sort(args[1]) != sort {
        return Err("poly_simp equality must have one numeric sort".to_string());
    }
    let mut budget = ParseBudget::new();
    let left = parse_polynomial(terms, args[0], &mut budget, 0)
        .ok_or_else(|| "poly_simp left side exceeds the supported envelope".to_string())?;
    let right = parse_polynomial(terms, args[1], &mut budget, 0)
        .ok_or_else(|| "poly_simp right side exceeds the supported envelope".to_string())?;
    if left == right {
        Ok(())
    } else {
        Err("poly_simp sides normalize to different polynomials".to_string())
    }
}

/// Whether the clause is an exact premise-free `poly_simp` identity.
#[must_use]
pub fn recognize_arith_poly_simp(terms: &TermStore, clause: &[TermId]) -> bool {
    polynomial_identity(terms, clause).is_ok()
}

#[cfg(test)]
mod tests {
    use super::*;

    fn ring_terms(offset: i64) -> (TermStore, TermId) {
        let mut terms = TermStore::new();
        let i = terms.mk_var("i", Sort::Int);
        let one = terms.mk_int(BigInt::from(1));
        let two = terms.mk_int(BigInt::from(2));
        let offset = terms.mk_int(BigInt::from(offset));
        let i_plus_one = terms.mk_add(vec![i, one]);
        let left = terms.mk_mul(vec![i_plus_one, i_plus_one]);
        let i_squared = terms.mk_mul(vec![i, i]);
        let twice_i = terms.mk_mul(vec![two, i]);
        let tail = terms.mk_add(vec![twice_i, offset]);
        let right = terms.mk_add(vec![i_squared, tail]);
        let equality = terms.mk_eq(left, right);
        (terms, equality)
    }

    #[test]
    fn recognizes_square_successor_ring_identity() {
        let (terms, equality) = ring_terms(1);
        assert!(recognize_arith_poly_simp(&terms, &[equality]));
        assert!(crate::recognize_arith_clause_tautology(&terms, &[equality]));
    }

    #[test]
    fn rejects_nearby_false_polynomial_equality() {
        let (terms, equality) = ring_terms(2);
        assert!(!recognize_arith_poly_simp(&terms, &[equality]));
    }

    #[test]
    fn rejects_oversized_numeric_constant_before_polynomial_ownership() {
        let mut terms = TermStore::new();
        let shift = MAX_COEFFICIENT_BITS as usize;
        let oversized_int = terms.mk_int(BigInt::one() << shift);
        let int_equality = terms.mk_eq(oversized_int, oversized_int);
        let oversized_real = terms.mk_rational(BigRational::from_integer(BigInt::one() << shift));
        let real_equality = terms.mk_eq(oversized_real, oversized_real);

        assert!(
            !recognize_arith_poly_simp(&terms, &[int_equality]),
            "an oversized stored integer must fail closed before its allocation is cloned"
        );
        assert!(
            !recognize_arith_poly_simp(&terms, &[real_equality]),
            "an oversized stored rational must fail closed before its allocation is cloned"
        );
    }

    #[test]
    fn accepts_exact_to_real_coercions_with_homogeneous_real_arithmetic() {
        let mut terms = TermStore::new();
        let x = terms.mk_var("coerced_poly_x", Sort::Int);
        let one_int = terms.mk_int(BigInt::one());
        let x_plus_one = terms.mk_app(Symbol::named("+"), [x, one_int], Sort::Int);
        let coerced_sum = terms.mk_app(Symbol::named("to_real"), [x_plus_one], Sort::Real);
        let coerced_x = terms.mk_app(Symbol::named("to_real"), [x], Sort::Real);
        let one_real = terms.mk_rational(BigRational::one());
        let real_sum = terms.mk_app(Symbol::named("+"), [coerced_x, one_real], Sort::Real);
        let equality = terms.mk_app(Symbol::named("="), [coerced_sum, real_sum], Sort::Bool);

        assert!(recognize_arith_poly_simp(&terms, &[equality]));
    }

    #[test]
    fn rejects_user_shadowed_to_real_ring_identity_in_both_exact_checkers() {
        let mut terms = TermStore::new();
        let x = terms.mk_var("shadowed_poly_x", Sort::Int);
        let one_int = terms.mk_int(BigInt::one());
        let x_plus_one = terms.mk_app(Symbol::named("+"), [x, one_int], Sort::Int);
        let applied_to_sum = terms.mk_app(Symbol::named("to_real"), [x_plus_one], Sort::Real);
        let applied_to_x = terms.mk_app(Symbol::named("to_real"), [x], Sort::Real);
        let one_real = terms.mk_rational(BigRational::one());
        let sum_after_application =
            terms.mk_app(Symbol::named("+"), [applied_to_x, one_real], Sort::Real);
        let equality = terms.mk_app(
            Symbol::named("="),
            [applied_to_sum, sum_after_application],
            Sort::Bool,
        );
        terms.mark_to_real_shadowed();

        assert!(
            !recognize_arith_poly_simp(&terms, &[equality]),
            "a user-shadowed uninterpreted to_real has no additive semantics"
        );
        assert!(
            !crate::recognize_arith_clause_tautology(&terms, &[equality]),
            "the shared strict arithmetic checker must honor the same shadow latch"
        );
    }

    #[test]
    fn rejects_malformed_arithmetic_sorts_arities_and_equality_sort() {
        let mut terms = TermStore::new();
        let x_int = terms.mk_var("malformed_poly_int", Sort::Int);
        let x_real = terms.mk_var("malformed_poly_real", Sort::Real);

        let mixed_add = terms.mk_app(Symbol::named("+"), [x_int, x_real], Sort::Int);
        let mixed_equality = terms.mk_app(Symbol::named("="), [mixed_add, mixed_add], Sort::Bool);
        assert!(
            !recognize_arith_poly_simp(&terms, &[mixed_equality]),
            "mixed Int/Real arithmetic without an explicit coercion must fail closed"
        );

        let bad_coercion = terms.mk_app(Symbol::named("to_real"), [x_real], Sort::Real);
        let bad_coercion_equality =
            terms.mk_app(Symbol::named("="), [bad_coercion, bad_coercion], Sort::Bool);
        assert!(
            !recognize_arith_poly_simp(&terms, &[bad_coercion_equality]),
            "to_real must have exactly an Int operand and Real result"
        );

        let bad_arity = terms.mk_app(Symbol::named("to_real"), [x_int, x_int], Sort::Real);
        let bad_arity_equality =
            terms.mk_app(Symbol::named("="), [bad_arity, bad_arity], Sort::Bool);
        assert!(
            !recognize_arith_poly_simp(&terms, &[bad_arity_equality]),
            "a malformed reserved operator must not become an opaque atom"
        );

        for operator in ["+", "*"] {
            let nullary = terms.mk_app(Symbol::named(operator), [], Sort::Int);
            let nullary_equality = terms.mk_app(Symbol::named("="), [nullary, nullary], Sort::Bool);
            assert!(
                !recognize_arith_poly_simp(&terms, &[nullary_equality]),
                "nullary {operator} must fail closed"
            );

            let unary = terms.mk_app(Symbol::named(operator), [x_int], Sort::Int);
            let unary_equality = terms.mk_app(Symbol::named("="), [unary, unary], Sort::Bool);
            assert!(
                !recognize_arith_poly_simp(&terms, &[unary_equality]),
                "unary {operator} must fail closed"
            );
        }

        let non_boolean_equality = terms.mk_app(Symbol::named("="), [x_int, x_int], Sort::Int);
        assert!(
            !recognize_arith_poly_simp(&terms, &[non_boolean_equality]),
            "a clause literal must be Boolean even when its operands are identical"
        );
    }

    #[test]
    fn rejects_expression_beyond_depth_cap() {
        let mut terms = TermStore::new();
        let x = terms.mk_var("deep_poly_x", Sort::Int);
        let zero = terms.mk_int(BigInt::zero());
        let mut expression = x;
        for _ in 0..=MAX_DEPTH {
            expression = terms.mk_app(Symbol::named("+"), [expression, zero], Sort::Int);
        }
        let equality = terms.mk_eq(expression, x);
        assert!(
            !recognize_arith_poly_simp(&terms, &[equality]),
            "an adversarial recursive polynomial must fail closed before stack exhaustion"
        );
    }

    #[test]
    fn flat_operator_arity_is_gated_before_sort_scan_at_exact_remaining_boundary() {
        let mut terms = TermStore::new();
        let atom = terms.mk_var("flat_poly_x", Sort::Int);
        let exact = terms.mk_app(Symbol::named("+"), [atom, atom, atom], Sort::Int);
        let over = terms.mk_app(Symbol::named("+"), [atom, atom, atom, atom], Sort::Int);

        let mut exact_budget = ParseBudget::new();
        exact_budget.nodes_left = 4;
        assert!(parse_polynomial(&terms, exact, &mut exact_budget, 0).is_some());
        assert_eq!(exact_budget.nodes_left, 0);

        let mut over_budget = ParseBudget::new();
        over_budget.nodes_left = 4;
        assert!(parse_polynomial(&terms, over, &mut over_budget, 0).is_none());
        assert_eq!(
            over_budget.nodes_left, 3,
            "an over-arity application must decline before scanning or visiting children"
        );
    }

    #[test]
    fn rejects_sum_beyond_monomial_cap() {
        let mut terms = TermStore::new();
        let atoms: Vec<TermId> = (0..=MAX_MONOMIALS)
            .map(|index| terms.mk_var(format!("many_poly_{index}"), Sort::Int))
            .collect();
        let sum = terms.mk_app(Symbol::named("+"), atoms, Sort::Int);
        let equality = terms.mk_eq(sum, sum);
        assert!(
            !recognize_arith_poly_simp(&terms, &[equality]),
            "a polynomial requiring too many resident monomials must fail closed"
        );
    }

    #[test]
    fn cumulative_resource_meters_fail_closed_at_their_boundaries() {
        let mut terms = TermStore::new();
        let atom = terms.mk_var("metered_poly_x", Sort::Int);
        let coefficient = BigRational::one();

        let mut factors = ParseBudget::new();
        factors.aggregate_factors = MAX_AGGREGATE_FACTORS;
        assert!(factors.charge_entry(&[atom], &coefficient).is_none());

        let mut bytes = ParseBudget::new();
        bytes.estimated_allocation_bytes = MAX_ESTIMATED_ALLOCATION_BYTES;
        assert!(bytes.charge_entry(&[], &coefficient).is_none());

        let mut work = ParseBudget::new();
        work.normalization_work = MAX_NORMALIZATION_WORK;
        assert!(work.charge_work(1).is_none());
    }

    #[test]
    fn dense_high_degree_polynomial_exhausts_cumulative_meter() {
        let mut terms = TermStore::new();
        let atoms: Vec<TermId> = (0..4_096)
            .map(|index| terms.mk_var(format!("dense_poly_{index}"), Sort::Int))
            .collect();
        let dense = terms.mk_app(Symbol::named("+"), atoms, Sort::Int);
        let multiplier = terms.mk_var("dense_poly_multiplier", Sort::Int);
        let mut factors = Vec::with_capacity(MAX_DEGREE + 1);
        factors.push(dense);
        factors.extend(std::iter::repeat_n(multiplier, MAX_DEGREE));
        let expanded = terms.mk_app(Symbol::named("*"), factors, Sort::Int);
        let equality = terms.mk_eq(expanded, expanded);

        assert!(
            !recognize_arith_poly_simp(&terms, &[equality]),
            "repeatedly copying a dense high-degree polynomial must fail closed at a cumulative cap"
        );
    }
}
