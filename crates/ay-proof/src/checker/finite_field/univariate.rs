// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//! Independent univariate finite-field refutations. Reconstruct the authored
//! polynomials, intersect their roots with X^p-X, and independently reconstruct
//! Boolean finite/cofinite root-set algebra. Complement retains excluded roots;
//! intersection is gcd, union lcm, and difference exact polynomial quotient.
//! X^p-X is square-free and has exactly the elements of F_p as roots (Fermat).
//! Thus a constant residual gcd certifies exhaustion without trusting a solver
//! polynomial, factor, root list or evaluator. See Shoup, A Computational
//! Introduction to Number Theory and Algebra, chapters 17/20.

use super::ProofCheckError;
use ay_core::{Constant, FiniteFieldSort, ProofId, Sort, Symbol, TermData, TermId, TermStore};
type Poly = Vec<u32>;

// Every stored polynomial is monic, square-free, and splits over F_p.
// Cofinite stores EXCLUDED roots, so complements never enumerate the field.
enum RootSet {
    Finite(Poly),
    Cofinite(Poly),
}
impl RootSet {
    fn complement(self) -> Self {
        match self {
            Self::Finite(p) => Self::Cofinite(p),
            Self::Cofinite(p) => Self::Finite(p),
        }
    }
}
struct Check<'a, 'p> {
    terms: &'a TermStore,
    field: Option<FiniteFieldSort>,
    variable: Option<TermId>,
    progress: &'p mut dyn FnMut(usize, usize) -> bool,
    work: usize,
}
impl Check<'_, '_> {
    fn pay(&mut self, work: usize, bytes: usize) -> Option<()> {
        self.work = self.work.checked_sub(work)?;
        (self.progress)(work, bytes).then_some(())
    }
    fn buffer(&mut self, count: usize) -> Option<Poly> {
        self.pay(count, count.checked_mul(std::mem::size_of::<u32>())?)?;
        let mut out = Vec::new();
        out.try_reserve_exact(count).ok()?;
        out.resize(count, 0);
        Some(out)
    }
    fn duplicate(&mut self, value: &[u32]) -> Option<Poly> {
        let mut out = self.buffer(value.len())?;
        out.copy_from_slice(value);
        Some(out)
    }
    fn trim(value: &mut Poly) {
        while value.last() == Some(&0) {
            value.pop();
        }
    }
    fn subtract(&self, a: u32, b: u32) -> Option<u32> {
        let p = u64::from(self.field?.modulus());
        Some(((u64::from(a) + p - u64::from(b)) % p) as u32)
    }
    fn sum(&self, a: u32, b: u32) -> Option<u32> {
        Some(((u64::from(a) + u64::from(b)) % u64::from(self.field?.modulus())) as u32)
    }
    fn product(&mut self, a: u32, b: u32) -> Option<u32> {
        self.pay(1, 0)?;
        Some((u64::from(a) * u64::from(b) % u64::from(self.field?.modulus())) as u32)
    }
    fn inverse(&mut self, value: u32) -> Option<u32> {
        if value == 0 {
            return None;
        }
        let mut base = value;
        let mut exponent = self.field?.modulus() - 2;
        let mut result = 1;
        while exponent != 0 {
            if exponent & 1 != 0 {
                result = self.product(result, base)?;
            }
            base = self.product(base, base)?;
            exponent >>= 1;
        }
        Some(result)
    }
    fn difference(&mut self, a: &[u32], b: &[u32]) -> Option<Poly> {
        let mut out = self.buffer(a.len().max(b.len()))?;
        for (i, coefficient) in out.iter_mut().enumerate() {
            *coefficient = self.subtract(
                a.get(i).copied().unwrap_or(0),
                b.get(i).copied().unwrap_or(0),
            )?;
        }
        Self::trim(&mut out);
        Some(out)
    }
    fn multiply(&mut self, a: &[u32], b: &[u32]) -> Option<Poly> {
        if a.is_empty() || b.is_empty() {
            return Some(Vec::new());
        }
        let mut out = self.buffer(a.len().checked_add(b.len())?.checked_sub(1)?)?;
        // Convolution by output degree, independently of producer traversal.
        for (degree, coefficient) in out.iter_mut().enumerate() {
            let low = degree.saturating_sub(b.len() - 1);
            let high = degree.min(a.len() - 1);
            for i in low..=high {
                let product = self.product(a[i], b[degree - i])?;
                *coefficient = self.sum(*coefficient, product)?;
            }
        }
        Self::trim(&mut out);
        Some(out)
    }
    fn division(&mut self, mut numerator: Poly, denominator: &[u32]) -> Option<(Poly, Poly)> {
        let inverse = self.inverse(*denominator.last()?)?;
        let mut quotient = self.buffer(
            numerator
                .len()
                .saturating_sub(denominator.len())
                .checked_add(1)?,
        )?;
        while numerator.len() >= denominator.len() && !numerator.is_empty() {
            self.pay(1, 0)?;
            let offset = numerator.len() - denominator.len();
            let scale = self.product(*numerator.last()?, inverse)?;
            quotient[offset] = scale;
            for (i, &coefficient) in denominator.iter().enumerate() {
                let product = self.product(scale, coefficient)?;
                numerator[offset + i] = self.subtract(numerator[offset + i], product)?;
            }
            Self::trim(&mut numerator);
        }
        Self::trim(&mut quotient);
        Some((quotient, numerator))
    }
    fn gcd(&mut self, mut a: Poly, mut b: Poly) -> Option<Poly> {
        while !b.is_empty() {
            let remainder = self.division(a, &b)?.1;
            a = b;
            b = remainder;
        }
        if let Some(&leading) = a.last() {
            let inverse = self.inverse(leading)?;
            for coefficient in &mut a {
                *coefficient = self.product(*coefficient, inverse)?;
            }
        }
        Some(a)
    }
    fn field_power(&mut self, modulus: &[u32]) -> Option<Poly> {
        // Left-to-right binary exponentiation of X^p modulo the authored gcd.
        let exponent = self.field?.modulus();
        let mut result = self.buffer(1)?;
        result[0] = 1;
        for bit in (0..32 - exponent.leading_zeros()).rev() {
            self.pay(1, 0)?;
            let square = self.multiply(&result, &result)?;
            result = self.division(square, modulus)?.1;
            if exponent & (1u32 << bit) != 0 {
                let product = self.multiply(&result, &[0, 1])?;
                result = self.division(product, modulus)?.1;
            }
        }
        Some(result)
    }
    fn parse(&mut self, term: TermId, depth: usize) -> Option<Poly> {
        self.pay(1, 0)?;
        let Sort::FiniteField(field) = self.terms.sort(term) else {
            return None;
        };
        if depth > 128 || self.field.is_some_and(|prior| prior != *field) {
            return None;
        }
        self.field = Some(*field);
        if let TermData::App(Symbol::Named(name), _) = self.terms.get(term) {
            self.pay(name.len(), 0)?;
            if self.terms.is_declared_function(name) {
                return None;
            }
        }
        match self.terms.get(term) {
            TermData::Var(..) => {
                if self.variable.is_some_and(|prior| prior != term) {
                    return None;
                }
                self.variable = Some(term);
                let mut out = self.buffer(2)?;
                out[1] = 1;
                Some(out)
            }
            TermData::Const(Constant::FiniteField {
                value,
                field: actual,
            }) if actual == field && *value < field.modulus() => {
                let mut out = self.buffer(usize::from(*value != 0))?;
                if let Some(coefficient) = out.first_mut() {
                    *coefficient = *value;
                }
                Some(out)
            }
            TermData::App(Symbol::Named(name), args) if args.len() <= 1024 => match name.as_str() {
                "ff.neg" if args.len() == 1 => {
                    let child = self.parse(args[0], depth + 1)?;
                    self.difference(&[], &child)
                }
                "ff.add" | "ff.bitsum" if args.len() >= 2 => {
                    let mut out = Vec::new();
                    let mut weight = 1;
                    for &arg in args {
                        let mut child = self.parse(arg, depth + 1)?;
                        for coefficient in &mut child {
                            *coefficient = self.product(*coefficient, weight)?;
                            *coefficient = self.subtract(0, *coefficient)?;
                        }
                        out = self.difference(&out, &child)?;
                        if name == "ff.bitsum" {
                            weight = self.sum(weight, weight)?;
                        }
                    }
                    Some(out)
                }
                "ff.mul" if args.len() >= 2 => {
                    let mut out = self.buffer(1)?;
                    out[0] = 1;
                    for &arg in args {
                        let child = self.parse(arg, depth + 1)?;
                        out = self.multiply(&out, &child)?;
                    }
                    Some(out)
                }
                _ => None,
            },
            _ => None,
        }
    }

    fn empty_set(&mut self) -> Option<RootSet> {
        let mut p = self.buffer(1)?;
        p[0] = 1;
        Some(RootSet::Finite(p))
    }
    fn field_roots(&mut self, p: Poly) -> Option<RootSet> {
        if p.is_empty() {
            return Some(self.empty_set()?.complement());
        }
        if p.len() == 1 {
            return self.empty_set();
        }
        let power = self.field_power(&p)?;
        let equation = self.difference(&power, &[0, 1])?;
        Some(RootSet::Finite(self.gcd(p, equation)?))
    }
    fn exact_quotient(&mut self, a: Poly, b: &Poly) -> Option<Poly> {
        let (q, r) = self.division(a, b)?;
        r.is_empty().then_some(q)
    }
    fn intersection(&mut self, a: RootSet, b: RootSet) -> Option<RootSet> {
        self.pay(1, 0)?;
        match (a, b) {
            // These identities do not depend on a modulus. Authored Boolean
            // constants can precede the first field term; all later authored
            // operands are still parsed and checked, even after an empty set.
            (RootSet::Finite(a), _) if a.len() == 1 => Some(RootSet::Finite(a)),
            (_, RootSet::Finite(b)) if b.len() == 1 => Some(RootSet::Finite(b)),
            (RootSet::Cofinite(a), b) if a.len() == 1 => Some(b),
            (a, RootSet::Cofinite(b)) if b.len() == 1 => Some(a),
            (RootSet::Finite(a), RootSet::Finite(b)) => Some(RootSet::Finite(self.gcd(a, b)?)),
            (RootSet::Finite(a), RootSet::Cofinite(b))
            | (RootSet::Cofinite(b), RootSet::Finite(a)) => {
                let copy = self.duplicate(&a)?;
                let common = self.gcd(copy, b)?;
                Some(RootSet::Finite(self.exact_quotient(a, &common)?))
            }
            (RootSet::Cofinite(a), RootSet::Cofinite(b)) => {
                let ac = self.duplicate(&a)?;
                let bc = self.duplicate(&b)?;
                let common = self.gcd(ac, bc)?;
                let quotient = self.exact_quotient(a, &common)?;
                Some(RootSet::Cofinite(self.multiply(&quotient, &b)?))
            }
        }
    }
    fn union(&mut self, a: RootSet, b: RootSet) -> Option<RootSet> {
        Some(
            self.intersection(a.complement(), b.complement())?
                .complement(),
        )
    }
    fn copy_set(&mut self, value: &RootSet) -> Option<RootSet> {
        Some(match value {
            RootSet::Finite(p) => RootSet::Finite(self.duplicate(p)?),
            RootSet::Cofinite(p) => RootSet::Cofinite(self.duplicate(p)?),
        })
    }
    fn symmetric_difference(&mut self, a: RootSet, b: RootSet) -> Option<RootSet> {
        let ac = self.copy_set(&a)?;
        let bc = self.copy_set(&b)?;
        let left = self.intersection(a, bc.complement())?;
        let right = self.intersection(ac.complement(), b)?;
        self.union(left, right)
    }
    fn boolean_set(&mut self, term: TermId, depth: usize) -> Option<RootSet> {
        self.pay(1, 0)?;
        if let TermData::App(Symbol::Named(name), _) = self.terms.get(term) {
            self.pay(name.len(), 0)?;
            if self.terms.is_declared_function(name) {
                return None;
            }
        }
        if depth > 128 || self.terms.sort(term) != &Sort::Bool {
            return None;
        }
        match self.terms.get(term) {
            TermData::Const(Constant::Bool(value)) => {
                let empty = self.empty_set()?;
                Some(if *value { empty.complement() } else { empty })
            }
            TermData::Not(child) => Some(self.boolean_set(*child, depth + 1)?.complement()),
            TermData::Ite(c, a, b) => {
                let yes = self.boolean_set(*c, depth + 1)?;
                let no = self.copy_set(&yes)?.complement();
                let left = self.boolean_set(*a, depth + 1)?;
                let right = self.boolean_set(*b, depth + 1)?;
                let left = self.intersection(yes, left)?;
                let right = self.intersection(no, right)?;
                self.union(left, right)
            }
            TermData::App(Symbol::Named(name), args) if args.len() <= 1024 => match name.as_str() {
                "not" if args.len() == 1 => {
                    Some(self.boolean_set(args[0], depth + 1)?.complement())
                }
                "and" | "or" => {
                    let empty = self.empty_set()?;
                    let mut out = if name == "and" {
                        empty.complement()
                    } else {
                        empty
                    };
                    for &arg in args {
                        let next = self.boolean_set(arg, depth + 1)?;
                        out = if name == "and" {
                            self.intersection(out, next)?
                        } else {
                            self.union(out, next)?
                        };
                    }
                    Some(out)
                }
                "xor" => {
                    let mut out = self.empty_set()?;
                    for &arg in args {
                        let next = self.boolean_set(arg, depth + 1)?;
                        out = self.symmetric_difference(out, next)?;
                    }
                    Some(out)
                }
                "=>" if args.len() == 2 => {
                    let left = self.boolean_set(args[0], depth + 1)?.complement();
                    let right = self.boolean_set(args[1], depth + 1)?;
                    self.union(left, right)
                }
                "=" | "distinct" if args.len() >= 2 => {
                    let mut out = self.empty_set()?.complement();
                    for i in 1..args.len() {
                        for j in 0..if name == "=" { 1 } else { i } {
                            if self.terms.sort(args[0]) == &Sort::Bool {
                                let left = self.boolean_set(args[i], depth + 1)?;
                                let right = self.boolean_set(args[j], depth + 1)?;
                                let different = self.symmetric_difference(left, right)?;
                                let next = if name == "=" {
                                    different.complement()
                                } else {
                                    different
                                };
                                out = self.intersection(out, next)?;
                                continue;
                            }
                            let left = self.parse(args[i], 0)?;
                            let right = self.parse(args[j], 0)?;
                            let difference = self.difference(&left, &right)?;
                            let roots = self.field_roots(difference)?;
                            let next = if name == "distinct" {
                                roots.complement()
                            } else {
                                roots
                            };
                            out = self.intersection(out, next)?;
                        }
                    }
                    Some(out)
                }
                _ => None,
            },
            _ => None,
        }
    }
}

/// Test a polynomial independently reconstructed by another checker kernel.
/// Borrow its original remaining work and progress owner; this is not a new
/// proof request, allowance, authored-term parser, or producer-payload entry.
pub(super) fn derived_has_no_field_roots(
    terms: &TermStore,
    variable: TermId,
    field: FiniteFieldSort,
    mut polynomial: Vec<u32>,
    fuel: &mut usize,
    progress: &mut dyn FnMut(usize, usize) -> bool,
) -> Option<bool> {
    if *fuel == 0 {
        return None;
    }
    if terms.sort(variable) != &Sort::FiniteField(field)
        || !matches!(terms.get(variable), TermData::Var(..))
    {
        *fuel = 0;
        return None;
    }
    let mut check = Check {
        terms,
        field: Some(field),
        variable: Some(variable),
        progress,
        work: *fuel,
    };
    let result = (|| {
        check.pay(polynomial.len().checked_mul(2)?, 0)?;
        if polynomial
            .iter()
            .any(|&coefficient| coefficient >= field.modulus())
        {
            return None;
        }
        Check::trim(&mut polynomial);
        Some(matches!(check.field_roots(polynomial)?, RootSet::Finite(p) if p.len() == 1))
    })();
    *fuel = if result.is_some() { check.work } else { 0 };
    result
}

pub(in crate::checker) fn validate(
    terms: &TermStore,
    step: ProofId,
    clause: &[TermId],
    progress: &mut dyn FnMut(usize, usize) -> bool,
) -> Result<(), ProofCheckError> {
    let valid = (|| -> Option<bool> {
        if clause.is_empty() || u32::try_from(clause.len()).is_err() {
            return None;
        }
        let mut checker = Check {
            terms,
            field: None,
            variable: None,
            progress,
            work: 4_000_000,
        };
        checker.pay(clause.len(), 0)?;
        let mut allowed = checker.empty_set()?.complement();
        for &literal in clause {
            if terms.sort(literal) != &Sort::Bool {
                return None;
            }
            let TermData::Not(root) = terms.get(literal) else {
                return None;
            };
            let next = checker.boolean_set(*root, 0)?;
            allowed = checker.intersection(allowed, next)?;
        }
        let field = checker.field?;
        Some(match allowed {
            RootSet::Finite(p) => p.len() == 1,
            // A monic split square-free polynomial has exactly degree roots.
            RootSet::Cofinite(p) => p.len().checked_sub(1)? == field.modulus() as usize,
        })
    })() == Some(true);
    if valid {
        Ok(())
    } else {
        Err(ProofCheckError::InvalidTheoryLemma {
            step,
            reason: "univariate finite-field exhaustion is invalid, unsupported, or over budget"
                .into(),
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn app(terms: &mut TermStore, name: &str, args: &[TermId], field: FiniteFieldSort) -> TermId {
        terms.mk_app(Symbol::Named(name.into()), args, Sort::FiniteField(field))
    }

    #[test]
    fn boolean_univariate_replay_constants_before_field_keep_original_obligations() {
        let mut terms = TermStore::new();
        let field = FiniteFieldSort::new(65537).unwrap();
        let x = terms.mk_var("x", Sort::FiniteField(field));
        let cube = app(&mut terms, "ff.mul", &[x, x, x], field);
        let value = terms.mk_finite_field(27, field);
        let equation = terms.mk_eq(cube, value);
        let three = terms.mk_finite_field(3, field);
        let root = terms.mk_eq(x, three);
        let exclusion = terms.mk_not_raw(root);
        let truth = terms.mk_bool(true);
        let nested = terms.mk_app(
            Symbol::Named("and".into()),
            &[truth, truth, equation],
            Sort::Bool,
        );
        let clause = [
            terms.mk_not_raw(truth),
            terms.mk_not_raw(truth),
            terms.mk_not_raw(nested),
            terms.mk_not_raw(exclusion),
        ];
        assert!(validate(&terms, ProofId(0), &clause, &mut |_, _| true).is_ok());
        // The same authored cubic without exclusion is SAT at 3. Neither
        // leading constants nor retained coefficients can prove it false.
        assert!(validate(&terms, ProofId(0), &clause[..3], &mut |_, _| true).is_err());
        assert!(validate(&terms, ProofId(0), &clause, &mut |_, _| false).is_err());
        let falsehood = terms.mk_bool(false);
        let false_clause = [
            terms.mk_not_raw(falsehood),
            terms.mk_not_raw(truth),
            terms.mk_not_raw(equation),
        ];
        assert!(validate(&terms, ProofId(0), &false_clause, &mut |_, _| true).is_ok());
        let wrong = terms.mk_app(Symbol::Named("=".into()), &[truth, x], Sort::Bool);
        let malformed = [terms.mk_not_raw(falsehood), terms.mk_not_raw(wrong)];
        assert!(
            validate(&terms, ProofId(0), &malformed, &mut |_, _| true).is_err(),
            "empty intersection cannot hide malformed later operands"
        );
    }

    #[test]
    fn boolean_univariate_replay_matches_exhaustive_authored_truth_and_stops() {
        for a in 0..7u32 {
            for b in 0..7u32 {
                for negate_a in [false, true] {
                    for negate_b in [false, true] {
                        for name in ["and", "or", "xor", "=>", "=", "distinct"] {
                            let mut terms = TermStore::new();
                            let field = FiniteFieldSort::new(7).unwrap();
                            let x = terms.mk_var("x", Sort::FiniteField(field));
                            let ac = terms.mk_finite_field(a, field);
                            let bc = terms.mk_finite_field(b, field);
                            let mut left = terms.mk_eq(x, ac);
                            let mut right = terms.mk_eq(x, bc);
                            if negate_a {
                                left = terms.mk_not_raw(left);
                            }
                            if negate_b {
                                right = terms.mk_not_raw(right);
                            }
                            let formula = terms.mk_app(
                                Symbol::Named(name.into()),
                                &[left, right],
                                Sort::Bool,
                            );
                            let clause = [terms.mk_not_raw(formula)];
                            let satisfiable = (0..7).any(|v| {
                                let l = (v == a) != negate_a;
                                let r = (v == b) != negate_b;
                                match name {
                                    "and" => l && r,
                                    "or" => l || r,
                                    "xor" | "distinct" => l != r,
                                    "=>" => !l || r,
                                    "=" => l == r,
                                    _ => unreachable!(),
                                }
                            });
                            assert_eq!(
                                validate(&terms, ProofId(0), &clause, &mut |_, _| true).is_ok(),
                                !satisfiable,
                                "{name} {a} {b} {negate_a} {negate_b}"
                            );
                            let mut polls = 0;
                            assert!(validate(&terms, ProofId(0), &clause, &mut |_, _| {
                                polls += 1;
                                polls < 3
                            })
                            .is_err());
                            assert_eq!(polls, 3, "no work after the original refusal");
                            assert_eq!(
                                validate(&terms, ProofId(0), &clause, &mut |_, _| true).is_ok(),
                                !satisfiable,
                                "fresh independent request"
                            );
                        }
                    }
                }
            }
        }
    }

    #[test]
    fn univariate_checker_agrees_with_independent_cubic_enumeration() {
        for a in 0..7u32 {
            for b in 0..7u32 {
                for c in 0..7u32 {
                    let mut terms = TermStore::new();
                    let field = FiniteFieldSort::new(7).unwrap();
                    let x = terms.mk_var("x", Sort::FiniteField(field));
                    let square = app(&mut terms, "ff.mul", &[x, x], field);
                    let cube = app(&mut terms, "ff.mul", &[x, square], field);
                    let a_term = terms.mk_finite_field(a, field);
                    let b_term = terms.mk_finite_field(b, field);
                    let c_term = terms.mk_finite_field(c, field);
                    let a_square = app(&mut terms, "ff.mul", &[a_term, square], field);
                    let b_x = app(&mut terms, "ff.mul", &[b_term, x], field);
                    let poly = app(&mut terms, "ff.add", &[cube, a_square, b_x, c_term], field);
                    let zero = terms.mk_finite_field(0, field);
                    let equation = terms.mk_eq(poly, zero);
                    let two = terms.mk_finite_field(2, field);
                    let excluded = terms.mk_eq(x, two);
                    let excluded = terms.mk_not_raw(excluded);
                    let clause = [terms.mk_not_raw(equation), terms.mk_not_raw(excluded)];
                    let satisfiable =
                        (0..7u32).any(|x| x != 2 && (x * x * x + a * x * x + b * x + c) % 7 == 0);
                    assert_eq!(
                        validate(&terms, ProofId(0), &clause, &mut |_, _| true).is_ok(),
                        !satisfiable,
                        "{a},{b},{c}"
                    );
                    assert!(validate(&terms, ProofId(0), &clause, &mut |_, _| false).is_err());
                }
            }
        }
    }
}
