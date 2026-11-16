// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//! Sparse polynomial ideal arithmetic. All stored rows remain combinations of
//! authored equations, or the valid F_p identities in the finite-domain
//! fallback; a nonzero constant is a genuine field contradiction.

use ay_core::{Constant, FiniteFieldSort, Sort, Symbol, TermData, TermId, TermStore};

struct Summand {
    exponents: Vec<u32>,
    coefficient: u32,
}
type Polynomial = Vec<Summand>;
mod finite_domain;
mod model;

enum Basis {
    Unit,
    Proper(Vec<Polynomial>),
}
pub(crate) enum Candidate {
    Contradiction,
    Model(Vec<(TermId, u32, FiniteFieldSort)>),
}

struct Ring<'a, 'b> {
    terms: &'a TermStore,
    variables: Vec<TermId>,
    field: FiniteFieldSort,
    fuel: &'b mut usize,
    control: &'b mut dyn FnMut(usize, usize) -> bool,
}

impl Ring<'_, '_> {
    fn pay(&mut self, work: usize, bytes: usize) -> Option<()> {
        if *self.fuel == 0 {
            return None;
        }
        let Some(left) = self.fuel.checked_sub(work) else {
            *self.fuel = 0;
            return None;
        };
        *self.fuel = left;
        if !(self.control)(work, bytes) {
            *self.fuel = 0;
            return None;
        }
        Some(())
    }
    fn reserve<T>(&mut self, out: &mut Vec<T>, extra: usize) -> Option<()> {
        let required = out.len().checked_add(extra)?;
        if required > out.capacity() {
            let target = required.max(out.capacity().max(4).checked_mul(2)?);
            self.pay(out.len(), target.checked_mul(size_of::<T>())?)?;
            if out.try_reserve_exact(target - out.len()).is_err() {
                *self.fuel = 0;
                return None;
            }
            if out.capacity() > target {
                self.pay(0, (out.capacity() - target).checked_mul(size_of::<T>())?)?;
            }
        }
        Some(())
    }
    fn exponents(&mut self, input: &[u32]) -> Option<Vec<u32>> {
        self.pay(input.len(), 0)?;
        let mut out = Vec::new();
        self.reserve(&mut out, input.len())?;
        out.extend_from_slice(input);
        Some(out)
    }
    fn zero_exponents(&mut self) -> Option<Vec<u32>> {
        let mut out = Vec::new();
        let n = self.variables.len();
        self.pay(n, 0)?;
        self.reserve(&mut out, n)?;
        out.resize(n, 0);
        Some(out)
    }
    fn sum(&self, a: u32, b: u32) -> u32 {
        ((u64::from(a) + u64::from(b)) % u64::from(self.field.modulus())) as u32
    }
    fn product(&mut self, a: u32, b: u32) -> Option<u32> {
        self.pay(1, 0)?;
        Some((u64::from(a) * u64::from(b) % u64::from(self.field.modulus())) as u32)
    }
    fn inverse(&mut self, mut a: u32) -> Option<u32> {
        if a == 0 {
            return None;
        }
        let mut exponent = self.field.modulus() - 2;
        let mut out = 1;
        while exponent != 0 {
            if exponent & 1 != 0 {
                out = self.product(out, a)?;
            }
            a = self.product(a, a)?;
            exponent >>= 1;
        }
        Some(out)
    }
    // Descending lexicographic monomials. Comparisons charge their complete
    // exponent width before touching it; no opaque unpriced map/hash/sort.
    fn add_summand(
        &mut self,
        out: &mut Polynomial,
        exponents: &[u32],
        coefficient: u32,
    ) -> Option<()> {
        self.pay(1, 0)?;
        if coefficient == 0 {
            return Some(());
        }
        let mut at = out.len();
        for i in 0..out.len() {
            self.pay(exponents.len(), 0)?;
            match exponents.cmp(out[i].exponents.as_slice()) {
                std::cmp::Ordering::Greater => {
                    at = i;
                    break;
                }
                std::cmp::Ordering::Equal => {
                    out[i].coefficient = self.sum(out[i].coefficient, coefficient);
                    if out[i].coefficient == 0 {
                        self.pay(out.len() - i, 0)?;
                        out.remove(i);
                    }
                    return Some(());
                }
                std::cmp::Ordering::Less => {}
            }
        }
        let exponents = self.exponents(exponents)?;
        self.reserve(out, 1)?;
        self.pay(out.len() - at, 0)?;
        out.insert(
            at,
            Summand {
                exponents,
                coefficient,
            },
        );
        Some(())
    }
    fn constant(&mut self, coefficient: u32) -> Option<Polynomial> {
        self.pay(1, 0)?;
        let mut out = Vec::new();
        if coefficient != 0 {
            let zero = self.zero_exponents()?;
            self.add_summand(&mut out, &zero, coefficient)?;
        }
        Some(out)
    }
    fn duplicate(&mut self, input: &Polynomial) -> Option<Polynomial> {
        let mut out = Vec::new();
        for term in input {
            self.add_summand(&mut out, &term.exponents, term.coefficient)?;
        }
        Some(out)
    }
    fn subtract(&mut self, mut out: Polynomial, other: &Polynomial) -> Option<Polynomial> {
        for term in other {
            self.add_summand(
                &mut out,
                &term.exponents,
                self.field.modulus() - term.coefficient,
            )?;
        }
        Some(out)
    }
    fn multiply(&mut self, a: &Polynomial, b: &Polynomial) -> Option<Polynomial> {
        let mut out = Vec::new();
        for left in a {
            for right in b {
                let mut exponents = self.exponents(&left.exponents)?;
                self.pay(exponents.len(), 0)?;
                for (exponent, add) in exponents.iter_mut().zip(&right.exponents) {
                    *exponent = exponent.checked_add(*add)?;
                }
                let coefficient = self.product(left.coefficient, right.coefficient)?;
                self.add_summand(&mut out, &exponents, coefficient)?;
            }
        }
        Some(out)
    }
    fn monomial_multiple(
        &mut self,
        input: &Polynomial,
        powers: &[u32],
        scale: u32,
    ) -> Option<Polynomial> {
        let mut out = Vec::new();
        for term in input {
            let mut exponents = self.exponents(&term.exponents)?;
            self.pay(exponents.len(), 0)?;
            for (exponent, add) in exponents.iter_mut().zip(powers) {
                *exponent = exponent.checked_add(*add)?;
            }
            let coefficient = self.product(term.coefficient, scale)?;
            self.add_summand(&mut out, &exponents, coefficient)?;
        }
        Some(out)
    }
    fn monic(&mut self, polynomial: &mut Polynomial) -> Option<()> {
        let Some(first) = polynomial.first() else {
            return Some(());
        };
        let inverse = self.inverse(first.coefficient)?;
        for term in polynomial {
            term.coefficient = self.product(term.coefficient, inverse)?;
        }
        Some(())
    }
    fn is_constant(&mut self, polynomial: &Polynomial) -> Option<bool> {
        self.pay(self.variables.len(), 0)?;
        Some(polynomial.len() == 1 && polynomial[0].exponents.iter().all(|&power| power == 0))
    }
    fn parse(&mut self, id: TermId, depth: usize) -> Option<Polynomial> {
        self.pay(1, 0)?;
        if depth > 128 || self.terms.sort(id) != &Sort::FiniteField(self.field) {
            return None;
        }
        match self.terms.get(id) {
            TermData::Var(..) => {
                self.pay(self.variables.len(), 0)?;
                let position = self.variables.iter().position(|&v| v == id)?;
                let mut powers = self.zero_exponents()?;
                powers[position] = 1;
                let mut out = Vec::new();
                self.add_summand(&mut out, &powers, 1)?;
                Some(out)
            }
            TermData::Const(Constant::FiniteField { value, field })
                if *field == self.field && *value < field.modulus() =>
            {
                self.constant(*value)
            }
            TermData::App(Symbol::Named(name), args) => match name.as_str() {
                "ff.neg" if args.len() == 1 => {
                    let child = self.parse(args[0], depth + 1)?;
                    self.subtract(Vec::new(), &child)
                }
                "ff.add" | "ff.bitsum" if args.len() >= 2 => {
                    let mut out = Vec::new();
                    let mut scale = 1;
                    for &arg in args {
                        let child = self.parse(arg, depth + 1)?;
                        for term in child {
                            let coefficient = self.product(term.coefficient, scale)?;
                            self.add_summand(&mut out, &term.exponents, coefficient)?;
                        }
                        if name == "ff.bitsum" {
                            scale = self.sum(scale, scale);
                        }
                    }
                    Some(out)
                }
                "ff.mul" if args.len() >= 2 => {
                    let mut out = self.constant(1)?;
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
    fn equations(
        &mut self,
        id: TermId,
        negative: bool,
        depth: usize,
        out: &mut Vec<Polynomial>,
    ) -> Option<()> {
        self.pay(1, 0)?;
        if depth > 128 || self.terms.sort(id) != &Sort::Bool {
            return None;
        }
        match self.terms.get(id) {
            TermData::Const(Constant::Bool(value)) => {
                if *value == negative {
                    let one = self.constant(1)?;
                    self.reserve(out, 1)?;
                    out.push(one);
                }
                Some(())
            }
            TermData::Not(child) => self.equations(*child, !negative, depth + 1, out),
            TermData::App(Symbol::Named(name), args) => match name.as_str() {
                "not" if args.len() == 1 => self.equations(args[0], !negative, depth + 1, out),
                "and" if !negative => {
                    for &arg in args {
                        self.equations(arg, false, depth + 1, out)?;
                    }
                    Some(())
                }
                "=" | "distinct" if args.len() >= 2 && (name == "=") != negative => {
                    if negative && args.len() != 2 {
                        return None;
                    }
                    let first = self.parse(args[0], 0)?;
                    for &arg in &args[1..] {
                        let other = self.parse(arg, 0)?;
                        let copy = self.duplicate(&first)?;
                        let polynomial = self.subtract(copy, &other)?;
                        self.reserve(out, 1)?;
                        out.push(polynomial);
                    }
                    Some(())
                }
                _ => None,
            },
            _ => None,
        }
    }
}

impl Ring<'_, '_> {
    fn reduce(&mut self, mut polynomial: Polynomial, basis: &[Polynomial]) -> Option<Polynomial> {
        let mut remainder = Vec::new();
        while !polynomial.is_empty() {
            self.pay(1, 0)?;
            let mut reduction = None;
            for row in basis {
                self.pay(self.variables.len(), 0)?;
                if row[0]
                    .exponents
                    .iter()
                    .zip(&polynomial[0].exponents)
                    .all(|(a, b)| a <= b)
                {
                    let mut powers = self.exponents(&polynomial[0].exponents)?;
                    self.pay(powers.len(), 0)?;
                    for (p, divisor) in powers.iter_mut().zip(&row[0].exponents) {
                        *p = p.checked_sub(*divisor)?;
                    }
                    reduction =
                        Some(self.monomial_multiple(row, &powers, polynomial[0].coefficient)?);
                    break;
                }
            }
            if let Some(multiple) = reduction {
                polynomial = self.subtract(polynomial, &multiple)?;
            } else {
                self.pay(polynomial.len(), 0)?;
                self.reserve(&mut remainder, 1)?;
                remainder.push(polynomial.remove(0));
            }
        }
        Some(remainder)
    }
    // Buchberger's algorithm with exact S-polynomial reduction. Each inserted
    // row stays in the authored ideal; no critical-pair success bit is proof.
    fn groebner(&mut self, generators: Vec<Polynomial>) -> Option<Basis> {
        let mut basis = Vec::new();
        for generator in generators {
            let mut row = self.reduce(generator, &basis)?;
            if row.is_empty() {
                continue;
            }
            self.monic(&mut row)?;
            if self.is_constant(&row)? {
                return Some(Basis::Unit);
            }
            self.reserve(&mut basis, 1)?;
            basis.push(row);
        }
        let mut j = 1;
        while j < basis.len() {
            for i in 0..j {
                self.pay(self.variables.len(), 0)?;
                let mut left = self.exponents(&basis[i][0].exponents)?;
                let mut right = self.exponents(&basis[j][0].exponents)?;
                for (a, b) in left.iter_mut().zip(&mut right) {
                    let lcm = (*a).max(*b);
                    *a = lcm.checked_sub(*a)?;
                    *b = lcm.checked_sub(*b)?;
                }
                let a = self.monomial_multiple(&basis[i], &left, 1)?;
                let b = self.monomial_multiple(&basis[j], &right, 1)?;
                let s = self.subtract(a, &b)?;
                let mut row = self.reduce(s, &basis)?;
                if row.is_empty() {
                    continue;
                }
                self.monic(&mut row)?;
                if self.is_constant(&row)? {
                    return Some(Basis::Unit);
                }
                self.reserve(&mut basis, 1)?;
                basis.push(row);
            }
            j += 1;
        }
        Some(Basis::Proper(basis))
    }
}

#[cfg(test)]
pub(super) fn witness(
    terms: &TermStore,
    roots: &[TermId],
    seen: &ay_core::kani_compat::DetHashSet<TermId>,
    fuel: &mut usize,
    control: &mut dyn FnMut(usize) -> bool,
) -> Option<Candidate> {
    let mut bytes = 0usize;
    witness_with_progress(terms, roots, seen, fuel, &mut |_, extra| {
        let Some(total) = bytes.checked_add(extra) else {
            return false;
        };
        bytes = total;
        control(total)
    })
}

// Preserve the native fuel/cumulative-byte contract while reporting every
// debit, including the borrowed univariate helper's actual work.
pub(super) fn witness_with_progress(
    terms: &TermStore,
    roots: &[TermId],
    seen: &ay_core::kani_compat::DetHashSet<TermId>,
    fuel: &mut usize,
    control: &mut dyn FnMut(usize, usize) -> bool,
) -> Option<Candidate> {
    let mut field = None;
    let mut count = 0usize;
    for &id in seen {
        let Some(left) = fuel.checked_sub(1) else {
            *fuel = 0;
            return None;
        };
        *fuel = left;
        if !control(1, 0) {
            *fuel = 0;
            return None;
        }
        match terms.sort(id) {
            Sort::FiniteField(current) => {
                if field.is_some_and(|old| old != *current) {
                    return None;
                }
                field = Some(*current);
                if matches!(terms.get(id), TermData::Var(..)) {
                    count = count.checked_add(1)?;
                }
            }
            Sort::Bool if !matches!(terms.get(id), TermData::Var(..)) => {}
            _ => return None,
        }
    }
    let field = field?;
    let mut ring = Ring {
        terms,
        variables: Vec::new(),
        field,
        fuel,
        control,
    };
    let mut variables = Vec::new();
    ring.reserve(&mut variables, count)?;
    for &id in seen {
        ring.pay(1, 0)?;
        if matches!(terms.get(id), TermData::Var(..)) {
            variables.push(id);
        }
    }
    ring.pay(count.checked_mul(count)?, 0)?;
    variables.sort_unstable();
    ring.variables = variables;
    let mut generators = Vec::new();
    for &root in roots {
        ring.equations(root, false, 0, &mut generators)?;
    }
    match ring.groebner(generators)? {
        Basis::Unit => Some(Candidate::Contradiction),
        Basis::Proper(basis) => match model::construct(&mut ring, &basis)? {
            Some(model) => Some(Candidate::Model(model)),
            None => finite_domain::refine(&mut ring, &basis),
        },
    }
}

/// Borrow an existing native construction owner's work/arena/stop only.
/// The integer guard is representational overflow protection, never an
/// allowance: EVERY debit is paid to the original owner before computation.
/// No model or theorem authority is produced by this candidate interface.
pub(super) fn witness_admitted(
    terms: &TermStore,
    roots: &[TermId],
    seen: &ay_core::kani_compat::DetHashSet<TermId>,
    owner: &dyn ay_core::term::TermConstructionAdmission,
) -> Option<Candidate> {
    let mut guard = usize::MAX;
    witness_with_progress(terms, roots, seen, &mut guard, &mut |work, bytes| {
        owner.admit(work, bytes).is_ok()
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    fn refute(
        terms: &TermStore,
        roots: &[TermId],
        seen: &ay_core::kani_compat::DetHashSet<TermId>,
        fuel: &mut usize,
        control: &mut dyn FnMut(usize) -> bool,
    ) -> Option<bool> {
        witness(terms, roots, seen, fuel, control)
            .map(|candidate| matches!(candidate, Candidate::Contradiction))
    }

    fn fixture(
        prime: u32,
        square: u32,
        product: u32,
    ) -> (
        TermStore,
        Vec<TermId>,
        ay_core::kani_compat::DetHashSet<TermId>,
    ) {
        let mut terms = TermStore::new();
        let field = FiniteFieldSort::new(prime).unwrap();
        let x = terms.mk_var("x", Sort::FiniteField(field));
        let y = terms.mk_var("y", Sort::FiniteField(field));
        let xx = terms.mk_app(
            Symbol::Named("ff.mul".into()),
            [x, x],
            Sort::FiniteField(field),
        );
        let xy = terms.mk_app(
            Symbol::Named("ff.mul".into()),
            [x, y],
            Sort::FiniteField(field),
        );
        let value = terms.mk_finite_field(square, field);
        let one = terms.mk_finite_field(product, field);
        let a = terms.mk_eq(xx, value);
        let b = terms.mk_eq(xy, one);
        let seen = [x, y, xx, xy, value, one, a, b].into_iter().collect();
        (terms, vec![a, b], seen)
    }
    #[test]
    fn ideal_buchberger_uses_real_multiplication_consequences_and_shared_fuel() {
        for prime in [2, 7, 65537, 4294967291] {
            let (terms, roots, seen) = fixture(prime, 0, 1);
            let mut fuel = 100_000;
            assert_eq!(
                refute(&terms, &roots, &seen, &mut fuel, &mut |_| true),
                Some(true)
            );
            assert!(fuel < 100_000);
            let (sat, roots, seen) = fixture(prime, 1, 1);
            assert_eq!(
                refute(&sat, &roots, &seen, &mut 100_000, &mut |_| true),
                Some(false)
            );
        }
        let (terms, roots, seen) = fixture(65537, 0, 1);
        let mut fuel = 2;
        assert!(refute(&terms, &roots, &seen, &mut fuel, &mut |_| true).is_none());
        assert_eq!(fuel, 0);
        let mut polls = 0;
        assert!(refute(&terms, &roots, &seen, &mut fuel, &mut |_| {
            polls += 1;
            true
        })
        .is_none());
        assert_eq!(polls, 0);
        let mut fuel = 100_000;
        assert!(refute(&terms, &roots, &seen, &mut fuel, &mut |_| false).is_none());
        assert_eq!(fuel, 0);
    }
    #[test]
    fn ideal_buchberger_never_refutes_exhaustively_witnessed_small_fields() {
        for prime in [2, 7] {
            for square in 0..prime {
                for product in 0..prime {
                    // Direct integer arithmetic over ALL F_p assignments is
                    // independent of either polynomial implementation.
                    let witnessed = (0..prime).any(|x| {
                        (0..prime).any(|y| x * x % prime == square && x * y % prime == product)
                    });
                    let (terms, roots, seen) = fixture(prime, square, product);
                    let derived = refute(&terms, &roots, &seen, &mut 100_000, &mut |_| true);
                    if witnessed {
                        assert_eq!(
                            derived,
                            Some(false),
                            "SAT F{prime}: x²={square},xy={product}"
                        );
                    }
                    if square == 0 && product != 0 {
                        assert_eq!(derived, Some(true));
                    }
                }
            }
        }
    }
    #[test]
    fn triangular_models_match_independent_exhaustive_small_field_truth() {
        for prime in [2, 7] {
            for square in 0..prime {
                for product in 0..prime {
                    let (terms, roots, seen) = fixture(prime, square, product);
                    let mut variables: Vec<_> = seen
                        .iter()
                        .copied()
                        .filter(|&id| matches!(terms.get(id), TermData::Var(..)))
                        .collect();
                    variables.sort_unstable();
                    let actual_sat = (0..prime).any(|x| {
                        (0..prime).any(|y| x * x % prime == square && x * y % prime == product)
                    });
                    match witness(&terms, &roots, &seen, &mut 200_000, &mut |_| true) {
                        Some(Candidate::Model(model)) => {
                            assert!(actual_sat);
                            assert_eq!(model.len(), 2);
                            let x = model
                                .iter()
                                .find(|(id, _, _)| *id == variables[0])
                                .unwrap()
                                .1;
                            let y = model
                                .iter()
                                .find(|(id, _, _)| *id == variables[1])
                                .unwrap()
                                .1;
                            assert!(x < prime && y < prime);
                            assert_eq!(x * x % prime, square);
                            assert_eq!(x * y % prime, product);
                        }
                        Some(Candidate::Contradiction) => assert!(!actual_sat),
                        None => {
                            panic!("finite-domain F{prime} decision missing: {square},{product}")
                        }
                    }
                }
            }
        }
    }
    #[test]
    fn triangular_models_backtrack_real_root_fibers_without_budget_renewal() {
        let prime = 7;
        let mut terms = TermStore::new();
        let field = FiniteFieldSort::new(prime).unwrap();
        let x = terms.mk_var("x", Sort::FiniteField(field));
        let y = terms.mk_var("y", Sort::FiniteField(field));
        let first = super::super::univariate::next_root(
            &terms,
            y,
            field,
            vec![6, 0, 1],
            &mut 100_000,
            &mut |_| true,
        )
        .unwrap()
        .unwrap()
        .value;
        let other = (prime - first) % prime;
        let denominator = (first + prime - other) % prime;
        let inverse = (1..prime).find(|&v| v * denominator % prime == 1).unwrap();
        let slope = 2 * inverse % prime;
        let intercept = (3 + prime - slope * first % prime) % prime;
        assert!(!(0..prime).any(|v| v * v % prime == 3));
        let xx = terms.mk_app(
            Symbol::Named("ff.mul".into()),
            [x, x],
            Sort::FiniteField(field),
        );
        let yy = terms.mk_app(
            Symbol::Named("ff.mul".into()),
            [y, y],
            Sort::FiniteField(field),
        );
        let scale = terms.mk_finite_field(slope, field);
        let offset = terms.mk_finite_field(intercept, field);
        let one = terms.mk_finite_field(1, field);
        let scaled = terms.mk_app(
            Symbol::Named("ff.mul".into()),
            [scale, y],
            Sort::FiniteField(field),
        );
        let rhs = terms.mk_app(
            Symbol::Named("ff.add".into()),
            [scaled, offset],
            Sort::FiniteField(field),
        );
        let a = terms.mk_eq(xx, rhs);
        let b = terms.mk_eq(yy, one);
        let seen = [x, y, xx, yy, scale, offset, one, scaled, rhs, a, b]
            .into_iter()
            .collect();
        let roots = [a, b];
        let mut fuel = 200_000;
        let Some(Candidate::Model(model)) =
            witness(&terms, &roots, &seen, &mut fuel, &mut |_| true)
        else {
            panic!("second algebraic fiber has a real model");
        };
        let xv = model.iter().find(|(id, _, _)| *id == x).unwrap().1;
        let yv = model.iter().find(|(id, _, _)| *id == y).unwrap().1;
        assert_ne!(yv, first, "first fiber has no field root");
        assert_eq!(yv * yv % prime, 1);
        assert_eq!(xv * xv % prime, (slope * yv + intercept) % prime);
        let spent = 200_000 - fuel;
        let mut short = spent - 1;
        assert!(witness(&terms, &roots, &seen, &mut short, &mut |_| true).is_none());
        assert_eq!(
            short, 0,
            "backtracking cannot renew the original caller fuel"
        );
    }
    #[test]
    fn parametric_bilinear_models_match_exhaustive_small_field_assignments() {
        for prime in [2, 7] {
            for b in 0..prime {
                for c in 0..prime {
                    for d in 0..prime {
                        let mut terms = TermStore::new();
                        let field = FiniteFieldSort::new(prime).unwrap();
                        let x = terms.mk_var("x", Sort::FiniteField(field));
                        let y = terms.mk_var("y", Sort::FiniteField(field));
                        let bc = terms.mk_finite_field(b, field);
                        let cc = terms.mk_finite_field(c, field);
                        let dc = terms.mk_finite_field(d, field);
                        let zero = terms.mk_finite_field(0, field);
                        let xy = terms.mk_app(
                            Symbol::Named("ff.mul".into()),
                            [x, y],
                            Sort::FiniteField(field),
                        );
                        let bx = terms.mk_app(
                            Symbol::Named("ff.mul".into()),
                            [bc, x],
                            Sort::FiniteField(field),
                        );
                        let cy = terms.mk_app(
                            Symbol::Named("ff.mul".into()),
                            [cc, y],
                            Sort::FiniteField(field),
                        );
                        let sum = terms.mk_app(
                            Symbol::Named("ff.add".into()),
                            [xy, bx, cy, dc],
                            Sort::FiniteField(field),
                        );
                        let equation = terms.mk_eq(sum, zero);
                        let seen = [x, y, bc, cc, dc, zero, xy, bx, cy, sum, equation]
                            .into_iter()
                            .collect();
                        let actual_sat = (0..prime)
                            .any(|a| (0..prime).any(|z| (a * z + b * a + c * z + d) % prime == 0));
                        assert!(actual_sat);
                        let mut fuel = 500_000;
                        let Some(Candidate::Model(model)) =
                            witness(&terms, &[equation], &seen, &mut fuel, &mut |_| true)
                        else {
                            panic!("regular F{prime} family {b},{c},{d}");
                        };
                        let xv = model.iter().find(|(id, _, _)| *id == x).unwrap().1;
                        let yv = model.iter().find(|(id, _, _)| *id == y).unwrap().1;
                        assert!(xv < prime && yv < prime);
                        assert_eq!((xv * yv + b * xv + c * yv + d) % prime, 0);
                    }
                }
            }
        }
    }
}
