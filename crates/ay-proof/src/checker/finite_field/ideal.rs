// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//! Sparse polynomial ideal arithmetic. All stored rows remain combinations of
//! authored equations and the valid F_p identities x_i^p-x_i; a nonzero
//! constant is a genuine field contradiction.

use ay_core::{Constant, FiniteFieldSort, Sort, Symbol, TermData, TermId, TermStore};

struct Summand {
    exponents: Vec<u32>,
    coefficient: u32,
}
type Polynomial = Vec<Summand>;

struct Ring<'a, 'b> {
    terms: &'a TermStore,
    variables: Vec<TermId>,
    // Independently introduced existential inverse coordinates. These are
    // polynomial columns, never source TermIds or trusted producer bindings.
    auxiliary_columns: usize,
    field: FiniteFieldSort,
    fuel: &'b mut usize,
    control: &'b mut dyn FnMut(usize, usize) -> bool,
}

impl Ring<'_, '_> {
    fn width(&self) -> usize {
        self.variables.len() + self.auxiliary_columns
    }
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
            self.pay(out.len(), target.checked_mul(std::mem::size_of::<T>())?)?;
            if out.try_reserve_exact(target - out.len()).is_err() {
                *self.fuel = 0;
                return None;
            }
            if out.capacity() > target {
                self.pay(
                    0,
                    (out.capacity() - target).checked_mul(std::mem::size_of::<T>())?,
                )?;
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
        let n = self.width();
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
        self.pay(self.width(), 0)?;
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
            TermData::App(Symbol::Named(name), args) if args.len() <= 1024 => match name.as_str() {
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
            TermData::App(Symbol::Named(name), args) if args.len() <= 1024 => match name.as_str() {
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
                "=" | "distinct" if args.len() == 2 && (name == "=") == negative => {
                    let left = self.parse(args[0], 0)?;
                    let right = self.parse(args[1], 0)?;
                    let difference = self.subtract(left, &right)?;
                    self.nonzero(difference, out)
                }
                _ => None,
            },
            _ => None,
        }
    }

    // Rabinowitsch: f != 0 iff a field coordinate Y satisfies Yf-1=0.
    // Reconstruct it here from the original signed source, independently of
    // the producer's TermStore variables, substitutions, or basis.
    fn nonzero(&mut self, mut difference: Polynomial, out: &mut Vec<Polynomial>) -> Option<()> {
        let next = self.auxiliary_columns.checked_add(1)?;
        self.variables.len().checked_add(next)?;
        self.pay(1, 0)?;
        self.auxiliary_columns = next;
        for polynomial in out.iter_mut().chain(std::iter::once(&mut difference)) {
            for term in polynomial {
                self.reserve(&mut term.exponents, 1)?;
                self.pay(1, 0)?;
                term.exponents.push(0);
            }
        }
        for term in &mut difference {
            self.pay(1, 0)?;
            *term.exponents.last_mut()? = 1;
        }
        let one = self.constant(1)?;
        let generator = self.subtract(difference, &one)?;
        self.reserve(out, 1)?;
        out.push(generator);
        Some(())
    }
}

impl Ring<'_, '_> {
    // Independent Macaulay row closure, NOT the producer's S-pair algorithm.
    // Pivots eliminate only identical leading monomials. Every row is an
    // F_p-linear combination of monomial multiples of authored generators
    // and the independently reconstructed field identities.
    fn no_field_root(&mut self, row: &Polynomial) -> Option<bool> {
        let mut variable = None;
        let mut degree = 0u32;
        for term in row {
            self.pay(term.exponents.len(), 0)?;
            for (index, &power) in term.exponents.iter().enumerate() {
                if power == 0 {
                    continue;
                }
                if variable.is_some_and(|previous| previous != index) {
                    return Some(false);
                }
                variable = Some(index);
                // Reduce as a function on F_p before choosing a dense buffer.
                // In particular, x^p-x must not allocate p coefficients.
                degree = degree.max(1 + (power - 1) % (self.field.modulus() - 1));
            }
        }
        let Some(variable) = variable else {
            return Some(false);
        };
        // The optional source-variable root-isolation shortcut requires a
        // genuine source declaration. Formal inverse columns remain handled
        // by the same independent Macaulay/field-identity closure below.
        if variable >= self.variables.len() {
            return Some(false);
        }
        let count = usize::try_from(degree).ok()?.checked_add(1)?;
        let mut coefficients = Vec::new();
        self.reserve(&mut coefficients, count)?;
        self.pay(count, 0)?;
        coefficients.resize(count, 0);
        for term in row {
            self.pay(1, 0)?;
            let power = term.exponents[variable];
            let reduced = if power == 0 {
                0
            } else {
                1 + (power - 1) % (self.field.modulus() - 1)
            };
            let at = usize::try_from(reduced).ok()?;
            coefficients[at] = self.sum(coefficients[at], term.coefficient);
        }
        super::univariate::derived_has_no_field_roots(
            self.terms,
            self.variables[variable],
            self.field,
            coefficients,
            self.fuel,
            self.control,
        )
    }
    fn echelon(&mut self, mut row: Polynomial, pivots: &[Polynomial]) -> Option<Polynomial> {
        while !row.is_empty() {
            let mut found = None;
            for pivot in pivots {
                self.pay(self.width(), 0)?;
                if pivot[0].exponents == row[0].exponents {
                    found = Some(pivot);
                    break;
                }
            }
            let Some(pivot) = found else {
                break;
            };
            let powers = self.zero_exponents()?;
            let scaled = self.monomial_multiple(pivot, &powers, row[0].coefficient)?;
            row = self.subtract(row, &scaled)?;
        }
        self.monic(&mut row)?;
        Some(row)
    }
    fn macaulay_contradiction(&mut self, generators: Vec<Polynomial>) -> Option<bool> {
        let mut pivots = Vec::new();
        for generator in generators {
            let row = self.echelon(generator, &pivots)?;
            if row.is_empty() {
                continue;
            }
            if self.is_constant(&row)? || self.no_field_root(&row)? {
                return Some(true);
            }
            self.reserve(&mut pivots, 1)?;
            pivots.push(row);
        }
        let mut next = 0;
        while next < pivots.len() {
            for variable in 0..self.width() {
                let mut powers = self.zero_exponents()?;
                powers[variable] = 1;
                let multiple = self.monomial_multiple(&pivots[next], &powers, 1)?;
                let row = self.echelon(multiple, &pivots)?;
                if row.is_empty() {
                    continue;
                }
                if self.is_constant(&row)? || self.no_field_root(&row)? {
                    return Some(true);
                }
                self.reserve(&mut pivots, 1)?;
                pivots.push(row);
            }
            next += 1;
        }
        Some(false)
    }
}

fn pay(
    fuel: &mut usize,
    progress: &mut dyn FnMut(usize, usize) -> bool,
    work: usize,
    bytes: usize,
) -> Option<()> {
    if *fuel == 0 {
        return None;
    }
    let Some(left) = fuel.checked_sub(work) else {
        *fuel = 0;
        return None;
    };
    *fuel = left;
    if !progress(work, bytes) {
        *fuel = 0;
        return None;
    }
    Some(())
}
fn reserve<T>(
    out: &mut Vec<T>,
    extra: usize,
    fuel: &mut usize,
    progress: &mut dyn FnMut(usize, usize) -> bool,
) -> Option<()> {
    let required = out.len().checked_add(extra)?;
    if required > out.capacity() {
        let capacity = required.max(out.capacity().max(4).checked_mul(2)?);
        pay(
            fuel,
            progress,
            out.len(),
            capacity.checked_mul(std::mem::size_of::<T>())?,
        )?;
        if out.try_reserve_exact(capacity - out.len()).is_err() {
            *fuel = 0;
            return None;
        }
        if out.capacity() > capacity {
            pay(
                fuel,
                progress,
                0,
                (out.capacity() - capacity).checked_mul(std::mem::size_of::<T>())?,
            )?;
        }
    }
    Some(())
}

fn replay(
    terms: &TermStore,
    clause: &[TermId],
    fuel: &mut usize,
    progress: &mut dyn FnMut(usize, usize) -> bool,
) -> Option<bool> {
    if clause.is_empty() {
        return None;
    }
    pay(fuel, progress, clause.len(), 0)?;
    let mut pending = Vec::new();
    reserve(&mut pending, clause.len(), fuel, progress)?;
    for &literal in clause {
        pay(fuel, progress, 1, 0)?;
        if terms.sort(literal) != &Sort::Bool {
            return None;
        }
        let premise = match terms.get(literal) {
            TermData::Not(root) => *root,
            _ => literal,
        };
        pending.push((premise, 0usize));
    }
    let mut seen = Vec::new();
    let mut variables = Vec::new();
    let mut field = None;
    // Inspect the complete authored DAG independently, before deriving any
    // contradiction. A false prefix cannot hide malformed/foreign operands.
    while let Some((id, depth)) = pending.pop() {
        pay(fuel, progress, seen.len().checked_add(1)?, 0)?;
        if depth > 128 {
            return None;
        }
        if seen.contains(&id) {
            continue;
        }
        reserve(&mut seen, 1, fuel, progress)?;
        seen.push(id);
        match terms.sort(id) {
            Sort::Bool => {}
            Sort::FiniteField(current) => {
                if field.is_some_and(|old| old != *current) {
                    return None;
                }
                field = Some(*current);
            }
            _ => return None,
        }
        match terms.get(id) {
            TermData::Var(..) if matches!(terms.sort(id), Sort::FiniteField(_)) => {
                reserve(&mut variables, 1, fuel, progress)?;
                variables.push(id);
            }
            TermData::Const(Constant::Bool(_)) if terms.sort(id) == &Sort::Bool => {}
            TermData::Const(Constant::FiniteField { value, field })
                if *value < field.modulus() && terms.sort(id) == &Sort::FiniteField(*field) => {}
            TermData::Not(child)
                if terms.sort(id) == &Sort::Bool && terms.sort(*child) == &Sort::Bool =>
            {
                reserve(&mut pending, 1, fuel, progress)?;
                pending.push((*child, depth + 1));
            }
            TermData::App(Symbol::Named(name), args) if args.len() <= 1024 => {
                pay(fuel, progress, name.len(), 0)?;
                if terms.is_declared_function(name) {
                    return None;
                }
                reserve(&mut pending, args.len(), fuel, progress)?;
                pay(fuel, progress, args.len(), 0)?;
                pending.extend(args.iter().copied().map(|id| (id, depth + 1)));
            }
            _ => return None,
        }
    }
    pay(
        fuel,
        progress,
        variables.len().checked_mul(variables.len())?,
        0,
    )?;
    // Reverse source-ID order is independent of the producer's variable order.
    variables.sort_unstable_by(|a, b| b.cmp(a));
    let mut ring = Ring {
        terms,
        variables,
        auxiliary_columns: 0,
        field: field?,
        fuel,
        control: progress,
    };
    let mut generators = Vec::new();
    for &literal in clause {
        match terms.get(literal) {
            TermData::Not(root) => ring.equations(*root, false, 0, &mut generators)?,
            _ => ring.equations(literal, true, 0, &mut generators)?,
        }
    }
    // Independently reconstruct the field identities, with reverse source-ID
    // variable order. No producer basis, selected model, or success bit enters
    // this replay. Fermat's identity holds for EVERY value of this validated
    // prime sort, so adjoining these rows preserves all authored F_p models.
    for variable in 0..ring.width() {
        let mut row = Vec::new();
        let mut powers = ring.zero_exponents()?;
        powers[variable] = 1;
        ring.add_summand(&mut row, &powers, ring.field.modulus() - 1)?;
        powers[variable] = ring.field.modulus();
        ring.add_summand(&mut row, &powers, 1)?;
        ring.reserve(&mut generators, 1)?;
        generators.push(row);
    }
    ring.macaulay_contradiction(generators)
}

pub(in crate::checker) fn validate(
    terms: &TermStore,
    step: ay_core::ProofId,
    clause: &[TermId],
    progress: &mut dyn FnMut(usize, usize) -> bool,
) -> Result<(), super::ProofCheckError> {
    let mut fuel = 4_000_000;
    if replay(terms, clause, &mut fuel, progress) == Some(true) {
        Ok(())
    } else {
        Err(super::ProofCheckError::InvalidTheoryLemma {
        step,
        reason:"authored sparse field ideal does not independently derive a finite-field contradiction within original resources".into(),
    })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    fn fixture(prime: u32, square: u32, product: u32) -> (TermStore, Vec<TermId>) {
        let mut terms = TermStore::new();
        let field = FiniteFieldSort::new(prime).unwrap();
        let x = terms.mk_var("x", Sort::FiniteField(field));
        let y = terms.mk_var("y", Sort::FiniteField(field));
        let xx = terms.mk_app(
            Symbol::Named("ff.mul".into()),
            &[x, x],
            Sort::FiniteField(field),
        );
        let xy = terms.mk_app(
            Symbol::Named("ff.mul".into()),
            &[x, y],
            Sort::FiniteField(field),
        );
        let a = terms.mk_finite_field(square, field);
        let one = terms.mk_finite_field(product, field);
        let equation = terms.mk_eq(xx, a);
        let inverse = terms.mk_eq(xy, one);
        let clause = vec![terms.mk_not_raw(equation), terms.mk_not_raw(inverse)];
        (terms, clause)
    }
    #[test]
    fn ideal_replay_derives_multiplication_consequences_and_refuses_actual_models() {
        for prime in [2, 7, 65537, 4294967291] {
            let (terms, clause) = fixture(prime, 0, 1);
            assert_eq!(
                replay(&terms, &clause, &mut 100_000, &mut |_, _| true),
                Some(true)
            );
            // x=y=1 is an independently evident authored model, so neither
            // altered coefficients nor a missing original premise prove false.
            let (satisfiable, sat_clause) = fixture(prime, 1, 1);
            assert_ne!(
                replay(&satisfiable, &sat_clause, &mut 20_000, &mut |_, _| true),
                Some(true)
            );
            assert_ne!(
                replay(&terms, &clause[..1], &mut 20_000, &mut |_, _| true),
                Some(true)
            );
        }
    }
    #[test]
    fn ideal_replay_original_refusal_is_sticky_and_fresh_requests_work() {
        let (terms, clause) = fixture(65537, 0, 1);
        let mut completed = 0;
        assert_eq!(
            replay(&terms, &clause, &mut 100_000, &mut |_, _| {
                completed += 1;
                true
            }),
            Some(true)
        );
        let cutoff = completed / 2;
        assert!(cutoff > 3);
        let mut polls = 0;
        let mut fuel = 100_000;
        assert!(replay(&terms, &clause, &mut fuel, &mut |_, _| {
            polls += 1;
            polls < cutoff
        })
        .is_none());
        assert_eq!(polls, cutoff);
        assert_eq!(fuel, 0);
        let before = polls;
        assert!(replay(&terms, &clause, &mut fuel, &mut |_, _| {
            polls += 1;
            true
        })
        .is_none());
        assert_eq!(polls, before, "no work after the original resource refusal");
        assert_eq!(
            replay(&terms, &clause, &mut 100_000, &mut |_, _| true),
            Some(true)
        );
        assert!(replay(&terms, &clause, &mut 100_000, &mut |_, bytes| bytes == 0).is_none());
    }
    #[test]
    fn ideal_replay_does_not_hide_malformed_or_mixed_source_behind_false() {
        let (mut terms, mut clause) = fixture(65537, 0, 1);
        let boolean = terms.mk_bool(false);
        clause.insert(0, terms.mk_not_raw(boolean));
        let field = FiniteFieldSort::new(7).unwrap();
        let other = terms.mk_var("foreign", Sort::FiniteField(field));
        let zero = terms.mk_finite_field(0, field);
        let foreign = terms.mk_eq(other, zero);
        clause.push(terms.mk_not_raw(foreign));
        assert!(replay(&terms, &clause, &mut 100_000, &mut |_, _| true).is_none());
        clause.pop();
        let bad = terms.mk_app(Symbol::Named("=".into()), &[boolean, other], Sort::Bool);
        clause.push(terms.mk_not_raw(bad));
        assert!(replay(&terms, &clause, &mut 100_000, &mut |_, _| true).is_none());
    }
    #[test]
    fn ideal_replay_never_refutes_exhaustive_small_field_assignments() {
        for prime in [2, 7] {
            for square in 0..prime {
                for product in 0..prime {
                    let witnessed = (0..prime).any(|x| {
                        (0..prime).any(|y| x * x % prime == square && x * y % prime == product)
                    });
                    let (terms, clause) = fixture(prime, square, product);
                    let derived = replay(&terms, &clause, &mut 20_000, &mut |_, _| true);
                    if witnessed {
                        assert_ne!(
                            derived,
                            Some(true),
                            "SAT F{prime}: x²={square},xy={product}"
                        );
                    }
                    if !witnessed {
                        assert_eq!(derived, Some(true));
                    }
                }
            }
        }
    }
    #[test]
    fn ideal_replay_signed_and_multi_arity_relations_keep_exact_semantics() {
        let (mut terms, clause) = fixture(65537, 0, 1);
        let TermData::Not(first) = terms.get(clause[0]) else {
            panic!("raw clause");
        };
        let TermData::App(_, args) = terms.get(*first) else {
            panic!("equation");
        };
        let args = args.clone();
        let different = terms.mk_app(Symbol::Named("distinct".into()), &args, Sort::Bool);
        let negated = terms.mk_not_raw(different);
        let equivalent = [terms.mk_not_raw(negated), clause[1]];
        assert_eq!(
            replay(&terms, &equivalent, &mut 100_000, &mut |_, _| true),
            Some(true)
        );
        let nary = terms.mk_app(
            Symbol::Named("=".into()),
            &[args[0], args[1], args[1]],
            Sort::Bool,
        );
        let equivalent = [terms.mk_not_raw(nary), clause[1]];
        assert_eq!(
            replay(&terms, &equivalent, &mut 100_000, &mut |_, _| true),
            Some(true)
        );
        let nary_distinct = terms.mk_app(
            Symbol::Named("distinct".into()),
            &[args[0], args[1], args[1]],
            Sort::Bool,
        );
        let not_nary = terms.mk_not_raw(nary_distinct);
        let unsupported = [terms.mk_not_raw(not_nary), clause[1]];
        assert!(replay(&terms, &unsupported, &mut 100_000, &mut |_, _| true).is_none());
        let unsupported = [terms.mk_not_raw(nary_distinct), clause[1]];
        assert!(replay(&terms, &unsupported, &mut 100_000, &mut |_, _| true).is_none());
        let TermData::Not(equation) = terms.get(clause[0]) else {
            panic!("raw clause");
        };
        let negative = terms.mk_not_raw(*equation);
        let unsupported = [terms.mk_not_raw(negative), clause[1]];
        assert_ne!(
            replay(&terms, &unsupported, &mut 100_000, &mut |_, _| true),
            Some(true)
        );
    }

    #[test]
    fn ideal_signed_inverse_columns_reject_forged_sat_fields_including_characteristic_two() {
        for p in [2u32, 3, 7, 65537] {
            let mut terms = TermStore::new();
            let field = FiniteFieldSort::new(p).unwrap();
            let x = terms.mk_var("x", Sort::FiniteField(field));
            let zero = terms.mk_finite_field(0, field);
            let one = terms.mk_finite_field(1, field);
            let x0 = terms.mk_eq(x, zero);
            let x1 = terms.mk_eq(x, one);
            let not_x0 = terms.mk_not_raw(x0);
            // x=0 and x!=0: a genuine signed contradiction.
            assert_eq!(
                replay(&terms, &[not_x0, x0], &mut 100_000, &mut |_, _| true),
                Some(true)
            );
            // x=1 and x!=0 is satisfiable in EVERY tested prime, including 2.
            let not_x1 = terms.mk_not_raw(x1);
            assert_ne!(
                replay(&terms, &[not_x1, x0], &mut 100_000, &mut |_, _| true),
                Some(true)
            );
            let square = terms.mk_app(
                Symbol::Named("ff.mul".into()),
                &[x, x],
                Sort::FiniteField(field),
            );
            let square0 = terms.mk_eq(square, zero);
            let not_square0 = terms.mk_not_raw(square0);
            assert_eq!(
                replay(&terms, &[not_square0, x0], &mut 100_000, &mut |_, _| true),
                Some(true)
            );
            assert_ne!(
                replay(&terms, &[not_square0], &mut 100_000, &mut |_, _| true),
                Some(true)
            );
        }
    }

    #[test]
    fn ideal_proof_rejects_registered_uninterpreted_field_operator_names() {
        use ay_core::{Proof, ProofStep, TheoryLemmaKind};
        let mut terms = TermStore::new();
        let field = FiniteFieldSort::new(7).unwrap();
        let x = terms.mk_var("x", Sort::FiniteField(field));
        let zero = terms.mk_finite_field(0, field);
        let one = terms.mk_finite_field(1, field);
        terms.register_declared_function("ff.mul");
        let application = terms.mk_app(
            Symbol::Named("ff.mul".into()),
            &[x, x],
            Sort::FiniteField(field),
        );
        // SAT: x=0 and the uninterpreted function maps (0,0) to 1.
        let first = terms.mk_eq(application, one);
        let second = terms.mk_eq(x, zero);
        let not_first = terms.mk_not_raw(first);
        let not_second = terms.mk_not_raw(second);
        let mut proof = Proof::new();
        let lemma = proof.add_step(ProofStep::TheoryLemma {
            theory: "FiniteField".into(),
            clause: vec![not_first, not_second],
            farkas: None,
            kind: TheoryLemmaKind::FiniteFieldIdeal,
            lia: None,
        });
        let a = proof.add_assume(first, None);
        let step = proof.add_resolution(vec![not_second], first, a, lemma);
        let b = proof.add_assume(second, None);
        proof.add_resolution(Vec::new(), second, b, step);
        let checked = crate::check_proof_strict_with_context_and_progress(
            &proof,
            &terms,
            None,
            None,
            Some(&[first, second]),
            &mut |_, _| true,
        );
        assert!(
            checked.is_err(),
            "an uninterpreted declaration cannot acquire multiplication semantics: {checked:?}"
        );
    }
}
