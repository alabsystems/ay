// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//! Univariate degree-two witnesses over an authenticated odd prime field.
//! Modular roots: Handbook of Applied Cryptography, algorithms 3.34/3.36,
//! https://cacr.uwaterloo.ca/hac/about/chap3.pdf. Nonresidue search is
//! deterministic and debits the caller's original work counter on every step.

use ay_core::kani_compat::DetHashSet as HashSet;
use ay_core::{Constant, FiniteFieldSort, Sort, Symbol, TermData, TermId, TermStore};

type Polynomial = [u32; 3];

pub(super) enum Candidate {
    Model(Vec<(TermId, u32, FiniteFieldSort)>),
    Contradiction,
}

#[derive(Clone, Copy)]
enum Constraint {
    Equal(Polynomial),
    Different(Polynomial),
}

struct Search<'a, 'c> {
    terms: &'a TermStore,
    variable: TermId,
    field: FiniteFieldSort,
    work: &'c mut usize,
    control: &'c mut dyn FnMut(usize, usize) -> bool,
    // Conservative cumulative storage for this optional algorithm, retained
    // in the SAME original arena. This is not a live allocator/RSS claim.
    bytes: usize,
}

impl Search<'_, '_> {
    fn pay(&mut self, work: usize, bytes: usize) -> Option<()> {
        *self.work = self.work.checked_sub(work)?;
        self.bytes = self.bytes.checked_add(bytes)?;
        (self.control)(work, self.bytes).then_some(())
    }

    fn add(&self, a: u32, b: u32) -> u32 {
        ((u64::from(a) + u64::from(b)) % u64::from(self.field.modulus())) as u32
    }
    fn sub(&self, a: u32, b: u32) -> u32 {
        ((u64::from(a) + u64::from(self.field.modulus()) - u64::from(b))
            % u64::from(self.field.modulus())) as u32
    }
    fn mul(&mut self, a: u32, b: u32) -> Option<u32> {
        self.pay(1, 0)?;
        Some((u64::from(a) * u64::from(b) % u64::from(self.field.modulus())) as u32)
    }
    fn power(&mut self, mut base: u32, mut exponent: u32) -> Option<u32> {
        let mut result = 1;
        while exponent != 0 {
            if exponent & 1 != 0 {
                result = self.mul(result, base)?;
            }
            base = self.mul(base, base)?;
            exponent >>= 1;
        }
        Some(result)
    }
    fn inverse(&mut self, value: u32) -> Option<u32> {
        (value != 0).then_some(())?;
        self.power(value, self.field.modulus() - 2)
    }
    fn root(&mut self, value: u32) -> Option<Option<u32>> {
        let p = self.field.modulus();
        if value == 0 {
            return Some(Some(0));
        }
        if self.power(value, (p - 1) / 2)? != 1 {
            return Some(None);
        }
        let s = (p - 1).trailing_zeros();
        let odd = (p - 1) >> s;
        let mut nonresidue = 2;
        while self.power(nonresidue, (p - 1) / 2)? != p - 1 {
            nonresidue = nonresidue.checked_add(1)?;
            if nonresidue >= p {
                return None;
            }
        }
        let mut c = self.power(nonresidue, odd)?;
        let mut r = self.power(value, (odd + 1) / 2)?;
        let inverse = self.inverse(value)?;
        for i in 1..s {
            let square = self.mul(r, r)?;
            let quotient = self.mul(square, inverse)?;
            let d = self.power(quotient, 1u32.checked_shl(s - i - 1)?)?;
            if d == p - 1 {
                r = self.mul(r, c)?;
            } else if d != 1 {
                return None;
            }
            c = self.mul(c, c)?;
        }
        (self.mul(r, r)? == value).then_some(Some(r))
    }

    fn polynomial(&mut self, term: TermId, depth: usize) -> Option<Polynomial> {
        self.pay(1, 0)?;
        if depth > 128 || self.terms.sort(term) != &Sort::FiniteField(self.field) {
            return None;
        }
        match self.terms.get(term) {
            TermData::Var(..) if term == self.variable => Some([0, 1, 0]),
            TermData::Const(Constant::FiniteField { value, field })
                if *field == self.field && *value < field.modulus() =>
            {
                Some([*value, 0, 0])
            }
            TermData::App(Symbol::Named(name), args) => match name.as_str() {
                "ff.neg" if args.len() == 1 => {
                    let child = self.polynomial(args[0], depth + 1)?;
                    Some(child.map(|c| self.sub(0, c)))
                }
                "ff.add" | "ff.bitsum" if args.len() >= 2 => {
                    let mut result = [0; 3];
                    let mut weight = 1;
                    for &arg in args {
                        let child = self.polynomial(arg, depth + 1)?;
                        for i in 0..3 {
                            let c = self.mul(weight, child[i])?;
                            result[i] = self.add(result[i], c);
                        }
                        if name == "ff.bitsum" {
                            weight = self.add(weight, weight);
                        }
                    }
                    Some(result)
                }
                "ff.mul" if args.len() >= 2 => {
                    let mut result = [1, 0, 0];
                    for &arg in args {
                        let child = self.polynomial(arg, depth + 1)?;
                        let mut product = [0; 3];
                        for i in 0..3 {
                            for j in 0..3 {
                                if result[i] == 0 || child[j] == 0 {
                                    continue;
                                }
                                if i + j > 2 {
                                    return None;
                                }
                                let c = self.mul(result[i], child[j])?;
                                product[i + j] = self.add(product[i + j], c);
                            }
                        }
                        result = product;
                    }
                    Some(result)
                }
                _ => None,
            },
            _ => None,
        }
    }

    fn push(&mut self, constraints: &mut Vec<Constraint>, constraint: Constraint) -> Option<()> {
        self.pay(1, 0)?;
        if constraints.len() == constraints.capacity() {
            let capacity = constraints.capacity().max(2).checked_mul(2)?;
            self.pay(0, capacity.checked_mul(std::mem::size_of::<Constraint>())?)?;
            constraints
                .try_reserve_exact(capacity - constraints.len())
                .ok()?;
        }
        constraints.push(constraint);
        Some(())
    }

    fn satisfies(&mut self, constraints: &[Constraint], value: u32) -> Option<bool> {
        for constraint in constraints {
            let (Constraint::Equal(poly) | Constraint::Different(poly)) = constraint;
            let high = self.mul(poly[2], value)?;
            let low = self.add(high, poly[1]);
            let low = self.mul(low, value)?;
            let evaluated = self.add(low, poly[0]);
            if matches!(constraint, Constraint::Equal(_)) != (evaluated == 0) {
                return Some(false);
            }
        }
        Some(true)
    }
}

pub(super) fn witness_with_progress(
    terms: &TermStore,
    roots: &[TermId],
    seen: &HashSet<TermId>,
    work: &mut usize,
    control: &mut dyn FnMut(usize, usize) -> bool,
) -> Option<Candidate> {
    *work = work.checked_sub(seen.len())?;
    if !control(seen.len(), 0) {
        return None;
    }
    let edges = seen.iter().try_fold(roots.len(), |count, term| {
        if !control(0, 0) {
            return None;
        }
        count.checked_add(match terms.get(*term) {
            TermData::App(_, args) => args.len(),
            TermData::Not(_) => 1,
            TermData::Ite(..) => 3,
            _ => 0,
        })
    })?;
    let stack_capacity = edges;
    let base = seen
        .len()
        .checked_mul(256)?
        .checked_add(stack_capacity.checked_mul(std::mem::size_of::<(TermId, bool, usize)>())?)?;
    if !control(0, base) {
        return None;
    }
    let inspect = seen.len().checked_add(edges)?;
    *work = work.checked_sub(inspect)?;
    if !control(inspect, base) {
        return None;
    }
    let mut field = None;
    let mut variable = None;
    for &term in seen {
        if !control(0, base) {
            return None;
        }
        if let Sort::FiniteField(f) = terms.sort(term) {
            if field.is_some_and(|prior| prior != *f) {
                return None;
            }
            field = Some(*f);
            if matches!(terms.get(term), TermData::Var(..)) {
                if variable.is_some_and(|prior| prior != term) {
                    return None;
                }
                variable = Some(term);
            }
        } else if matches!(terms.get(term), TermData::Var(..)) {
            return None;
        }
    }
    let field = field?;
    if field.modulus() == 2 {
        return None;
    }
    let variable = variable?;
    let mut search = Search {
        terms,
        variable,
        field,
        work,
        control,
        bytes: base,
    };
    let mut pending = Vec::with_capacity(stack_capacity);
    pending.extend(roots.iter().copied().map(|term| (term, false, 0usize)));
    let mut constraints = Vec::new();
    while let Some((term, negative, depth)) = pending.pop() {
        search.pay(1, 0)?;
        if depth > 128 || terms.sort(term) != &Sort::Bool {
            return None;
        }
        match terms.get(term) {
            TermData::Const(Constant::Bool(value)) => {
                if *value == negative {
                    return Some(Candidate::Contradiction);
                }
            }
            TermData::Not(child) => pending.push((*child, !negative, depth + 1)),
            TermData::App(Symbol::Named(name), args) if name == "not" && args.len() == 1 => {
                pending.push((args[0], !negative, depth + 1));
            }
            TermData::App(Symbol::Named(name), args) if name == "and" && !negative => {
                if pending.len().checked_add(args.len())? > stack_capacity {
                    return None;
                }
                pending.extend(args.iter().copied().map(|arg| (arg, false, depth + 1)));
            }
            TermData::App(Symbol::Named(name), args)
                if matches!(name.as_str(), "=" | "distinct") && args.len() >= 2 =>
            {
                let equal = (name == "=") != negative;
                if negative && args.len() != 2 {
                    return None;
                }
                for i in 1..args.len() {
                    let left = search.polynomial(args[i], 0)?;
                    for j in 0..if equal { 1 } else { i } {
                        let right = search.polynomial(args[j], 0)?;
                        let poly = std::array::from_fn(|k| search.sub(left[k], right[k]));
                        search.push(
                            &mut constraints,
                            if equal {
                                Constraint::Equal(poly)
                            } else {
                                Constraint::Different(poly)
                            },
                        )?;
                    }
                }
            }
            _ => return None,
        }
    }
    search.pay(constraints.len(), 0)?;
    let pin = constraints.iter().find_map(|c| match c {
        Constraint::Equal(poly) if *poly != [0; 3] => Some(*poly),
        _ => None,
    });
    let mut candidates = [0u32; 2];
    let count = if let Some([c, b, a]) = pin {
        if a == 0 {
            if b == 0 {
                return Some(Candidate::Contradiction);
            }
            let inverse = search.inverse(b)?;
            candidates[0] = search.mul(search.sub(0, c), inverse)?;
            1
        } else {
            let square = search.mul(b, b)?;
            let product = search.mul(a, c)?;
            let product = search.mul(4 % field.modulus(), product)?;
            let discriminant = search.sub(square, product);
            let Some(root) = search.root(discriminant)? else {
                return Some(Candidate::Contradiction);
            };
            let twice = search.add(a, a);
            let inverse = search.inverse(twice)?;
            let negative_b = search.sub(0, b);
            let plus = search.add(negative_b, root);
            let minus = search.sub(negative_b, root);
            candidates[0] = search.mul(plus, inverse)?;
            candidates[1] = search.mul(minus, inverse)?;
            2
        }
    } else {
        // A nonzero degree-d polynomial excludes at most d points. Search at
        // most one more point than the total excluded-root bound; no field-
        // width-sized table or exhaustive large-prime assignment space.
        let mut excluded = 0u32;
        search.pay(constraints.len(), 0)?;
        for constraint in &constraints {
            if let Constraint::Different(poly) = constraint {
                if *poly == [0; 3] {
                    return Some(Candidate::Contradiction);
                }
                excluded = excluded.checked_add(if poly[2] != 0 {
                    2
                } else {
                    u32::from(poly[1] != 0)
                })?;
            }
        }
        for value in 0..excluded.checked_add(1)?.min(field.modulus()) {
            if search.satisfies(&constraints, value)? {
                search.pay(0, std::mem::size_of::<(TermId, u32, FiniteFieldSort)>())?;
                return Some(Candidate::Model(vec![(variable, value, field)]));
            }
        }
        return None;
    };
    for value in candidates.into_iter().take(count) {
        if search.satisfies(&constraints, value)? {
            search.pay(0, std::mem::size_of::<(TermId, u32, FiniteFieldSort)>())?;
            return Some(Candidate::Model(vec![(variable, value, field)]));
        }
    }
    Some(Candidate::Contradiction)
}
