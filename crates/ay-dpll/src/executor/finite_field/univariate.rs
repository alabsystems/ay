// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//! Univariate witnesses over prime fields. Isolate F_p roots with
//! gcd(f, X^p-X), combine finite/cofinite Boolean root sets, then split with quadratic characters
//! (Cantor-Zassenhaus). See Z3 5.3.3 src/math/ff/ff_f4.cpp, roots/split_roots.
//! The independent model evaluator checks every candidate; independent native
//! theorem replay checks root exhaustion. Resource exhaustion supplies neither
//! verdict. Operations borrow the original attempt's fuel/arena callbacks.

use ay_core::kani_compat::DetHashSet as HashSet;
use ay_core::{Constant, FiniteFieldSort, Sort, Symbol, TermData, TermId, TermStore};

type Poly = Vec<u32>;
pub(super) enum Candidate {
    Model(Vec<(TermId, u32, FiniteFieldSort)>),
    Contradiction,
}
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
enum Progress<'a> {
    #[cfg(test)]
    Cumulative(&'a mut dyn FnMut(usize) -> bool),
    Original(&'a mut dyn FnMut(usize, usize) -> bool),
}
struct Search<'terms, 'fuel, 'control> {
    terms: &'terms TermStore,
    variable: TermId,
    field: FiniteFieldSort,
    fuel: &'fuel mut usize,
    control: Progress<'control>,
    bytes: usize,
}

impl Search<'_, '_, '_> {
    fn pay(&mut self, work: usize, bytes: usize) -> Option<()> {
        *self.fuel = self.fuel.checked_sub(work)?;
        self.bytes = self.bytes.checked_add(bytes)?;
        #[cfg(test)]
        let admitted = match &mut self.control {
            Progress::Cumulative(control) => control(self.bytes),
            Progress::Original(control) => control(work, bytes),
        };
        #[cfg(not(test))]
        let admitted = {
            let Progress::Original(control) = &mut self.control;
            control(work, bytes)
        };
        admitted.then_some(())
    }
    fn zeros(&mut self, len: usize) -> Option<Poly> {
        self.pay(len, len.checked_mul(size_of::<u32>())?)?;
        let mut out = Vec::new();
        out.try_reserve_exact(len).ok()?;
        out.resize(len, 0);
        Some(out)
    }
    fn copy(&mut self, value: &[u32]) -> Option<Poly> {
        let mut out = self.zeros(value.len())?;
        out.copy_from_slice(value);
        Some(out)
    }
    fn trim(poly: &mut Poly) {
        while poly.last() == Some(&0) {
            poly.pop();
        }
    }
    fn add(&self, a: u32, b: u32) -> u32 {
        ((u64::from(a) + u64::from(b)) % u64::from(self.field.modulus())) as u32
    }
    fn sub(&self, a: u32, b: u32) -> u32 {
        ((u64::from(a) + u64::from(self.field.modulus()) - u64::from(b))
            % u64::from(self.field.modulus())) as u32
    }
    fn mul(&self, a: u32, b: u32) -> u32 {
        (u64::from(a) * u64::from(b) % u64::from(self.field.modulus())) as u32
    }
    fn inverse(&mut self, value: u32) -> Option<u32> {
        if value == 0 {
            return None;
        }
        let mut result = 1;
        let mut base = value;
        let mut exponent = self.field.modulus() - 2;
        while exponent != 0 {
            self.pay(2, 0)?;
            if exponent & 1 != 0 {
                result = self.mul(result, base);
            }
            base = self.mul(base, base);
            exponent >>= 1;
        }
        Some(result)
    }
    fn difference(&mut self, a: &[u32], b: &[u32]) -> Option<Poly> {
        let mut out = self.zeros(a.len().max(b.len()))?;
        for (i, value) in out.iter_mut().enumerate() {
            *value = self.sub(
                a.get(i).copied().unwrap_or(0),
                b.get(i).copied().unwrap_or(0),
            );
        }
        Self::trim(&mut out);
        Some(out)
    }
    fn product(&mut self, a: &[u32], b: &[u32]) -> Option<Poly> {
        if a.is_empty() || b.is_empty() {
            return Some(Vec::new());
        }
        self.pay(a.len().checked_mul(b.len())?, 0)?;
        let mut out = self.zeros(a.len().checked_add(b.len())?.checked_sub(1)?)?;
        for (i, &left) in a.iter().enumerate() {
            for (j, &right) in b.iter().enumerate() {
                out[i + j] = self.add(out[i + j], self.mul(left, right));
            }
        }
        Self::trim(&mut out);
        Some(out)
    }
    fn divide(&mut self, mut a: Poly, b: &[u32]) -> Option<(Poly, Poly)> {
        let inverse = self.inverse(*b.last()?)?;
        let mut quotient = self.zeros(a.len().saturating_sub(b.len()).checked_add(1)?)?;
        while !a.is_empty() && a.len() >= b.len() {
            self.pay(b.len(), 0)?;
            let shift = a.len() - b.len();
            let factor = self.mul(*a.last()?, inverse);
            quotient[shift] = factor;
            for (i, &coefficient) in b.iter().enumerate() {
                a[i + shift] = self.sub(a[i + shift], self.mul(factor, coefficient));
            }
            Self::trim(&mut a);
        }
        Self::trim(&mut quotient);
        Some((quotient, a))
    }
    fn gcd(&mut self, mut a: Poly, mut b: Poly) -> Option<Poly> {
        while !b.is_empty() {
            let (_, rest) = self.divide(a, &b)?;
            a = b;
            b = rest;
        }
        if let Some(&leading) = a.last() {
            let inverse = self.inverse(leading)?;
            self.pay(a.len(), 0)?;
            for coefficient in &mut a {
                *coefficient = self.mul(*coefficient, inverse);
            }
        }
        Some(a)
    }
    fn power_mod(&mut self, mut base: Poly, mut exponent: u32, modulus: &[u32]) -> Option<Poly> {
        let mut result = self.zeros(1)?;
        result[0] = 1;
        while exponent != 0 {
            self.pay(1, 0)?;
            if exponent & 1 != 0 {
                let product = self.product(&result, &base)?;
                result = self.divide(product, modulus)?.1;
            }
            exponent >>= 1;
            if exponent != 0 {
                let square = self.product(&base, &base)?;
                base = self.divide(square, modulus)?.1;
            }
        }
        Some(result)
    }
    fn evaluate(&mut self, polynomial: &[u32], value: u32) -> Option<u32> {
        self.pay(polynomial.len(), 0)?;
        Some(polynomial.iter().rev().fold(0, |sum, &coefficient| {
            self.add(self.mul(sum, value), coefficient)
        }))
    }
    fn polynomial(&mut self, term: TermId, depth: usize) -> Option<Poly> {
        self.pay(1, 0)?;
        if depth > 128 || self.terms.sort(term) != &Sort::FiniteField(self.field) {
            return None;
        }
        match self.terms.get(term) {
            TermData::Var(..) if term == self.variable => {
                let mut out = self.zeros(2)?;
                out[1] = 1;
                Some(out)
            }
            TermData::Const(Constant::FiniteField { value, field })
                if *field == self.field && *value < field.modulus() =>
            {
                let mut out = self.zeros(usize::from(*value != 0))?;
                if let Some(constant) = out.first_mut() {
                    *constant = *value;
                }
                Some(out)
            }
            TermData::App(Symbol::Named(name), args) => match name.as_str() {
                "ff.neg" if args.len() == 1 => {
                    let mut out = self.polynomial(args[0], depth + 1)?;
                    self.pay(out.len(), 0)?;
                    for value in &mut out {
                        *value = self.sub(0, *value);
                    }
                    Some(out)
                }
                "ff.add" | "ff.bitsum" if args.len() >= 2 => {
                    let mut out = Vec::new();
                    let mut weight = 1;
                    for &arg in args {
                        let mut child = self.polynomial(arg, depth + 1)?;
                        self.pay(child.len(), 0)?;
                        for value in &mut child {
                            *value = self.sub(0, self.mul(weight, *value));
                        }
                        out = self.difference(&out, &child)?;
                        if name == "ff.bitsum" {
                            weight = self.add(weight, weight);
                        }
                    }
                    Some(out)
                }
                "ff.mul" if args.len() >= 2 => {
                    let mut out = self.zeros(1)?;
                    out[0] = 1;
                    for &arg in args {
                        let child = self.polynomial(arg, depth + 1)?;
                        out = self.product(&out, &child)?;
                    }
                    Some(out)
                }
                _ => None,
            },
            _ => None,
        }
    }

    fn empty_set(&mut self) -> Option<RootSet> {
        let mut p = self.zeros(1)?;
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
        let x = self.copy(&[0, 1])?;
        let power = self.power_mod(x, self.field.modulus(), &p)?;
        let equation = self.difference(&power, &[0, 1])?;
        Some(RootSet::Finite(self.gcd(p, equation)?))
    }
    fn exact_quotient(&mut self, a: Poly, b: &Poly) -> Option<Poly> {
        let (q, r) = self.divide(a, b)?;
        r.is_empty().then_some(q)
    }
    fn intersection(&mut self, a: RootSet, b: RootSet) -> Option<RootSet> {
        match (a, b) {
            (RootSet::Finite(a), RootSet::Finite(b)) => Some(RootSet::Finite(self.gcd(a, b)?)),
            (RootSet::Finite(a), RootSet::Cofinite(b))
            | (RootSet::Cofinite(b), RootSet::Finite(a)) => {
                let copy = self.copy(&a)?;
                let common = self.gcd(copy, b)?;
                Some(RootSet::Finite(self.exact_quotient(a, &common)?))
            }
            (RootSet::Cofinite(a), RootSet::Cofinite(b)) => {
                let ac = self.copy(&a)?;
                let bc = self.copy(&b)?;
                let common = self.gcd(ac, bc)?;
                let quotient = self.exact_quotient(a, &common)?;
                Some(RootSet::Cofinite(self.product(&quotient, &b)?))
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
            RootSet::Finite(p) => RootSet::Finite(self.copy(p)?),
            RootSet::Cofinite(p) => RootSet::Cofinite(self.copy(p)?),
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
            TermData::App(Symbol::Named(name), args) => match name.as_str() {
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
                            let left = self.polynomial(args[i], 0)?;
                            let right = self.polynomial(args[j], 0)?;
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
    fn root(&mut self, mut polynomial: Poly, forbidden: &[Poly]) -> Option<Option<u32>> {
        if polynomial.is_empty() {
            let mut bound = 1usize;
            for polynomial in forbidden {
                self.pay(1, 0)?;
                if polynomial.is_empty() {
                    return Some(None);
                }
                bound = bound.checked_add(polynomial.len().saturating_sub(1))?;
            }
            for value in 0..bound.min(self.field.modulus() as usize) {
                self.pay(1, 0)?;
                let mut valid = true;
                for polynomial in forbidden {
                    self.pay(1, 0)?;
                    if self.evaluate(polynomial, value as u32)? == 0 {
                        valid = false;
                        break;
                    }
                }
                if valid {
                    return Some(Some(value as u32));
                }
            }
            return (bound >= self.field.modulus() as usize).then_some(None);
        }
        if polynomial.len() <= 1 {
            return Some(None);
        }
        let x = self.copy(&[0, 1])?;
        let power = self.power_mod(x, self.field.modulus(), &polynomial)?;
        let field_equation = self.difference(&power, &[0, 1])?;
        polynomial = self.gcd(polynomial, field_equation)?;
        for exclusion in forbidden {
            let copy = self.copy(&polynomial)?;
            let excluded = self.copy(exclusion)?;
            let divisor = self.gcd(copy, excluded)?;
            let (quotient, remainder) = self.divide(polynomial, &divisor)?;
            if !remainder.is_empty() {
                return None;
            }
            polynomial = quotient;
        }
        while polynomial.len() > 2 {
            let mut found = None;
            // Deterministic trial order; fuel bounds an unlucky split search.
            for shift in 0..self.field.modulus() {
                let base = self.copy(&[shift, 1])?;
                let power = self.power_mod(base, (self.field.modulus() - 1) / 2, &polynomial)?;
                let difference = self.difference(&power, &[1])?;
                let copy = self.copy(&polynomial)?;
                let factor = self.gcd(copy, difference)?;
                if factor.len() > 1 && factor.len() < polynomial.len() {
                    found = Some(factor);
                    break;
                }
            }
            polynomial = found?;
        }
        if polynomial.len() == 1 {
            return Some(None);
        }
        if polynomial.len() != 2 {
            return None;
        }
        let inverse = self.inverse(polynomial[1])?;
        Some(Some(self.mul(self.sub(0, polynomial[0]), inverse)))
    }
}

pub(super) fn witness_with_progress(
    terms: &TermStore,
    roots: &[TermId],
    seen: &HashSet<TermId>,
    fuel: &mut usize,
    control: &mut dyn FnMut(usize, usize) -> bool,
) -> Option<Candidate> {
    *fuel = fuel.checked_sub(seen.len())?;
    if !control(seen.len(), 0) {
        return None;
    }
    let mut variable = None;
    let mut field = None;
    for &term in seen {
        if !control(0, 0) {
            return None;
        }
        if let Sort::FiniteField(current) = terms.sort(term) {
            if field.is_some_and(|old| old != *current) {
                return None;
            }
            field = Some(*current);
            if matches!(terms.get(term), TermData::Var(..)) {
                if variable.is_some_and(|old| old != term) {
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
    let mut bytes = 0usize;
    let mut cumulative = |work, extra| {
        let Some(total) = bytes.checked_add(extra) else {
            return false;
        };
        bytes = total;
        control(work, total)
    };
    let mut search = Search {
        terms,
        variable,
        field,
        fuel,
        control: Progress::Original(&mut cumulative),
        bytes: 0,
    };
    search.pay(roots.len(), seen.len().checked_mul(256)?)?;
    let mut allowed = search.empty_set()?.complement();
    for &root in roots {
        let next = search.boolean_set(root, 0)?;
        allowed = search.intersection(allowed, next)?;
    }
    let value = match allowed {
        RootSet::Finite(p) => search.root(p, &[])?,
        RootSet::Cofinite(p) => search.root(Vec::new(), &[p])?,
    };
    let Some(value) = value else {
        return Some(Candidate::Contradiction);
    };
    search.pay(1, size_of::<(TermId, u32, FiniteFieldSort)>())?;
    Some(Candidate::Model(vec![(variable, value, field)]))
}

/// One algebraically isolated root and the polynomial with ALL copies of
/// that factor removed. This is proposal arithmetic, never theorem evidence.
pub(super) struct RootChoice {
    pub(super) value: u32,
    pub(super) remaining: Vec<u32>,
}

/// Reuse the admitted arithmetic with the actual authored variable/domain.
/// `Some(None)` means no F_p root; `None` is terminal original refusal.
/// The callback reports cumulative storage for THIS call. An outer ledger
/// must retain prior calls and add only each monotonic delta.
#[cfg(test)]
pub(super) fn next_root(
    terms: &TermStore,
    variable: TermId,
    field: FiniteFieldSort,
    polynomial: Vec<u32>,
    fuel: &mut usize,
    control: &mut dyn FnMut(usize) -> bool,
) -> Option<Option<RootChoice>> {
    next_root_controlled(
        terms,
        variable,
        field,
        polynomial,
        fuel,
        Progress::Cumulative(control),
    )
}

pub(super) fn next_root_with_progress(
    terms: &TermStore,
    variable: TermId,
    field: FiniteFieldSort,
    polynomial: Vec<u32>,
    fuel: &mut usize,
    control: &mut dyn FnMut(usize, usize) -> bool,
) -> Option<Option<RootChoice>> {
    next_root_controlled(
        terms,
        variable,
        field,
        polynomial,
        fuel,
        Progress::Original(control),
    )
}

fn next_root_controlled(
    terms: &TermStore,
    variable: TermId,
    field: FiniteFieldSort,
    mut polynomial: Vec<u32>,
    fuel: &mut usize,
    control: Progress<'_>,
) -> Option<Option<RootChoice>> {
    if *fuel == 0 {
        return None;
    }
    if terms.sort(variable) != &Sort::FiniteField(field)
        || !matches!(terms.get(variable), TermData::Var(..))
    {
        *fuel = 0;
        return None;
    }
    let mut search = Search {
        terms,
        variable,
        field,
        fuel,
        control,
        bytes: 0,
    };
    let result = (|| {
        search.pay(polynomial.len().checked_mul(2)?, 0)?;
        if polynomial
            .iter()
            .any(|&coefficient| coefficient >= field.modulus())
        {
            return None;
        }
        Search::trim(&mut polynomial);
        if polynomial.is_empty() {
            return None;
        } // zero is a whole domain, not an empty root set
        if polynomial.len() == 1 {
            return Some(None);
        }
        let value = if field.modulus() == 2 {
            // X²-X = X(X+1) is the complete square-free field polynomial
            // in characteristic two. Factor by gcd, rather than value trials.
            let copy = search.copy(&polynomial)?;
            let x = search.copy(&[0, 1])?;
            if search.gcd(copy, x)?.len() == 2 {
                Some(0)
            } else {
                let copy = search.copy(&polynomial)?;
                let x_plus_one = search.copy(&[1, 1])?;
                (search.gcd(copy, x_plus_one)?.len() == 2).then_some(1)
            }
        } else {
            let copy = search.copy(&polynomial)?;
            search.root(copy, &[])?
        };
        let Some(value) = value else {
            return Some(None);
        };
        let factor = search.copy(&[search.sub(0, value), 1])?;
        loop {
            let copy = search.copy(&polynomial)?;
            let (quotient, remainder) = search.divide(copy, &factor)?;
            if !remainder.is_empty() {
                break;
            }
            polynomial = quotient;
            if polynomial.len() <= 1 {
                break;
            }
        }
        Some(Some(RootChoice {
            value,
            remaining: polynomial,
        }))
    })();
    if result.is_none() {
        *search.fuel = 0;
    }
    result
}

/// Selection from the complement of a proved forbidden-root set.
pub(super) enum OutsideRoots {
    Point(u32),
    Empty,
    Unsupported,
}

/// Domain selection is used only AFTER a rational-family identity is proved.
/// Every admitted point is valid for the entire family, so this is certified
/// finite/cofinite avoidance, not speculative model-value trials.
#[cfg(test)]
pub(super) fn outside_roots(
    terms: &TermStore,
    variable: TermId,
    field: FiniteFieldSort,
    forbidden: Vec<u32>,
    fuel: &mut usize,
    control: &mut dyn FnMut(usize) -> bool,
) -> Option<OutsideRoots> {
    outside_roots_controlled(
        terms,
        variable,
        field,
        forbidden,
        fuel,
        Progress::Cumulative(control),
    )
}

pub(super) fn outside_roots_with_progress(
    terms: &TermStore,
    variable: TermId,
    field: FiniteFieldSort,
    forbidden: Vec<u32>,
    fuel: &mut usize,
    control: &mut dyn FnMut(usize, usize) -> bool,
) -> Option<OutsideRoots> {
    outside_roots_controlled(
        terms,
        variable,
        field,
        forbidden,
        fuel,
        Progress::Original(control),
    )
}

fn outside_roots_controlled(
    terms: &TermStore,
    variable: TermId,
    field: FiniteFieldSort,
    mut forbidden: Vec<u32>,
    fuel: &mut usize,
    control: Progress<'_>,
) -> Option<OutsideRoots> {
    if *fuel == 0 {
        return None;
    }
    if terms.sort(variable) != &Sort::FiniteField(field)
        || !matches!(terms.get(variable), TermData::Var(..))
    {
        *fuel = 0;
        return None;
    }
    let mut search = Search {
        terms,
        variable,
        field,
        fuel,
        control,
        bytes: 0,
    };
    let result = (|| {
        search.pay(forbidden.len().checked_mul(2)?, 0)?;
        if forbidden
            .iter()
            .any(|&coefficient| coefficient >= field.modulus())
        {
            return None;
        }
        Search::trim(&mut forbidden);
        if forbidden.is_empty() {
            return Some(OutsideRoots::Empty);
        }
        if forbidden[0] != 0 {
            return Some(OutsideRoots::Point(0));
        }
        if field.modulus() == 2 {
            // The only remaining possible domain component is X+1, from the
            // exact factorization X²-X=X(X+1). No scalar-sized search.
            let copy = search.copy(&forbidden)?;
            let factor = search.copy(&[1, 1])?;
            return Some(if search.gcd(copy, factor)?.len() == 1 {
                OutsideRoots::Point(1)
            } else {
                OutsideRoots::Empty
            });
        }
        // The nonroot algorithm uses at most degree+1 points, justified by
        // the root bound. Never let it turn into enumeration of the field.
        if forbidden.len() >= field.modulus() as usize {
            return Some(OutsideRoots::Unsupported);
        }
        Some(match search.root(Vec::new(), &[forbidden])? {
            Some(value) => OutsideRoots::Point(value),
            None => OutsideRoots::Empty,
        })
    })();
    if result.is_none() {
        *search.fuel = 0;
    }
    result
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parametric_outside_roots_matches_independent_domain_truth() {
        for prime in [2, 7] {
            let mut terms = TermStore::new();
            let field = FiniteFieldSort::new(prime).unwrap();
            let variable = terms.mk_var("t", Sort::FiniteField(field));
            for a in 0..prime {
                for b in 0..prime {
                    for c in 0..prime {
                        let evaluate = |t: u32| (t * t * t + a * t * t + b * t + c) % prime;
                        let possible = (0..prime).any(|t| evaluate(t) != 0);
                        match outside_roots(
                            &terms,
                            variable,
                            field,
                            vec![c, b, a, 1],
                            &mut 100_000,
                            &mut |_| true,
                        )
                        .unwrap()
                        {
                            OutsideRoots::Point(point) => {
                                assert!(possible);
                                assert_ne!(evaluate(point), 0);
                            }
                            OutsideRoots::Empty => assert!(!possible),
                            OutsideRoots::Unsupported => panic!("small exact domain"),
                        }
                    }
                }
            }
            let mut fuel = 100_000;
            let mut polls = 0;
            assert!(
                outside_roots(&terms, variable, field, vec![0, 1], &mut fuel, &mut |_| {
                    polls += 1;
                    false
                })
                .is_none()
            );
            assert_eq!(fuel, 0);
            let before = polls;
            assert!(
                outside_roots(&terms, variable, field, vec![0, 1], &mut fuel, &mut |_| {
                    polls += 1;
                    true
                })
                .is_none()
            );
            assert_eq!(polls, before);
        }
    }

    #[test]
    fn next_root_choices_match_exhaustive_fields_without_duplicates_or_fresh_fuel() {
        for prime in [2, 7] {
            let mut terms = TermStore::new();
            let field = FiniteFieldSort::new(prime).unwrap();
            let variable = terms.mk_var("x", Sort::FiniteField(field));
            for a in 0..prime {
                for b in 0..prime {
                    for c in 0..prime {
                        let mut polynomial = vec![c, b, a, 1];
                        let expected: Vec<_> = (0..prime)
                            .filter(|&x| (x * x * x + a * x * x + b * x + c) % prime == 0)
                            .collect();
                        let mut actual = Vec::new();
                        let mut fuel = 100_000;
                        while let Some(choice) =
                            next_root(&terms, variable, field, polynomial, &mut fuel, &mut |_| {
                                true
                            })
                            .expect("bounded cubic roots")
                        {
                            assert!(
                                !actual.contains(&choice.value),
                                "repeated factor cannot repeat a branch"
                            );
                            actual.push(choice.value);
                            polynomial = choice.remaining;
                        }
                        actual.sort_unstable();
                        assert_eq!(actual, expected, "F{prime}: {a},{b},{c}");
                        assert!(fuel < 100_000);
                    }
                }
            }
        }
    }
    #[test]
    fn next_root_refusal_is_terminal_and_bound_to_original_source_variable() {
        let mut terms = TermStore::new();
        let field = FiniteFieldSort::new(65537).unwrap();
        let variable = terms.mk_var("x", Sort::FiniteField(field));
        let mut fuel = 100_000;
        let mut polls = 0;
        assert!(next_root(
            &terms,
            variable,
            field,
            vec![65536, 0, 1],
            &mut fuel,
            &mut |_| {
                polls += 1;
                polls < 3
            }
        )
        .is_none());
        assert_eq!(fuel, 0);
        assert_eq!(polls, 3);
        assert!(next_root(
            &terms,
            variable,
            field,
            vec![65536, 0, 1],
            &mut fuel,
            &mut |_| {
                polls += 1;
                true
            }
        )
        .is_none());
        assert_eq!(polls, 3);
        let other = FiniteFieldSort::new(7).unwrap();
        assert!(next_root(
            &terms,
            variable,
            other,
            vec![6, 0, 1],
            &mut 100_000,
            &mut |_| true
        )
        .is_none());
        assert!(
            next_root(&terms, variable, field, vec![0], &mut 100_000, &mut |_| {
                true
            })
            .is_none()
        );
        assert!(next_root(
            &terms,
            variable,
            field,
            vec![65537, 1],
            &mut 100_000,
            &mut |_| true
        )
        .is_none());
    }

    #[test]
    fn boolean_root_sets_match_exhaustive_field_membership_and_share_refusal() {
        let mut terms = TermStore::new();
        let field = FiniteFieldSort::new(7).unwrap();
        let variable = terms.mk_var("x", Sort::FiniteField(field));
        let mut fuel = 1_000_000;
        let mut admit = |_| true;
        let mut search = Search {
            terms: &terms,
            variable,
            field,
            fuel: &mut fuel,
            control: Progress::Cumulative(&mut admit),
            bytes: 0,
        };
        for a in 0..7 {
            for b in 0..7 {
                for ca in [false, true] {
                    for cb in [false, true] {
                        let pa = search.copy(&[(7 - a) % 7, 1]).unwrap();
                        let pb = search.copy(&[(7 - b) % 7, 1]).unwrap();
                        let left = if ca {
                            RootSet::Cofinite(pa)
                        } else {
                            RootSet::Finite(pa)
                        };
                        let right = if cb {
                            RootSet::Cofinite(pb)
                        } else {
                            RootSet::Finite(pb)
                        };
                        let result = search.intersection(left, right).unwrap();
                        for x in 0..7 {
                            let (RootSet::Finite(p) | RootSet::Cofinite(p)) = &result;
                            let zero = search.evaluate(p, x).unwrap() == 0;
                            let actual = if matches!(result, RootSet::Cofinite(_)) {
                                !zero
                            } else {
                                zero
                            };
                            assert_eq!(actual, ((x == a) != ca) && ((x == b) != cb));
                        }
                    }
                }
            }
        }
        let remaining = *search.fuel;
        assert!(remaining < 1_000_000);
        *search.fuel = 0;
        assert!(search.empty_set().is_none());
        assert!(search.field_roots(vec![1, 0, 1]).is_none());
    }

    #[test]
    fn univariate_roots_agree_with_exhaustive_small_field_oracle() {
        let mut terms = TermStore::new();
        let field = FiniteFieldSort::new(7).unwrap();
        let variable = terms.mk_var("x", Sort::FiniteField(field));
        for a in 0..7 {
            for b in 0..7 {
                for c in 0..7 {
                    let polynomial = vec![c, b, a, 1];
                    // Separate integer evaluator; neither the polynomial
                    // kernel nor the production model evaluator is its oracle.
                    let value = |x: u32| (x * x * x + a * x * x + b * x + c) % 7;
                    let expected = (0..7).any(|x| value(x) == 0 && x != 2);
                    let mut fuel = 100_000;
                    let mut admit = |_| true;
                    let mut search = Search {
                        terms: &terms,
                        variable,
                        field,
                        fuel: &mut fuel,
                        control: Progress::Cumulative(&mut admit),
                        bytes: 0,
                    };
                    let root = search
                        .root(polynomial.clone(), &[vec![5, 1]])
                        .expect("complete small-field root isolation");
                    assert_eq!(root.is_some(), expected, "{polynomial:?}");
                    if let Some(root) = root {
                        assert_eq!(value(root), 0);
                        assert_ne!(root, 2);
                    }
                }
            }
        }
    }

    #[test]
    fn univariate_root_search_retains_original_fuel_and_refusal() {
        let mut terms = TermStore::new();
        let field = FiniteFieldSort::new(65537).unwrap();
        let variable = terms.mk_var("x", Sort::FiniteField(field));
        let mut fuel = 0;
        let mut admit = |_| true;
        let mut search = Search {
            terms: &terms,
            variable,
            field,
            fuel: &mut fuel,
            control: Progress::Cumulative(&mut admit),
            bytes: 0,
        };
        assert!(search.root(vec![65510, 0, 0, 1], &[]).is_none());
        assert!(search.root(Vec::new(), &[]).is_none());
        assert_eq!(fuel, 0);

        let mut fuel = 100_000;
        let mut calls = 0;
        let mut refuse = |_| {
            calls += 1;
            calls < 3
        };
        let mut search = Search {
            terms: &terms,
            variable,
            field,
            fuel: &mut fuel,
            control: Progress::Cumulative(&mut refuse),
            bytes: 0,
        };
        assert!(search.root(vec![65510, 0, 0, 1], &[]).is_none());
        assert_eq!(calls, 3);
        assert!(fuel < 100_000);
    }
}
