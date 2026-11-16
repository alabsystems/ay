// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Original-owned sparse ring normalization (Z3 5.3.3 poly_rewriter).
//! Coefficients and compact positive degrees are canonical numeric TermIds;
//! copies of a polynomial therefore never hide a variable-sized bigint clone.
use super::{
    field_to_bv::Borrowed,
    polynomial_parameters::{PolynomialParameters, Settings},
    tactic_parameters::Steps,
    tactics::TacticFailure,
};
use ay_core::term::{
    reserve_counted, CountedRingBuiltin as Op, CountedTermBuilder, TermConstructionAdmission,
};
use ay_core::{Constant, Sort, Symbol, TermData, TermId, TermStore};
use std::cmp::Ordering;

mod ordering;
use ordering::sort;

fn fail() -> TacticFailure {
    TacticFailure::new("polynomial rewrite stopped or source is not well-typed")
}
fn pay(owner: &dyn TermConstructionAdmission, n: usize) -> Result<(), TacticFailure> {
    owner.admit(n, 0).map_err(|_| fail())
}
type Builder<'a, 'b, 'c> = CountedTermBuilder<'a, 'b, Borrowed<'c>>;
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
struct Factor {
    atom: TermId,
    degree: TermId,
}
struct Row {
    coefficient: TermId,
    factors: Vec<Factor>,
    order: usize,
}
struct Poly {
    rows: Vec<Row>,
}
#[derive(Clone, Copy)]
enum SumMode {
    Add,
    Subtract,
}

struct Ring<'a, 'b, 'c, 'd> {
    builder: Builder<'a, 'b, 'c>,
    owner: &'c dyn TermConstructionAdmission,
    settings: Settings,
    steps: &'d mut Steps,
}
impl Ring<'_, '_, '_, '_> {
    fn head(&self, id: TermId, name: &str) -> Result<bool, TacticFailure> {
        match self.builder.terms().get(id) {
            TermData::App(Symbol::Named(h), _) => {
                pay(self.owner, h.len())?;
                Ok(h == name && !self.builder.terms().is_declared_function(h))
            }
            _ => Ok(false),
        }
    }
    fn args(&self, id: TermId) -> Result<Vec<TermId>, TacticFailure> {
        let TermData::App(_, args) = self.builder.terms().get(id) else {
            return Err(fail());
        };
        let mut result = Vec::new();
        reserve_counted(&mut result, args.len(), self.owner).map_err(|_| fail())?;
        pay(self.owner, args.len())?;
        result.extend_from_slice(args);
        Ok(result)
    }
    fn number(&self, id: TermId) -> bool {
        matches!(
            self.builder.terms().get(id),
            TermData::Const(Constant::Int(_) | Constant::Rational(_))
        )
    }
    fn one(&mut self, prototype: TermId) -> Result<TermId, TacticFailure> {
        self.builder.number_like(1, prototype).map_err(|_| fail())
    }
    fn one_degree(&mut self) -> Result<TermId, TacticFailure> {
        self.owner.admit(1, 8).map_err(|_| fail())?;
        self.builder
            .integer(&num_bigint::BigInt::from(1))
            .map_err(|_| fail())
    }
    fn atom(&mut self, id: TermId, prototype: TermId) -> Result<Poly, TacticFailure> {
        let coefficient = self.one(prototype)?;
        let degree = self.one_degree()?;
        let mut factors = Vec::new();
        reserve_counted(&mut factors, 1, self.owner).map_err(|_| fail())?;
        factors.push(Factor { atom: id, degree });
        let mut rows = Vec::new();
        reserve_counted(&mut rows, 1, self.owner).map_err(|_| fail())?;
        rows.push(Row {
            coefficient,
            factors,
            order: 0,
        });
        Ok(Poly { rows })
    }
    fn literal(&mut self, id: TermId, prototype: TermId) -> Result<Poly, TacticFailure> {
        let coefficient = self
            .builder
            .number_convert_like(id, prototype)
            .map_err(|_| fail())?;
        let mut rows = Vec::new();
        reserve_counted(&mut rows, 1, self.owner).map_err(|_| fail())?;
        rows.push(Row {
            coefficient,
            factors: Vec::new(),
            order: 0,
        });
        Ok(Poly { rows })
    }
    fn compact(&mut self, factors: &mut Vec<Factor>) -> Result<(), TacticFailure> {
        sort(factors, self.owner, &mut |a, b| {
            pay(self.owner, 1)?;
            Ok(a.atom.cmp(&b.atom))
        })?;
        let mut out = 0;
        for index in 0..factors.len() {
            pay(self.owner, 1)?;
            let next = factors[index];
            if out > 0 && factors[out - 1].atom == next.atom {
                factors[out - 1].degree = self
                    .builder
                    .number_add(factors[out - 1].degree, next.degree)
                    .map_err(|_| fail())?;
            } else {
                factors[out] = next;
                out += 1
            }
        }
        factors.truncate(out);
        Ok(())
    }
    fn monomial(&mut self, id: TermId, prototype: TermId) -> Result<Row, TacticFailure> {
        let mut coefficient = self.one(prototype)?;
        let mut pending = Vec::new();
        reserve_counted(&mut pending, 1, self.owner).map_err(|_| fail())?;
        pending.push(id);
        let mut factors = Vec::new();
        let one = self.one_degree()?;
        while let Some(term) = pending.pop() {
            pay(self.owner, 1)?;
            if self.number(term) {
                let value = self
                    .builder
                    .number_convert_like(term, prototype)
                    .map_err(|_| fail())?;
                coefficient = self
                    .builder
                    .number_product(coefficient, value)
                    .map_err(|_| fail())?;
                continue;
            }
            if self.head(term, "*")? {
                let args = self.args(term)?;
                if args.len() < 2 {
                    return Err(fail());
                }
                if self.settings.flat {
                    reserve_counted(&mut pending, args.len(), self.owner).map_err(|_| fail())?;
                    pay(self.owner, args.len())?;
                    pending.extend(args.into_iter().rev());
                    continue;
                }
                // The native non-flat rule still extracts one leading coefficient.
                if args.len() == 2 && self.number(args[0]) {
                    reserve_counted(&mut pending, 2, self.owner).map_err(|_| fail())?;
                    pending.extend([args[1], args[0]]);
                    continue;
                }
            }
            let (atom, degree) = if self.settings.mul_to_power && self.head(term, "^")? {
                let args = self.args(term)?;
                if args.len() != 2 {
                    return Err(fail());
                }
                if self.number(args[1])
                    && self
                        .builder
                        .number_positive_integral(args[1])
                        .map_err(|_| fail())?
                {
                    (
                        args[0],
                        self.builder.number_integer(args[1]).map_err(|_| fail())?,
                    )
                } else {
                    (term, one)
                }
            } else {
                (term, one)
            };
            reserve_counted(&mut factors, 1, self.owner).map_err(|_| fail())?;
            factors.push(Factor { atom, degree });
        }
        self.compact(&mut factors)?;
        Ok(Row {
            coefficient,
            factors,
            order: 0,
        })
    }
    fn canonical(&mut self, mut rows: Vec<Row>) -> Result<Poly, TacticFailure> {
        for (i, row) in rows.iter_mut().enumerate() {
            pay(self.owner, 1)?;
            row.order = i;
        }
        sort(&mut rows, self.owner, &mut |a, b| {
            pay(
                self.owner,
                a.factors
                    .len()
                    .min(b.factors.len())
                    .checked_add(1)
                    .ok_or_else(fail)?,
            )?;
            Ok(a.factors.cmp(&b.factors))
        })?;
        let mut output: Vec<Row> = Vec::new();
        reserve_counted(&mut output, rows.len(), self.owner).map_err(|_| fail())?;
        for row in rows {
            if let Some(previous) = output.last_mut() {
                pay(
                    self.owner,
                    previous
                        .factors
                        .len()
                        .min(row.factors.len())
                        .checked_add(1)
                        .ok_or_else(fail)?,
                )?;
                if previous.factors == row.factors {
                    previous.coefficient = self
                        .builder
                        .number_add(previous.coefficient, row.coefficient)
                        .map_err(|_| fail())?;
                    previous.order = previous.order.min(row.order);
                    continue;
                }
            }
            output.push(row);
        }
        let mut nonzero = Vec::new();
        reserve_counted(&mut nonzero, output.len(), self.owner).map_err(|_| fail())?;
        for row in output {
            if !self
                .builder
                .number_is_zero(row.coefficient)
                .map_err(|_| fail())?
            {
                nonzero.push(row)
            }
        }
        if !self.settings.sort_sums {
            sort(&mut nonzero, self.owner, &mut |a, b| {
                pay(self.owner, 1)?;
                Ok(match (a.factors.is_empty(), b.factors.is_empty()) {
                    (true, false) => Ordering::Less,
                    (false, true) => Ordering::Greater,
                    _ => a.order.cmp(&b.order),
                })
            })?;
        }
        Ok(Poly { rows: nonzero })
    }
    fn sum(&mut self, id: TermId, prototype: TermId) -> Result<Poly, TacticFailure> {
        let mut pending = Vec::new();
        reserve_counted(&mut pending, 1, self.owner).map_err(|_| fail())?;
        pending.push(id);
        let mut rows = Vec::new();
        while let Some(term) = pending.pop() {
            pay(self.owner, 1)?;
            if self.settings.flat && self.head(term, "+")? {
                let args = self.args(term)?;
                if args.len() < 2 {
                    return Err(fail());
                }
                reserve_counted(&mut pending, args.len(), self.owner).map_err(|_| fail())?;
                pay(self.owner, args.len())?;
                pending.extend(args.into_iter().rev());
            } else {
                let row = self.monomial(term, prototype)?;
                reserve_counted(&mut rows, 1, self.owner).map_err(|_| fail())?;
                rows.push(row);
            }
        }
        self.canonical(rows)
    }
    fn add_args(
        &mut self,
        args: &[TermId],
        prototype: TermId,
        mode: SumMode,
    ) -> Result<Poly, TacticFailure> {
        let mut rows = Vec::new();
        for (index, &id) in args.iter().enumerate() {
            let child = self.sum(id, prototype)?;
            reserve_counted(&mut rows, child.rows.len(), self.owner).map_err(|_| fail())?;
            for mut row in child.rows {
                pay(self.owner, 1)?;
                if matches!(mode, SumMode::Subtract) && (index > 0 || args.len() == 1) {
                    row.coefficient = self
                        .builder
                        .number_negate(row.coefficient)
                        .map_err(|_| fail())?;
                }
                rows.push(row);
            }
        }
        self.canonical(rows)
    }
    fn product(&mut self, args: &[TermId], prototype: TermId) -> Result<Poly, TacticFailure> {
        let mut flat = Vec::new();
        let mut pending = Vec::new();
        reserve_counted(&mut pending, args.len(), self.owner).map_err(|_| fail())?;
        pay(self.owner, args.len())?;
        pending.extend(args.iter().rev().copied());
        while let Some(id) = pending.pop() {
            pay(self.owner, 1)?;
            if self.builder.terms().sort(id) != self.builder.terms().sort(prototype) {
                return Err(fail());
            }
            if self.settings.flat && self.head(id, "*")? {
                let child = self.args(id)?;
                if child.len() < 2 {
                    return Err(fail());
                }
                reserve_counted(&mut pending, child.len(), self.owner).map_err(|_| fail())?;
                pay(self.owner, child.len())?;
                pending.extend(child.into_iter().rev());
            } else {
                reserve_counted(&mut flat, 1, self.owner).map_err(|_| fail())?;
                flat.push(id);
            }
        }
        // Validate/normalize every input before any zero-product return.
        let mut coefficient = self.one(prototype)?;
        let mut others = Vec::new();
        for id in flat {
            if self.number(id) {
                let n = self
                    .builder
                    .number_convert_like(id, prototype)
                    .map_err(|_| fail())?;
                coefficient = self
                    .builder
                    .number_product(coefficient, n)
                    .map_err(|_| fail())?;
            } else {
                reserve_counted(&mut others, 1, self.owner).map_err(|_| fail())?;
                others.push(id);
            }
        }
        if self
            .builder
            .number_is_zero(coefficient)
            .map_err(|_| fail())?
            || others.is_empty()
        {
            return self.literal(coefficient, prototype);
        }
        let scalar_sum = others.len() == 1 && self.head(others[0], "+")?;
        let factor_count = others
            .len()
            .checked_add(usize::from(
                !self
                    .builder
                    .number_is_one(coefficient)
                    .map_err(|_| fail())?,
            ))
            .ok_or_else(fail)?;
        let limit = (self.settings.blowup as u64)
            .checked_mul(u64::try_from(factor_count).map_err(|_| fail())?)
            .and_then(|n| n.checked_add(1))
            .ok_or_else(fail)?;
        let mut choices = Vec::new();
        reserve_counted(&mut choices, others.len(), self.owner).map_err(|_| fail())?;
        let mut size = 1u64;
        let mut additive = false;
        for &id in &others {
            let choice = if (self.settings.som || scalar_sum) && self.head(id, "+")? {
                additive = true;
                self.args(id)?
            } else {
                let mut v = Vec::new();
                reserve_counted(&mut v, 1, self.owner).map_err(|_| fail())?;
                v.push(id);
                v
            };
            size = size.saturating_mul(u64::try_from(choice.len()).map_err(|_| fail())?);
            choices.push(choice);
        }
        if !additive || (!scalar_sum && size > limit) {
            let mut factors = Vec::new();
            let degree = self.one_degree()?;
            reserve_counted(&mut factors, others.len(), self.owner).map_err(|_| fail())?;
            for id in others {
                factors.push(Factor { atom: id, degree });
            }
            self.compact(&mut factors)?;
            let mut rows = Vec::new();
            reserve_counted(&mut rows, 1, self.owner).map_err(|_| fail())?;
            rows.push(Row {
                coefficient,
                factors,
                order: 0,
            });
            return Ok(Poly { rows });
        }
        let count = usize::try_from(size).map_err(|_| fail())?;
        let mut indices = Vec::new();
        reserve_counted(&mut indices, choices.len(), self.owner).map_err(|_| fail())?;
        indices.resize(choices.len(), 0usize);
        let mut rows = Vec::new();
        reserve_counted(&mut rows, count, self.owner).map_err(|_| fail())?;
        for _ in 0..count {
            self.steps.visit(self.owner)?;
            let mut row = Row {
                coefficient,
                factors: Vec::new(),
                order: 0,
            };
            for (choice, &index) in choices.iter().zip(&indices) {
                let selected = self.monomial(choice[index], prototype)?;
                row.coefficient = self
                    .builder
                    .number_product(row.coefficient, selected.coefficient)
                    .map_err(|_| fail())?;
                reserve_counted(&mut row.factors, selected.factors.len(), self.owner)
                    .map_err(|_| fail())?;
                pay(self.owner, selected.factors.len())?;
                row.factors.extend(selected.factors);
            }
            self.compact(&mut row.factors)?;
            rows.push(row);
            for (index, choice) in indices.iter_mut().zip(&choices).rev() {
                pay(self.owner, 1)?;
                *index += 1;
                if *index < choice.len() {
                    break;
                }
                *index = 0;
            }
        }
        self.canonical(rows)
    }
    fn coerce(&mut self, id: TermId, prototype: TermId) -> Result<TermId, TacticFailure> {
        if self.builder.terms().sort(id) == self.builder.terms().sort(prototype) {
            return Ok(id);
        }
        if self.builder.terms().sort(id) == &Sort::Int
            && self.builder.terms().sort(prototype) == &Sort::Real
        {
            if self.number(id) {
                return self
                    .builder
                    .number_convert_like(id, prototype)
                    .map_err(|_| fail());
            }
            return self
                .builder
                .ring_apply(Op::ToReal, &[id])
                .map_err(|_| fail());
        }
        Err(fail())
    }
    fn lift(&mut self, id: TermId, prototype: TermId) -> Result<Poly, TacticFailure> {
        if self.builder.terms().sort(id) != &Sort::Int
            || self.builder.terms().sort(prototype) != &Sort::Real
        {
            return Err(fail());
        }
        if !self.settings.push_to_real {
            let cast = self
                .builder
                .ring_apply(Op::ToReal, &[id])
                .map_err(|_| fail())?;
            return self.atom(cast, prototype);
        }
        let source = self.sum(id, id)?;
        let mut rows = Vec::new();
        reserve_counted(&mut rows, source.rows.len(), self.owner).map_err(|_| fail())?;
        for mut row in source.rows {
            row.coefficient = self
                .builder
                .number_convert_like(row.coefficient, prototype)
                .map_err(|_| fail())?;
            for factor in &mut row.factors {
                factor.atom = self
                    .builder
                    .ring_apply(Op::ToReal, &[factor.atom])
                    .map_err(|_| fail())?;
            }
            self.compact(&mut row.factors)?;
            rows.push(row);
        }
        self.canonical(rows)
    }
    fn arithmetic_app(&self, id: TermId) -> Result<bool, TacticFailure> {
        if let TermData::App(Symbol::Named(head), _) = self.builder.terms().get(id) {
            pay(self.owner, head.len())?;
            Ok(!self.builder.terms().is_declared_function(head)
                && matches!(
                    head.as_str(),
                    "+" | "-"
                        | "*"
                        | "/"
                        | "div"
                        | "mod"
                        | "rem"
                        | "abs"
                        | "min"
                        | "max"
                        | "to_real"
                        | "to_int"
                        | "^"
                        | "sin"
                        | "cos"
                        | "tan"
                        | "asin"
                        | "acos"
                        | "atan"
                        | "sinh"
                        | "cosh"
                        | "tanh"
                        | "exp"
                        | "log"
                ))
        } else {
            Ok(false)
        }
    }
    fn power(&mut self, mut id: TermId, args: &[TermId]) -> Result<TermId, TacticFailure> {
        if args.len() != 2
            || self.builder.terms().sort(id) != &Sort::Real
            || self.builder.terms().sort(args[0]) != self.builder.terms().sort(args[1])
            || !matches!(self.builder.terms().sort(args[0]), Sort::Int | Sort::Real)
        {
            return Err(fail());
        }
        let (mut base, mut exponent) = (args[0], args[1]);
        // arith_rewriter::mk_power_core combines nested positive integral
        // powers before considering max_degree or expand_power. Compact exact
        // coefficients avoid allocating a repeated-factor vector just to do
        // this scalar exponent arithmetic.
        loop {
            if !self.number(exponent) {
                break;
            }
            if self.builder.number_is_one(exponent).map_err(|_| fail())? {
                return self.coerce(base, id);
            }
            let positive = self
                .builder
                .number_positive_integral(exponent)
                .map_err(|_| fail())?;
            if positive
                && self.number(base)
                && self.builder.number_is_zero(base).map_err(|_| fail())?
            {
                return self.builder.number_like(0, id).map_err(|_| fail());
            }
            if !positive || !self.head(base, "^")? {
                break;
            }
            let inner = self.args(base)?;
            if inner.len() != 2 {
                return Err(fail());
            }
            if !self.number(inner[1])
                || !self
                    .builder
                    .number_positive_integral(inner[1])
                    .map_err(|_| fail())?
            {
                break;
            }
            self.steps.visit(self.owner)?;
            let degree = self
                .builder
                .number_convert_like(inner[1], exponent)
                .map_err(|_| fail())?;
            exponent = self
                .builder
                .number_product(exponent, degree)
                .map_err(|_| fail())?;
            base = self.coerce(inner[0], id)?;
            id = self
                .builder
                .ring_apply(Op::Power, &[base, exponent])
                .map_err(|_| fail())?;
        }
        if self.number(base) && self.builder.number_is_one(base).map_err(|_| fail())? {
            return self.builder.number_like(1, id).map_err(|_| fail());
        }
        if !self.number(exponent) {
            return Ok(id);
        }
        let Some(n) = self.builder.number_natural(exponent).map_err(|_| fail())? else {
            return Ok(id);
        };
        if n == 1 {
            return self.coerce(base, id);
        }
        if n == 0 {
            if self.number(base) && !self.builder.number_is_zero(base).map_err(|_| fail())? {
                return self.builder.number_like(1, id).map_err(|_| fail());
            }
            return Ok(id);
        }
        let expand = n <= self.settings.max_degree
            && (self.number(base)
                || self.settings.expand_power
                || (self.settings.som && self.arithmetic_app(base)?));
        if !expand {
            return Ok(id);
        }
        let count = usize::try_from(n).map_err(|_| fail())?;
        let mut repeated = Vec::new();
        reserve_counted(&mut repeated, count, self.owner).map_err(|_| fail())?;
        pay(self.owner, count)?;
        repeated.extend(std::iter::repeat_n(base, count));
        let poly = self.product(&repeated, base)?;
        let output = self.emit(poly, base)?;
        if self.builder.terms().sort(base) == &Sort::Int {
            let lifted = self.lift(output, id)?;
            self.emit(lifted, id)
        } else {
            Ok(output)
        }
    }
    fn division(&mut self, id: TermId, args: &[TermId]) -> Result<TermId, TacticFailure> {
        if args.len() != 2
            || self.builder.terms().sort(id) != &Sort::Real
            || args
                .iter()
                .any(|arg| self.builder.terms().sort(*arg) != &Sort::Real)
        {
            return Err(fail());
        }
        if !self.number(args[1]) || self.builder.number_is_zero(args[1]).map_err(|_| fail())? {
            return Ok(id);
        }
        let reciprocal = self
            .builder
            .number_reciprocal(args[1])
            .map_err(|_| fail())?;
        let poly = self.product(&[reciprocal, args[0]], id)?;
        self.emit(poly, id)
    }
    fn emit(&mut self, poly: Poly, prototype: TermId) -> Result<TermId, TacticFailure> {
        let mut sum = Vec::new();
        reserve_counted(&mut sum, poly.rows.len(), self.owner).map_err(|_| fail())?;
        for row in poly.rows {
            if self
                .builder
                .number_is_zero(row.coefficient)
                .map_err(|_| fail())?
            {
                continue;
            }
            let mut product = Vec::new();
            if row.factors.is_empty()
                || !self
                    .builder
                    .number_is_one(row.coefficient)
                    .map_err(|_| fail())?
            {
                reserve_counted(&mut product, 1, self.owner).map_err(|_| fail())?;
                product.push(row.coefficient);
            }
            for factor in row.factors {
                if self.settings.mul_to_power
                    && !self
                        .builder
                        .number_is_one(factor.degree)
                        .map_err(|_| fail())?
                {
                    let degree = self
                        .builder
                        .number_convert_like(factor.degree, factor.atom)
                        .map_err(|_| fail())?;
                    let power = self
                        .builder
                        .ring_apply(Op::Power, &[factor.atom, degree])
                        .map_err(|_| fail())?;
                    let power = if self.builder.terms().sort(prototype) == &Sort::Int {
                        self.builder
                            .ring_apply(Op::ToInt, &[power])
                            .map_err(|_| fail())?
                    } else {
                        power
                    };
                    reserve_counted(&mut product, 1, self.owner).map_err(|_| fail())?;
                    product.push(power);
                } else {
                    let n = self
                        .builder
                        .number_usize(factor.degree)
                        .map_err(|_| fail())?
                        .ok_or_else(fail)?;
                    reserve_counted(&mut product, n, self.owner).map_err(|_| fail())?;
                    pay(self.owner, n)?;
                    let atom = self.coerce(factor.atom, prototype)?;
                    product.extend(std::iter::repeat_n(atom, n));
                }
            }
            let value = match product.as_slice() {
                [] => self.one(prototype)?,
                [one] => *one,
                _ => self
                    .builder
                    .ring_apply(Op::Multiply, &product)
                    .map_err(|_| fail())?,
            };
            sum.push(value);
        }
        match sum.as_slice() {
            [] => self.builder.number_like(0, prototype).map_err(|_| fail()),
            [one] => Ok(*one),
            _ => self.builder.ring_apply(Op::Add, &sum).map_err(|_| fail()),
        }
    }
}

#[cfg(test)]
pub(super) fn rewrite(
    store: &mut TermStore,
    roots: &[TermId],
    parameters: PolynomialParameters,
    steps: &mut Steps,
    owner: &dyn TermConstructionAdmission,
) -> Result<Vec<TermId>, TacticFailure> {
    normalize(store, roots, parameters, RewriteDomain::Ring, steps, owner)
}

pub(super) fn rewrite_with_sequences(
    store: &mut TermStore,
    roots: &[TermId],
    maximum: u32,
    parameters: PolynomialParameters,
    steps: &mut Steps,
    owner: &dyn TermConstructionAdmission,
) -> Result<Vec<TermId>, TacticFailure> {
    normalize(
        store,
        roots,
        parameters,
        RewriteDomain::RingAndSequences(maximum),
        steps,
        owner,
    )
}

#[derive(Clone, Copy)]
enum RewriteDomain {
    #[cfg(test)]
    Ring,
    RingAndSequences(u32),
}

fn normalize(
    store: &mut TermStore,
    roots: &[TermId],
    parameters: PolynomialParameters,
    domain: RewriteDomain,
    steps: &mut Steps,
    owner: &dyn TermConstructionAdmission,
) -> Result<Vec<TermId>, TacticFailure> {
    // Upstream BR_REWRITE1/2 revisit generated arithmetic. A single original
    // DAG walk is insufficient for e.g. scalar distribution into a nested
    // non-flat sum. Retain the SAME Steps, counter, deadline and arena across
    // all passes; resource refusal, not an arbitrary pass cap, bounds work.
    let mut current = Vec::new();
    reserve_counted(&mut current, roots.len(), owner).map_err(|_| fail())?;
    pay(owner, roots.len())?;
    current.extend_from_slice(roots);
    loop {
        #[cfg(test)]
        let next = match domain {
            RewriteDomain::Ring => rewrite_once(store, &current, parameters, steps, owner)?,
            RewriteDomain::RingAndSequences(maximum) => {
                let words = super::tactic_sequence_rewrite::rewrite(
                    store, &current, maximum, steps, owner,
                )?;
                rewrite_once(store, &words, parameters, steps, owner)?
            }
        };
        #[cfg(not(test))]
        let next = {
            let RewriteDomain::RingAndSequences(maximum) = domain;
            let words =
                super::tactic_sequence_rewrite::rewrite(store, &current, maximum, steps, owner)?;
            rewrite_once(store, &words, parameters, steps, owner)?
        };
        pay(owner, current.len())?;
        if next == current {
            owner.check().map_err(|_| fail())?;
            return Ok(next);
        }
        current = next;
    }
}

fn rewrite_once(
    store: &mut TermStore,
    roots: &[TermId],
    parameters: PolynomialParameters,
    steps: &mut Steps,
    owner: &dyn TermConstructionAdmission,
) -> Result<Vec<TermId>, TacticFailure> {
    let seen = super::tactic_solve_eqs::reachable(store, roots, owner)?;
    let mut mapped = Vec::new();
    reserve_counted(&mut mapped, seen.len(), owner).map_err(|_| fail())?;
    pay(owner, seen.len())?;
    mapped.resize(seen.len(), None);
    let borrowed = Borrowed(owner);
    let builder = CountedTermBuilder::with_admission(store, &borrowed).map_err(|_| fail())?;
    let mut ring = Ring {
        builder,
        owner,
        settings: parameters.settings(),
        steps,
    };
    let mut args = Vec::new();
    for (index, &present) in seen.iter().enumerate() {
        if !present {
            continue;
        }
        ring.steps.visit(owner)?;
        let source = TermId(index as u32);
        args.clear();
        super::tactic_solve_eqs::children(ring.builder.terms().get(source), &mut args, owner)?;
        for id in &mut args {
            *id = mapped[id.index()].ok_or_else(fail)?;
        }
        let rebuilt = if ring.number(source) {
            // Validate every numeric leaf before parent identity/zero rules;
            // an invalid raw Rational denominator must not disappear under
            // e.g. 1^bad or a zero product. This is borrowed inspection only.
            ring.builder.number_is_zero(source).map_err(|_| fail())?;
            source
        } else {
            ring.builder
                .rebuild_existing(source, &args)
                .map_err(|_| fail())?
        };
        let scalar = matches!(ring.builder.terms().sort(rebuilt), Sort::Int | Sort::Real);
        let basic = scalar
            && (ring.head(rebuilt, "+")? || ring.head(rebuilt, "-")? || ring.head(rebuilt, "*")?);
        if basic
            && (args.is_empty()
                || args
                    .iter()
                    .any(|id| ring.builder.terms().sort(*id) != ring.builder.terms().sort(rebuilt)))
        {
            return Err(fail());
        }
        let value = if scalar && ring.head(rebuilt, "+")? {
            let poly = ring.add_args(&args, rebuilt, SumMode::Add)?;
            ring.emit(poly, rebuilt)?
        } else if scalar && ring.head(rebuilt, "-")? {
            let poly = ring.add_args(&args, rebuilt, SumMode::Subtract)?;
            ring.emit(poly, rebuilt)?
        } else if scalar && ring.head(rebuilt, "*")? {
            let poly = ring.product(&args, rebuilt)?;
            ring.emit(poly, rebuilt)?
        } else if scalar && ring.head(rebuilt, "^")? {
            ring.power(rebuilt, &args)?
        } else if scalar && ring.head(rebuilt, "/")? {
            ring.division(rebuilt, &args)?
        } else if scalar && ring.head(rebuilt, "to_real")? {
            if args.len() != 1 {
                return Err(fail());
            }
            let poly = ring.lift(args[0], rebuilt)?;
            ring.emit(poly, rebuilt)?
        } else {
            rebuilt
        };
        mapped[index] = Some(value);
    }
    let mut result = Vec::new();
    reserve_counted(&mut result, roots.len(), owner).map_err(|_| fail())?;
    for id in roots {
        pay(owner, 1)?;
        result.push(mapped[id.index()].ok_or_else(fail)?);
    }
    ring.builder.finish().map_err(|_| fail())?;
    Ok(result)
}

#[cfg(test)]
mod tests {
    use super::*;
    use ay_core::original_query::{CountedAdmission, FiniteAdmissionGrant};
    use std::sync::Arc;
    fn owner(work: u64, storage: usize) -> CountedAdmission {
        CountedAdmission::new(
            FiniteAdmissionGrant::new(work, storage),
            None,
            Arc::new(|| false),
        )
        .unwrap()
    }
    fn app(store: &mut TermStore, head: &str, args: &[TermId]) -> TermId {
        store.mk_app_structural(Symbol::named(head), args, Sort::Int)
    }
    fn run(
        store: &mut TermStore,
        root: TermId,
        blowup: u32,
        admission: &dyn TermConstructionAdmission,
    ) -> Result<TermId, TacticFailure> {
        let mut options = PolynomialParameters::default();
        options.set(
            "som",
            super::super::tactic_parameters::TacticParameterValue::Bool(true),
        )?;
        options.set(
            "som_blowup",
            super::super::tactic_parameters::TacticParameterValue::UInt(blowup),
        )?;
        rewrite(store, &[root], options, &mut Steps::new(None), admission).map(|v| v[0])
    }
    #[test]
    fn sum_of_monomials_combines_signed_coefficients_and_cartesian_duplicates() {
        let mut store = TermStore::new();
        let x = store.mk_var("x", Sort::Int);
        let one = store.mk_int(1.into());
        let two = store.mk_int(2.into());
        let three = store.mk_int(3.into());
        let left = app(&mut store, "+", &[x, one]);
        let right = app(&mut store, "+", &[x, two]);
        let source = app(&mut store, "*", &[left, right]);
        let output = run(&mut store, source, 10, &owner(1 << 20, 16 << 20)).unwrap();
        let square = app(&mut store, "*", &[x, x]);
        let linear = app(&mut store, "*", &[three, x]);
        let expected = app(&mut store, "+", &[two, linear, square]);
        assert_eq!(output, expected);
        let neg = app(&mut store, "-", &[output]);
        let cancel = app(&mut store, "+", &[output, neg]);
        let output = run(&mut store, cancel, 10, &owner(1 << 20, 16 << 20)).unwrap();
        assert!(matches!(store.get(output), TermData::Const(Constant::Int(n)) if n == &0.into()));
    }
    #[test]
    fn blowup_prices_cartesian_terms_before_combining_and_keeps_opaque_heads() {
        let mut store = TermStore::new();
        let x = store.mk_var("x", Sort::Int);
        let y = store.mk_var("y", Sort::Int);
        let sum = app(&mut store, "+", &[x, y]);
        let source = app(&mut store, "*", &[sum, sum]);
        let output = run(&mut store, source, 1, &owner(1 << 20, 16 << 20)).unwrap();
        assert_eq!(
            output, source,
            "four Cartesian terms exceed 2*1+1 despite only three collected monomials"
        );
        let output = run(&mut store, source, 2, &owner(1 << 20, 16 << 20)).unwrap();
        assert_ne!(output, source);
        let opaque = app(&mut store, "opaque", &[sum]);
        assert_eq!(
            run(&mut store, opaque, 10, &owner(1 << 20, 16 << 20)).unwrap(),
            opaque
        );
    }
    #[test]
    fn polynomial_growth_and_cumulative_original_refusal_never_renew() {
        let mut store = TermStore::new();
        let x = store.mk_var("x", Sort::Int);
        let one = store.mk_int(1.into());
        let sum = app(&mut store, "+", &[x, one]);
        let source = app(&mut store, "*", &[sum, sum, sum]);
        let original = owner(1 << 20, 256);
        assert!(run(&mut store, source, 10, &original).is_err());
        assert!(run(&mut store, source, 0, &original).is_err());
        assert!(original.check().is_err());
    }
    #[test]
    fn declared_ring_heads_remain_opaque_and_generated_heads_refuse_shadowing() {
        let mut store = TermStore::new();
        let x = store.mk_var("x", Sort::Int);
        let one = store.mk_int(1.into());
        let source = app(&mut store, "+", &[x, one]);
        store.register_declared_function("+");
        assert_eq!(
            run(&mut store, source, 10, &owner(1 << 20, 16 << 20)).unwrap(),
            source
        );
        let subtraction = app(&mut store, "-", &[x, one]);
        assert!(
            run(&mut store, subtraction, 10, &owner(1 << 20, 16 << 20)).is_err(),
            "normalization must not publish a declared + as builtin addition"
        );
    }

    #[test]
    fn requested_uint_max_power_expansion_refuses_before_the_declared_repeat_allocation() {
        use super::super::tactic_parameters::TacticParameterValue as V;
        use num_rational::BigRational;
        let mut store = TermStore::new();
        let x = store.mk_var("growth_x", Sort::Real);
        let degree = store.mk_rational(BigRational::from_integer(u32::MAX.into()));
        let source = store.mk_app_structural(Symbol::named("^"), [x, degree], Sort::Real);
        let mut parameters = PolynomialParameters::default();
        parameters.set("expand_power", V::Bool(true)).unwrap();
        parameters.set("max_degree", V::UInt(u32::MAX)).unwrap();
        let original = owner(1 << 20, 1 << 20);
        assert!(rewrite(
            &mut store,
            &[source],
            parameters,
            &mut Steps::new(None),
            &original
        )
        .is_err());
        assert!(original.check().is_err());
        assert!(run(&mut store, x, 0, &original).is_err());
    }

    #[test]
    fn nested_positive_powers_combine_before_degree_limits_and_zero_needs_no_expansion() {
        use num_rational::BigRational;
        let mut store = TermStore::new();
        let x = store.mk_var("nested_x", Sort::Real);
        let literal =
            |store: &mut TermStore, n: u32| store.mk_rational(BigRational::from_integer(n.into()));
        let two = literal(&mut store, 2);
        let three = literal(&mut store, 3);
        let six = literal(&mut store, 6);
        let inner = store.mk_app_structural(Symbol::named("^"), [x, two], Sort::Real);
        let outer = store.mk_app_structural(Symbol::named("^"), [inner, three], Sort::Real);
        let output = run(&mut store, outer, 10, &owner(1 << 20, 16 << 20)).unwrap();
        let expected = store.mk_app_structural(Symbol::named("^"), [x, six], Sort::Real);
        assert_eq!(
            output, expected,
            "nested powers do not force expansion of a bare variable"
        );
        let zero = literal(&mut store, 0);
        let huge = literal(&mut store, u32::MAX);
        let zero_power = store.mk_app_structural(Symbol::named("^"), [zero, huge], Sort::Real);
        assert_eq!(
            run(&mut store, zero_power, 0, &owner(1 << 20, 16 << 20)).unwrap(),
            zero
        );
    }

    #[test]
    fn malformed_numeric_leaf_cannot_disappear_under_a_power_identity() {
        use num_rational::BigRational;
        let mut store = TermStore::new();
        let one = store.mk_rational(BigRational::from_integer(1.into()));
        let bad = store.mk_rational(BigRational::new_raw(1.into(), 0.into()));
        let source = store.mk_app_structural(Symbol::named("^"), [one, bad], Sort::Real);
        assert!(run(&mut store, source, 10, &owner(1 << 20, 16 << 20)).is_err());
    }

    #[test]
    fn generated_scalar_distribution_reaches_nonflat_normal_form_without_new_steps() {
        use super::super::tactic_parameters::TacticParameterValue as V;
        let mut store = TermStore::new();
        let x = store.mk_var("nonflat_x", Sort::Int);
        let one = store.mk_int(1.into());
        let two = store.mk_int(2.into());
        let three = store.mk_int(3.into());
        let six = store.mk_int(6.into());
        let inner = app(&mut store, "+", &[x, one]);
        let outer = app(&mut store, "+", &[inner, two]);
        let source = app(&mut store, "*", &[three, outer]);
        let mut options = PolynomialParameters::default();
        options.set("flat", V::Bool(false)).unwrap();
        let output = rewrite(
            &mut store,
            &[source],
            options,
            &mut Steps::new(None),
            &owner(1 << 20, 16 << 20),
        )
        .unwrap()[0];
        let scaled = app(&mut store, "*", &[three, x]);
        let nested = app(&mut store, "+", &[three, scaled]);
        let expected = app(&mut store, "+", &[six, nested]);
        assert_eq!(
            output, expected,
            "same nested AST as pinned C arity inspection, not its flattened display"
        );
        let mut bounded = Steps::new(Some(1));
        assert!(rewrite(
            &mut store,
            &[source],
            options,
            &mut bounded,
            &owner(1 << 20, 16 << 20)
        )
        .is_err());
    }
    #[test]
    fn ring_folded_sequence_exponent_is_revisited_under_the_same_steps() {
        let mut store = TermStore::new();
        let one = store.mk_int(1.into());
        let two = store.mk_int(2.into());
        let exponent = app(&mut store, "+", &[one, two]);
        let base = store.mk_string("ab".into());
        let source =
            store.mk_app_structural(Symbol::named("seq.power"), [base, exponent], Sort::String);
        let output = rewrite_with_sequences(
            &mut store,
            &[source],
            4,
            PolynomialParameters::default(),
            &mut Steps::new(None),
            &owner(1 << 20, 16 << 20),
        )
        .unwrap()[0];
        assert!(
            matches!(store.get(output), TermData::Const(Constant::String(word)) if word == "ababab")
        );
        assert!(
            rewrite_with_sequences(
                &mut store,
                &[source],
                4,
                PolynomialParameters::default(),
                &mut Steps::new(Some(10)),
                &owner(1 << 20, 16 << 20)
            )
            .is_err(),
            "revisiting newly folded exponents cannot renew Steps"
        );
    }

    #[test]
    fn rational_coefficients_and_positive_powers_preserve_zero_power_underspecification() {
        use num_rational::BigRational;
        let mut store = TermStore::new();
        let x = store.mk_var("x", Sort::Real);
        let half = store.mk_rational(BigRational::new(1.into(), 2.into()));
        let third = store.mk_rational(BigRational::new(1.into(), 3.into()));
        let sixth = store.mk_rational(BigRational::new(1.into(), 6.into()));
        let sum = store.mk_app_structural(Symbol::named("+"), [x, third], Sort::Real);
        let source = store.mk_app_structural(Symbol::named("*"), [half, sum], Sort::Real);
        let output = run(&mut store, source, 0, &owner(1 << 20, 16 << 20)).unwrap();
        let scaled = store.mk_app_structural(Symbol::named("*"), [half, x], Sort::Real);
        let expected = store.mk_app_structural(Symbol::named("+"), [sixth, scaled], Sort::Real);
        assert_eq!(
            output, expected,
            "scalar distribution is not gated by som_blowup"
        );
        let zero = store.mk_rational(BigRational::from_integer(0.into()));
        let power = store.mk_app_structural(Symbol::named("^"), [x, zero], Sort::Real);
        assert_eq!(
            run(&mut store, power, 10, &owner(1 << 20, 16 << 20)).unwrap(),
            power
        );
        let three = store.mk_rational(BigRational::from_integer(3.into()));
        let power = store.mk_app_structural(Symbol::named("^"), [sum, three], Sort::Real);
        let output = run(&mut store, power, 10, &owner(1 << 20, 16 << 20)).unwrap();
        assert!(!matches!(store.get(output), TermData::App(Symbol::Named(h), _) if h == "^"));
    }
}
