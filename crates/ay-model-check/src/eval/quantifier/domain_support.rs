// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Finite support for one range-guarded Int or signed/unsigned BV quantifier.
//!
//! `support(term, value)` over-approximates where `term` MAY equal `value`.
//! Therefore values outside false-support satisfy a universal body, and values
//! outside true-support cannot witness an existential body. Unknown atoms have
//! WHOLE support in both polarities; complementing an approximation is unsound.

use super::{QuantifierKind, QuantifierRejection};
use crate::eval::{EvalError, Evaluator};
use crate::ModelValue;
use ay_core::term::{Constant, Symbol, TermData};
use ay_core::{Sort, TermId};
use num_bigint::BigInt;
use num_traits::{One, ToPrimitive, Zero};
use std::cell::Cell;

mod endpoint;
mod intervals;
mod signed;
use intervals::{Bound, Intervals};

const MAX_SUPPORT_DEPTH: usize = 64;
const MAX_GUARDED_BITVEC_WIDTH: u32 = 128;
const MAX_RANGE_BOUND_BITS: u64 = 4096;

fn charge(evaluator: &Evaluator<'_>, amount: usize) -> Result<(), QuantifierRejection> {
    evaluator
        .charge_quantifier_work(amount)
        .map_err(QuantifierRejection::UnevaluableBody)
}

struct Span {
    start: BigInt,
    count: usize,
}

pub(super) struct GuardedDomain {
    spans: Vec<Span>,
    pub(super) count: usize,
}

impl GuardedDomain {
    /// Endpoints are evaluated before installing the new lexical binding, but
    /// under the enclosing quantifier's ACTIVE metered scope. Endpoints use
    /// the narrow, typed, binder-independent grammar in `endpoint`.
    pub(super) fn derive(
        evaluator: &Evaluator<'_>,
        kind: QuantifierKind,
        bindings: &[(String, Sort)],
        body: TermId,
        depth: usize,
        assignments_left: usize,
    ) -> Result<Option<Self>, QuantifierRejection> {
        let [binding] = bindings else {
            return Ok(None);
        };
        Self::derive_pending(
            evaluator,
            kind,
            binding,
            bindings,
            body,
            depth,
            assignments_left,
        )
    }

    /// Already installed prefix bindings may determine a dependent range. The
    /// current and future group binders are unavailable, even if the model or
    /// an enclosing quantifier has a value with the same name.
    pub(super) fn derive_pending(
        evaluator: &Evaluator<'_>,
        kind: QuantifierKind,
        binding: &(String, Sort),
        unavailable: &[(String, Sort)],
        body: TermId,
        depth: usize,
        assignments_left: usize,
    ) -> Result<Option<Self>, QuantifierRejection> {
        let (name, sort) = binding;
        charge(evaluator, 1)?;
        let carrier = match sort {
            Sort::Int => Intervals::whole(),
            Sort::BitVec(bitvec) if (1..=MAX_GUARDED_BITVEC_WIDTH).contains(&bitvec.width) => {
                Intervals::between(
                    Bound::Finite(BigInt::zero()),
                    Bound::Finite(BigInt::one() << bitvec.width),
                )
            }
            _ => return Ok(None),
        };
        let analysis = SupportAnalysis {
            evaluator,
            name,
            sort,
            unavailable,
            eval_depth: depth,
            saw_bound_comparison: Cell::new(false),
        };
        let support = analysis.support(body, kind.decisive_value(), 0)?;
        // Preserve whole-carrier refusal for unused wide binders. This path
        // supplies a range theorem, not an unbounded quantifier simplifier.
        if !analysis.saw_bound_comparison.get() {
            return Ok(None);
        }
        let support = support.intersection(carrier, evaluator)?;
        let mut spans = Vec::new();
        charge(evaluator, support.0.len())?;
        spans
            .try_reserve(support.0.len())
            .map_err(|_| QuantifierRejection::EvaluationBudget)?;
        let mut count = 0usize;
        for interval in support.0 {
            let (Bound::Finite(start), Bound::Finite(end)) = (interval.lower, interval.upper)
            else {
                return Ok(None);
            };
            charge(
                evaluator,
                (start.bits().max(end.bits()).div_ceil(64).max(1)) as usize,
            )?;
            let length = (end - &start)
                .to_usize()
                .ok_or(QuantifierRejection::AssignmentBudget)?;
            count = count
                .checked_add(length)
                .filter(|count| *count <= assignments_left)
                .ok_or(QuantifierRejection::AssignmentBudget)?;
            spans.push(Span {
                start,
                count: length,
            });
        }
        Ok(Some(Self { spans, count }))
    }

    pub(super) fn value_at(
        &self,
        evaluator: &Evaluator<'_>,
        sort: &Sort,
        mut ordinal: usize,
    ) -> Result<ModelValue, QuantifierRejection> {
        for span in &self.spans {
            charge(evaluator, 1)?;
            if ordinal >= span.count {
                ordinal -= span.count;
                continue;
            }
            charge(evaluator, span.start.bits().div_ceil(64).max(1) as usize)?;
            let value = &span.start + BigInt::from(ordinal);
            return match sort {
                Sort::Int => Ok(ModelValue::Int(value)),
                Sort::BitVec(bitvec) => Ok(ModelValue::BitVec {
                    width: bitvec.width,
                    value,
                }),
                _ => Err(QuantifierRejection::UnsupportedDomain),
            };
        }
        Err(QuantifierRejection::BindingSortMismatch)
    }
}

struct SupportAnalysis<'a, 'model> {
    evaluator: &'a Evaluator<'model>,
    name: &'a str,
    sort: &'a Sort,
    unavailable: &'a [(String, Sort)],
    eval_depth: usize,
    saw_bound_comparison: Cell<bool>,
}

impl SupportAnalysis<'_, '_> {
    fn support(
        &self,
        term: TermId,
        desired: bool,
        depth: usize,
    ) -> Result<Intervals, QuantifierRejection> {
        charge(self.evaluator, 1)?;
        if depth > MAX_SUPPORT_DEPTH {
            return Err(QuantifierRejection::NestingLimit);
        }
        if self.evaluator.terms.sort(term) != &Sort::Bool {
            return Err(QuantifierRejection::NonBooleanBody);
        }
        match self.evaluator.terms.get(term) {
            TermData::Const(Constant::Bool(value)) => Ok(if *value == desired {
                Intervals::whole()
            } else {
                Intervals::empty()
            }),
            TermData::Not(inner) => self.support(*inner, !desired, depth + 1),
            TermData::App(symbol, args) => {
                // `eval` gives checked projections priority over ALL named
                // operators. A structural range theorem cannot override that
                // interpretation, even for an apparently built-in connective.
                if self
                    .evaluator
                    .model
                    .projection_argument(term)
                    .map_err(|error| {
                        QuantifierRejection::UnevaluableBody(EvalError::Refused(error.to_string()))
                    })?
                    .is_some()
                {
                    return Ok(Intervals::whole());
                }
                let Symbol::Named(operator) = symbol else {
                    return Ok(Intervals::whole());
                };
                charge(self.evaluator, operator.len().div_ceil(64).max(1))?;
                // A declared function has its committed interpretation, even
                // when its spelling resembles a connective or comparison.
                if self.evaluator.terms.is_declared_function(operator) {
                    return Ok(Intervals::whole());
                }
                match (operator.as_str(), args.as_slice()) {
                    ("not", [inner]) => self.support(*inner, !desired, depth + 1),
                    ("and" | "or", _) => self.boolean_support(operator, args, desired, depth),
                    ("=>", [left, right]) => {
                        let left = self.support(*left, !desired, depth + 1)?;
                        let right = self.support(*right, desired, depth + 1)?;
                        if desired {
                            left.union(right, self.evaluator)
                        } else {
                            left.intersection(right, self.evaluator)
                        }
                    }
                    (_, [left, right]) => self.comparison(operator, *left, *right, desired),
                    _ => Ok(Intervals::whole()),
                }
            }
            _ => Ok(Intervals::whole()),
        }
    }

    fn boolean_support(
        &self,
        operator: &str,
        args: &[TermId],
        desired: bool,
        depth: usize,
    ) -> Result<Intervals, QuantifierRejection> {
        let union = (operator == "and") != desired;
        let mut support = if union {
            Intervals::empty()
        } else {
            Intervals::whole()
        };
        for &arg in args {
            let child = self.support(arg, desired, depth + 1)?;
            support = if union {
                support.union(child, self.evaluator)?
            } else {
                support.intersection(child, self.evaluator)?
            };
        }
        Ok(support)
    }

    fn is_bound(&self, term: TermId) -> bool {
        matches!(self.evaluator.terms.get(term), TermData::Var(name, _) if name == self.name)
    }

    fn comparison(
        &self,
        operator: &str,
        left: TermId,
        right: TermId,
        desired: bool,
    ) -> Result<Intervals, QuantifierRejection> {
        let accepted = match self.sort {
            Sort::Int => matches!(operator, "<" | "<=" | ">" | ">=" | "=" | "distinct"),
            Sort::BitVec(_) => matches!(
                operator,
                "bvult"
                    | "bvule"
                    | "bvugt"
                    | "bvuge"
                    | "bvslt"
                    | "bvsle"
                    | "bvsgt"
                    | "bvsge"
                    | "="
                    | "distinct"
            ),
            _ => false,
        };
        if !accepted || self.is_bound(left) == self.is_bound(right) {
            return Ok(Intervals::whole());
        }
        if self.evaluator.terms.sort(left) != self.sort
            || self.evaluator.terms.sort(right) != self.sort
        {
            return Err(QuantifierRejection::BindingSortMismatch);
        }
        let reversed = self.is_bound(right);
        let Some(endpoint) = self.endpoint(if reversed { left } else { right })? else {
            return Ok(Intervals::whole());
        };
        self.saw_bound_comparison.set(true);
        let (operator, desired) = match operator {
            "distinct" => ("=", !desired),
            "bvult" => ("<", desired),
            "bvule" => ("<=", desired),
            "bvugt" => (">", desired),
            "bvuge" => (">=", desired),
            other => (other, desired),
        };
        let operator = match (operator, reversed) {
            ("<", true) => ">",
            ("<=", true) => ">=",
            (">", true) => "<",
            (">=", true) => "<=",
            ("bvslt", true) => "bvsgt",
            ("bvsle", true) => "bvsge",
            ("bvsgt", true) => "bvslt",
            ("bvsge", true) => "bvsle",
            (other, _) => other,
        };
        if matches!(operator, "bvslt" | "bvsle" | "bvsgt" | "bvsge") {
            return self.signed_comparison(operator, endpoint, desired);
        }
        let next = &endpoint + BigInt::one();
        let (lower, upper) = match (operator, desired) {
            ("<", true) | (">=", false) => (Bound::NegativeInfinity, Bound::Finite(endpoint)),
            ("<", false) | (">=", true) => (Bound::Finite(endpoint), Bound::PositiveInfinity),
            ("<=", true) | (">", false) => (Bound::NegativeInfinity, Bound::Finite(next)),
            ("<=", false) | (">", true) => (Bound::Finite(next), Bound::PositiveInfinity),
            ("=", true) => (Bound::Finite(endpoint), Bound::Finite(next)),
            ("=", false) => {
                return Intervals::between(Bound::NegativeInfinity, Bound::Finite(endpoint)).union(
                    Intervals::between(Bound::Finite(next), Bound::PositiveInfinity),
                    self.evaluator,
                );
            }
            _ => return Ok(Intervals::whole()),
        };
        Ok(Intervals::between(lower, upper))
    }
}

#[cfg(test)]
mod tests;

#[cfg(test)]
#[path = "domain_support/tests/signed_integration.rs"]
mod signed_integration;
