// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The value side of a printed `evaluate` step.
//!
//! Pinned Carcara 1.1.0 (git 9a352ee) checks `(cl (= t v)) :rule evaluate` by
//! evaluating `t` and comparing the result with `v` SYNTACTICALLY: `v` must be
//! a literal it reads as that constant. MEASURED there: `-4`, `-4.0`, `2.5`
//! and `-0.125` are literals; the printer's canonical `(- 4)`, `(- 4.0)`,
//! `(/ 5.0 2.0)` and `(- (/ 1.0 8.0))` are applications, so
//! `(= (+ (- 2) (- 2)) (- 4)) :rule evaluate` fails ("expected terms to be
//! equal: '-4' and '(- 4)'"), and a value with no finite decimal (`1/3`) has
//! no literal at all ("'-1/3' and '(- (/ 1.0 3.0))'").
//!
//! AY's ground evaluator compares VALUES over the term store, where `-4` and
//! `(- 4)` are one constant, so it accepts every such step. The printer is
//! where the two must agree: a value whose printed spelling is not its
//! literal is evaluated to the literal and joined to the printed spelling by
//! Carcara's own `refl` (measured `valid`: `-4`/`(- 4)`, `-4.0`/`(- 4.0)`,
//! `2.5`/`(/ 5.0 2.0)`, `-0.125`/`(- (/ 1.0 8.0))`) and `trans`; a value with
//! no literal is an honest `hole`, never an `evaluate` the checker refuses.

use super::{split_application, AlethePrinter};
use crate::checker::carcara_numeric_literal;
use ay_core::term::{Constant, Symbol, TermData};
use ay_core::{ProofId, TermId};
use num_rational::BigRational;

/// How Carcara's `evaluate` can read the value side of one printed step.
enum ValueSpelling {
    /// The printed value is already the literal (or not a numeric constant
    /// this module judges): print the step unchanged.
    Literal,
    /// The literal Carcara reads for the value, and the printed spelling it
    /// differs from.
    Respelled {
        literal: String,
        printed: String,
        evaluated: String,
    },
    /// No literal spells the value.
    Unspellable,
}

impl AlethePrinter<'_> {
    /// `(step id clause_str :rule evaluate)` when Carcara reads the printed
    /// value as a literal; otherwise the literal bridge, or `hole` when the
    /// value has no literal. `clause` is the step AY's ground evaluator
    /// accepted; `clause_str` is its printed clause.
    pub(super) fn format_evaluate_step(
        &self,
        id: ProofId,
        clause: &[TermId],
        clause_str: &str,
    ) -> String {
        match self.evaluate_value_spelling(clause, clause_str) {
            ValueSpelling::Literal => format!("(step {id} {clause_str} :rule evaluate)"),
            ValueSpelling::Respelled {
                literal,
                printed,
                evaluated,
            } => format!(
                "(step {id}.lit (cl (= {evaluated} {literal})) :rule evaluate)\n\
                 (step {id}.sp (cl (= {literal} {printed})) :rule refl)\n\
                 (step {id} {clause_str} :rule trans :premises ({id}.lit {id}.sp))"
            ),
            ValueSpelling::Unspellable => {
                format!(
                    "(step {id} {clause_str} :rule {})",
                    ay_core::UNPROVED_STEP_RULE
                )
            }
        }
    }

    fn evaluate_value_spelling(&self, clause: &[TermId], clause_str: &str) -> ValueSpelling {
        let [literal] = clause else {
            return ValueSpelling::Literal;
        };
        let TermData::App(Symbol::Named(equals), operands) = self.terms.get(*literal) else {
            return ValueSpelling::Literal;
        };
        let [_, value] = operands.as_slice() else {
            return ValueSpelling::Literal;
        };
        if equals != "=" {
            return ValueSpelling::Literal;
        }
        let (rational, integral) = match self.terms.get(*value) {
            TermData::Const(Constant::Int(integer)) => {
                (BigRational::from_integer(integer.clone()), true)
            }
            TermData::Const(Constant::Rational(rational)) => (rational.0.clone(), false),
            _ => return ValueSpelling::Literal,
        };
        let Some(clause_parts) = split_application(clause_str, "cl") else {
            return ValueSpelling::Unspellable;
        };
        let [printed_equality] = clause_parts.as_slice() else {
            return ValueSpelling::Unspellable;
        };
        let Some(sides) = split_application(printed_equality, "=") else {
            return ValueSpelling::Unspellable;
        };
        let [evaluated, printed] = sides.as_slice() else {
            return ValueSpelling::Unspellable;
        };
        let Some(literal) = carcara_numeric_literal(&rational, integral) else {
            return ValueSpelling::Unspellable;
        };
        if *printed == literal {
            return ValueSpelling::Literal;
        }
        // `refl` relates the literal to the printer's OWN rendering of this
        // constant only; an override's spelling is not judged here.
        let TermData::Const(constant) = self.terms.get(*value) else {
            return ValueSpelling::Unspellable;
        };
        if *printed != Self::format_constant(constant) {
            return ValueSpelling::Unspellable;
        }
        ValueSpelling::Respelled {
            literal,
            printed: printed.clone(),
            evaluated: evaluated.clone(),
        }
    }
}

#[cfg(test)]
#[path = "evaluate_literal_tests.rs"]
mod tests;
