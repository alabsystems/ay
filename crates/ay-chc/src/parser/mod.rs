// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![deny(clippy::unwrap_used)]

//! CHC parser for SMT-LIB CHC format
//!
//! This module parses the CHC-COMP and SMT-LIB CHC format, which extends SMT-LIB 2.6
//! with commands for defining Horn clauses:
//!
//! ```text
//! (declare-rel Inv (Int))           ; Declare predicate Inv : Int -> Bool
//! (declare-var x Int)               ; Declare variable x
//! (rule (=> (= x 0) (Inv x)))       ; x = 0 => Inv(x)
//! (rule (=> (and (Inv x) (< x 10)) (Inv (+ x 1))))  ; Inv(x) /\ x < 10 => Inv(x+1)
//! (query Inv)                       ; Check if Inv is satisfiable
//! ```
//!
//! ## Supported Commands
//!
//! - `(set-logic HORN)` - Set logic (ignored but checked)
//! - `(declare-rel <name> (<sorts>))` - Declare a predicate
//! - `(declare-var <name> <sort>)` - Declare a variable
//! - `(declare-fun <name> (<sorts>) <return-sort>)` - Declare a function (predicates return Bool)
//! - `(declare-datatype <name> ((<ctor> (<sel> <sort>)*)*))` - Declare a datatype (#1279)
//! - `(rule <expr>)` or `(rule (=> <body> <head>))` - Add a Horn clause
//! - `(ay-declare-action <name>)` - Fixture-only declaration for action-decomposed CHC
//! - `(ay-action-rule <name> <expr>)` - Fixture-only Horn clause tagged with an action
//! - `(query <pred>)` - Add a query (safety property)
//! - `(check-sat)` - Solve the CHC problem
//! - `(exit)` - Exit (ignored)

mod application;
mod bitvector;
mod clauses;
mod commands;
mod expr;
mod lexer;
mod sorts;
#[cfg(test)]
mod tests;

use crate::{ActionId, ChcError, ChcProblem, ChcResult, ChcSort, PredicateId};
use ay_core::kani_compat::DetHashMap as FxHashMap;
use ay_core::kani_compat::DetHashSet as FxHashSet;

/// CHC parser state
pub struct ChcParser {
    /// The CHC problem being built
    problem: ChcProblem,
    /// Declared variables (name -> sort)
    variables: FxHashMap<String, ChcSort>,
    /// Declared predicates (name -> (id, sorts))
    predicates: FxHashMap<String, (PredicateId, Vec<ChcSort>)>,
    /// Fixture-only TLA+ action declarations (name -> id)
    actions: FxHashMap<String, ActionId>,
    /// Declared sorts (datatype names)
    declared_sorts: FxHashSet<String>,
    /// Declared datatype sorts with full constructor/selector metadata.
    /// Populated by `parse_declare_datatype`; looked up by `parse_sort`.
    declared_datatype_sorts: FxHashMap<String, ChcSort>,
    /// Declared functions (constructors, selectors, testers)
    /// Maps name -> (return_sort, arg_sorts)
    functions: FxHashMap<String, (ChcSort, Vec<ChcSort>)>,
    /// Overloaded declared functions keyed by surface name.
    overloaded_functions: FxHashMap<String, Vec<(ChcSort, Vec<ChcSort>)>>,
    /// Polarity of the expression position currently being parsed:
    /// `+1` positive, `-1` negative (under an odd number of negations /
    /// on the antecedent side of `=>`), `0` mixed/unknown.
    ///
    /// Quantifier stripping is only equivalence-preserving for `forall` at
    /// positive polarity and `exists` at negative polarity, so
    /// `parse_quantifier_expr` needs to know where it is.
    polarity: i8,
    /// Current position in input
    pos: usize,
    /// Input string
    input: String,
}

impl ChcParser {
    /// Create a new parser
    pub fn new() -> Self {
        Self {
            problem: ChcProblem::new(),
            variables: FxHashMap::default(),
            predicates: FxHashMap::default(),
            actions: FxHashMap::default(),
            declared_sorts: FxHashSet::default(),
            declared_datatype_sorts: FxHashMap::default(),
            functions: FxHashMap::default(),
            overloaded_functions: FxHashMap::default(),
            polarity: 1,
            pos: 0,
            input: String::new(),
        }
    }

    pub(super) fn register_function(
        &mut self,
        name: String,
        ret_sort: ChcSort,
        arg_sorts: Vec<ChcSort>,
    ) {
        let signature = (ret_sort, arg_sorts);

        if let Some(existing) = self.functions.get(&name).cloned() {
            self.overloaded_functions
                .entry(name.clone())
                .or_insert_with(|| vec![existing])
                .push(signature.clone());
        } else if let Some(overloads) = self.overloaded_functions.get_mut(&name) {
            overloads.push(signature.clone());
        }

        self.functions.insert(name, signature);
    }

    pub(super) fn resolve_function_signature(
        &self,
        name: &str,
        arg_sorts: &[ChcSort],
    ) -> ChcResult<Option<(ChcSort, Vec<ChcSort>)>> {
        let Some(candidates) = self.overloaded_functions.get(name) else {
            return Ok(None);
        };

        let mut matches = candidates.iter().filter(|(_ret_sort, expected_args)| {
            expected_args.len() == arg_sorts.len()
                && expected_args
                    .iter()
                    .zip(arg_sorts.iter())
                    .all(|(expected, actual)| Self::sorts_compatible(expected, actual))
        });

        let Some(first) = matches.next().cloned() else {
            return Ok(None);
        };

        if matches.next().is_some() {
            return Err(ChcError::Parse(format!(
                "Ambiguous overloaded function '{name}' for argument sorts {:?}",
                arg_sorts
            )));
        }

        Ok(Some(first))
    }

    pub(super) fn sorts_compatible(expected: &ChcSort, actual: &ChcSort) -> bool {
        match (expected, actual) {
            (
                ChcSort::Array(expected_key, expected_val),
                ChcSort::Array(actual_key, actual_val),
            ) => {
                Self::sorts_compatible(expected_key, actual_key)
                    && Self::sorts_compatible(expected_val, actual_val)
            }
            (ChcSort::Datatype { name: expected, .. }, ChcSort::Datatype { name: actual, .. })
            | (ChcSort::Datatype { name: expected, .. }, ChcSort::Uninterpreted(actual))
            | (ChcSort::Uninterpreted(expected), ChcSort::Datatype { name: actual, .. }) => {
                expected == actual
            }
            _ => expected == actual,
        }
    }

    /// Parse a CHC file and return the problem
    pub fn parse(input: &str) -> ChcResult<ChcProblem> {
        // Preflight: detect unsupported floating-point tokens before generic parsing.
        // Native ay-chc accepts Bool/Int/Real/BV/Array only. FP sorts and rounding-mode
        // constants produce confusing generic parse errors without this check.
        Self::check_unsupported_fp_tokens(input)?;

        let mut parser = Self::new();
        parser.input = input.to_string();
        parser.pos = 0;

        while parser.pos < parser.input.len() {
            parser.skip_whitespace_and_comments();
            if parser.pos >= parser.input.len() {
                break;
            }
            parser.parse_command()?;
        }

        Ok(parser.problem)
    }

    /// Preflight check: reject CHC input containing floating-point sorts or rounding-mode tokens.
    ///
    /// The CHC pipeline (parser, PDR, TPA, PDKind, etc.) has no FP theory support.
    /// Without this check, FP tokens produce confusing generic parse errors like
    /// "Unknown indexed sort: FloatingPoint" or silent misinterpretation of
    /// rounding-mode constants as integer variables.
    ///
    /// Returns `Err(ChcError::UnsupportedFloatingPoint)` with an actionable message
    /// directing consumers to lower FP terms to BV before HORN solving.
    fn check_unsupported_fp_tokens(input: &str) -> ChcResult<()> {
        // Tokens that prove FP HORN ingress. Ordered by likelihood in model-checker-consumer-generated CHC.
        const FP_TOKENS: &[&str] = &[
            "FloatingPoint",
            "RoundingMode",
            "roundNearestTiesToEven",
            "roundNearestTiesToAway",
            "roundTowardPositive",
            "roundTowardNegative",
            "roundTowardZero",
            "fp.add",
            "fp.sub",
            "fp.mul",
            "fp.div",
            "fp.sqrt",
            "fp.rem",
            "fp.abs",
            "fp.neg",
            "fp.fma",
            "fp.min",
            "fp.max",
            "fp.lt",
            "fp.leq",
            "fp.gt",
            "fp.geq",
            "fp.eq",
            "fp.isNormal",
            "fp.isSubnormal",
            "fp.isZero",
            "fp.isInfinite",
            "fp.isNaN",
            "fp.isNegative",
            "fp.isPositive",
            "to_fp",
            "fp.to_ubv",
            "fp.to_sbv",
            "fp.to_real",
        ];

        // Strip SMT-LIB line comments before scanning. Comments start with ';'
        // and extend to end-of-line. Without this, FP tokens inside comments
        // (e.g. "; FloatingPoint should be ignored") cause false rejections.
        let stripped: String = input
            .lines()
            .map(|line| match line.find(';') {
                Some(pos) => &line[..pos],
                None => line,
            })
            .collect::<Vec<_>>()
            .join("\n");

        for token in FP_TOKENS {
            if stripped.contains(token) {
                return Err(ChcError::UnsupportedFloatingPoint((*token).to_string()));
            }
        }

        Ok(())
    }
}

impl Default for ChcParser {
    fn default() -> Self {
        Self::new()
    }
}
