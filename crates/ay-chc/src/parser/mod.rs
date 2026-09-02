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
//! - `(declare-fun <name> (<scalar-sorts>) <scalar-return-sort>)` - Declare a predicate or UF
//!   (`Bool` return means a Horn relation on this textual surface; other scalar
//!   returns mean an ordinary UF). The typed API can still represent an
//!   ordinary Bool-returning function explicitly as `ChcExpr::FuncApp`.
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

/// Whether `name` belongs to the active SMT theory's term namespace.
///
/// Typed problem construction bypasses command parsing, so validation reuses
/// this exact parser policy instead of maintaining a second builtin list.
pub(crate) fn is_builtin_term_symbol(name: &str) -> bool {
    commands::BUILTIN_TERM_SYMBOLS.contains(&name)
}

use crate::{ActionId, ChcError, ChcProblem, ChcResult, ChcSort, PredicateId};
use ay_core::kani_compat::DetHashMap as FxHashMap;
use ay_core::kani_compat::DetHashSet as FxHashSet;

/// CHC parser state
pub struct ChcParser {
    /// The CHC problem being built
    problem: ChcProblem,
    /// Declared variables (name -> sort)
    variables: FxHashMap<String, ChcSort>,
    /// Names hoisted into `variables` by a stripped QUANTIFIER BINDER in the
    /// clause currently being parsed.
    ///
    /// Only binder-vs-binder collisions are variable capture. A binder that
    /// shadows a file-scoped `declare-var` is the ordinary
    /// `(declare-var x Int)` + `(forall ((x Int)) ...)` idiom and must be left
    /// exactly alone — renaming it churns variable names through the emitted
    /// formula and breaks name-dependent machinery downstream (BMC witness
    /// replay, formula-form round trips).
    ///
    /// Reset per clause. NOTE this set is only a collision TRACKER: it never
    /// removes anything from `variables`, so resolution behaviour outside a
    /// genuine capture is bit-for-bit what it was.
    clause_binder_names: FxHashSet<String>,
    /// Names bound by a file-scoped `declare-var` / `declare-const`.
    ///
    /// A binder that shadows one of these DOES capture whenever the clause also
    /// uses the outer name outside the binder -- e.g.
    /// `(rule (=> (and (exists ((y Int)) (P y)) (= y 7)) (Q y)))`, where the
    /// `y` in `(= y 7)` and `(Q y)` is the declare-var. Renaming the BINDER is
    /// sound either way: the declare-var binding is left completely intact for
    /// the rest of the clause, and the binder gets a private name. This is the
    /// opposite of the earlier attempt, which REMOVED names from scope.
    declared_var_names: FxHashSet<String>,
    /// Active binder renames, innermost last: (source name -> minted name).
    ///
    /// Empty in every clause that has no capture, which is nearly all of them,
    /// so the lookup in `parse_symbol_expr` costs one `is_empty` check.
    active_renames: Vec<(String, String)>,
    /// Counter making each minted binder name unique within a parse.
    capture_counter: usize,
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
    /// Ordinary non-Bool functions introduced by `declare-fun`.
    ///
    /// Datatype constructors/selectors may be overloaded by the SMT-LIB
    /// datatype surface, while ordinary uninterpreted functions may not.  Keep
    /// their names separate so a later datatype declaration cannot silently
    /// turn a user UF into an overload (or make lookup ambiguous).
    uninterpreted_functions: FxHashSet<String>,
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
            clause_binder_names: FxHashSet::default(),
            declared_var_names: FxHashSet::default(),
            active_renames: Vec::new(),
            capture_counter: 0,
            predicates: FxHashMap::default(),
            actions: FxHashMap::default(),
            declared_sorts: FxHashSet::default(),
            declared_datatype_sorts: FxHashMap::default(),
            functions: FxHashMap::default(),
            uninterpreted_functions: FxHashSet::default(),
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

    /// Clear the per-clause binder-collision tracker.
    ///
    /// Binder scopes are per-clause, so `forall ((u Int)) ...` appearing in
    /// clause after clause is ordinary and must NOT read as capture. This
    /// clears only the TRACKER; `variables` is deliberately untouched, so
    /// nothing about name resolution changes outside a genuine capture.
    pub(super) fn end_clause_binder_scope(&mut self) {
        self.clause_binder_names.clear();
        self.active_renames.clear();
    }

    /// Mint a binder name that cannot collide with any symbol in the input.
    ///
    /// A fixed prefix is not proof of freshness -- `!` is a legal SMT-LIB
    /// symbol character, so the input may already contain `ay!cap!1!y`.
    /// Extend the counter until the candidate occurs nowhere in the source.
    pub(super) fn fresh_binder_name(&mut self, original: &str) -> String {
        loop {
            self.capture_counter += 1;
            let candidate = format!("ay!cap!{}!{}", self.capture_counter, original);
            if !self.input.contains(candidate.as_str()) {
                return candidate;
            }
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
