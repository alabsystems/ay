// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! CHC problem definition

use crate::bv_util::bv_mask;
use crate::clause::ActionId;
use crate::{
    ChcExpr, ChcOp, ChcResult, ChcSort, ChcVar, ClauseBody, ClauseHead, HornClause, Predicate,
    PredicateId,
};
use ay_core::kani_compat::{DetHashMap as FxHashMap, DetHashSet as FxHashSet};
use std::sync::Arc;

mod analysis;
mod api;
mod case_split;
mod preprocess;
mod scalarization;
#[cfg(test)]
mod tests;

/// Stable identity for one independently solvable safety query.
///
/// A query can be introduced through a nullary marker such as
/// `error_p7 => error`, `error => false`.  In that case `query_clause_index`
/// identifies the original `error => false` clause and
/// `defining_clause_index` identifies the selected marker definition.  For a
/// direct false-head query, `defining_clause_index` is `None`.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct ChcQueryObligationId {
    query_clause_index: usize,
    defining_clause_index: Option<usize>,
    label: String,
    content_sha256: String,
}

impl ChcQueryObligationId {
    /// Index of the false-head clause in the original problem.
    pub fn query_clause_index(&self) -> usize {
        self.query_clause_index
    }

    /// Index of the nullary marker's defining clause, when the query was
    /// unfolded through one.
    pub fn defining_clause_index(&self) -> Option<usize> {
        self.defining_clause_index
    }

    /// Stable human-readable label for diagnostics and result correlation.
    pub fn label(&self) -> &str {
        &self.label
    }

    /// SHA-256 of the obligation's deterministic normalized CHC input.
    ///
    /// Unlike the source-clause indices, this binds the identity to the exact
    /// independently solvable problem content and remains stable across
    /// repeated construction of the same slice.
    pub fn content_sha256(&self) -> &str {
        &self.content_sha256
    }
}

/// One exact, independently solvable slice of a multi-query CHC problem.
///
/// The contained problem retains only definitions in the selected query's
/// backwards dependency cone.  Its verdict is therefore equivalent to the
/// corresponding query in the source problem, while unrelated difficult
/// properties cannot consume its solve budget.
#[derive(Debug, Clone)]
pub struct ChcQueryObligation {
    id: ChcQueryObligationId,
    problem: ChcProblem,
}

impl ChcQueryObligation {
    /// Stable identity of this query slice.
    pub fn id(&self) -> &ChcQueryObligationId {
        &self.id
    }

    /// Independently solvable problem for this query.
    pub fn problem(&self) -> &ChcProblem {
        &self.problem
    }

    /// Consume the slice and return its independently solvable problem.
    pub fn into_problem(self) -> ChcProblem {
        self.problem
    }

    /// Consume the slice and return both its identity and problem.
    pub fn into_parts(self) -> (ChcQueryObligationId, ChcProblem) {
        (self.id, self.problem)
    }
}

/// A constant array index, either an integer or a bitvector.
///
/// Used during scalarization to represent the set of constant indices at which
/// arrays are accessed.
#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
enum ConstIndex {
    Int(i128),
    BitVec(u128, u32), // (value, width)
}

impl ConstIndex {
    /// Convert this index back to a ChcExpr literal.
    fn to_expr(&self) -> ChcExpr {
        match self {
            Self::Int(k) => ChcExpr::Int(*k),
            Self::BitVec(v, w) => ChcExpr::BitVec(*v, *w),
        }
    }

    /// Coerce this index to match the target key sort (#6084).
    ///
    /// When a `Select(Array(BitVec(N), _), Int(k))` is encountered during
    /// scalarization, the constant index is `Int(k)` but needs to become
    /// `BitVec(k, N)` so the generated scalar variable and equality have
    /// the correct sort.
    fn coerce_to_sort(self, key_sort: &ChcSort) -> Option<Self> {
        match (&self, key_sort) {
            (Self::Int(k), ChcSort::BitVec(w)) => Some(Self::BitVec(*k as u128 & bv_mask(*w), *w)),
            // i128-lockstep: a 128-bit BV constant with the top bit set has no
            // exact Int (i128) value; skip the index (leave the cell
            // unscalarized) instead of truncating like the old `as i64` did.
            (Self::BitVec(v, _), ChcSort::Int) => i128::try_from(*v).ok().map(Self::Int),
            _ => Some(self),
        }
    }

    /// Suffix string for naming scalar variables, e.g. "0", "neg3", "bv5_32".
    fn suffix(&self) -> String {
        match self {
            Self::Int(k) => {
                if *k < 0 {
                    format!("neg{}", k.unsigned_abs())
                } else {
                    k.to_string()
                }
            }
            Self::BitVec(v, w) => format!("bv{v}_{w}"),
        }
    }
}

/// One predicate argument after array scalarization.
#[derive(Debug, Clone)]
pub(crate) enum ArrayScalarizedArg {
    /// The scalarized argument is the original predicate argument at this index.
    Original(usize),
    /// The scalarized argument represents `(select original_arg index)`.
    Select { original_arg: usize, index: ChcExpr },
}

/// Reversal map for CHC array scalarization.
#[derive(Debug, Clone)]
pub(crate) struct ArrayScalarizationMap {
    pub(crate) original_predicates: Vec<Predicate>,
    pub(crate) pred_args: FxHashMap<PredicateId, Vec<ArrayScalarizedArg>>,
}

/// A Constrained Horn Clause problem
///
/// Contains:
/// - A set of predicate declarations (uninterpreted relations)
/// - A set of Horn clauses (rules)
/// - Query clauses (clauses with false head)
#[derive(Debug, Clone)]
pub struct ChcProblem {
    /// Predicate declarations
    predicates: Vec<Predicate>,
    /// Map from name to predicate ID
    predicate_names: FxHashMap<String, PredicateId>,
    /// All Horn clauses
    clauses: Vec<HornClause>,
    /// Number of false-head queries pruned because their body simplified to
    /// false. Such inputs are trivially safe, but still syntactically contain
    /// a safety query and should pass problem validation.
    pruned_false_queries: usize,
    /// Whether the input used Z3 fixedpoint format (declare-rel/rule/query).
    /// In fixedpoint format, sat/unsat polarity is inverted relative to SMT-LIB HORN:
    /// - HORN: sat = satisfiable (safe), unsat = unsatisfiable (unsafe)
    /// - Fixedpoint: sat = query reachable (unsafe), unsat = query unreachable (safe)
    fixedpoint_format: bool,
    /// Set when the parser stripped a `forall` from a NEGATIVE-polarity
    /// position (a rule body). Hoisting the bound variable into the flat
    /// clause scope turns `forall i. (B(i) -> H)` into `(exists i. B(i)) -> H`,
    /// i.e. it WEAKENS the antecedent. That is a sound over-approximation for
    /// proofs -- an `unsat`/Safe answer stays valid a fortiori -- but it can
    /// FABRICATE a counterexample, so a Sat/Unsafe answer must be downgraded to
    /// Unknown. See `parser/expr.rs::parse_quantifier_expr`.
    stripped_body_forall: bool,
    /// Datatype definitions from declare-datatype commands (#7016).
    /// Maps datatype name → Vec<(constructor_name, Vec<(selector_name, selector_sort)>)>.
    /// Preserves structural metadata that the function signature map discards.
    datatype_defs: FxHashMap<String, Vec<(String, Vec<(String, ChcSort)>)>>,
    /// Optional action names for TLA+ per-action invariant discovery (#8215).
    /// Indexed by `ActionId`. When populated, the problem has a TLA+-style action
    /// decomposition where the next-state relation is `Next = A1 \/ ... \/ An`.
    action_names: Vec<String>,
}

impl Default for ChcProblem {
    fn default() -> Self {
        Self::new()
    }
}
