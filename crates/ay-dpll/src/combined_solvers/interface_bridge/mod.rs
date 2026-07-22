// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// #8529: Use deterministic hash maps in all builds.
use ay_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};
mod propagate;

use ay_core::term::{Constant, Symbol, TermData};
use ay_core::{TermId, TermStore};
use num_bigint::BigInt;
use num_rational::BigRational;

pub(super) use super::interface_bridge_eval::{
    evaluate_arith_term_with_reasons, evaluate_bool_term, evaluate_real_arith_term_with_reasons,
    evaluate_real_bool_term, lia_get_int_value_with_reasons, lra_get_real_value_with_reasons,
};
pub(in crate::combined_solvers) use propagate::has_unjustified_int_leaf;

/// Trail entry for incremental push/pop of interface term tracking (#3077).
/// Instead of cloning 3 HashSets on every push, we record individual insertions
/// and undo them on pop.
enum InterfaceTrailEntry {
    /// Scope boundary marker. Pop undoes entries until the matching marker.
    ScopeMarker,
    /// An arith term was added to interface_arith_terms.
    ArithTerm(TermId),
    /// A constant mapping was added to int_const_terms.
    ConstTerm(BigInt),
    /// A rational constant mapping was added to real_const_terms (#4915).
    RealConstTerm(BigRational),
    /// An equality pair was added to propagated_interface_eqs.
    PropagatedEq(TermId, TermId),
    /// A value was recorded in propagated_term_values (arith_term, const_term).
    /// Used to undo value tracking on pop.
    PropagatedValue(TermId),
}

/// Shared Nelson-Oppen interface term tracking state (#3788).
///
/// Extracted from the duplicated fields in `UfLiaSolver`, `AufLiaSolver`,
/// and `StringsLiaSolver`. Manages the interface arithmetic terms, integer
/// constant registry, propagated equality deduplication, and trail-based
/// incremental push/pop.
pub(super) struct InterfaceBridge {
    /// Interface arithmetic terms — pure arithmetic expressions appearing in EUF
    /// equalities with uninterpreted function terms (#1893).
    interface_arith_terms: HashSet<TermId>,
    /// Map from integer constant values to their TermIds in the formula.
    int_const_terms: HashMap<BigInt, TermId>,
    /// Map from rational constant values to their TermIds in the formula (#4915).
    /// Used by UfLraSolver for Real-valued interface bridge evaluation.
    real_const_terms: HashMap<BigRational, TermId>,
    /// Track which (arith_term, const_term) equalities we've already propagated.
    propagated_interface_eqs: HashSet<(TermId, TermId)>,
    /// Track the const_term last propagated for each arith_term.
    /// Used to detect contradictory value changes across N-O iterations:
    /// if an arith_term was previously equated to const_A but now evaluates
    /// to const_B (const_A != const_B), the second propagation is suppressed
    /// to prevent EUF from deriving the false equality const_A = const_B.
    /// Model-dependent bridge equalities can become stale when the LIA model
    /// changes between N-O iterations due to back-propagated equalities.
    propagated_term_values: HashMap<TermId, TermId>,
    /// Trail-based undo log for incremental push/pop (#3077).
    interface_trail: Vec<InterfaceTrailEntry>,
    /// Push/pop depth counter for balance checking (#4714, #4995).
    scope_depth: usize,
}

impl InterfaceBridge {
    pub(super) fn new() -> Self {
        Self {
            interface_arith_terms: HashSet::default(),
            int_const_terms: HashMap::default(),
            real_const_terms: HashMap::default(),
            propagated_interface_eqs: HashSet::default(),
            propagated_term_values: HashMap::default(),
            interface_trail: Vec::new(),
            scope_depth: 0,
        }
    }

    /// Track interface arithmetic terms from an asserted literal (#1893, #4767, #5081).
    ///
    /// Tracks both pure-arithmetic terms (original behavior) and UF-mixed terms
    /// like `(+ (g x) 1)` that combine arithmetic with UF subterms. The latter
    /// are needed for Nelson-Oppen propagation when LIA knows the UF values.
    ///
    /// Also tracks distinct/disequality arguments (#5081): after mk_distinct,
    /// `(distinct A B)` becomes `NOT(= A B)`. Both sides are registered so
    /// the bridge can evaluate them and propagate value equalities to EUF.
    pub(super) fn track_interface_term(&mut self, terms: &TermStore, literal: TermId) {
        use crate::term_helpers::{extract_interface_arith_term, extract_uf_mixed_interface_term};
        if let Some(arith_term) = extract_interface_arith_term(terms, literal) {
            if self.interface_arith_terms.insert(arith_term) {
                self.interface_trail
                    .push(InterfaceTrailEntry::ArithTerm(arith_term));
            }
        }
        // Also track UF-mixed terms like (+ (g x) 1) for evaluation by the bridge (#4767).
        if let Some(uf_mixed_term) = extract_uf_mixed_interface_term(terms, literal) {
            if self.interface_arith_terms.insert(uf_mixed_term) {
                self.interface_trail
                    .push(InterfaceTrailEntry::ArithTerm(uf_mixed_term));
            }
        }
        // #uflia-hard-mixed-eq: track UF-mixed compound operands of equality
        // atoms even when NEITHER side is pure arithmetic. The extractors
        // above both require a pure-arith side, so an equality between a UF
        // application and a UF-mixed compound (`(= (Sum a b) (+ (Sum c d) y x))`,
        // mathsat EufLaArithmetic hard*) registered nothing: the bridge never
        // evaluated the compound, the `compound = constant` interface equality
        // was never proposed, and the disequality refutation (SAT asserts the
        // atom false; EUF must derive both sides ~ the same constant) was
        // unreachable — the N-O search accepted a model the strict
        // ite_uf_definition gate then rejected, degrading UNSAT to unknown.
        {
            use crate::term_helpers::extract_uf_mixed_eq_operands;
            let (mixed_lhs, mixed_rhs) = extract_uf_mixed_eq_operands(terms, literal);
            for t in [mixed_lhs, mixed_rhs].into_iter().flatten() {
                if self.interface_arith_terms.insert(t) {
                    self.interface_trail.push(InterfaceTrailEntry::ArithTerm(t));
                }
            }
        }
        // Track distinct argument terms so the bridge evaluates them (#5081).
        self.track_distinct_args(terms, literal);
    }

    /// Register both sides of distinct/disequality as interface arith terms (#5081).
    ///
    /// After `mk_distinct`, binary `distinct` becomes `NOT(= LHS RHS)`.
    /// If LHS or RHS is an Int-sorted expression that is arithmetically evaluable,
    /// register it so the bridge can evaluate it and propagate `term = constant`
    /// equalities to EUF. When both sides evaluate to the same integer, EUF's
    /// distinct check detects the conflict.
    pub(super) fn track_distinct_args(&mut self, terms: &TermStore, literal: TermId) {
        use crate::term_helpers::decode_non_bool_eq;
        // Unwrap NOT for distinct (= NOT(= ...))
        let inner = match terms.get(literal) {
            TermData::Not(inner) => *inner,
            _ => return,
        };
        let (lhs, rhs) = match decode_non_bool_eq(terms, inner) {
            Some(pair) => pair,
            None => return,
        };
        // Register both sides if they are arithmetic-sorted and evaluable.
        // The bridge's evaluate_arith_term_with_reasons handles Int;
        // evaluate_real_arith_term_with_reasons handles Real (#4906).
        for arg in <[_; 2]>::from((lhs, rhs)) {
            if matches!(terms.sort(arg), ay_core::Sort::Int | ay_core::Sort::Real)
                && is_arith_evaluable(terms, arg)
                && self.interface_arith_terms.insert(arg)
            {
                self.interface_trail
                    .push(InterfaceTrailEntry::ArithTerm(arg));
            }
        }
    }

    /// Register arithmetic arguments of UF applications as interface terms. (#5081)
    pub(super) fn track_uf_arith_args(&mut self, terms: &TermStore, root: TermId) {
        let mut stack = vec![root];
        let mut visited = HashSet::default();
        while let Some(term) = stack.pop() {
            if !visited.insert(term) {
                continue;
            }
            match terms.get(term) {
                TermData::App(Symbol::Named(name), args) => {
                    // Array congruence also needs arithmetic index terms from
                    // builtins like `select` / `store`, not just UF arguments.
                    let track_args = !BUILTIN_OPS.contains(&name.as_str())
                        || name == "select"
                        || name == "store";
                    if track_args && !args.is_empty() {
                        // #6846: Track the UF application ITSELF as an interface
                        // arith term when it has Int/Real sort. Without this,
                        // discover_model_equality() cannot detect when two UF
                        // applications (e.g., RF(expr1) and RF(expr2)) evaluate
                        // to the same value in the arithmetic model.
                        if !BUILTIN_OPS.contains(&name.as_str())
                            && matches!(terms.sort(term), ay_core::Sort::Int | ay_core::Sort::Real)
                            && self.interface_arith_terms.insert(term)
                        {
                            self.interface_trail
                                .push(InterfaceTrailEntry::ArithTerm(term));
                        }
                        for &arg in args {
                            if is_arith_evaluable(terms, arg)
                                && self.interface_arith_terms.insert(arg)
                            {
                                self.interface_trail
                                    .push(InterfaceTrailEntry::ArithTerm(arg));
                            }
                        }
                    }
                    stack.extend(args.iter().copied());
                }
                TermData::Not(inner) => stack.push(*inner),
                TermData::Ite(c, t, e) => stack.extend([*c, *t, *e]),
                _ => {}
            }
        }
    }

    // Constant collection and evaluation/propagation methods live in propagate.rs.

    /// Push a scope marker for incremental solving.
    pub(super) fn push(&mut self) {
        self.scope_depth += 1;
        self.interface_trail.push(InterfaceTrailEntry::ScopeMarker);
    }

    /// Pop entries back to the most recent scope marker (#3077).
    pub(super) fn pop(&mut self) {
        if self.scope_depth == 0 {
            return;
        }
        self.scope_depth -= 1;
        let arith_count_before = self.interface_arith_terms.len();
        let const_count_before = self.int_const_terms.len();
        let real_const_count_before = self.real_const_terms.len();
        let eq_count_before = self.propagated_interface_eqs.len();
        let mut found_marker = false;
        while let Some(entry) = self.interface_trail.pop() {
            match entry {
                InterfaceTrailEntry::ScopeMarker => {
                    found_marker = true;
                    break;
                }
                InterfaceTrailEntry::ArithTerm(t) => {
                    let removed = self.interface_arith_terms.remove(&t);
                    debug_assert!(
                        removed,
                        "BUG: InterfaceBridge pop: ArithTerm {t:?} not in set"
                    );
                }
                InterfaceTrailEntry::ConstTerm(n) => {
                    let removed = self.int_const_terms.remove(&n);
                    debug_assert!(
                        removed.is_some(),
                        "BUG: InterfaceBridge pop: ConstTerm {n:?} not in map"
                    );
                }
                InterfaceTrailEntry::RealConstTerm(r) => {
                    let removed = self.real_const_terms.remove(&r);
                    debug_assert!(
                        removed.is_some(),
                        "BUG: InterfaceBridge pop: RealConstTerm {r:?} not in map"
                    );
                }
                InterfaceTrailEntry::PropagatedEq(a, b) => {
                    let removed = self.propagated_interface_eqs.remove(&(a, b));
                    debug_assert!(
                        removed,
                        "BUG: InterfaceBridge pop: PropagatedEq ({a:?}, {b:?}) not in set"
                    );
                }
                InterfaceTrailEntry::PropagatedValue(t) => {
                    let removed = self.propagated_term_values.remove(&t);
                    debug_assert!(
                        removed.is_some(),
                        "BUG: InterfaceBridge pop: PropagatedValue {t:?} not in map"
                    );
                }
            }
        }
        if !found_marker {
            return;
        }
        // After pop, all sets must be no larger than before (pop only removes).
        debug_assert!(
            self.interface_arith_terms.len() <= arith_count_before,
            "BUG: InterfaceBridge pop grew arith_terms ({} -> {})",
            arith_count_before,
            self.interface_arith_terms.len()
        );
        debug_assert!(
            self.int_const_terms.len() <= const_count_before,
            "BUG: InterfaceBridge pop grew const_terms ({} -> {})",
            const_count_before,
            self.int_const_terms.len()
        );
        debug_assert!(
            self.real_const_terms.len() <= real_const_count_before,
            "BUG: InterfaceBridge pop grew real_const_terms ({} -> {})",
            real_const_count_before,
            self.real_const_terms.len()
        );
        debug_assert!(
            self.propagated_interface_eqs.len() <= eq_count_before,
            "BUG: InterfaceBridge pop grew propagated_eqs ({} -> {})",
            eq_count_before,
            self.propagated_interface_eqs.len()
        );
    }

    /// Clear all interface term tracking state.
    pub(super) fn reset(&mut self) {
        assert!(
            self.scope_depth == 0,
            "BUG: InterfaceBridge reset with unbalanced push/pop (scope_depth={})",
            self.scope_depth
        );
        self.interface_arith_terms.clear();
        self.int_const_terms.clear();
        self.real_const_terms.clear();
        self.propagated_interface_eqs.clear();
        self.propagated_term_values.clear();
        self.interface_trail.clear();
    }

    /// Check if a term is tracked as an interface arithmetic term.
    #[cfg(test)]
    pub(super) fn contains_arith_term(&self, term: &TermId) -> bool {
        self.interface_arith_terms.contains(term)
    }

    /// Return interface arithmetic terms in deterministic sorted order.
    /// Used by tests and by model equality discovery (#4906).
    pub(super) fn sorted_arith_terms(&self) -> Vec<TermId> {
        let mut terms: Vec<TermId> = self.interface_arith_terms.iter().copied().collect();
        terms.sort_unstable();
        terms
    }
}

const BUILTIN_OPS: &[&str] = &[
    "+", "-", "*", "/", "div", "mod", "abs", "<", "<=", ">", ">=", "=", "and", "or", "not", "xor",
    "=>", "distinct",
];
/// Check if a term is evaluable as arithmetic by the N-O bridge (#5081).
///
/// True for Int-sorted terms that the bridge's `evaluate_arith_term_with_reasons`
/// can handle: arithmetic ops, variables, constants, ITEs, and UF applications
/// with Int sort (resolved via EUF's int-value map through `get_int_value_with_reasons`).
fn is_arith_evaluable(terms: &TermStore, term: TermId) -> bool {
    match terms.get(term) {
        TermData::Var(_, _) | TermData::Ite(_, _, _) => {
            matches!(terms.sort(term), ay_core::Sort::Int | ay_core::Sort::Real)
        }
        TermData::Const(Constant::Int(_) | Constant::Rational(_)) => true,
        TermData::App(Symbol::Named(name), args) => {
            if !args.is_empty()
                && matches!(name.as_str(), "+" | "-" | "*" | "/" | "div" | "mod" | "abs")
            {
                return true;
            }
            // Int/Real-valued array reads can appear directly in shared
            // disequalities, e.g. `(not (= (select a k) (select b k)))`.
            // Register them as interface terms so EUF-propagated disequalities
            // constrain the arithmetic model used for AUFLIA model extraction.
            if name == "select"
                && matches!(terms.sort(term), ay_core::Sort::Int | ay_core::Sort::Real)
            {
                return true;
            }
            // UF applications with Int or Real sort are evaluable via EUF fallback (#5081):
            // resolved through the get_int/real_value_with_reasons closure that queries EUF.
            if !BUILTIN_OPS.contains(&name.as_str())
                && matches!(terms.sort(term), ay_core::Sort::Int | ay_core::Sort::Real)
            {
                return true;
            }
            false
        }
        _ => false,
    }
}

#[allow(clippy::panic)]
#[cfg(test)]
mod tests;
