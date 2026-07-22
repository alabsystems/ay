// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Nelson-Oppen interface term evaluation and equality propagation.
//!
//! Contains the integer and real constant collection + evaluation loops
//! that discover interface equalities from arithmetic model values.
//!
//! Split from `mod.rs` for code health (#5970).

// #8529: Use deterministic hash sets in all builds.
use ay_core::kani_compat::DetHashSet as HashSet;
use ay_core::term::{Constant, Symbol, TermData};
use ay_core::{DiscoveredEquality, TermId, TermStore, TheoryLit};
use num_bigint::BigInt;
use num_rational::BigRational;

use super::InterfaceBridge;
use super::InterfaceTrailEntry;
use super::{
    evaluate_arith_term_with_reasons, evaluate_bool_term, evaluate_real_arith_term_with_reasons,
    evaluate_real_bool_term,
};

/// Red zone size for `stacker::maybe_grow` in constant collection recursion (#8414).
const CONST_COLLECT_STACK_RED_ZONE: usize = 32 * 1024;

/// Stack segment size allocated by stacker for constant collection recursion.
const CONST_COLLECT_STACK_SIZE: usize = 1024 * 1024;

/// Detect self-evidencing reason sets for a discovered bridge equality (#8742).
///
/// When the ONLY reason for the bridge equality `lhs = rhs` is the equality
/// atom `(= lhs rhs) = true` (or the argument-swapped form `(= rhs lhs) = true`),
/// the reason is tautological. LIA's tight bound on `lhs` was set purely
/// because SAT assigned the equality atom `true`; there is no independent
/// arithmetic justification such as a pair of bounds derived from other
/// inequalities. Propagating this equality into EUF with a self-evidencing
/// reason causes conflict analysis to produce tautological learnt clauses
/// (e.g. not-T OR not-not-T which reduces to a tautology), so SAT never
/// backtracks the decision that forced the equality atom true.
///
/// The canonical trigger: array extensionality Skolems. LIA assigns the
/// fresh Skolem `__ext_diff = 0` whose sole reason chain is
/// `{(= 0 __ext_diff) = true}` after a `NeedModelEqualities` round forces
/// the equality atom at the SAT layer. The bridge then would propagate
/// `__ext_diff = 0` back into EUF with the same atom as its reason, which
/// collides with a pre-existing top-level `(= 0 __ext_diff) = false`
/// assertion and produces false-UNSAT.
fn reasons_are_self_evidencing(
    terms: &TermStore,
    lhs: TermId,
    rhs: TermId,
    reasons: &[TheoryLit],
) -> bool {
    if reasons.len() != 1 {
        return false;
    }
    let reason = &reasons[0];
    if !reason.value {
        return false;
    }
    match terms.get(reason.term) {
        TermData::App(sym, args) if sym.name() == "=" && args.len() == 2 => {
            (args[0] == lhs && args[1] == rhs) || (args[0] == rhs && args[1] == lhs)
        }
        _ => false,
    }
}

/// Check if an Int-sorted term has any variable leaf whose model value has
/// empty reasons (non-tight bounds) (#8147). When `true`, the evaluated
/// value is partially justified and the resulting equality should be treated
/// as speculative rather than hard-committed to sub-solvers. Without this
/// check, compound terms like `(+ tight_x free_u)` get classified as "proved"
/// because `tight_x` contributes reasons, masking that `free_u`'s value is a
/// model artifact. Gaussian elimination then treats the bridge equality as a
/// hard constraint, deriving spurious UNSAT when later N-O rounds change the
/// free variable.
pub(in crate::combined_solvers) fn has_unjustified_int_leaf(
    terms: &TermStore,
    get_int_value_with_reasons: &impl Fn(TermId) -> Option<(BigInt, Vec<TheoryLit>)>,
    term: TermId,
) -> bool {
    match terms.get(term) {
        TermData::Const(_) => false,
        TermData::Var(_, _) => get_int_value_with_reasons(term)
            .map(|(_, reasons)| reasons.is_empty())
            .unwrap_or(true),
        TermData::App(Symbol::Named(name), args) => {
            let n = name.as_str();
            if n == "+" || n == "-" || n == "*" {
                args.iter()
                    .any(|&arg| has_unjustified_int_leaf(terms, get_int_value_with_reasons, arg))
            } else {
                // UF application or unknown function: treat as leaf variable.
                get_int_value_with_reasons(term)
                    .map(|(_, reasons)| reasons.is_empty())
                    .unwrap_or(true)
            }
        }
        TermData::App(_, _) => get_int_value_with_reasons(term)
            .map(|(_, reasons)| reasons.is_empty())
            .unwrap_or(true),
        TermData::Ite(cond, then_t, else_t) => {
            // Mirror the evaluator's ITE dispatch EXACTLY (#w11-ite-sum
            // wrong-UNSAT): `evaluate_arith_term_with_reasons` resolves an ITE
            // by (a) deciding the condition as an arithmetic predicate and
            // recursing into the TAKEN branch, or — when the condition cannot
            // be decided (e.g. a bare Bool variable, as in the bit-recombination
            // index sums `(+ (ite b0 1 0) (* (ite b1 1 0) 2) ...)`) — (b)
            // falling back to the ITE term's own LIA model value. Checking only
            // the two branches wrongly classified `(ite b 1 0)` as justified
            // (both branches are constants) even though its evaluated value in
            // case (b) was a bare simplex model choice with EMPTY reasons.
            // `check_int_equality_value_mismatches` then turned a value
            // coincidence between two such ite-sums into a hard theory
            // conflict that unconditionally forced the indices equal —
            // deriving false UNSAT on satisfiable QF_AUFLIA instances.
            let mut cond_reasons = Vec::new();
            match evaluate_bool_term(terms, get_int_value_with_reasons, *cond, &mut cond_reasons) {
                Some(cond_value) => {
                    // Case (a): the decision is justified only when the
                    // condition's own arithmetic leaves are, and then the
                    // TAKEN branch must be justified as well.
                    let branch = if cond_value { *then_t } else { *else_t };
                    ite_cond_has_unjustified_int_leaf(terms, get_int_value_with_reasons, *cond)
                        || has_unjustified_int_leaf(terms, get_int_value_with_reasons, branch)
                }
                // Case (b): the value is the ITE term's own model lookup —
                // justified only when that lookup carries tight-bound reasons.
                None => get_int_value_with_reasons(term)
                    .map(|(_, reasons)| reasons.is_empty())
                    .unwrap_or(true),
            }
        }
        _ => get_int_value_with_reasons(term)
            .map(|(_, reasons)| reasons.is_empty())
            .unwrap_or(true),
    }
}

/// Justification mirror of `evaluate_bool_term` for ITE conditions
/// (#w11-ite-sum): a condition the evaluator decides is justified only when
/// every arithmetic operand it compared has no unjustified leaf. Shapes the
/// evaluator cannot decide (bare Bool variables, non-comparison applications)
/// return `true` — callers reach this only in the decided case, and staying
/// conservative there can only demote an equality to speculative.
fn ite_cond_has_unjustified_int_leaf(
    terms: &TermStore,
    get_int_value_with_reasons: &impl Fn(TermId) -> Option<(BigInt, Vec<TheoryLit>)>,
    cond: TermId,
) -> bool {
    match terms.get(cond) {
        TermData::Const(Constant::Bool(_)) => false,
        TermData::Not(inner) => {
            ite_cond_has_unjustified_int_leaf(terms, get_int_value_with_reasons, *inner)
        }
        TermData::App(Symbol::Named(name), args)
            if args.len() == 2 && matches!(name.as_str(), "<" | "<=" | ">" | ">=" | "=") =>
        {
            args.iter()
                .any(|&arg| has_unjustified_int_leaf(terms, get_int_value_with_reasons, arg))
        }
        _ => true,
    }
}

/// Check if a Real-sorted term has any variable leaf with unjustified (non-tight)
/// bounds (#8147). Parallel to `has_unjustified_int_leaf`.
fn has_unjustified_real_leaf(
    terms: &TermStore,
    get_real_value_with_reasons: &impl Fn(TermId) -> Option<(BigRational, Vec<TheoryLit>)>,
    term: TermId,
) -> bool {
    match terms.get(term) {
        TermData::Const(_) => false,
        TermData::Var(_, _) => get_real_value_with_reasons(term)
            .map(|(_, reasons)| reasons.is_empty())
            .unwrap_or(true),
        TermData::App(Symbol::Named(name), args) => {
            let n = name.as_str();
            if n == "+" || n == "-" || n == "*" || n == "/" {
                args.iter()
                    .any(|&arg| has_unjustified_real_leaf(terms, get_real_value_with_reasons, arg))
            } else {
                get_real_value_with_reasons(term)
                    .map(|(_, reasons)| reasons.is_empty())
                    .unwrap_or(true)
            }
        }
        TermData::App(_, _) => get_real_value_with_reasons(term)
            .map(|(_, reasons)| reasons.is_empty())
            .unwrap_or(true),
        TermData::Ite(cond, then_t, else_t) => {
            // Mirror of the Int Ite arm above (#w11-ite-sum): follow the
            // evaluator's actual dispatch instead of checking both branches.
            let mut cond_reasons = Vec::new();
            match evaluate_real_bool_term(
                terms,
                get_real_value_with_reasons,
                *cond,
                &mut cond_reasons,
            ) {
                Some(cond_value) => {
                    let branch = if cond_value { *then_t } else { *else_t };
                    ite_cond_has_unjustified_real_leaf(terms, get_real_value_with_reasons, *cond)
                        || has_unjustified_real_leaf(terms, get_real_value_with_reasons, branch)
                }
                None => get_real_value_with_reasons(term)
                    .map(|(_, reasons)| reasons.is_empty())
                    .unwrap_or(true),
            }
        }
        _ => get_real_value_with_reasons(term)
            .map(|(_, reasons)| reasons.is_empty())
            .unwrap_or(true),
    }
}

/// Justification mirror of `evaluate_real_bool_term` for ITE conditions
/// (#w11-ite-sum). Parallel to `ite_cond_has_unjustified_int_leaf`.
fn ite_cond_has_unjustified_real_leaf(
    terms: &TermStore,
    get_real_value_with_reasons: &impl Fn(TermId) -> Option<(BigRational, Vec<TheoryLit>)>,
    cond: TermId,
) -> bool {
    match terms.get(cond) {
        TermData::Const(Constant::Bool(_)) => false,
        TermData::Not(inner) => {
            ite_cond_has_unjustified_real_leaf(terms, get_real_value_with_reasons, *inner)
        }
        TermData::App(Symbol::Named(name), args)
            if args.len() == 2 && matches!(name.as_str(), "<" | "<=" | ">" | ">=" | "=") =>
        {
            args.iter()
                .any(|&arg| has_unjustified_real_leaf(terms, get_real_value_with_reasons, arg))
        }
        _ => true,
    }
}

impl InterfaceBridge {
    /// Collect integer constants from a term and register them.
    /// Uses a visited set to avoid exponential re-traversal of shared DAG subterms (#3712).
    pub(crate) fn collect_int_constants(&mut self, terms: &TermStore, term: TermId) {
        let mut visited = HashSet::default();
        self.collect_int_constants_inner(terms, term, &mut visited);
    }

    /// Uses `stacker::maybe_grow` for stack safety on deeply nested terms (#8414).
    fn collect_int_constants_inner(
        &mut self,
        terms: &TermStore,
        term: TermId,
        visited: &mut HashSet<TermId>,
    ) {
        stacker::maybe_grow(
            CONST_COLLECT_STACK_RED_ZONE,
            CONST_COLLECT_STACK_SIZE,
            || {
                if !visited.insert(term) {
                    return;
                }
                match terms.get(term) {
                    TermData::Const(Constant::Int(n)) if !self.int_const_terms.contains_key(n) => {
                        self.int_const_terms.insert(n.clone(), term);
                        self.interface_trail
                            .push(InterfaceTrailEntry::ConstTerm(n.clone()));
                    }
                    TermData::App(_, args) => {
                        for &arg in args {
                            self.collect_int_constants_inner(terms, arg, visited);
                        }
                    }
                    TermData::Not(inner) => {
                        self.collect_int_constants_inner(terms, *inner, visited)
                    }
                    TermData::Ite(c, t, e) => {
                        self.collect_int_constants_inner(terms, *c, visited);
                        self.collect_int_constants_inner(terms, *t, visited);
                        self.collect_int_constants_inner(terms, *e, visited);
                    }
                    _ => {}
                }
            },
        ) // stacker::maybe_grow
    }

    /// Evaluate interface terms and return new equalities with reasons (#4068).
    ///
    /// The `get_int_value_with_reasons` closure returns both the integer value
    /// and the `TheoryLit` reasons (from LIA tight bounds) that fix a variable
    /// to that value. These reasons are collected across all variables in each
    /// arithmetic term so that receiving theories have complete proof provenance
    /// for conflict explanations.
    ///
    /// The caller is responsible for asserting the returned equalities into
    /// whichever sub-solvers need them (EUF, and optionally Strings).
    ///
    /// #6846: Equalities with empty reasons (free UF-valued variables) are
    /// returned as speculative pairs rather than asserted directly. The
    /// combined solver upgrades them to `NeedModelEquality` /
    /// `NeedModelEqualities` at fixpoint so the SAT layer can choose them
    /// explicitly instead of hard-wiring proofless equalities into EUF.
    pub(crate) fn evaluate_and_propagate(
        &mut self,
        terms: &TermStore,
        get_int_value_with_reasons: &impl Fn(TermId) -> Option<(BigInt, Vec<TheoryLit>)>,
        debug: bool,
        label: &str,
    ) -> (Vec<DiscoveredEquality>, Vec<(TermId, TermId)>) {
        let mut arith_terms: Vec<TermId> = self.interface_arith_terms.iter().copied().collect();
        arith_terms.sort_unstable(); // Deterministic iteration order (#3041)
        if debug {
            for &t in &arith_terms {
                safe_eprintln!("[N-O {}] Interface term {:?}: {:?}", label, t, terms.get(t));
            }
        }
        let mut new_eqs = Vec::new();
        let mut speculative_pairs = Vec::new();
        for arith_term in arith_terms {
            let mut reasons = Vec::new();
            let eval = evaluate_arith_term_with_reasons(
                terms,
                get_int_value_with_reasons,
                arith_term,
                &mut reasons,
            );
            if debug && eval.is_none() {
                safe_eprintln!("[N-O {}] Eval FAILED for {:?}", label, arith_term);
            }
            if let Some(value) = eval {
                if debug && !self.int_const_terms.contains_key(&value) {
                    safe_eprintln!(
                        "[N-O {}] No const term for {:?} = {}",
                        label,
                        arith_term,
                        value
                    );
                }
                if debug {
                    safe_eprintln!(
                        "[N-O {}] Evaluated {:?} = {} ({} reasons)",
                        label,
                        arith_term,
                        value,
                        reasons.len()
                    );
                }
                if let Some(&const_term) = self.int_const_terms.get(&value) {
                    // Skip trivially-true self-equalities: a bare constant
                    // (e.g., `10`) can appear both as an interface arith term
                    // and in int_const_terms, yielding arith_term == const_term.
                    if arith_term == const_term {
                        continue;
                    }
                    // SOUNDNESS (#mixed-uf-sort): symmetric to the Real path —
                    // never equate interface terms of different sorts by value
                    // alone (a Real term sharing an Int constant's value must not
                    // be merged with it).
                    if terms.sort(arith_term) != terms.sort(const_term) {
                        continue;
                    }
                    // #6846 + #8147: equalities with no arithmetic provenance
                    // OR with partially unjustified leaves are speculative.
                    // Without has_unjustified_int_leaf, a compound term like
                    // (+ tight_x free_u) is classified as "proved" because
                    // tight_x contributes reasons, masking free_u's unjustified
                    // model value. Gaussian elimination then overconstrains.
                    if reasons.is_empty()
                        || has_unjustified_int_leaf(terms, get_int_value_with_reasons, arith_term)
                    {
                        speculative_pairs.push((arith_term, const_term));
                        continue;
                    }
                    // #8742: Guard against self-evidencing reasons. When the
                    // ONLY reason for the bridge equality `lhs = rhs` is the
                    // equality atom itself (`(= lhs rhs) = true`), the reason
                    // is tautological — LIA has no independent arithmetic
                    // justification for the equality beyond SAT's assignment
                    // of the equality atom. Propagating this equality to EUF
                    // with a self-evidencing reason makes conflict learning
                    // produce tautological clauses that never backtrack the
                    // SAT decision that set the equality atom true. Route it
                    // through speculative pairs so NeedModelEqualities handles
                    // it explicitly at the SAT layer.
                    if reasons_are_self_evidencing(terms, arith_term, const_term, &reasons) {
                        if debug {
                            safe_eprintln!(
                                "[N-O {}] SKIP self-evidencing: {:?} = {:?} (reason is the equality atom itself)",
                                label,
                                arith_term,
                                const_term,
                            );
                        }
                        speculative_pairs.push((arith_term, const_term));
                        continue;
                    }
                    // Contradictory value guard: if this arith_term was
                    // previously propagated with a DIFFERENT const_term,
                    // the LIA model changed between N-O iterations. The old
                    // equality (e.g., sum=0) is already in EUF; propagating
                    // the new one (sum=10) would let EUF derive 0=10 →
                    // false-UNSAT. Skip to avoid the contradiction (#6846).
                    if let Some(&prev_const) = self.propagated_term_values.get(&arith_term) {
                        if prev_const != const_term {
                            if debug {
                                safe_eprintln!(
                                    "[N-O {}] SKIP contradictory: {:?} was {:?} now {:?}",
                                    label,
                                    arith_term,
                                    prev_const,
                                    const_term
                                );
                            }
                            continue;
                        }
                    }
                    let pair = (arith_term, const_term);
                    if self.propagated_interface_eqs.insert(pair) {
                        self.interface_trail
                            .push(InterfaceTrailEntry::PropagatedEq(arith_term, const_term));
                        // Record the value for contradictory-change detection.
                        if self
                            .propagated_term_values
                            .insert(arith_term, const_term)
                            .is_none()
                        {
                            self.interface_trail
                                .push(InterfaceTrailEntry::PropagatedValue(arith_term));
                        }
                        if debug {
                            safe_eprintln!(
                                "[N-O {}] Interface term {:?} = {} (const {:?}, {} reasons)",
                                label,
                                arith_term,
                                value,
                                const_term,
                                reasons.len()
                            );
                        }
                        // Deduplicate reasons by term to keep conflict clauses minimal.
                        reasons.sort_by_key(|r| r.term);
                        reasons.dedup_by_key(|r| r.term);
                        new_eqs.push(DiscoveredEquality::new(arith_term, const_term, reasons));
                    }
                }
            }
        }
        // Postcondition (#4714):
        for eq in &new_eqs {
            debug_assert!(
                eq.lhs != eq.rhs,
                "BUG: {label} evaluate_and_propagate returned self-equality ({:?} = {:?})",
                eq.lhs,
                eq.rhs
            );
        }
        (new_eqs, speculative_pairs)
    }

    /// Collect rational (Real) constants from a term and register them (#4915).
    /// Parallel to `collect_int_constants` but for Real-sorted constants.
    pub(crate) fn collect_real_constants(&mut self, terms: &TermStore, term: TermId) {
        let mut visited = HashSet::default();
        self.collect_real_constants_inner(terms, term, &mut visited);
    }

    /// Uses `stacker::maybe_grow` for stack safety on deeply nested terms (#8414).
    fn collect_real_constants_inner(
        &mut self,
        terms: &TermStore,
        term: TermId,
        visited: &mut HashSet<TermId>,
    ) {
        stacker::maybe_grow(
            CONST_COLLECT_STACK_RED_ZONE,
            CONST_COLLECT_STACK_SIZE,
            || {
                if !visited.insert(term) {
                    return;
                }
                match terms.get(term) {
                    TermData::Const(Constant::Rational(r))
                        if !self.real_const_terms.contains_key(&r.0) =>
                    {
                        self.real_const_terms.insert(r.0.clone(), term);
                        self.interface_trail
                            .push(InterfaceTrailEntry::RealConstTerm(r.0.clone()));
                    }
                    TermData::Const(Constant::Int(n)) => {
                        // Integer constants can appear in Real-sorted expressions
                        // (e.g., `(= x 2)` where x is Real is parsed as `(= x 2.0)`).
                        let rational = BigRational::from(n.clone());
                        if !self.real_const_terms.contains_key(&rational) {
                            self.real_const_terms.insert(rational.clone(), term);
                            self.interface_trail
                                .push(InterfaceTrailEntry::RealConstTerm(rational));
                        }
                    }
                    TermData::App(_, args) => {
                        for &arg in args {
                            self.collect_real_constants_inner(terms, arg, visited);
                        }
                    }
                    TermData::Not(inner) => {
                        self.collect_real_constants_inner(terms, *inner, visited)
                    }
                    TermData::Ite(c, t, e) => {
                        self.collect_real_constants_inner(terms, *c, visited);
                        self.collect_real_constants_inner(terms, *t, visited);
                        self.collect_real_constants_inner(terms, *e, visited);
                    }
                    _ => {}
                }
            },
        ) // stacker::maybe_grow
    }

    /// Evaluate Real-valued interface terms and return new equalities (#4915).
    ///
    /// Parallel to `evaluate_and_propagate` but uses rational arithmetic.
    /// See `evaluate_and_propagate` docs for empty-reason handling (#6846).
    pub(crate) fn evaluate_and_propagate_real(
        &mut self,
        terms: &TermStore,
        get_real_value_with_reasons: &impl Fn(TermId) -> Option<(BigRational, Vec<TheoryLit>)>,
        debug: bool,
        label: &str,
    ) -> (Vec<DiscoveredEquality>, Vec<(TermId, TermId)>) {
        let mut arith_terms: Vec<TermId> = self.interface_arith_terms.iter().copied().collect();
        arith_terms.sort_unstable(); // Deterministic iteration order (#3041)
        let mut new_eqs = Vec::new();
        let mut speculative_pairs = Vec::new();
        for arith_term in arith_terms {
            let mut reasons = Vec::new();
            if let Some(value) = evaluate_real_arith_term_with_reasons(
                terms,
                get_real_value_with_reasons,
                arith_term,
                &mut reasons,
            ) {
                if let Some(&const_term) = self.real_const_terms.get(&value) {
                    if arith_term == const_term {
                        continue;
                    }
                    // SOUNDNESS (#mixed-uf-sort): never equate two interface
                    // terms of different sorts merely because their numeric
                    // values coincide. An Int term and a Real term can share a
                    // value (`1` and `1.0`) yet are distinct interface variables;
                    // propagating `int_term = real_const` is a spurious cross-sort
                    // equality that yields a wrong UNSAT (and a downstream panic)
                    // for mixed Int/Real UF arguments such as `p (Int Real)`.
                    if terms.sort(arith_term) != terms.sort(const_term) {
                        continue;
                    }
                    // Filter out non-Boolean reason terms. NRA's McCormick
                    // refinement can produce bounds whose reasons reference
                    // bare Real/Int variables instead of Boolean assertion
                    // atoms. These can't map to SAT literals, causing partial
                    // conflict clauses dropped by soundness guard #3826.
                    reasons.retain(|r| {
                        (r.term.0 as usize) < terms.len()
                            && matches!(terms.sort(r.term), ay_core::Sort::Bool)
                    });
                    // #8147: same partially-justified guard as Int path.
                    if reasons.is_empty()
                        || has_unjustified_real_leaf(terms, get_real_value_with_reasons, arith_term)
                    {
                        speculative_pairs.push((arith_term, const_term));
                        continue;
                    }
                    // Contradictory value guard (parallel to Int path).
                    if let Some(&prev_const) = self.propagated_term_values.get(&arith_term) {
                        if prev_const != const_term {
                            if debug {
                                safe_eprintln!(
                                    "[N-O {}] SKIP contradictory real: {:?} was {:?} now {:?}",
                                    label,
                                    arith_term,
                                    prev_const,
                                    const_term
                                );
                            }
                            continue;
                        }
                    }
                    let pair = (arith_term, const_term);
                    if self.propagated_interface_eqs.insert(pair) {
                        self.interface_trail
                            .push(InterfaceTrailEntry::PropagatedEq(arith_term, const_term));
                        if self
                            .propagated_term_values
                            .insert(arith_term, const_term)
                            .is_none()
                        {
                            self.interface_trail
                                .push(InterfaceTrailEntry::PropagatedValue(arith_term));
                        }
                        if debug {
                            safe_eprintln!(
                                "[N-O {}] Real interface term {:?} = {} (const {:?}, {} reasons)",
                                label,
                                arith_term,
                                value,
                                const_term,
                                reasons.len()
                            );
                        }
                        reasons.sort_by_key(|r| r.term);
                        reasons.dedup_by_key(|r| r.term);
                        new_eqs.push(DiscoveredEquality::new(arith_term, const_term, reasons));
                    }
                }
            }
        }
        for eq in &new_eqs {
            debug_assert!(
                eq.lhs != eq.rhs,
                "BUG: {label} evaluate_and_propagate_real returned self-equality ({:?} = {:?})",
                eq.lhs,
                eq.rhs
            );
        }
        // speculative_pairs contains zero-reason equalities from line 435.
        // Callers route these through NeedModelEquality/NeedModelEqualities
        // (SAT-level decisions), matching the #6846 fix for the Int path.
        // See UfNraSolver::check() and combiner_check.rs:326-354.
        (new_eqs, speculative_pairs)
    }
}
