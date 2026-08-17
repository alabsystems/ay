// Copyright 2026 Andrew Yates
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0

//! Theory domain classification and semantic propagation dispatch.
//!
//! Classifies theory atoms by domain (Arithmetic, EUF, Array, BitVec, String, Unknown)
//! and dispatches semantic propagation verification to the appropriate theory-specific
//! verifier (LRA, EUF, combined ArrayEuf solver, or structural checks for BV/String).
//!
//! Prior to #4535, BV, array, and string domain literals were classified as Unknown
//! and silently accepted without any verification. Now each domain has explicit
//! verification: semantic checks where a fresh solver can re-verify (LRA, EUF, Array),
//! and structural checks where the theory solver architecture prevents independent
//! re-verification (BV bit-blasting, String lemma-based reasoning).
use ay_core::{Sort, Symbol, TermData, TermId, TermStore, TheoryLit, TheoryPropagation};

use super::euf::{verify_euf_conflict, verify_euf_propagation};
use super::structural::{verify_theory_conflict, verify_theory_propagation};
use super::VerificationError;
use crate::term_helpers::{is_uf_int_equality, is_uf_real_equality};

fn is_pure_arithmetic_term(terms: &TermStore, term: TermId) -> bool {
    match terms.get(term) {
        TermData::Const(c) => matches!(
            c,
            ay_core::Constant::Int(_) | ay_core::Constant::Rational(_)
        ),
        TermData::Var(_, _) => matches!(terms.sort(term), Sort::Int | Sort::Real),
        TermData::App(Symbol::Named(name), args) => match name.as_str() {
            "+" | "-" | "*" | "/" | "div" | "mod" | "abs" | "to_real" | "to_int" => {
                args.iter().all(|&arg| is_pure_arithmetic_term(terms, arg))
            }
            _ => false,
        },
        TermData::Ite(_, then_br, else_br) => {
            is_pure_arithmetic_term(terms, *then_br) && is_pure_arithmetic_term(terms, *else_br)
        }
        _ => false,
    }
}

fn is_int_linear_expr(terms: &TermStore, term: TermId) -> bool {
    match terms.get(term) {
        TermData::Const(ay_core::Constant::Int(_)) => true,
        TermData::Const(ay_core::Constant::Rational(_)) => false,
        TermData::Var(_, _) => matches!(terms.sort(term), Sort::Int),
        TermData::App(Symbol::Named(name), args) => match name.as_str() {
            "+" => args.iter().all(|&arg| is_int_linear_expr(terms, arg)),
            "-" if args.len() == 1 => is_int_linear_expr(terms, args[0]),
            "-" if args.len() == 2 => {
                is_int_linear_expr(terms, args[0]) && is_int_linear_expr(terms, args[1])
            }
            "*" if args.len() == 2 => {
                (is_int_constant(terms, args[0]) && is_int_linear_expr(terms, args[1]))
                    || (is_int_constant(terms, args[1]) && is_int_linear_expr(terms, args[0]))
            }
            _ => false,
        },
        _ => false,
    }
}

fn is_int_constant(terms: &TermStore, term: TermId) -> bool {
    matches!(terms.get(term), TermData::Const(ay_core::Constant::Int(_)))
}

fn is_int_linear_atom(terms: &TermStore, term: TermId) -> bool {
    match terms.get(term) {
        TermData::App(Symbol::Named(name), args)
            if matches!(name.as_str(), "<=" | "<" | ">=" | ">" | "=") =>
        {
            args.len() == 2
                && args.iter().all(|&arg| matches!(terms.sort(arg), Sort::Int))
                && args.iter().all(|&arg| is_int_linear_expr(terms, arg))
        }
        _ => false,
    }
}

fn propagation_is_int_linear(propagation: &TheoryPropagation, terms: &TermStore) -> bool {
    is_int_linear_atom(terms, propagation.literal.term)
        && propagation
            .reason
            .iter()
            .all(|lit| is_int_linear_atom(terms, lit.term))
}

// #8529: Used in all builds (verify_propagation_semantic is now release-enabled).
fn format_term_recursive(terms: &TermStore, term: TermId, depth: u32) -> String {
    if depth == 0 {
        return format!("{term:?}");
    }
    match terms.get(term) {
        TermData::Const(c) => format!("{c:?}"),
        TermData::Var(name, _) => name.clone(),
        TermData::App(sym, args) => {
            let arg_strs: Vec<String> = args
                .iter()
                .map(|&arg| format_term_recursive(terms, arg, depth - 1))
                .collect();
            format!("({} {})", sym.name(), arg_strs.join(" "))
        }
        TermData::Not(inner) => {
            format!("(not {})", format_term_recursive(terms, *inner, depth - 1))
        }
        other => format!("{other:?}"),
    }
}

/// Classify theory atoms as arithmetic, EUF, or unknown.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum TheoryDomain {
    Arithmetic,
    Euf,
    Array,
    BitVec,
    String,
    Unknown,
}

/// Check if a sort requires routing to a specialized theory domain.
///
/// Returns the specific domain for BV, String, and Array sorts.
/// Returns `None` for sorts handled by EUF/Arithmetic or unknown sorts
/// that have no dedicated verifier.
fn classify_sort_domain(sort: &Sort) -> Option<TheoryDomain> {
    match sort {
        Sort::BitVec(_) => Some(TheoryDomain::BitVec),
        Sort::String | Sort::Seq(_) | Sort::RegLan => Some(TheoryDomain::String),
        Sort::Array(_) => Some(TheoryDomain::Array),
        Sort::Bool | Sort::Int | Sort::Real | Sort::Uninterpreted(_) => None,
        Sort::FloatingPoint(_, _) | Sort::Datatype(_) => Some(TheoryDomain::Unknown),
        _ => Some(TheoryDomain::Unknown),
    }
}

/// Returns true if a sort requires a specialized theory verifier that is NOT
/// handled by EUF or Arithmetic solvers.
fn requires_specialized_theory_verifier(sort: &Sort) -> bool {
    classify_sort_domain(sort).is_some()
}

/// Check if a term involves bitvector operations or sorts.
fn term_has_bv_context(terms: &TermStore, term: TermId) -> bool {
    if matches!(terms.sort(term), Sort::BitVec(_)) {
        return true;
    }
    match terms.get(term) {
        TermData::App(Symbol::Named(name), _) => name.starts_with("bv"),
        _ => false,
    }
}

/// Check if a term involves string operations or sorts.
fn term_has_string_context(terms: &TermStore, term: TermId) -> bool {
    if matches!(terms.sort(term), Sort::String | Sort::RegLan | Sort::Seq(_)) {
        return true;
    }
    match terms.get(term) {
        TermData::App(Symbol::Named(name), _) => {
            name.starts_with("str.")
                || name == "str.++"
                || name == "re.range"
                || name.starts_with("re.")
                || name == "seq.unit"
        }
        TermData::Const(ay_core::Constant::String(_)) => true,
        _ => false,
    }
}

/// Whether a term actually CONTAINS native string/seq/regex theory content —
/// a `str.*`/`re.*`/`seq.*` application or a string literal — anywhere in its
/// subterm DAG.
///
/// A String/Seq/RegLan SORT alone deliberately does not count: without native
/// operations such a sort is just an opaque EUF equality carrier (the same
/// principle as `features::detect_sort_theory`, #9227), and conflicts over it
/// are exactly congruence-closure conflicts that `verify_euf_conflict` can
/// re-verify. Classifying them into the String domain sends them to the
/// structural string verifier, which cannot verify plain UF equalities; since
/// the #8595 fail-open removal such conflicts are then never learned and
/// trivially-UNSAT EUF queries over Seq-sorted carriers degrade to Unknown
/// (verification-consumer's UF-encoded `Seq<Int>` regression, 2026-07-05).
fn term_mentions_native_string_content(terms: &TermStore, term: TermId) -> bool {
    let mut visited: std::collections::HashSet<TermId> = std::collections::HashSet::new();
    let mut stack = vec![term];
    while let Some(t) = stack.pop() {
        if !visited.insert(t) {
            continue;
        }
        match terms.get(t) {
            TermData::App(Symbol::Named(name), args) => {
                if name.starts_with("str.") || name.starts_with("re.") || name.starts_with("seq.") {
                    return true;
                }
                stack.extend(args.iter().copied());
            }
            TermData::App(_, args) => stack.extend(args.iter().copied()),
            TermData::Const(ay_core::Constant::String(_)) => return true,
            TermData::Not(inner) => stack.push(*inner),
            TermData::Ite(c, a, b) => {
                stack.push(*c);
                stack.push(*a);
                stack.push(*b);
            }
            TermData::Let(bindings, body) => {
                for (_, v) in bindings {
                    stack.push(*v);
                }
                stack.push(*body);
            }
            TermData::Forall(_, body, _) | TermData::Exists(_, body, _) => stack.push(*body),
            _ => {}
        }
    }
    false
}

fn term_has_array_context(terms: &TermStore, term: TermId) -> bool {
    if matches!(terms.sort(term), Sort::Array(_)) {
        return true;
    }
    match terms.get(term) {
        TermData::App(Symbol::Named(name), args) => {
            if name == "select" || name == "store" {
                return true;
            }
            args.iter().any(|&arg| term_has_array_context(terms, arg))
        }
        TermData::Not(inner) => term_has_array_context(terms, *inner),
        TermData::Ite(c, then_br, else_br) => {
            term_has_array_context(terms, *c)
                || term_has_array_context(terms, *then_br)
                || term_has_array_context(terms, *else_br)
        }
        TermData::Let(bindings, body) => {
            bindings
                .iter()
                .any(|(_, value)| term_has_array_context(terms, *value))
                || term_has_array_context(terms, *body)
        }
        TermData::Forall(_, body, _) | TermData::Exists(_, body, _) => {
            term_has_array_context(terms, *body)
        }
        _ => false,
    }
}

/// Determine which theory domain a term belongs to.
///
/// Arithmetic: `<=`, `<`, `>=`, `>`, or `=`/`distinct` over Int/Real sorts.
/// EUF: `=`/`distinct` over uninterpreted or other non-arithmetic sorts,
/// or uninterpreted predicate applications.
/// BitVec: operations or equalities over BitVec-sorted terms.
/// String: operations or equalities over String/RegLan/Seq-sorted terms.
pub(super) fn classify_term_domain(terms: &TermStore, term: TermId) -> TheoryDomain {
    let mut t = term;
    // Unwrap NOT layers
    while let TermData::Not(inner) = terms.get(t) {
        t = *inner;
    }

    match terms.get(t) {
        TermData::App(Symbol::Named(name), args) => match name.as_str() {
            "<=" | "<" | ">=" | ">" => {
                if args.iter().any(|&arg| term_has_array_context(terms, arg)) {
                    TheoryDomain::Array
                } else {
                    TheoryDomain::Arithmetic
                }
            }
            "=" | "distinct" if args.len() == 2 => {
                // Equalities over select/store terms are array-domain even when the
                // element sort is arithmetic. Verifying them with the LRA solver
                // loses the array ROW axioms that justify the propagation.
                if term_has_array_context(terms, args[0]) || term_has_array_context(terms, args[1])
                {
                    return TheoryDomain::Array;
                }
                let arg_sort = terms.sort(args[0]);
                match arg_sort {
                    Sort::Int | Sort::Real => {
                        if is_pure_arithmetic_term(terms, args[0])
                            && is_pure_arithmetic_term(terms, args[1])
                        {
                            TheoryDomain::Arithmetic
                        } else {
                            TheoryDomain::Unknown
                        }
                    }
                    Sort::Bool => TheoryDomain::Unknown,
                    Sort::Array(_) => TheoryDomain::Array,
                    Sort::BitVec(_) => TheoryDomain::BitVec,
                    Sort::String | Sort::RegLan => TheoryDomain::String,
                    // An equality over Seq-SORTED terms is only a string/seq-
                    // theory atom when a side actually contains native
                    // string/seq content. Otherwise the sort is an opaque EUF
                    // carrier (UF-encoded sequences, e.g. verification-consumer's Seq<Int>)
                    // and the conflict is verifiable — and thus learnable — by
                    // congruence closure. EUF-UNSAT implies UNSAT in every
                    // stronger theory, so this reroute is sound; the previous
                    // String classification sent such conflicts to the
                    // structural string verifier, which fails on plain UF
                    // equalities, and since the #8595 fail-open removal they
                    // were never learned — degrading valid UNSATs to Unknown.
                    Sort::Seq(_) => {
                        if term_mentions_native_string_content(terms, args[0])
                            || term_mentions_native_string_content(terms, args[1])
                        {
                            TheoryDomain::String
                        } else {
                            TheoryDomain::Euf
                        }
                    }
                    _ if requires_specialized_theory_verifier(arg_sort) => TheoryDomain::Unknown,
                    _ => {
                        // Check if either argument is an array operation (select/store).
                        // Array theory propagations (e.g., ROW2) involve equalities over
                        // element-sorted terms that require array axioms to verify, not
                        // just EUF congruence closure.
                        if is_array_operation(terms, args[0]) || is_array_operation(terms, args[1])
                        {
                            TheoryDomain::Array
                        } else {
                            TheoryDomain::Euf
                        }
                    }
                }
            }
            // BV operations: bvadd, bvand, bvult, bvslt, etc.
            _ if name.starts_with("bv") => TheoryDomain::BitVec,
            // String operations: str.len, str.++, str.contains, etc.
            _ if name.starts_with("str.") || name.starts_with("re.") || name == "seq.unit" => {
                TheoryDomain::String
            }
            _ => {
                let result_sort = terms.sort(t);
                // Route to specific domain based on sort. Seq-sorted results
                // only classify as String-domain when native string/seq
                // content is actually present; a bare UF over the Seq carrier
                // sort is EUF (see `term_mentions_native_string_content`).
                if let Some(domain) = classify_sort_domain(result_sort) {
                    if domain != TheoryDomain::String
                        || !matches!(result_sort, Sort::Seq(_))
                        || term_mentions_native_string_content(terms, t)
                    {
                        return domain;
                    }
                }
                let arg_requires_specialized = |arg: TermId| {
                    let arg_sort = terms.sort(arg);
                    match classify_sort_domain(arg_sort) {
                        // Seq-SORTED arg without native string content is an
                        // opaque EUF carrier, not a string-theory operand.
                        Some(TheoryDomain::String) if matches!(arg_sort, Sort::Seq(_)) => {
                            term_mentions_native_string_content(terms, arg)
                        }
                        Some(_) => true,
                        None => false,
                    }
                };
                if args.iter().any(|&arg| arg_requires_specialized(arg)) {
                    // Check if any arg is BV or String specifically
                    if args.iter().any(|&arg| term_has_bv_context(terms, arg)) {
                        return TheoryDomain::BitVec;
                    }
                    if args.iter().any(|&arg| term_has_string_context(terms, arg)) {
                        return TheoryDomain::String;
                    }
                    TheoryDomain::Unknown
                } else {
                    TheoryDomain::Euf
                }
            }
        },
        _ => TheoryDomain::Unknown,
    }
}

// #8529: Used in all builds (verify_propagation_semantic is now release-enabled).
fn propagation_has_arithmetic_context(terms: &TermStore, propagation: &TheoryPropagation) -> bool {
    matches!(
        classify_term_domain(terms, propagation.literal.term),
        TheoryDomain::Arithmetic
    ) || propagation.reason.iter().any(|lit| {
        matches!(
            classify_term_domain(terms, lit.term),
            TheoryDomain::Arithmetic
        )
    })
}

/// Check if a term is an array operation (select or store).
fn is_array_operation(terms: &TermStore, term: TermId) -> bool {
    matches!(
        terms.get(term),
        TermData::App(Symbol::Named(name), _) if name == "select" || name == "store"
    )
}

/// Classify the domain of an entire propagation.
///
/// Array propagations often contain EUF-domain reason literals (index equalities/
/// disequalities). When any term is Array-domain, promote the whole propagation
/// to Array since the combined ArrayEuf verifier handles both.
// #8529: Used in all builds (verify_propagation_semantic is now release-enabled).
pub(crate) fn classify_propagation_domain(
    terms: &TermStore,
    propagation: &TheoryPropagation,
) -> TheoryDomain {
    let prop_domain = classify_term_domain(terms, propagation.literal.term);
    if prop_domain == TheoryDomain::Unknown {
        return TheoryDomain::Unknown;
    }

    let mut result = prop_domain;
    for lit in &propagation.reason {
        let d = classify_term_domain(terms, lit.term);
        match (result, d) {
            // Same domain — no change
            (a, b) if a == b => {}
            // Any Unknown makes the whole thing Unknown
            (_, TheoryDomain::Unknown) => return TheoryDomain::Unknown,
            // Array + EUF promotes to Array (combined solver handles both)
            (TheoryDomain::Array, TheoryDomain::Euf) | (TheoryDomain::Euf, TheoryDomain::Array) => {
                result = TheoryDomain::Array
            }
            // Array + Arithmetic: the combined solver handles integer index reasoning
            (TheoryDomain::Array, TheoryDomain::Arithmetic)
            | (TheoryDomain::Arithmetic, TheoryDomain::Array) => result = TheoryDomain::Array,
            // BV + EUF stays BV (BV solver handles equality reasoning)
            (TheoryDomain::BitVec, TheoryDomain::Euf)
            | (TheoryDomain::Euf, TheoryDomain::BitVec) => result = TheoryDomain::BitVec,
            // String + EUF stays String (String solver handles equality reasoning)
            (TheoryDomain::String, TheoryDomain::Euf)
            | (TheoryDomain::Euf, TheoryDomain::String) => result = TheoryDomain::String,
            // String + Arithmetic stays String (length constraints involve arithmetic)
            (TheoryDomain::String, TheoryDomain::Arithmetic)
            | (TheoryDomain::Arithmetic, TheoryDomain::String) => result = TheoryDomain::String,
            // All other mixed domains are Unknown
            _ => return TheoryDomain::Unknown,
        }
    }

    result
}

/// Verify an LRA propagation by checking that reason ∧ ¬propagated is UNSAT.
///
/// Two-tier verification:
/// 1. **Fast algebraic check**: For single-variable bound-chain propagations
///    (the common case), verify soundness with O(1) rational arithmetic.
///    This avoids the expensive fresh-solver approach for ~80% of propagations.
/// 2. **Full solver fallback**: For multi-variable propagations where the
///    algebraic check is inconclusive, create a fresh LRA solver.
///
/// Reference: Z3 does not re-verify propagations at all — its bound propagation
/// logic is considered correct by construction. This verification exists because
/// of AY-specific bug #6242/#6582 where deferred-reason materialization could
/// produce stale reasons after simplex basis changes.
// #8529: Used in all builds (verify_propagation_semantic is now release-enabled).
pub(super) fn verify_lra_propagation(
    propagation: &TheoryPropagation,
    terms: &TermStore,
) -> Result<(), VerificationError> {
    use ay_core::{TheoryResult, TheorySolver};
    use ay_lra::LraSolver;

    verify_theory_propagation(propagation)?;

    // Fast path: algebraic verification for bound-chain propagations.
    // When the propagated atom is a single-variable bound, check if any
    // reason atom individually implies it via rational comparison.
    // This avoids creating a full LRA solver for the common case where
    // a tighter bound on variable x implies a weaker bound on the same x.
    // Covers single-reason chains and multi-reason interval propagations.
    if let Some(result) = try_algebraic_verify(propagation, terms) {
        ay_lia::instrument::bump_verify_lra_algebraic();
        return result;
    }

    ay_lia::instrument::bump_verify_fresh_lra_solve();
    let mut verify_lra = LraSolver::new(terms);
    // #8257: Enable verification mode to skip post-simplex propagation
    // (implied bounds, bound propagations). The verification solver only
    // needs the simplex SAT/UNSAT result, not bound derivations.
    verify_lra.set_verification_mode();

    for lit in &propagation.reason {
        verify_lra.assert_literal(lit.term, lit.value);
    }

    verify_lra.assert_literal(propagation.literal.term, !propagation.literal.value);

    match verify_lra.check() {
        TheoryResult::Unsat(_) | TheoryResult::UnsatWithFarkas(_) => Ok(()),
        TheoryResult::Sat => {
            if crate::theory_debug_flags::debug_verify() {
                let propagated = format_term_recursive(terms, propagation.literal.term, 6);
                let reasons: Vec<String> = propagation
                    .reason
                    .iter()
                    .map(|lit| {
                        format!(
                            "{}={}",
                            format_term_recursive(terms, lit.term, 6),
                            lit.value
                        )
                    })
                    .collect();
                tracing::error!(
                    propagated_term = ?propagation.literal.term,
                    propagated_value = propagation.literal.value,
                    propagated_expr = %propagated,
                    reason = ?reasons,
                    "LRA propagation semantic check found a SAT counterexample"
                );
            }
            Err(VerificationError::PropagationNotImplied {
                term: propagation.literal.term,
                value: propagation.literal.value,
            })
        }
        // Unknown: the standalone LRA solver cannot verify this propagation.
        // This is expected for cross-theory (Nelson-Oppen) propagations where
        // LRA alone cannot reproduce the implication. Treat as "skip" not "fail".
        TheoryResult::Unknown => Ok(()),
        // Split/lemma requests: the standalone solver needs more information than
        // a single-theory check can provide. Skip rather than fail.
        TheoryResult::NeedSplit(_)
        | TheoryResult::NeedDisequalitySplit(_)
        | TheoryResult::NeedExpressionSplit(_)
        | TheoryResult::NeedExpressionSplits(_)
        | TheoryResult::NeedStringLemma(_)
        | TheoryResult::NeedLemmas(_)
        | TheoryResult::NeedModelEquality(_)
        | TheoryResult::NeedModelEqualities(_) => Ok(()),
        // All current TheoryResult variants handled above (#4906, #6149).
        // Wildcard covers future variants from #[non_exhaustive].
        _ => unreachable!("unhandled TheoryResult variant — update this match"),
    }
}

/// Verify an LIA propagation by checking that reason ∧ ¬propagated is UNSAT
/// under integer arithmetic.
///
/// This mirrors `verify_lra_propagation`, but uses `LiaSolver` so integer-gap
/// implications remain valid. For example, `not (1 <= x)` entails `x <= 0`
/// over `Int`, but not over `Real`. Routing such propagations through the LRA
/// verifier caused valid integer bound propagations to be rejected (#6242).
// #8529: Used in all builds (verify_propagation_semantic is now release-enabled).
pub(super) fn verify_lia_propagation(
    propagation: &TheoryPropagation,
    terms: &TermStore,
) -> Result<(), VerificationError> {
    use ay_core::{TheoryResult, TheorySolver};
    use ay_lia::LiaSolver;

    verify_theory_propagation(propagation)?;

    ay_lia::instrument::bump_verify_fresh_lia_solve();
    let mut verify_lia = LiaSolver::new(terms);
    for lit in &propagation.reason {
        verify_lia.assert_literal(lit.term, lit.value);
    }
    verify_lia.assert_literal(propagation.literal.term, !propagation.literal.value);

    match verify_lia.check() {
        TheoryResult::Unsat(_) | TheoryResult::UnsatWithFarkas(_) => Ok(()),
        TheoryResult::Sat => {
            if crate::theory_debug_flags::debug_verify() {
                let propagated = format_term_recursive(terms, propagation.literal.term, 6);
                let reasons: Vec<String> = propagation
                    .reason
                    .iter()
                    .map(|lit| {
                        format!(
                            "{}={}",
                            format_term_recursive(terms, lit.term, 6),
                            lit.value
                        )
                    })
                    .collect();
                tracing::error!(
                    propagated_term = ?propagation.literal.term,
                    propagated_value = propagation.literal.value,
                    propagated_expr = %propagated,
                    reason = ?reasons,
                    "LIA propagation semantic check found a SAT counterexample"
                );
            }
            Err(VerificationError::PropagationNotImplied {
                term: propagation.literal.term,
                value: propagation.literal.value,
            })
        }
        // NeedLemmas/Unknown/splits mean the standalone LIA verifier cannot
        // finish cheaply. This mirrors the existing LIA conflict verifier:
        // keep the soundness gate fail-closed for concrete SAT counterexamples
        // while avoiding false rejections for incomplete verification.
        _ => Ok(()),
    }
}

/// Coefficients, constant, is_le flag, strict flag for a parsed linear inequality.
// #8529: Used in all builds (verify_propagation_semantic is now release-enabled).
type LinearIneq = (
    Vec<(TermId, num_rational::BigRational)>,
    num_rational::BigRational,
    bool,
    bool,
);

/// Parse a linear inequality atom into (linear_expr_coeffs, constant, is_le, strict).
///
/// Returns None if the atom structure is not a simple linear inequality.
/// For an atom `(<= (+ (* c1 x1) ... (* cn xn) k) 0)` or `(>= ...)`:
///   - coeffs: [(var_term, coeff), ...]
///   - constant: k
///   - is_le: true for <=/<, false for >=/>
///   - strict: true for </>
// #8529: Used in all builds (verify_propagation_semantic is now release-enabled).
fn parse_linear_ineq_atom(terms: &TermStore, atom: TermId, value: bool) -> Option<LinearIneq> {
    use num_rational::BigRational;

    let (inner, negated) = match terms.get(atom) {
        TermData::Not(inner) => (*inner, true),
        _ => (atom, false),
    };

    let effective_value = if negated { !value } else { value };

    match terms.get(inner) {
        TermData::App(Symbol::Named(name), args) => {
            let (is_le_base, strict_base, is_eq) = match name.as_str() {
                "<=" => (true, false, false),
                "<" => (true, true, false),
                ">=" => (false, false, false),
                ">" => (false, true, false),
                "=" => (true, false, true), // equality: treat as <= for now
                _ => return None,
            };
            // For equality with value=false (disequality), we can't derive
            // useful bounds algebraically.
            if is_eq && !effective_value {
                return None;
            }
            if args.len() != 2 {
                return None;
            }

            // For value=false: negate the comparison.
            // ¬(x <= k) => x > k  => is_le=false, strict=true
            // ¬(x < k)  => x >= k => is_le=false, strict=false
            // ¬(x >= k) => x < k  => is_le=true, strict=true
            // ¬(x > k)  => x <= k => is_le=true, strict=false
            let (is_le, strict) = if effective_value {
                (is_le_base, strict_base)
            } else {
                (!is_le_base, !strict_base)
            };

            // Extract: lhs OP rhs => (lhs - rhs) OP 0
            let lhs = args[0];
            let rhs = args[1];

            let mut coeffs = Vec::new();
            let mut constant = BigRational::new(0.into(), 1.into());

            collect_linear_terms(
                terms,
                lhs,
                &BigRational::new(1.into(), 1.into()),
                &mut coeffs,
                &mut constant,
            )?;
            collect_linear_terms(
                terms,
                rhs,
                &BigRational::new((-1).into(), 1.into()),
                &mut coeffs,
                &mut constant,
            )?;

            Some((coeffs, constant, is_le, strict))
        }
        _ => None,
    }
}

/// Collect linear terms from an arithmetic expression.
/// Returns None if unsupported structure is encountered.
// #8529: Used in all builds (verify_propagation_semantic is now release-enabled).
fn collect_linear_terms(
    terms: &TermStore,
    term: TermId,
    scale: &num_rational::BigRational,
    coeffs: &mut Vec<(TermId, num_rational::BigRational)>,
    constant: &mut num_rational::BigRational,
) -> Option<()> {
    use ay_core::Constant;
    use num_rational::BigRational;

    match terms.get(term) {
        TermData::Const(Constant::Int(n)) => {
            *constant += scale * BigRational::new(n.clone(), 1.into());
            Some(())
        }
        TermData::Const(Constant::Rational(r)) => {
            *constant += scale * &r.0;
            Some(())
        }
        TermData::Var(_, _) => {
            coeffs.push((term, scale.clone()));
            Some(())
        }
        TermData::App(Symbol::Named(name), args) => match name.as_str() {
            "+" => {
                for &arg in args.iter() {
                    collect_linear_terms(terms, arg, scale, coeffs, constant)?;
                }
                Some(())
            }
            "-" if args.len() == 1 => {
                let neg_scale = -scale.clone();
                collect_linear_terms(terms, args[0], &neg_scale, coeffs, constant)
            }
            "-" if args.len() == 2 => {
                collect_linear_terms(terms, args[0], scale, coeffs, constant)?;
                let neg_scale = -scale.clone();
                collect_linear_terms(terms, args[1], &neg_scale, coeffs, constant)
            }
            "*" if args.len() == 2 => {
                // Only handle constant * variable or constant * constant.
                let c0 = extract_constant(terms, args[0]);
                let c1 = extract_constant(terms, args[1]);
                match (c0, c1) {
                    (Some(c), None) => {
                        let new_scale = scale * &c;
                        collect_linear_terms(terms, args[1], &new_scale, coeffs, constant)
                    }
                    (None, Some(c)) => {
                        let new_scale = scale * &c;
                        collect_linear_terms(terms, args[0], &new_scale, coeffs, constant)
                    }
                    (Some(c0), Some(c1)) => {
                        *constant += scale * &c0 * &c1;
                        Some(())
                    }
                    (None, None) => None, // non-linear
                }
            }
            _ => None,
        },
        _ => None,
    }
}

fn extract_constant(terms: &TermStore, term: TermId) -> Option<num_rational::BigRational> {
    use ay_core::Constant;
    use num_rational::BigRational;
    match terms.get(term) {
        TermData::Const(Constant::Int(n)) => Some(BigRational::new(n.clone(), 1.into())),
        TermData::Const(Constant::Rational(r)) => Some(r.0.clone()),
        TermData::App(Symbol::Named(name), args) if name.as_str() == "-" && args.len() == 1 => {
            extract_constant(terms, args[0]).map(|c| -c)
        }
        _ => None,
    }
}

/// Try to verify an LRA propagation algebraically without creating a solver.
///
/// For propagations where all atoms (reason + propagated) reference the same
/// single variable, verify soundness with O(n) rational arithmetic instead
/// of creating a fresh LRA solver. Returns:
/// - Some(Ok(())) if verified sound
/// - Some(Err(_)) if verified unsound
/// - None if the algebraic check is inconclusive (fall through to solver)
///
/// Handles the common cases:
/// 1. Single reason, single variable (bound chain: x<=3 => x<=5)
/// 2. Multiple reasons, all on the same variable (interval propagation)
// #8529: Used in all builds (verify_propagation_semantic is now release-enabled).
fn try_algebraic_verify(
    propagation: &TheoryPropagation,
    terms: &TermStore,
) -> Option<Result<(), VerificationError>> {
    use num_traits::{Signed, Zero};

    // Parse the propagated atom.
    let prop_parsed =
        parse_linear_ineq_atom(terms, propagation.literal.term, propagation.literal.value)?;
    let (prop_coeffs, prop_const, prop_is_le, prop_strict) = prop_parsed;

    // Filter zero-coefficient variables.
    let prop_coeffs: Vec<_> = prop_coeffs
        .into_iter()
        .filter(|(_, c)| !c.is_zero())
        .collect();
    if prop_coeffs.is_empty() {
        return None;
    }

    // === Path 1: Single-variable propagation ===
    if prop_coeffs.len() == 1 {
        let (prop_var, ref prop_coeff) = prop_coeffs[0];
        let prop_bound = -&prop_const / prop_coeff;
        let prop_upper =
            (prop_is_le && prop_coeff.is_positive()) || (!prop_is_le && prop_coeff.is_negative());

        // Helper to check if a reason atom is a true equality.
        let check_eq = |reason: &TheoryLit| -> bool {
            if !reason.value {
                return false;
            }
            let inner = match terms.get(reason.term) {
                TermData::Not(_) => return false,
                _ => reason.term,
            };
            matches!(terms.get(inner), TermData::App(Symbol::Named(name), args) if name.as_str() == "=" && args.len() == 2)
        };

        // We only need ONE reason to imply the propagated bound for soundness.
        for reason in &propagation.reason {
            let reason_parsed = match parse_linear_ineq_atom(terms, reason.term, reason.value) {
                Some(p) => p,
                None => continue,
            };
            let (reason_coeffs, reason_const, reason_is_le, reason_strict) = reason_parsed;

            if reason_coeffs.len() != 1 {
                continue;
            }
            let (reason_var, ref reason_coeff) = reason_coeffs[0];
            if reason_var != prop_var || reason_coeff.is_zero() {
                continue;
            }

            let reason_bound = -&reason_const / reason_coeff;
            let reason_upper = (reason_is_le && reason_coeff.is_positive())
                || (!reason_is_le && reason_coeff.is_negative());

            // For equality reasons, check both directions: the equality
            // (= x k, true) provides both x <= k and x >= k.
            let is_eq = check_eq(reason);

            let check_implied = |r_upper: bool| -> bool {
                if r_upper && prop_upper {
                    reason_bound < prop_bound
                        || (reason_bound == prop_bound && (reason_strict || !prop_strict))
                } else if !r_upper && !prop_upper {
                    reason_bound > prop_bound
                        || (reason_bound == prop_bound && (reason_strict || !prop_strict))
                } else {
                    // MIXED DIRECTIONS (upper reason vs lower propagation, or
                    // vice versa): a one-sided reason can NEVER entail a bound
                    // in the opposite direction — `(-inf, b_r]` is never a
                    // subset of `[b_p, +inf)`, and symmetrically. So the fast
                    // path must decline and let the full solver check decide.
                    //
                    // SOUNDNESS (#lra-fastpath-mixed-direction): these two
                    // branches previously returned `reason_bound < prop_bound`
                    // / `reason_bound > prop_bound`, which tests whether
                    // `reason AND prop` is UNSATISFIABLE — the OPPOSITE of
                    // entailment. Concretely, reason `x <= 3` was accepted as
                    // entailing propagation `x >= 5` (3 < 5), and equality
                    // reasons hit it too (`x = 3` "entails" `x >= 5` via the
                    // upper half). That is a FALSE ACCEPT inside the very gate
                    // that exists to catch unsound implied-bound propagations
                    // (see mod.rs: promoted to all builds after unsound
                    // propagations caused false SAT on QF_LRA synched.base).
                    // Declining is strictly conservative: the caller falls
                    // through to the fresh-LRA-solver check, which decides
                    // genuinely-entailed cases correctly.
                    false
                }
            };

            if check_implied(reason_upper) {
                return Some(Ok(()));
            }
            // For equalities, also check the opposite direction.
            if is_eq && check_implied(!reason_upper) {
                return Some(Ok(()));
            }
        }
        return None;
    }

    // === Path 2: Multi-variable compound propagation ===
    // For propagated atom: sum(c_i * x_i) + k OP 0
    // Each reason must be a single-variable bound. Collect the tightest
    // bound on each variable in the needed direction, then check if the
    // sum of scaled reason bounds implies the propagated constraint.
    //
    // For each variable x_i with coefficient c_i in the propagated expression:
    //   - If prop_is_le (upper bound on expression):
    //     - c_i > 0: need upper bound on x_i (tightest x_i <= b_i)
    //     - c_i < 0: need lower bound on x_i (tightest x_i >= b_i)
    //   - If !prop_is_le (lower bound on expression):
    //     - c_i > 0: need lower bound on x_i (tightest x_i >= b_i)
    //     - c_i < 0: need upper bound on x_i (tightest x_i <= b_i)
    //
    // Then check: sum(c_i * b_i) + k OP 0
    use ay_core::kani_compat::DetHashMap as HashMap;
    let mut var_bounds: HashMap<TermId, (num_rational::BigRational, bool)> = HashMap::default();

    // Parse all reason atoms and collect per-variable bounds.
    // Helper: check if a reason atom is an equality (provides both directions).
    let is_equality_reason = |reason: &TheoryLit| -> bool {
        if !reason.value {
            return false;
        }
        let inner = match terms.get(reason.term) {
            TermData::Not(_) => return false, // negated equality is disequality
            _ => reason.term,
        };
        matches!(terms.get(inner), TermData::App(Symbol::Named(name), args) if name.as_str() == "=" && args.len() == 2)
    };

    for reason in &propagation.reason {
        let reason_parsed = match parse_linear_ineq_atom(terms, reason.term, reason.value) {
            Some(p) => p,
            None => continue,
        };
        let (reason_coeffs, reason_const, reason_is_le, reason_strict) = reason_parsed;

        if reason_coeffs.len() != 1 {
            continue;
        }
        let (reason_var, ref reason_coeff) = reason_coeffs[0];
        if reason_coeff.is_zero() {
            continue;
        }

        let reason_bound = -&reason_const / reason_coeff;
        let reason_upper = (reason_is_le && reason_coeff.is_positive())
            || (!reason_is_le && reason_coeff.is_negative());

        // For equality reasons (= x k, true), the bound applies in BOTH
        // directions (upper and lower). For inequalities, only one direction.
        let provides_both_directions = is_equality_reason(reason);

        // Determine if this reason provides a bound in the needed direction
        // for this variable in the propagated expression.
        let prop_coeff_for_var = prop_coeffs
            .iter()
            .find(|(v, _)| *v == reason_var)
            .map(|(_, c)| c);
        let Some(prop_c) = prop_coeff_for_var else {
            continue;
        };

        // Determine needed direction: for prop_is_le, positive coeff needs
        // upper bound, negative coeff needs lower bound.
        let need_upper =
            (prop_is_le && prop_c.is_positive()) || (!prop_is_le && prop_c.is_negative());

        // Skip if this reason doesn't provide the needed bound direction.
        // Exception: equalities provide both directions.
        if reason_upper != need_upper && !provides_both_directions {
            continue;
        }

        // Keep the tightest bound (smallest for upper, largest for lower).
        var_bounds
            .entry(reason_var)
            .and_modify(|(existing, existing_strict)| {
                let tighter = if need_upper {
                    &reason_bound < existing
                        || (&reason_bound == existing && reason_strict && !*existing_strict)
                } else {
                    &reason_bound > existing
                        || (&reason_bound == existing && reason_strict && !*existing_strict)
                };
                if tighter {
                    *existing = reason_bound.clone();
                    *existing_strict = reason_strict;
                }
            })
            .or_insert((reason_bound, reason_strict));
    }

    // Check if all variables in the propagated expression have a bound.
    if var_bounds.len() < prop_coeffs.len() {
        return None; // Missing bounds for some variables
    }

    // Compute: sum(c_i * b_i) + k and check if it satisfies the propagated constraint.
    let mut sum = prop_const;
    let mut any_strict_reason = false;
    for (var, coeff) in &prop_coeffs {
        let (bound, strict) = var_bounds.get(var)?;
        sum += coeff * bound;
        if *strict {
            any_strict_reason = true;
        }
    }

    // The propagated constraint is: sum OP 0
    // For is_le: sum <= 0 (or sum < 0 if strict)
    // For !is_le: sum >= 0 (or sum > 0 if strict)
    let implied = if prop_is_le {
        sum.is_negative() || (sum.is_zero() && (any_strict_reason || !prop_strict))
    } else {
        sum.is_positive() || (sum.is_zero() && (any_strict_reason || !prop_strict))
    };

    if implied {
        return Some(Ok(()));
    }

    None
}

/// Verify an array propagation by checking that reason ∧ ¬propagated is UNSAT.
///
/// Uses the combined ArrayEuf solver since array propagations involve both
/// array axioms (ROW1/ROW2) and EUF congruence closure for equality reasoning.
/// This closes the verification gap documented in #4535 for array propagations.
// #8529: Used in all builds (verify_propagation_semantic is now release-enabled).
pub(super) fn verify_array_propagation(
    propagation: &TheoryPropagation,
    terms: &TermStore,
) -> Result<(), VerificationError> {
    use crate::combined_solvers::combiner::TheoryCombiner;
    use ay_core::TheorySolver;

    verify_theory_propagation(propagation)?;
    let has_arithmetic_context = propagation_has_arithmetic_context(terms, propagation);

    let mut verify_solver = TheoryCombiner::array_euf(terms);

    // Register every atom BEFORE asserting (#soundness-qf-ax-swap).
    // `ArraySolver::assert_literal` only records the assignment; the
    // select/store subterm walk that arms ROW1/ROW2 axiom instantiation
    // happens in `register_atom`. Without registration the fresh verifier
    // sees no array structure, vacuously answers Sat for valid
    // read-over-store propagations, and the caller then DROPS the theory's
    // propagation — silencing the level-0 conflict that proves unsat and
    // letting the search finalize a wrong SAT (QF_AX swap family).
    for lit in &propagation.reason {
        verify_solver.register_atom(lit.term);
    }
    verify_solver.register_atom(propagation.literal.term);

    // Assert all reason literals
    for lit in &propagation.reason {
        verify_solver.assert_literal(lit.term, lit.value);
    }

    // Assert negation of the propagated literal
    verify_solver.assert_literal(propagation.literal.term, !propagation.literal.value);

    // If reason ∧ ¬propagated is UNSAT, then reason ⊨ propagated (valid).
    // The check case-splits on requested model equalities (bounded) so that
    // entailments whose derivation is insensitive to an undecided index pair
    // are still recognized (#soundness-qf-ax-swap): the one-shot check used
    // to surface `NeedModelEqualities` for an IRRELEVANT undecided pair and
    // the propagation was rejected — dropping the theory's level-0 refutation
    // and letting the swap family finalize a wrong SAT.
    match array_entailment_check_with_splits(&mut verify_solver, terms, ARRAY_VERIFY_SPLIT_DEPTH) {
        ArrayEntailVerdict::Entailed => Ok(()),
        ArrayEntailVerdict::NotEntailed | ArrayEntailVerdict::SplitUnconfirmed
            if has_arithmetic_context =>
        {
            tracing::debug!(
                term = ?propagation.literal.term,
                value = propagation.literal.value,
                "array propagation verification inconclusive \
                 (standalone ArrayEuf solver lacks arithmetic context)"
            );
            Ok(())
        }
        ArrayEntailVerdict::NotEntailed => Err(VerificationError::PropagationNotImplied {
            term: propagation.literal.term,
            value: propagation.literal.value,
        }),
        // The solver demanded case splits and they could not all be resolved
        // to Entailed. Pre-split semantics rejected every pure-array
        // NeedModelEquality outcome; the split driver only rescues the
        // fully-resolved entailments (#soundness-qf-ax-swap), so anything
        // less stays fail-closed here — accepting it would admit
        // non-entailed propagations whenever the requested equality atom
        // happens not to be interned.
        ArrayEntailVerdict::SplitUnconfirmed => Err(VerificationError::PropagationNotImplied {
            term: propagation.literal.term,
            value: propagation.literal.value,
        }),
        // Inconclusive (top-level Unknown / lemma requests): matches the
        // long-standing optimistic policy for Unknown/NeedLemmas.
        ArrayEntailVerdict::Inconclusive => Ok(()),
    }
}

/// Maximum model-equality case-split depth for array propagation verification.
const ARRAY_VERIFY_SPLIT_DEPTH: usize = 8;

/// Verdict of the split-driven array entailment check.
enum ArrayEntailVerdict {
    /// reason ∧ ¬propagated is UNSAT under every case split — the
    /// propagation is definitively implied.
    Entailed,
    /// A case was found where reason ∧ ¬propagated is satisfiable — the
    /// reason set does NOT entail the propagated literal.
    NotEntailed,
    /// The solver could not decide at the top level (lemma requests or
    /// Unknown), without any case split being demanded.
    Inconclusive,
    /// The solver demanded model-equality case splits and they could not all
    /// be resolved to `Entailed` (missing interned equality atom, exhausted
    /// depth budget, or an undecided branch). Distinct from `Inconclusive`
    /// so the pure-array caller can stay fail-closed on it.
    SplitUnconfirmed,
}

/// Drive `TheoryCombiner::array_euf` to a definitive verdict by case-splitting
/// on requested model equalities (#soundness-qf-ax-swap).
///
/// The standalone array+EUF combiner reports `NeedModelEquality(s)` when it
/// wants a SAT-level decision on an undecided index pair. During propagation
/// verification there is no SAT solver to decide, but entailment can still be
/// established by checking BOTH polarities: reason ∧ ¬prop is unsat iff it is
/// unsat under `(= a b)` AND under `(not (= a b))`. Splits reuse the already
/// interned equality atom (`find_eq`); a request whose atom does not exist is
/// left unresolved (`Inconclusive`), never guessed.
fn array_entailment_check_with_splits(
    verify_solver: &mut crate::combined_solvers::combiner::TheoryCombiner<'_>,
    terms: &TermStore,
    depth: usize,
) -> ArrayEntailVerdict {
    use ay_core::{TheoryResult, TheorySolver};

    match verify_solver.check() {
        TheoryResult::Unsat(_) | TheoryResult::UnsatWithFarkas(_) => ArrayEntailVerdict::Entailed,
        TheoryResult::Sat => ArrayEntailVerdict::NotEntailed,
        TheoryResult::NeedModelEquality(req) => {
            split_on_model_equality_requests(verify_solver, terms, depth, &[req])
        }
        TheoryResult::NeedModelEqualities(reqs) => {
            split_on_model_equality_requests(verify_solver, terms, depth, &reqs)
        }
        // Unknown / lemma / split requests: cannot decide here.
        _ => ArrayEntailVerdict::Inconclusive,
    }
}

/// Case-split helper for [`array_entailment_check_with_splits`].
fn split_on_model_equality_requests(
    verify_solver: &mut crate::combined_solvers::combiner::TheoryCombiner<'_>,
    terms: &TermStore,
    depth: usize,
    requests: &[ay_core::ModelEqualityRequest],
) -> ArrayEntailVerdict {
    use ay_core::TheorySolver;

    if depth == 0 {
        return ArrayEntailVerdict::SplitUnconfirmed;
    }
    // Pick the first request whose equality atom already exists — splits
    // must not fabricate terms (the store is shared and borrowed immutably).
    let Some(eq_atom) = requests
        .iter()
        .find_map(|req| terms.find_eq(req.lhs, req.rhs))
    else {
        return ArrayEntailVerdict::SplitUnconfirmed;
    };
    let mut all_entailed = true;
    for value in [true, false] {
        verify_solver.push();
        verify_solver.assert_literal(eq_atom, value);
        let verdict = array_entailment_check_with_splits(verify_solver, terms, depth - 1);
        verify_solver.pop();
        match verdict {
            ArrayEntailVerdict::NotEntailed => return ArrayEntailVerdict::NotEntailed,
            ArrayEntailVerdict::Inconclusive | ArrayEntailVerdict::SplitUnconfirmed => {
                all_entailed = false
            }
            ArrayEntailVerdict::Entailed => {}
        }
    }
    if all_entailed {
        ArrayEntailVerdict::Entailed
    } else {
        ArrayEntailVerdict::SplitUnconfirmed
    }
}

/// Verify a BV conflict structurally (#4535).
///
/// The BV solver uses eager bit-blasting: it generates CNF clauses from BV
/// operations and delegates satisfiability to the SAT solver. A fresh BV
/// solver's `check()` always returns SAT (it cannot independently detect
/// conflicts without a SAT solver backend). Therefore, BV conflicts are
/// verified structurally: non-empty, no duplicates, no contradictory literals.
///
/// This is the same approach used for string conflicts. Full semantic
/// verification of BV conflicts would require a complete SAT+BV pipeline,
/// which is tracked as future work.
pub(crate) fn verify_bv_conflict_semantic(
    conflict: &[TheoryLit],
    _terms: &TermStore,
) -> Result<(), VerificationError> {
    verify_theory_conflict(conflict)?;
    tracing::debug!(
        lit_count = conflict.len(),
        "BV theory conflict passed structural verification (#4535)"
    );
    Ok(())
}

/// Verify a BV propagation structurally (#4535).
///
/// Like BV conflicts, the BV solver's eager bit-blasting architecture means
/// a fresh solver cannot semantically re-verify propagations independently.
/// Structural checks ensure the propagation is well-formed (non-empty reason,
/// no duplicates, no circularity).
// #8529: Used in all builds (verify_propagation_semantic is now release-enabled).
pub(crate) fn verify_bv_propagation(
    propagation: &TheoryPropagation,
    _terms: &TermStore,
) -> Result<(), VerificationError> {
    verify_theory_propagation(propagation)?;
    tracing::debug!(
        term = ?propagation.literal.term,
        value = propagation.literal.value,
        reason_count = propagation.reason.len(),
        "BV theory propagation passed structural verification (#4535)"
    );
    Ok(())
}

/// Verify a String conflict structurally and log for the domain (#4535).
///
/// String theory verification is limited to structural checks because the
/// StringSolver returns `NeedStringLemma` or `NeedLemmas` rather than
/// straightforward UNSAT for most conflicts — the theory requires iterative
/// lemma-based reasoning that a single fresh solver `check()` cannot replicate.
///
/// Structural checks catch: empty conflicts, duplicate literals, contradictory
/// literals. These are the same checks applied to all theories via
/// `verify_theory_conflict`, but explicitly routed here so string conflicts
/// are no longer silently accepted.
pub(crate) fn verify_string_conflict_structural(
    conflict: &[TheoryLit],
    terms: &TermStore,
) -> Result<(), VerificationError> {
    verify_theory_conflict(conflict)?;

    // Semantic spuriousness gate (soundness, string disjunction case-split).
    //
    // The structural checks above only catch malformed conflicts (empty,
    // duplicate, tautological). They do NOT catch a string conflict whose
    // reason set is an INCOMPLETE explanation: e.g. an I_CYCLE-derived
    // ConstantConflict over `(str.++ s1 "b") = ""` whose explanation chains
    // to the asserted literal `(= s0 "")` while dropping the cycle source
    // word equation `(= s1 (str.++ s0 s1 "b"))`. The resulting conflict
    // `{(= s0 "")}` claims `s0 = ""` is contradictory, but `s0 = ""` is
    // trivially satisfiable — so the learned blocking clause `¬(= s0 "")`
    // is unsound and produces a false UNSAT on disjunctions like
    // `(or (= s0 "") (= s1 (str.++ s0 s1 "b")))`.
    //
    // To catch this WITHOUT a full CEGAR re-solve (which the StringSolver
    // needs for most conflicts — see the historical note above), re-solve
    // the conflict's literal set in ISOLATION with a fresh StringSolver. If
    // that fresh solve returns a definitive `Sat`, the conjunction of the
    // conflict literals is satisfiable, so the conflict is provably spurious
    // and MUST be rejected (caller degrades SAT-search to Unknown). Any other
    // fresh result (Unsat / Unknown / NeedStringLemma / NeedLemmas) leaves the
    // conflict trusted, preserving prior behaviour — so this only ever turns a
    // would-be wrong-UNSAT into a sound Unknown, never the reverse. Capped by
    // conflict size to bound cost on string-heavy benchmarks.
    // SOUNDNESS (#qfs-nf-cap-fail-closed): this cap USED to fail OPEN — a
    // conflict larger than the cap skipped the entire semantic gate below and
    // was trusted on structural checks alone (non-empty, no duplicate, no
    // contradictory pair), which carry no semantic content. NF-derived string
    // explanations union `state.explain(..)` over every normal-form dep with no
    // cap, so multi-variable word equations — exactly the population the
    // #6261/#6275 rationale calls potentially spurious — routinely exceed a
    // small cap. A cost cap that fails open is a soundness hole by
    // construction: it trusts precisely the largest, least-verifiable
    // conflicts. Raised so that essentially every real conflict is verified
    // (the gate is a fresh solve over only the conflict literals, so cost
    // scales with the conflict, not the problem), and made FAIL-CLOSED beyond
    // it: an unverifiable conflict is rejected, which degrades the search to
    // Unknown rather than admitting a possible wrong UNSAT.
    const MAX_RESOLVE_CONFLICT_LITS: usize = 64;
    if conflict.len() > MAX_RESOLVE_CONFLICT_LITS {
        tracing::warn!(
            lit_count = conflict.len(),
            cap = MAX_RESOLVE_CONFLICT_LITS,
            "string theory conflict rejected: too large to verify semantically \
             (fail-closed; previously such conflicts were trusted unverified)"
        );
        return Err(VerificationError::ConflictIsSat);
    }
    if !conflict.is_empty() {
        use ay_core::TheorySolver;
        let mut fresh = ay_strings::StringSolver::new(terms);
        // Pre-register the empty string so endpoint-empty / cycle (I_CYCLE)
        // inferences in the fresh solver match the production solver's view
        // (solve_strings always sets it). Without this, a genuine occurs-check
        // conflict such as `s1 = (str.++ s0 s1 "b")` would NOT be re-detected in
        // isolation (cycle detection skips empty siblings, which requires the
        // empty-string EQC), and the fresh solve would wrongly report SAT,
        // rejecting a VALID conflict. We look the constant up immutably; if it
        // is not interned (no `""` anywhere in the problem) cycle detection
        // still works structurally for non-empty siblings.
        if let Some(eid) =
            terms.find_interned(&TermData::Const(ay_core::Constant::String(String::new())))
        {
            fresh.set_empty_string_id(eid);
        }
        for lit in conflict {
            fresh.assert_literal(lit.term, lit.value);
        }
        let fresh_result = fresh.check();
        // (A) A definitive `Sat` from the fresh re-solve proves the conflict's
        // literal conjunction is satisfiable — the conflict is spurious.
        let mut spurious = matches!(fresh_result, ay_core::TheoryResult::Sat);

        // (B) When the fresh re-solve is INCONCLUSIVE (`Unknown` /
        // `NeedStringLemma` / `NeedLemmas` — it would need CEGAR to decide) AND
        // the conflict consists solely of (dis)equality literals over strings,
        // its joint unsatisfiability is NOT independently established. Such a
        // conflict is trustworthy only if a contradiction is forced by the
        // GROUND content the conflict itself pins: substitute every positive
        // `var = const` binding the conflict asserts, ground-fold the remaining
        // (dis)equalities, and require some literal to ground-evaluate against
        // its asserted polarity. If NO ground contradiction exists, the
        // (dis)equalities are satisfiable by the free leaves — so the conflict
        // is spurious (e.g. `¬(= "b" (str.++ s "b" u))` over free s,u, or
        // `(= s0 "")`). This keeps GROUND-derivable conflicts (e.g.
        // `x = "hello" ∧ str.substr(x,1,3) = "abc"`, which folds to
        // `"ell" = "abc"`) trusted while rejecting incomplete-reason ones.
        if !spurious && !matches!(fresh_result, ay_core::TheoryResult::Unsat(_)) {
            // Each literal may be a binary string (dis)equality OR a
            // positive/negative atom of str.contains / str.prefixof /
            // str.suffixof. Mixed predicate+equality conflicts (e.g.
            // `{str.contains(s,"a")+, (= (str.++ s "") (str.++ "b" sk))+}`)
            // were previously TRUSTED unconditionally, letting spurious
            // conflicts with incomplete explanations become empty clauses at
            // level 0 → wrong UNSAT. Any other literal shape (str.len
            // arithmetic, str.in_re, str.<, non-string atoms) keeps today's
            // trusted behaviour.
            let all_checkable = conflict.iter().all(|l| {
                matches!(
                    terms.get(l.term),
                    TermData::App(Symbol::Named(name), eargs)
                        if (name == "=" && eargs.len() == 2
                            && *terms.sort(eargs[0]) == Sort::String)
                        || (matches!(
                                name.as_str(),
                                "str.contains" | "str.prefixof" | "str.suffixof"
                            ) && eargs.len() == 2)
                )
            });
            if all_checkable && !string_conflict_has_ground_contradiction(terms, conflict) {
                spurious = true;
            }
        }

        if spurious {
            tracing::warn!(
                lit_count = conflict.len(),
                "string theory conflict rejected: fresh isolated re-solve did not establish \
                 joint unsatisfiability of the conflict literals, and no ground contradiction \
                 is pinned (spurious wrong-UNSAT guard, string disjunction case-split)"
            );
            return Err(VerificationError::ConflictIsSat);
        }
    }

    tracing::debug!(
        lit_count = conflict.len(),
        "string theory conflict passed structural + isolated-resolve verification"
    );
    Ok(())
}

/// Decide whether a string conflict made of (dis)equalities and
/// contains/prefixof/suffixof atoms is forced by GROUND content that the
/// conflict's own literals pin.
///
/// Builds a `var -> const` substitution from every positive `(= var c)` /
/// `(= c var)` literal in the conflict, then ground-folds each literal's two
/// sides under that substitution. Returns `true` iff some literal
/// ground-evaluates against its asserted polarity:
/// - a positive `(= a b)` whose folded sides are unequal constants, or a
///   negated `¬(= a b)` whose folded sides are equal constants;
/// - a `str.contains` / `str.prefixof` / `str.suffixof` atom whose two args
///   both fold to concrete strings and whose concrete truth value differs
///   from the literal's asserted polarity (e.g. `{(= x "b")+,
///   contains(x,"a")+}` folds `contains("b","a")` to false ≠ asserted true —
///   a genuine, model-independent contradiction).
///
/// Returns `false` when no literal can be ground-refuted (free leaves remain),
/// which means the conflict's joint unsatisfiability is NOT pinned by ground
/// content and must come from incomplete-reason inference. Used purely as a
/// soundness gate; a `false` only ever degrades a conflict to Unknown.
fn string_conflict_has_ground_contradiction(terms: &TermStore, conflict: &[TheoryLit]) -> bool {
    use ay_core::kani_compat::DetHashMap;
    // Collect var -> const bindings from positive equalities.
    let mut subst: DetHashMap<TermId, String> = DetHashMap::default();
    for l in conflict {
        if !l.value {
            continue;
        }
        if let TermData::App(Symbol::Named(name), eargs) = terms.get(l.term) {
            if name == "=" && eargs.len() == 2 {
                let (a, b) = (eargs[0], eargs[1]);
                if let (TermData::Var(..), TermData::Const(ay_core::Constant::String(s))) =
                    (terms.get(a), terms.get(b))
                {
                    subst.insert(a, s.clone());
                } else if let (TermData::Const(ay_core::Constant::String(s)), TermData::Var(..)) =
                    (terms.get(a), terms.get(b))
                {
                    subst.insert(b, s.clone());
                }
            }
        }
    }
    // Ground-fold each literal under the substitution; refute on polarity.
    for l in conflict {
        let TermData::App(Symbol::Named(name), eargs) = terms.get(l.term) else {
            continue;
        };
        if eargs.len() != 2 {
            continue;
        }
        // Unfoldable args contribute nothing (continue).
        let (Some(a), Some(b)) = (
            ground_fold_string_under_subst(terms, eargs[0], &subst, 64),
            ground_fold_string_under_subst(terms, eargs[1], &subst, 64),
        ) else {
            continue;
        };
        let folded = match name.as_str() {
            // Positive `(= a b)` is contradicted when a != b; negated when a == b.
            "=" => a == b,
            // SMT-LIB argument order (see eval_string.rs):
            // (str.contains haystack needle) — args[0] contains args[1];
            // (str.prefixof prefix full)     — args[1] starts with args[0];
            // (str.suffixof suffix full)     — args[1] ends with args[0].
            "str.contains" => a.contains(&b),
            "str.prefixof" => b.starts_with(&a),
            "str.suffixof" => b.ends_with(&a),
            _ => continue,
        };
        if folded != l.value {
            return true;
        }
    }
    false
}

/// Ground-fold a string-sorted term to a concrete value under a `var -> const`
/// substitution, returning `None` if any leaf cannot be resolved. Self-contained
/// (handles `str.++`, `str.at`, `str.substr`, constants, substituted vars) and
/// SOUND: returns `None` rather than guessing on unhandled / unresolved terms.
fn ground_fold_string_under_subst(
    terms: &TermStore,
    term: TermId,
    subst: &ay_core::kani_compat::DetHashMap<TermId, String>,
    fuel: u32,
) -> Option<String> {
    if fuel == 0 {
        return None;
    }
    match terms.get(term) {
        TermData::Const(ay_core::Constant::String(s)) => Some(s.clone()),
        TermData::Var(..) => subst.get(&term).cloned(),
        TermData::App(Symbol::Named(name), args) => match name.as_str() {
            "str.++" => {
                let mut out = String::new();
                for &a in args {
                    out.push_str(&ground_fold_string_under_subst(terms, a, subst, fuel - 1)?);
                }
                Some(out)
            }
            "str.at" if args.len() == 2 => {
                let s = ground_fold_string_under_subst(terms, args[0], subst, fuel - 1)?;
                let i = ground_fold_int(terms, args[1])?;
                let chars: Vec<char> = s.chars().collect();
                if i < 0 {
                    return Some(String::new());
                }
                let idx = usize::try_from(i).ok()?;
                Some(chars.get(idx).map(|c| c.to_string()).unwrap_or_default())
            }
            "str.substr" if args.len() == 3 => {
                let s = ground_fold_string_under_subst(terms, args[0], subst, fuel - 1)?;
                let start = ground_fold_int(terms, args[1])?;
                let len = ground_fold_int(terms, args[2])?;
                let chars: Vec<char> = s.chars().collect();
                if start < 0 || len <= 0 {
                    return Some(String::new());
                }
                let start = usize::try_from(start).ok()?;
                let len = usize::try_from(len).ok()?;
                if start >= chars.len() {
                    return Some(String::new());
                }
                let end = start.saturating_add(len).min(chars.len());
                Some(chars[start..end].iter().collect())
            }
            _ => None,
        },
        _ => None,
    }
}

/// Resolve a literal non-negative integer constant (or simple negation).
fn ground_fold_int(terms: &TermStore, term: TermId) -> Option<i64> {
    match terms.get(term) {
        TermData::Const(ay_core::Constant::Int(n)) => i64::try_from(n.clone()).ok(),
        TermData::App(Symbol::Named(name), args) if name == "-" && args.len() == 1 => {
            ground_fold_int(terms, args[0]).map(|n| -n)
        }
        _ => None,
    }
}

/// Verify a String propagation structurally (#4535).
///
/// Like string conflicts, the string solver's lemma-based architecture makes
/// semantic re-verification via a fresh solver impractical. Structural checks
/// ensure the propagation is well-formed (non-empty reason, no duplicates,
/// no circularity).
// #8529: Used in all builds (verify_propagation_semantic is now release-enabled).
pub(crate) fn verify_string_propagation(
    propagation: &TheoryPropagation,
    _terms: &TermStore,
) -> Result<(), VerificationError> {
    verify_theory_propagation(propagation)?;
    tracing::debug!(
        term = ?propagation.literal.term,
        value = propagation.literal.value,
        reason_count = propagation.reason.len(),
        "string theory propagation passed structural verification (#4535)"
    );
    Ok(())
}

/// Full-state soundness guard for level-0 conflicts (#7935).
///
/// When a theory conflict is reported at decision level 0, verify that ALL
/// currently-asserted theory atoms (not just the conflict subset) are jointly
/// UNSAT. Individual conflict atoms may form genuine contradictions, but if the
/// full assignment is satisfiable, then the BCP chain derived an incorrect
/// forced assignment — the conflict is an artifact of incremental solver state
/// corruption and must be rejected.
///
/// This catches bugs that per-conflict semantic checks miss: each 2-atom
/// conflict may be logically valid in isolation, but the OVERALL assignment
/// that forced both atoms should never arise from a satisfiable formula.
///
/// Returns Ok(()) if the full state IS unsatisfiable (conflict is sound), or
/// Err if the full state is satisfiable (conflict is spurious).
pub(crate) fn verify_lra_full_state_satisfiable(
    all_theory_atoms: &[TheoryLit],
    terms: &TermStore,
) -> Result<(), VerificationError> {
    use ay_core::{TheoryResult, TheorySolver};
    use ay_lra::LraSolver;

    if all_theory_atoms.is_empty() {
        return Ok(());
    }

    let mut verify_lra = LraSolver::new(terms);
    // #8257: Enable verification mode to skip post-simplex propagation.
    verify_lra.set_verification_mode();
    // Register atoms first so the fresh solver knows their structure.
    for lit in all_theory_atoms {
        verify_lra.register_atom(lit.term);
    }
    for lit in all_theory_atoms {
        verify_lra.assert_literal(lit.term, lit.value);
    }

    match verify_lra.check() {
        TheoryResult::Unsat(_) | TheoryResult::UnsatWithFarkas(_) => {
            // Full state is genuinely UNSAT — conflict is sound.
            Ok(())
        }
        TheoryResult::Sat => Err(VerificationError::InvalidFarkas {
            reason: format!(
                "LRA full-state soundness check (#7935): fresh solver says SAT for all {} \
                 asserted theory atoms — level-0 conflict is spurious",
                all_theory_atoms.len()
            ),
        }),
        // Unknown / split: cannot definitively verify. Accept the conflict
        // optimistically to avoid suppressing genuine conflicts.
        _ => Ok(()),
    }
}

/// Verify an LRA conflict by checking that the conflict atoms are jointly UNSAT.
///
/// Creates a fresh LRA solver, asserts every conflict literal with its stated
/// value, and checks for UNSAT.  If the fresh solver says SAT, the conflict
/// is spurious — the underlying theory produced an incorrect explanation.
///
/// This is the conflict analogue of `verify_lra_propagation` (#6242).
///
/// Promoted to all builds (#6564).
pub(crate) fn verify_lra_conflict_semantic(
    conflict: &[TheoryLit],
    terms: &TermStore,
) -> Result<(), VerificationError> {
    use ay_core::{TheoryResult, TheorySolver};
    use ay_lra::LraSolver;

    ay_lia::instrument::bump_verify_fresh_lra_solve();
    let mut verify_lra = LraSolver::new(terms);
    // #8257: Enable verification mode to skip post-simplex propagation.
    verify_lra.set_verification_mode();
    for lit in conflict {
        verify_lra.assert_literal(lit.term, lit.value);
    }

    match verify_lra.check() {
        TheoryResult::Unsat(_) | TheoryResult::UnsatWithFarkas(_) => Ok(()),
        TheoryResult::Sat => Err(VerificationError::InvalidFarkas {
            reason: format!(
                "LRA conflict semantic check: fresh solver says SAT for {}-literal conflict",
                conflict.len()
            ),
        }),
        // Unknown / split: cannot verify — accept optimistically.
        _ => Ok(()),
    }
}

/// Verify an LIA conflict by checking that the conflict atoms are jointly UNSAT
/// under integer arithmetic.
///
/// Creates a fresh LIA solver, asserts every conflict literal with its stated
/// value, and checks for UNSAT.  If the fresh solver says SAT, the conflict
/// is spurious — the underlying theory produced an incorrect explanation.
///
/// Unlike `verify_lra_conflict_semantic`, this correctly handles integer-gap
/// conflicts (e.g., `x > 5 AND x < 6`) that are UNSAT over integers but SAT
/// over reals. (#6853)
/// Wall-clock budget for a single semantic conflict verification (#verify-budget).
///
/// Verifications are supposed to be cheap — they re-check one conflict, not the problem.
/// The budget exists so a pathological case cannot spend the solve's time inside a
/// verifier; exceeding it degrades to the pre-existing "accept optimistically" path.
/// Override with `AY_VERIFY_SOLVE_BUDGET_MS`.
fn verify_solve_budget() -> std::time::Duration {
    std::time::Duration::from_secs(1)
}

pub(crate) fn verify_lia_conflict_semantic(
    conflict: &[TheoryLit],
    terms: &TermStore,
) -> Result<(), VerificationError> {
    use ay_core::{TheoryResult, TheorySolver};
    use ay_lia::LiaSolver;

    ay_lia::instrument::bump_verify_fresh_lia_solve();
    let mut verify_lia = LiaSolver::new(terms);
    // #verify-budget: bound this verification.
    //
    // This runs per theory conflict on the default-on path and previously installed NO
    // deadline and no timeout callback, so every `should_timeout()` inside `check_inner`
    // was inert and the `try_patching -> continue` loop ran uncounted. A single spurious
    // conflict on a large arithmetic problem could therefore burn unbounded wall clock
    // inside a *verifier* — time that comes straight out of the solve budget, i.e. out of
    // answers.
    //
    // The fallback is unchanged: on `Unknown` this function already accepts optimistically
    // (`_ => Ok(())` below), which is exactly what a budget trip produces. So bounding it
    // can cost verification strength on a pathological conflict, never correctness of the
    // accept/reject contract. `set_deadline` (not the callback) is used because it also
    // propagates into the IntSat probe's BigInt loop.
    verify_lia.set_deadline(ay_core::time::Instant::now() + verify_solve_budget());
    for lit in conflict {
        verify_lia.assert_literal(lit.term, lit.value);
    }

    match verify_lia.check() {
        TheoryResult::Unsat(_) | TheoryResult::UnsatWithFarkas(_) => Ok(()),
        TheoryResult::Sat => Err(VerificationError::ConflictIsSat),
        // NeedLemmas: LIA found it needs cuts but hasn't proven UNSAT yet.
        // Accept optimistically — the conflict may still be valid but require
        // branch-and-bound exploration that a single check() doesn't perform.
        TheoryResult::NeedLemmas(_) => Ok(()),
        // Unknown / split: cannot verify — accept optimistically.
        _ => Ok(()),
    }
}

/// Verify a mixed-domain theory conflict using the Nelson-Oppen combined solver
/// (#8123).
///
/// For conflicts involving literals from multiple theory domains (e.g., both
/// arithmetic and EUF), individual theory solvers cannot validate the conflict
/// in isolation. The combined solver performs joint verification via the
/// Nelson-Oppen fixpoint loop, which correctly handles cross-theory reasoning
/// (e.g., EUF congruence producing equalities that create arithmetic conflicts).
///
/// Selects the appropriate combiner based on which sorts appear in the conflict:
/// - Int-sorted operands -> UF+LIA (handles integer gap conflicts correctly)
/// - Real-sorted operands -> UF+LRA
/// - Neither -> UF+LIA (safe default; LIA subsumes pure EUF reasoning)
/// Verify a conflict that mentions Seq-sorted terms by re-solving it in a
/// fresh EUF+Seq combined solver — the same combination that DERIVED it.
///
/// Seq sorts classify to [`TheoryDomain::String`], whose structural verifier
/// re-solves with `ay_strings::StringSolver`. That solver has no notion of
/// `seq.unit` / `seq.empty`, so it reported a genuine unit-vs-empty conflict
/// (`s = seq.unit(5)` and `s = seq.empty`, whose contradiction needs EUF
/// transitivity PLUS the Seq theory's unit/empty disjointness) as SATISFIABLE.
/// The conflict was then discarded as unverifiable and the split loop degraded
/// a provable UNSAT to Unknown. The verification combiner cannot stand in here
/// either — it only carries Int/Real/Array solvers, no Seq.
///
/// `NeedLemmas` / other non-definitive outcomes are accepted optimistically,
/// exactly as the LIA verifier does: the conflict may be real but need lemmas a
/// single `check()` does not derive. Only a definitive `Sat` refutes it.
fn verify_seq_conflict_semantic(
    conflict: &[TheoryLit],
    terms: &TermStore,
) -> Result<(), VerificationError> {
    use ay_core::{TheoryResult, TheorySolver};

    let mut fresh = crate::combined_solvers::adapters::UfSeqSolver::new(terms);
    for lit in conflict {
        fresh.register_atom(lit.term);
    }
    for lit in conflict {
        fresh.assert_literal(lit.term, lit.value);
    }
    match fresh.check() {
        TheoryResult::Unsat(_) | TheoryResult::UnsatWithFarkas(_) => Ok(()),
        TheoryResult::Sat => Err(VerificationError::ConflictIsSat),
        _ => Ok(()),
    }
}

/// True when any conflict literal mentions a `Seq`-sorted term (as opposed to
/// String/RegLan, which the structural string verifier handles).
fn conflict_involves_seq_sort(terms: &TermStore, conflict: &[TheoryLit]) -> bool {
    fn mentions_seq(terms: &TermStore, term: TermId, depth: u32) -> bool {
        if depth == 0 {
            return false;
        }
        if matches!(terms.sort(term), Sort::Seq(_)) {
            return true;
        }
        match terms.get(term) {
            TermData::App(_, args) => args.iter().any(|&a| mentions_seq(terms, a, depth - 1)),
            TermData::Not(inner) => mentions_seq(terms, *inner, depth - 1),
            _ => false,
        }
    }
    conflict.iter().any(|lit| mentions_seq(terms, lit.term, 8))
}

// ---------------------------------------------------------------------------
// Mixed string+arith conflict verification (#mixed-string-verify-gap)
// ---------------------------------------------------------------------------

/// Observable counters for the mixed string+arith conflict gate.
///
/// The gap this closes was INVISIBLE: `is_verifiable_mixed_domain` bailed on
/// any String-domain literal and `verify_mixed_conflict_semantic` returned
/// `Ok(())`, so a mixed string+arithmetic conflict was accepted with no
/// semantic verification and no trace of the fact. Every path through the gate
/// — verified, rejected, or skipped — now bumps a counter here, so "a silent
/// accept" is no longer possible: `mixed_string_verify_counts()` reports the
/// exact population, and `--verify-mixed-strings-stats` streams each event to
/// stderr.
pub(crate) mod mixed_string_verify_stats {
    use std::sync::atomic::{AtomicU64, Ordering};

    /// Mixed string conflicts re-solved by a fresh `StringsLiaSolver`.
    pub(crate) static VERIFIED: AtomicU64 = AtomicU64::new(0);
    /// ... of which were REJECTED because the fresh re-solve proved the
    /// conflict's literal conjunction satisfiable (definitive `Sat`).
    pub(crate) static REJECTED_SAT: AtomicU64 = AtomicU64::new(0);
    /// Rejected fail-closed because the conflict exceeded the size cap.
    pub(crate) static REJECTED_OVER_CAP: AtomicU64 = AtomicU64::new(0);
    /// Skipped: the context contains Real arithmetic or an int<->real bridge,
    /// which the LIA-only SLIA adapter cannot faithfully re-solve.
    pub(crate) static SKIPPED_INT_REAL: AtomicU64 = AtomicU64::new(0);
    /// Skipped: a BitVec or truly-unknown literal — no fresh solver reproduces
    /// this conflict (the residual, still-unverified population).
    pub(crate) static SKIPPED_UNVERIFIABLE: AtomicU64 = AtomicU64::new(0);
    /// Skipped: the conflict mentions `Seq`-sorted terms, which the QF_SLIA
    /// adapter has no theory for.
    pub(crate) static SKIPPED_SEQ: AtomicU64 = AtomicU64::new(0);
    /// Fresh re-solve said `Sat`, but a string->int bridge term (`str.len`,
    /// `str.indexof`, ...) was left unpinned so LIA treated it as an
    /// unconstrained Int — the verdict proves nothing. Accepted (counted).
    pub(crate) static ACCEPTED_SAT_UNFAITHFUL: AtomicU64 = AtomicU64::new(0);
    /// Fresh re-solve said `Sat`, but the conflict's OWN ground content refutes
    /// a literal — the conflict is genuinely UNSAT and the `Sat` is an artifact
    /// of the dropped length coupling. Accepted (counted): a VALID conflict the
    /// naive gate would have thrown away.
    pub(crate) static ACCEPTED_SAT_GROUND_REFUTED: AtomicU64 = AtomicU64::new(0);

    /// Snapshot of every counter, in declaration order.
    #[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
    pub(crate) struct Counts {
        pub verified: u64,
        pub rejected_sat: u64,
        pub rejected_over_cap: u64,
        pub skipped_int_real: u64,
        pub skipped_unverifiable: u64,
        pub skipped_seq: u64,
        pub accepted_sat_unfaithful: u64,
        pub accepted_sat_ground_refuted: u64,
    }

    pub(crate) fn snapshot() -> Counts {
        Counts {
            verified: VERIFIED.load(Ordering::Relaxed),
            rejected_sat: REJECTED_SAT.load(Ordering::Relaxed),
            rejected_over_cap: REJECTED_OVER_CAP.load(Ordering::Relaxed),
            skipped_int_real: SKIPPED_INT_REAL.load(Ordering::Relaxed),
            skipped_unverifiable: SKIPPED_UNVERIFIABLE.load(Ordering::Relaxed),
            skipped_seq: SKIPPED_SEQ.load(Ordering::Relaxed),
            accepted_sat_unfaithful: ACCEPTED_SAT_UNFAITHFUL.load(Ordering::Relaxed),
            accepted_sat_ground_refuted: ACCEPTED_SAT_GROUND_REFUTED.load(Ordering::Relaxed),
        }
    }

    /// Bump `counter` and return the PREVIOUS value (0 on the first event, so
    /// callers can warn once and debug thereafter).
    pub(super) fn bump(counter: &AtomicU64) -> u64 {
        counter.fetch_add(1, Ordering::Relaxed)
    }

    /// `--verify-mixed-strings-stats` — stream every gate event to stderr.
    pub(super) fn stats_stream_enabled() -> bool {
        static ON: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
        *ON.get_or_init(|| ay_core::misc_cli_flags().verify_mixed_strings_stats)
    }
}

/// Compile-time pin for the non-disableable mixed string soundness gate.
fn mixed_strings_gate_enabled() -> bool {
    true
}

/// Record a gate event: counter bump + tracing (WARN on the first occurrence of
/// each class so it cannot pass unnoticed, DEBUG thereafter to avoid flooding
/// string-heavy solves) + optional stderr stream.
fn observe_mixed_string_event(
    counter: &std::sync::atomic::AtomicU64,
    what: &'static str,
    lit_count: usize,
) {
    let prev = mixed_string_verify_stats::bump(counter);
    if prev == 0 {
        tracing::warn!(
            lit_count,
            event = what,
            "mixed string+arith conflict verification gate: first {what} event \
             (#mixed-string-verify-gap; counters via mixed_string_verify_counts)"
        );
    } else {
        tracing::debug!(lit_count, event = what, "mixed string+arith gate event");
    }
    if mixed_string_verify_stats::stats_stream_enabled() {
        safe_eprintln!(
            "[MIXED-STR-VERIFY] {what} lits={lit_count} totals={:?}",
            mixed_string_verify_stats::snapshot()
        );
    }
}

/// Public snapshot of the mixed string+arith gate counters (observability).
#[allow(
    dead_code,
    reason = "observability accessor; used by tests and callers auditing the gate"
)]
pub(crate) fn mixed_string_verify_counts() -> mixed_string_verify_stats::Counts {
    mixed_string_verify_stats::snapshot()
}

/// Whether a fresh QF_SLIA `Sat` verdict on a mixed conflict can be trusted.
///
/// The isolated re-solve is WEAKER than the production pipeline in one specific
/// way: the executor injects `str.len` axioms (non-negativity, zero-length <->
/// empty, concat additivity, ground folds) as top-level ASSERTIONS before
/// Tseitin encoding, and the verifier — which holds `&TermStore` and cannot
/// mint terms — has no way to reproduce them. So the fresh LIA solver sees
/// `(str.len x)` as an unconstrained opaque Int variable. Against
/// `{(= x "ab"), (>= (str.len x) 3)}` — a genuinely UNSAT conflict — it happily
/// picks `len_x = 3` and reports `Sat`. Rejecting on that `Sat` would throw
/// away a VALID conflict, which is the exact completeness failure the design
/// note warns about.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum SliaSatTrust {
    /// No string->int bridge term is left dangling, so the `Sat` verdict is a
    /// sound basis for rejecting the context as satisfiable.
    Trustworthy,
    /// The context's ground content refutes one of its literals: the context is
    /// genuinely unsatisfiable and the `Sat` is an artifact of the
    /// dropped length coupling. Accept.
    GroundRefuted,
    /// A string->int bridge term is unpinned (or is a function this check does
    /// not evaluate), so LIA's freedom to choose its value explains the `Sat`.
    /// The verdict proves nothing. Accept.
    Unfaithful,
}

/// True when `t` is a string->integer bridge application: an Int-sorted
/// application with a String/RegLan/Seq-sorted argument (`str.len`,
/// `str.indexof`, `str.to_int`, `str.to_code`, ...). These are exactly the
/// terms the isolated LIA solver models as unconstrained opaque variables.
fn is_string_to_int_bridge(terms: &TermStore, t: TermId) -> bool {
    if !matches!(terms.sort(t), Sort::Int) {
        return false;
    }
    match terms.get(t) {
        TermData::App(_, args) => args
            .iter()
            .any(|&a| matches!(terms.sort(a), Sort::String | Sort::RegLan | Sort::Seq(_))),
        _ => false,
    }
}

/// Evaluate an Int-sorted term to a concrete value using `pins` (ground-pinned
/// `str.len` terms) plus integer constants and linear/product arithmetic.
/// Returns `None` for anything not fully determined.
fn eval_int_with_pins(
    terms: &TermStore,
    t: TermId,
    pins: &ay_core::kani_compat::DetHashMap<TermId, i64>,
    fuel: u32,
) -> Option<i64> {
    if fuel == 0 {
        return None;
    }
    if let Some(&v) = pins.get(&t) {
        return Some(v);
    }
    match terms.get(t) {
        TermData::Const(ay_core::Constant::Int(n)) => i64::try_from(n.clone()).ok(),
        TermData::App(Symbol::Named(name), args) => match name.as_str() {
            "+" => args.iter().try_fold(0i64, |acc, &a| {
                acc.checked_add(eval_int_with_pins(terms, a, pins, fuel - 1)?)
            }),
            "-" if args.len() == 1 => {
                eval_int_with_pins(terms, args[0], pins, fuel - 1).and_then(|v| 0i64.checked_sub(v))
            }
            "-" if args.len() == 2 => {
                let a = eval_int_with_pins(terms, args[0], pins, fuel - 1)?;
                let b = eval_int_with_pins(terms, args[1], pins, fuel - 1)?;
                a.checked_sub(b)
            }
            "*" => args.iter().try_fold(1i64, |acc, &a| {
                acc.checked_mul(eval_int_with_pins(terms, a, pins, fuel - 1)?)
            }),
            _ => None,
        },
        _ => None,
    }
}

/// Ground-evaluate an arithmetic ATOM (comparison / Int equality) under `pins`.
/// `None` when the atom is not fully determined.
fn eval_arith_atom_with_pins(
    terms: &TermStore,
    atom: TermId,
    pins: &ay_core::kani_compat::DetHashMap<TermId, i64>,
) -> Option<bool> {
    let TermData::App(Symbol::Named(name), args) = terms.get(atom) else {
        return None;
    };
    if args.len() != 2 {
        return None;
    }
    let a = eval_int_with_pins(terms, args[0], pins, 32)?;
    let b = eval_int_with_pins(terms, args[1], pins, 32)?;
    match name.as_str() {
        "<=" => Some(a <= b),
        "<" => Some(a < b),
        ">=" => Some(a >= b),
        ">" => Some(a > b),
        "=" => Some(a == b),
        "distinct" => Some(a != b),
        _ => None,
    }
}

/// Decide whether the fresh QF_SLIA `Sat` verdict for the complete asserted
/// verification context is trustworthy
/// (see [`SliaSatTrust`]).
///
/// 1. Build the `var -> const` string substitution the context itself pins
///    (positive `(= v "…")` literals), exactly like
///    [`string_conflict_has_ground_contradiction`].
/// 2. Find every string->int bridge subterm. If there are none, the fresh solve
///    dropped no coupling: `Trustworthy`.
/// 3. Pin each `str.len` whose argument ground-folds (SMT-LIB length = code
///    points, matching `ground_eval_string_term`). Any bridge term that is not
///    a ground-foldable `str.len` leaves an unconstrained Int behind:
///    `Unfaithful`.
/// 4. With every bridge pinned, each literal that MENTIONS a bridge term must
///    ground-evaluate. One that evaluates AGAINST its asserted polarity shows
///    the context inconsistent (`GroundRefuted`). One that cannot be evaluated
///    (e.g. `(<= (+ (str.len x) n) 1)` with `n` free) means LIA's choice of the
///    length still drives the verdict: `Unfaithful`. Only when all of them
///    check out is the `Sat` verdict `Trustworthy`.
fn assess_slia_sat_trust(terms: &TermStore, context: &[TheoryLit]) -> SliaSatTrust {
    use ay_core::kani_compat::{DetHashMap, DetHashSet};

    let mut subst: DetHashMap<TermId, String> = DetHashMap::default();
    for l in context {
        if !l.value {
            continue;
        }
        if let TermData::App(Symbol::Named(name), eargs) = terms.get(l.term) {
            if name == "=" && eargs.len() == 2 {
                let (a, b) = (eargs[0], eargs[1]);
                if let (TermData::Var(..), TermData::Const(ay_core::Constant::String(s))) =
                    (terms.get(a), terms.get(b))
                {
                    subst.insert(a, s.clone());
                } else if let (TermData::Const(ay_core::Constant::String(s)), TermData::Var(..)) =
                    (terms.get(a), terms.get(b))
                {
                    subst.insert(b, s.clone());
                }
            }
        }
    }

    let mut pins: DetHashMap<TermId, i64> = DetHashMap::default();
    let mut any_bridge = false;
    let mut unfaithful = false;
    let mut visited: DetHashSet<TermId> = DetHashSet::default();
    let mut stack: Vec<TermId> = context.iter().map(|l| l.term).collect();
    while let Some(t) = stack.pop() {
        if !visited.insert(t) {
            continue;
        }
        if is_string_to_int_bridge(terms, t) {
            any_bridge = true;
            match terms.get(t) {
                TermData::App(Symbol::Named(name), args)
                    if name == "str.len" && args.len() == 1 =>
                {
                    match ground_fold_string_under_subst(terms, args[0], &subst, 64) {
                        Some(s) => {
                            if let Ok(n) = i64::try_from(s.chars().count()) {
                                pins.insert(t, n);
                            } else {
                                unfaithful = true;
                            }
                        }
                        None => unfaithful = true,
                    }
                }
                _ => unfaithful = true,
            }
        }
        match terms.get(t) {
            TermData::Not(inner) => stack.push(*inner),
            TermData::Ite(c, a, b) => {
                stack.push(*c);
                stack.push(*a);
                stack.push(*b);
            }
            TermData::App(_, args) => stack.extend(args.iter().copied()),
            _ => {}
        }
    }

    if !any_bridge {
        return SliaSatTrust::Trustworthy;
    }
    if unfaithful {
        return SliaSatTrust::Unfaithful;
    }

    for l in context {
        let mut atom = l.term;
        let mut polarity = l.value;
        while let TermData::Not(inner) = terms.get(atom) {
            atom = *inner;
            polarity = !polarity;
        }
        if !term_mentions_pinned_bridge(terms, atom, &pins) {
            continue;
        }
        match eval_arith_atom_with_pins(terms, atom, &pins) {
            Some(v) if v != polarity => return SliaSatTrust::GroundRefuted,
            Some(_) => {}
            None => return SliaSatTrust::Unfaithful,
        }
    }
    SliaSatTrust::Trustworthy
}

/// Whether any subterm of `t` is one of the pinned `str.len` bridge terms.
fn term_mentions_pinned_bridge(
    terms: &TermStore,
    t: TermId,
    pins: &ay_core::kani_compat::DetHashMap<TermId, i64>,
) -> bool {
    let mut visited: ay_core::kani_compat::DetHashSet<TermId> = Default::default();
    let mut stack = vec![t];
    while let Some(x) = stack.pop() {
        if !visited.insert(x) {
            continue;
        }
        if pins.contains_key(&x) {
            return true;
        }
        match terms.get(x) {
            TermData::Not(inner) => stack.push(*inner),
            TermData::Ite(c, a, b) => {
                stack.push(*c);
                stack.push(*a);
                stack.push(*b);
            }
            TermData::App(_, args) => stack.extend(args.iter().copied()),
            _ => {}
        }
    }
    false
}

/// Fail-closed size cap for the mixed string+arith gate.
///
/// Mirrors `MAX_RESOLVE_CONFLICT_LITS` in [`verify_string_conflict_structural`]
/// (`e40292e686`): the fresh re-solve's cost scales with the CONFLICT, not the
/// problem, so the cap only exists to bound pathological explosions — and it
/// FAILS CLOSED. A cost cap that fails open trusts precisely the largest, least
/// verifiable conflicts, which is a soundness hole by construction.
const MAX_MIXED_STRING_CONFLICT_LITS: usize = 64;

/// Verify a MIXED string + arithmetic/EUF/array conflict by re-solving its
/// literals in isolation with a fresh QF_SLIA (`Strings` + `EUF` + `LIA`)
/// adapter (#mixed-string-verify-gap).
///
/// # The gap this closes
///
/// `classify_conflict_domain` returns `Unknown` for a conflict that mixes a
/// String-domain literal (`(= x "ab")`) with an Arithmetic one
/// (`(<= (str.len x) 2)` classifies Arithmetic — the `str.len` lives *inside*
/// an arithmetic atom). `Unknown` dispatches to
/// [`verify_mixed_conflict_semantic`], whose first act was to bail out of
/// `is_verifiable_mixed_domain` on the String literal and `return Ok(())`. So
/// the conflict hit NEITHER gate: not the string gate (it is not pure-String),
/// not the Nelson-Oppen gate (it bailed). QF_SLIA conflicts routinely have
/// exactly this shape, and the strings NF machinery is the component whose
/// conflicts the #6261/#6275 rationale calls potentially spurious.
///
/// # Why not the naive fixes
///
/// Rejecting mixed string conflicts outright would reject VALID ones (a
/// conflict can be valid because of its arithmetic part while its string part
/// alone is satisfiable). Feeding one to a bare `StringSolver` would DROP the
/// arithmetic literals and manufacture spurious `Sat` verdicts. The production
/// QF_SLIA adapter is the only fresh solver that reads this exact fragment.
///
/// # Contract
///
/// REJECT only on a definitive `Sat` — the fresh combined solve reached its
/// Nelson-Oppen fixpoint with the string theory complete and LIA decided, which
/// establishes the conflict's literal conjunction satisfiable, i.e. the
/// conflict is spurious. Every other outcome (`Unsat` / `Unknown` / `NeedStringLemma` /
/// `NeedLemmas` / any split request) keeps the pre-fix accept. This is
/// completeness-neutral by construction: it only ever adds a rejection where a
/// fresh combined solve establishes satisfiability, so it can turn a would-be
/// wrong UNSAT into a sound Unknown, never the reverse.
///
/// Three fragments are OUTSIDE the adapter and are skipped (observably, via
/// their own counters) rather than judged: `Seq`-sorted content (no Seq theory
/// in the adapter), Array or Real content (the adapter carries neither theory),
/// and — checked only once a `Sat` actually comes back — contexts whose
/// `str.len` coupling the isolated solve could not reproduce (see
/// [`SliaSatTrust`]).
///
/// # Boundedness
///
/// The fresh adapter inherits NO deadline or interrupt (there is none to
/// inherit — `make_verification_combiner` also builds with `deadline: None`),
/// so Unknown outcomes are not manufactured by an inherited timeout. The solve
/// is instead bounded structurally: the literal-count cap above, and the
/// adapter's own `MAX_ITERATIONS = 100` Nelson-Oppen round cap, whose
/// exhaustion falls out of the loop as a non-`Sat` result — i.e. bounded-out is
/// INCONCLUSIVE (accept), never `Sat`.
fn verify_strings_mixed_conflict_semantic(
    conflict: &[TheoryLit],
    terms: &TermStore,
    verification_context: &[TheoryLit],
) -> Result<(), VerificationError> {
    use ay_core::{TheoryResult, TheorySolver};

    if conflict.is_empty() {
        // Structurally rejected upstream by `verify_theory_conflict`.
        return Ok(());
    }
    debug_assert!(mixed_strings_gate_enabled());

    // `Seq`-sorted content (`seq.unit` / `seq.empty` / Seq (dis)equalities)
    // classifies String-domain but is NOT the QF_SLIA fragment: the adapter's
    // `StringSolver` has no notion of `seq.unit`, so it reports a genuine
    // unit-vs-empty conflict as satisfiable (the exact false positive
    // `verify_seq_conflict_semantic` exists to avoid). A conflict mixing Seq
    // with arithmetic reaches neither that verifier (it is not pure-String
    // domain) nor a faithful re-solve here — so skip it, observably.
    if conflict_involves_seq_sort(terms, verification_context) {
        observe_mixed_string_event(
            &mixed_string_verify_stats::SKIPPED_SEQ,
            "skipped-seq-sort",
            conflict.len(),
        );
        return Ok(());
    }

    // Any Real arithmetic (including an explicit
    // `to_real`/`to_int`/`is_int` bridge) is OUTSIDE the SLIA fragment: the
    // adapter carries a single LIA solver, so Real-sorted atoms and the
    // int<->real coupling are dropped and a `Sat` verdict would not establish
    // spuriousness. Mirror the #6853 skip — observably.
    let has_real = verification_context
        .iter()
        .any(|lit| conflict_involves_real_sort(terms, lit.term));
    if has_real || conflict_involves_int_real_mix(terms, verification_context) {
        observe_mixed_string_event(
            &mixed_string_verify_stats::SKIPPED_INT_REAL,
            "skipped-real-or-int-real",
            conflict.len(),
        );
        return Ok(());
    }
    // `StringsLiaSolver` has no ArraySolver. A context that combines native
    // string content with select/store semantics therefore cannot use its
    // `Sat` as a rejection verdict.
    if verification_context
        .iter()
        .any(|lit| term_has_array_context(terms, lit.term))
    {
        observe_mixed_string_event(
            &mixed_string_verify_stats::SKIPPED_UNVERIFIABLE,
            "skipped-string-array-mix",
            conflict.len(),
        );
        return Ok(());
    }
    if conflict_involves_nonlinear(terms, verification_context) {
        tracing::debug!(
            lit_count = conflict.len(),
            "mixed string+nonlinear conflict skipped semantic re-verification: \
             the QF_SLIA adapter carries only linear integer arithmetic"
        );
        return Ok(());
    }

    if conflict.len() > MAX_MIXED_STRING_CONFLICT_LITS {
        observe_mixed_string_event(
            &mixed_string_verify_stats::REJECTED_OVER_CAP,
            "rejected-over-cap",
            conflict.len(),
        );
        tracing::warn!(
            lit_count = conflict.len(),
            cap = MAX_MIXED_STRING_CONFLICT_LITS,
            "mixed string+arith conflict rejected: too large to verify semantically \
             (fail-closed, mirroring e40292e686)"
        );
        return Err(VerificationError::ConflictIsSat);
    }

    let mut fresh = crate::combined_solvers::StringsLiaSolver::new(terms);
    // Pre-register the empty string exactly as the executor's SLIA pipeline
    // does, so endpoint-empty / cycle (I_CYCLE) inferences in the fresh solver
    // match the production solver's view. Without it a genuine occurs-check
    // conflict is not re-detected in isolation and the fresh solve wrongly
    // reports Sat, rejecting a VALID conflict. Looked up immutably; if `""` is
    // not interned anywhere in the problem, cycle detection still works
    // structurally for non-empty siblings.
    if let Some(eid) =
        terms.find_interned(&TermData::Const(ay_core::Constant::String(String::new())))
    {
        fresh.set_empty_string_id(eid);
    }

    // Support axioms hold in every model of the problem, so asserting them
    // alongside the conflict can only CONFIRM a genuine conflict (turning a
    // spurious-looking `Sat` into `Unsat`) — never manufacture a rejection.
    for lit in verification_context {
        fresh.register_atom(lit.term);
    }
    for lit in verification_context {
        fresh.assert_literal(lit.term, lit.value);
    }

    let result = fresh.check();
    observe_mixed_string_event(
        &mixed_string_verify_stats::VERIFIED,
        "verified",
        conflict.len(),
    );

    if matches!(result, TheoryResult::Sat) {
        // The isolated adapter has no `str.len` axioms (the executor injects
        // those as assertions; a `&TermStore` verifier cannot mint terms), so a
        // bare `Sat` is only a sound rejection basis when no string->int bridge
        // term was left unconstrained. Check before rejecting — otherwise a
        // VALID conflict such as `{(= x "ab"), (>= (str.len x) 3)}` would be
        // thrown away, which is precisely the completeness failure this design
        // set out to avoid.
        match assess_slia_sat_trust(terms, verification_context) {
            SliaSatTrust::Trustworthy => {}
            SliaSatTrust::GroundRefuted => {
                observe_mixed_string_event(
                    &mixed_string_verify_stats::ACCEPTED_SAT_GROUND_REFUTED,
                    "accepted-sat-ground-refuted",
                    conflict.len(),
                );
                return Ok(());
            }
            SliaSatTrust::Unfaithful => {
                observe_mixed_string_event(
                    &mixed_string_verify_stats::ACCEPTED_SAT_UNFAITHFUL,
                    "accepted-sat-unfaithful-bridge",
                    conflict.len(),
                );
                return Ok(());
            }
        }
        observe_mixed_string_event(
            &mixed_string_verify_stats::REJECTED_SAT,
            "rejected-conflict-is-sat",
            conflict.len(),
        );
        tracing::warn!(
            lit_count = conflict.len(),
            "mixed string+arith conflict rejected: fresh isolated QF_SLIA re-solve \
             proved the conflict literals JOINTLY SATISFIABLE (spurious conflict; \
             search degrades to Unknown rather than emitting a possible wrong UNSAT)"
        );
        return Err(VerificationError::ConflictIsSat);
    }

    tracing::debug!(
        lit_count = conflict.len(),
        "mixed string+arith conflict passed isolated QF_SLIA re-solve verification"
    );
    Ok(())
}

#[derive(Debug, PartialEq, Eq)]
pub(super) enum LemmaTrailClosure {
    /// A valid theory clause is fully falsified by the fixed verification trail.
    Contradiction,
    /// Every clause is satisfied after asserting these unit-implied literals.
    Complete(Vec<TheoryLit>),
    /// At least one clause still has multiple unassigned literals.
    Inconclusive,
}

/// Close a batch of valid theory clauses under the fixed verification trail.
///
/// This is deliberately only unit propagation, not a SAT branch chooser.
/// `NeedLemmas` clauses are permanent theory-valid clauses, but choosing one
/// disjunct from a multi-live clause would strengthen the context without
/// justification and could make a satisfiable conflict look unsatisfiable.
pub(super) fn close_valid_lemma_clauses(
    clauses: &[Vec<TheoryLit>],
    trail: &mut ay_core::kani_compat::DetHashMap<TermId, bool>,
) -> LemmaTrailClosure {
    let mut units = Vec::new();

    loop {
        let mut changed = false;
        let mut unresolved = false;

        for clause in clauses {
            // A syntactic `p OR NOT p` is satisfied independently of the
            // trail. Clauses are canonicalized by the caller, so opposite
            // polarities for one term are adjacent.
            if clause
                .windows(2)
                .any(|pair| pair[0].term == pair[1].term && pair[0].value != pair[1].value)
            {
                continue;
            }
            if clause
                .iter()
                .any(|lit| trail.get(&lit.term) == Some(&lit.value))
            {
                continue;
            }

            let mut live = clause
                .iter()
                .copied()
                .filter(|lit| !trail.contains_key(&lit.term));
            let Some(unit) = live.next() else {
                // An empty clause, or a clause whose every literal has the
                // opposite trail polarity, refutes the fixed context.
                return LemmaTrailClosure::Contradiction;
            };
            if live.next().is_some() {
                unresolved = true;
                continue;
            }

            trail.insert(unit.term, unit.value);
            units.push(unit);
            changed = true;
        }

        if !changed {
            return if unresolved {
                LemmaTrailClosure::Inconclusive
            } else {
                LemmaTrailClosure::Complete(units)
            };
        }
    }
}

pub(super) fn verify_mixed_conflict_semantic(
    conflict: &[TheoryLit],
    terms: &TermStore,
    support_axioms: &[TheoryLit],
) -> Result<(), VerificationError> {
    use ay_core::{TheoryResult, TheorySolver};

    // Every fragment choice and every definitive `Sat` verdict must describe
    // the complete context asserted into the fresh solver. In particular, a
    // support-only String/Seq or Int<->Real bridge cannot be ignored merely
    // because it is absent from the conflict explanation.
    let verification_context: Vec<_> = conflict
        .iter()
        .chain(support_axioms.iter())
        .copied()
        .collect();

    // Keep a complete fixed-context trail. In particular, support axioms must
    // participate in lemma cardinality: they may falsify all but one disjunct
    // (or the entire clause) even when that atom is absent from the conflict.
    let mut trail =
        ay_core::kani_compat::det_hash_map_with_capacity(conflict.len() + support_axioms.len());
    for lit in &verification_context {
        if trail
            .insert(lit.term, lit.value)
            .is_some_and(|old| old != lit.value)
        {
            // The conflict plus unconditional support is already
            // contradictory, so accepting the conflict is sound.
            return Ok(());
        }
    }

    // Route by which fresh solver (if any) can reproduce this conflict.
    // Arithmetic/EUF/Array -> Nelson-Oppen combiner (below). String literals
    // mixed with those -> fresh QF_SLIA adapter. BitVec / truly-unknown ->
    // still unverifiable, but now COUNTED rather than silently accepted.
    match classify_mixed_verifiability(terms, verification_context.iter().map(|l| l.term)) {
        MixedVerifiability::Combined => {}
        MixedVerifiability::StringsCombined => {
            return verify_strings_mixed_conflict_semantic(conflict, terms, &verification_context);
        }
        MixedVerifiability::Unverifiable => {
            observe_mixed_string_event(
                &mixed_string_verify_stats::SKIPPED_UNVERIFIABLE,
                "skipped-unverifiable-domain",
                conflict.len(),
            );
            return Ok(());
        }
    }

    // Mixed int/real (LIRA) conflicts are OUTSIDE the verifiable fragment:
    // no combiner interprets the int<->real bridge (`to_real` / `to_int` /
    // `is_int`), and `make_verification_combiner` picks UF+LIA whenever any
    // int-sorted operand appears, which leaves Real-sorted atoms and the
    // bridge coupling uninterpreted. A `Sat` verdict from such a re-solve
    // does NOT prove the conflict spurious — e.g. the VALID AUFLIRA conflict
    //   { k+2 <= 0,  0 <= x,  to_real(k+1) = f(k+1),  x < f(k+1) }
    // (k Int, x Real, f: Int -> Real) is reported SAT because the
    // k <-> to_real(k) coupling is dropped, and the hard
    // `ConflictIsSat -> Unknown` gate then degrades a decidable linear
    // mixed-int/real query to `unknown` (archimedean_nat regression).
    // Mirror the nonlinear skip (#7978): accept optimistically.
    if conflict_involves_int_real_mix(terms, &verification_context) {
        tracing::debug!(
            lit_count = conflict.len(),
            "mixed int/real (LIRA-bridged) conflict skipped semantic re-verification: \
             fresh combiners interpret a single numeric sort, so their SAT verdicts \
             are not trustworthy here (#6853 completeness)"
        );
        return Ok(());
    }
    if conflict_involves_nonlinear(terms, &verification_context) {
        tracing::debug!(
            lit_count = conflict.len(),
            "mixed nonlinear conflict skipped semantic re-verification: the \
             verification combiner carries only linear arithmetic solvers"
        );
        return Ok(());
    }

    // Chain the support-axiom terms into the combiner-selection scan so a
    // support atom carrying a sort ABSENT from the conflict (e.g. an Int-sorted
    // Seq-length axiom instance beside an EUF-only conflict) still steers the
    // UF+LIA / UF+LRA / Array combiner choice (the factory scans only its
    // `atoms` argument).
    let selected_combiner_kind =
        verification_combiner_kind(terms, verification_context.iter().map(|lit| lit.term));
    let mut combiner =
        make_verification_combiner(terms, verification_context.iter().map(|lit| lit.term));
    let mut verified_combiner_context = verification_context.clone();

    for lit in &verification_context {
        combiner.register_atom(lit.term);
    }
    // Register and assert the support axioms (#8123 datatype tautologies AND
    // #AUFLIA-support ground instances of unconditionally-asserted Foralls) so
    // the combined solver can reprove a conflict the isolated combiner would
    // otherwise call spuriously-Sat. Every support literal is true in every
    // model of the problem, so it can only CONFIRM a genuine conflict, never
    // manufacture one.
    for lit in &verification_context {
        combiner.assert_literal(lit.term, lit.value);
    }

    // Array and datatype solvers DRAIN a NeedLemmas batch after returning it:
    // the production DPLL(T) layer normally installs those clauses in SAT.
    // A bare second check therefore does not retain the emitted disjunction.
    // Materialize only consequences justified by this fixed trail:
    //   * zero live literals refutes the context immediately;
    //   * one live literal is unit-implied and may be asserted;
    //   * multiple live literals require a SAT split, so remain inconclusive.
    // Rechecking is sound only when every emitted clause is satisfied after
    // this closure. Speculative model equalities and arithmetic split requests
    // are never asserted here.
    const MAX_VERIFY_LEMMA_BATCHES: usize = 16;
    let mut remaining_batches = MAX_VERIFY_LEMMA_BATCHES;
    let mut seen_clauses: ay_core::kani_compat::DetHashSet<Vec<TheoryLit>> = Default::default();
    let mut result = combiner.check();

    loop {
        match result {
            TheoryResult::Unsat(_) | TheoryResult::UnsatWithFarkas(_) => return Ok(()),
            TheoryResult::Sat => return Err(VerificationError::ConflictIsSat),
            TheoryResult::NeedLemmas(lemmas) => {
                if remaining_batches == 0 || lemmas.is_empty() {
                    return Ok(());
                }
                remaining_batches -= 1;

                let mut clauses = Vec::with_capacity(lemmas.len());
                let mut has_new_clause = false;
                for lemma in lemmas {
                    let mut clause = lemma.clause;
                    clause.sort_unstable();
                    clause.dedup();
                    has_new_clause |= seen_clauses.insert(clause.clone());
                    clauses.push(clause);
                }

                match close_valid_lemma_clauses(&clauses, &mut trail) {
                    LemmaTrailClosure::Contradiction => return Ok(()),
                    LemmaTrailClosure::Inconclusive => return Ok(()),
                    LemmaTrailClosure::Complete(units) => {
                        // A repeated, already-satisfied batch cannot change
                        // this single-path verifier. Stop instead of spinning.
                        if units.is_empty() && !has_new_clause {
                            return Ok(());
                        }

                        // Lemma atoms were not part of the original combiner
                        // selection. Before a later `Sat` can reject the
                        // conflict, check that all materialized units remain in
                        // the same supported fragment and require the same
                        // concrete combiner. A support/lemma-only String,
                        // BitVec, nonlinear, or Int<->Real bridge is therefore
                        // inconclusive rather than a false definitive `Sat`.
                        verified_combiner_context.extend(units.iter().copied());
                        let still_combined = matches!(
                            classify_mixed_verifiability(
                                terms,
                                verified_combiner_context.iter().map(|lit| lit.term),
                            ),
                            MixedVerifiability::Combined
                        );
                        let same_combiner = verification_combiner_kind(
                            terms,
                            verified_combiner_context.iter().map(|lit| lit.term),
                        ) == selected_combiner_kind;
                        if !still_combined
                            || !same_combiner
                            || conflict_involves_int_real_mix(terms, &verified_combiner_context)
                            || conflict_involves_nonlinear(terms, &verified_combiner_context)
                        {
                            return Ok(());
                        }

                        for unit in units {
                            combiner.register_atom(unit.term);
                            combiner.assert_literal(unit.term, unit.value);
                        }
                        result = combiner.check();
                    }
                }
            }
            // NeedModelEquality/NeedModelEqualities are retractable model
            // guidance, while NeedSplit/NeedDisequalitySplit/
            // NeedExpressionSplit(s) require genuine SAT case splits. An
            // immutable, single-path verifier cannot resolve them without
            // choosing an unjustified branch. Unknown and string requests are
            // likewise inconclusive. Preserve the existing optimistic policy.
            _ => return Ok(()),
        }
    }
}

/// Verify a theory conflict semantically by dispatching to the appropriate
/// theory-specific verifier.
///
/// Determines the theory domain from conflict literal structure, then verifies
/// that all conflict atoms are jointly UNSAT via a fresh theory solver.
///
/// For mixed-domain conflicts (e.g., Arithmetic + EUF), uses the Nelson-Oppen
/// combined solver rather than skipping verification (#8123).
///
/// Promoted to all builds (#6564) to catch unsound conflicts.
pub(crate) fn verify_conflict_semantic(
    conflict: &[TheoryLit],
    terms: &TermStore,
    support_axioms: &[TheoryLit],
) -> Result<(), VerificationError> {
    verify_conflict_semantic_impl(conflict, terms, support_axioms, false)
}

/// Per-query memo type for fail-closed semantic conflict-verification
/// verdicts (#4535 memoized verifier): sorted conflict literal set -> whether
/// `verify_conflict_semantic` accepted it.
pub(crate) type ConflictSemanticVerifyMemo = ay_core::kani_compat::DetHashMap<Vec<TheoryLit>, bool>;

/// Memoized wrapper around [`verify_conflict_semantic`] (#4535 memoized
/// verifier).
///
/// The fail-closed semantic gate re-solves every theory conflict with a fresh
/// theory solver / Nelson-Oppen combiner. On verification-consumer AUFLIA VCs the
/// IDENTICAL conflict is re-derived up to thousands of times within one query
/// (index_range's LRA `contradictory_variable_bounds` was observed 2304x),
/// each re-derivation re-paying the full re-solve. The verdict is a pure
/// function of the conflict literal SET (a fresh re-solve verdict is a
/// property of the set, not the order), the term content behind the ids
/// (append-only within a session), and the support-axiom set — so cache it in
/// the caller-owned `memo`, keyed by the sorted literal vector. The Executor
/// clears its memo at `check_sat_internal` entry and on every support-set
/// rebuild (`process_quantifiers`), so no verdict outlives the state it was
/// computed against.
///
/// SOUNDNESS: a memoized `Ok` re-admits a literal set already proven jointly
/// UNSAT under this exact term/support state, so learning the clause is
/// exactly as justified as on the first derivation. A memoized `Err` keeps
/// the fail-closed bail — the conflict is NOT learned, identical to
/// re-running a failing verification.
pub(crate) fn verify_conflict_semantic_memoized(
    memo: &mut ConflictSemanticVerifyMemo,
    conflict: &[TheoryLit],
    terms: &TermStore,
    support_axioms: &[TheoryLit],
) -> Result<(), VerificationError> {
    let mut key = conflict.to_vec();
    key.sort_unstable();
    if let Some(&ok) = memo.get(&key) {
        ay_lia::instrument::bump_verify_conflict_memoized(true);
        return if ok {
            Ok(())
        } else {
            Err(VerificationError::Internal(
                "memoized verdict: identical conflict literal set previously failed \
                 fail-closed semantic verification in this query (#4535 memo)"
                    .to_string(),
            ))
        };
    }
    ay_lia::instrument::bump_verify_conflict_memoized(false);
    let result = verify_conflict_semantic_impl(conflict, terms, support_axioms, false);
    memo.insert(key, result.is_ok());
    result
}

/// Variant of [`verify_conflict_semantic`] for callers that have ALREADY run
/// `verify_euf_conflict` on exactly this conflict (with the same `support_axioms`).
///
/// The eager BCP path and the final-check path both run the direct EUF
/// fresh-solver re-solve first (it must run first: integer-variable equality
/// conflicts classified as Arithmetic need congruence closure), then call the
/// semantic dispatcher — which, for `TheoryDomain::Euf`, dispatches to the
/// byte-identical `verify_euf_conflict(conflict, terms, support_axioms)` again.
/// On congruence-heavy QF_UF (PEQ finite-model instances) that duplicate
/// fresh-solver re-solve was measured at ~30% of total solve time.
///
/// This variant skips ONLY the exact-duplicate Euf-domain dispatch; every
/// other domain (Arithmetic/BV/String/Array/Mixed/Unknown) verifies exactly
/// as before. Gate strength is unchanged: the identical check with identical
/// inputs was already performed by the caller.
pub(crate) fn verify_conflict_semantic_euf_prechecked(
    conflict: &[TheoryLit],
    terms: &TermStore,
    support_axioms: &[TheoryLit],
) -> Result<(), VerificationError> {
    verify_conflict_semantic_impl(conflict, terms, support_axioms, true)
}

fn verify_conflict_semantic_impl(
    conflict: &[TheoryLit],
    terms: &TermStore,
    support_axioms: &[TheoryLit],
    euf_prechecked: bool,
) -> Result<(), VerificationError> {
    // Pre-check: conflicts with contradictory literals (same term, opposite
    // values) are tautological as clauses — they cannot cause false-UNSAT.
    // The fresh-solver verifiers below assert each literal in sequence,
    // where later assertions overwrite earlier ones for the same term,
    // causing the verifier to see only one polarity and falsely report SAT.
    // Skip verification for these degenerate conflicts. (#8123/#4666)
    {
        let mut seen = ay_core::kani_compat::det_hash_map_with_capacity(conflict.len());
        for lit in conflict {
            if let Some(&prev_val) = seen.get(&lit.term) {
                if prev_val != lit.value {
                    // Same term appears with both true and false — tautological
                    // clause. Harmless but useless; skip semantic verification.
                    return Ok(());
                }
            }
            seen.insert(lit.term, lit.value);
        }
    }

    let domain = classify_conflict_domain(terms, conflict);
    match domain {
        TheoryDomain::Arithmetic => {
            // NIA conflicts contain nonlinear terms (e.g., x*y) that LIA/LRA
            // verifiers cannot evaluate. Skip semantic re-verification for
            // these — the NIA solver's bounded enumeration is itself exhaustive
            // and sound (#7978).
            if conflict_involves_nonlinear(terms, conflict) {
                return Ok(());
            }
            // Mixed int/real (LIRA) conflicts: neither the pure-LIA nor the
            // pure-LRA fresh re-solve is faithful (each interprets a single
            // numeric sort and drops the `to_real` bridge coupling), so a SAT
            // verdict would be a false positive on a valid bridged conflict.
            // Skip, mirroring the nonlinear skip above (#6853 completeness).
            if conflict_involves_int_real_mix(terms, conflict) {
                tracing::debug!(
                    lit_count = conflict.len(),
                    "mixed int/real arithmetic conflict skipped semantic \
                     re-verification (single-sort LIA/LRA verifiers are not \
                     faithful for LIRA-bridged conflicts)"
                );
                return Ok(());
            }
            // If any conflict literal involves Sort::Int, use the LIA verifier
            // which correctly handles integer-gap conflicts (e.g., x > 5 AND x < 6
            // is UNSAT over integers but SAT over reals). (#6849, #6853)
            let has_int = conflict
                .iter()
                .any(|lit| conflict_involves_int_sort(terms, lit.term));
            if has_int {
                verify_lia_conflict_semantic(conflict, terms)
            } else {
                verify_lra_conflict_semantic(conflict, terms)
            }
        }
        TheoryDomain::Euf => {
            if euf_prechecked {
                // Caller already ran the identical EUF fresh-solver re-solve
                // (see verify_conflict_semantic_euf_prechecked docs).
                Ok(())
            } else {
                verify_euf_conflict(conflict, terms, support_axioms)
            }
        }
        // BV conflicts: re-verify via fresh BV solver (#4535).
        TheoryDomain::BitVec => verify_bv_conflict_semantic(conflict, terms),
        // String conflicts: structural checks only (#4535).
        TheoryDomain::String => {
            if conflict_involves_seq_sort(terms, conflict) {
                verify_seq_conflict_semantic(conflict, terms)
            } else {
                verify_string_conflict_structural(conflict, terms)
            }
        }
        // Mixed, Array, and Unknown domains: use Nelson-Oppen combined solver
        // to verify the conflict across theory boundaries (#8123).
        TheoryDomain::Array => verify_mixed_conflict_semantic(conflict, terms, support_axioms),
        TheoryDomain::Unknown => {
            // #4535: Unknown-domain conflicts are NOT skipped — they are
            // delegated to the Nelson-Oppen combined verifier below, which
            // either reproves them (learnable) or fail-closes. Logged at
            // DEBUG: this is the routine dispatch route for mixed verification-consumer
            // AUFLIA conflicts (fired hundreds of times per solve as a WARN,
            // masquerading as a missing-verifier defect).
            tracing::debug!(
                lit_count = conflict.len(),
                "Unknown-domain theory conflict delegated to Nelson-Oppen \
                 combined verifier (#4535)"
            );
            verify_mixed_conflict_semantic(conflict, terms, support_axioms)
        }
    }
}

/// Check if a term or its operands involve Sort::Int.
/// Check if any conflict literal involves a nonlinear multiplication term.
///
/// A multiplication is nonlinear when it has two or more non-constant operands
/// (e.g., `x*y`). This is used to skip LIA/LRA semantic verification for NIA
/// conflicts, since linear solvers cannot evaluate nonlinear constraints (#7978).
fn conflict_involves_nonlinear(terms: &TermStore, conflict: &[TheoryLit]) -> bool {
    conflict
        .iter()
        .any(|lit| term_has_nonlinear_mul(terms, lit.term))
}

/// Recursively check if a term or its subterms contain a nonlinear multiplication.
fn term_has_nonlinear_mul(terms: &TermStore, term: TermId) -> bool {
    match terms.get(term) {
        TermData::Not(inner) => term_has_nonlinear_mul(terms, *inner),
        TermData::App(Symbol::Named(name), args) => {
            if name.as_str() == "*" {
                // Count non-constant variable-like operands
                let var_count = args
                    .iter()
                    .filter(|&&a| terms.extract_integer_constant(a).is_none())
                    .count();
                if var_count >= 2 {
                    return true;
                }
            }
            // Recurse into arguments
            args.iter().any(|&a| term_has_nonlinear_mul(terms, a))
        }
        _ => false,
    }
}

/// Whether a conflict spans BOTH integer and real arithmetic — directly
/// (some literal has an Int-sorted operand while another has a Real-sorted
/// operand) or through an explicit int<->real bridge application
/// (`to_real` / `to_int` / `is_int`) in any subterm.
///
/// The fresh-solver semantic verifiers interpret ONE numeric sort:
/// `verify_lia_conflict_semantic` / `TheoryCombiner::uf_lia` leave Real atoms
/// uninterpreted, and `verify_lra_conflict_semantic` / `uf_lra` drop
/// integrality and the `to_real` coupling. Their `Sat` verdicts are therefore
/// not trustworthy on such conflicts (known false-positive class); callers
/// skip semantic re-verification instead (#6853 completeness).
fn conflict_involves_int_real_mix(terms: &TermStore, conflict: &[TheoryLit]) -> bool {
    let mut has_int = false;
    let mut has_real = false;
    for lit in conflict {
        if term_has_int_real_bridge(terms, lit.term) {
            return true;
        }
        has_int |= conflict_involves_int_sort(terms, lit.term);
        has_real |= conflict_involves_real_sort(terms, lit.term);
    }
    has_int && has_real
}

/// Recursively check whether a term contains an int<->real bridge application
/// (`to_real`, `to_int`, `is_int`).
///
/// Walks the term DAG with a visited set: hash-consed terms share subterms
/// heavily (the QF_AX swap chains reference the previous chain level ~3 times
/// per store level), so the naive tree recursion re-visited shared nodes
/// near-exponentially — measured at ~5% of total solve time on the swap
/// family, on a logic with no arithmetic at all. Memoization only skips
/// already-visited nodes, so the answer is unchanged.
fn term_has_int_real_bridge(terms: &TermStore, term: TermId) -> bool {
    fn walk(
        terms: &TermStore,
        term: TermId,
        visited: &mut std::collections::HashSet<TermId>,
    ) -> bool {
        if !visited.insert(term) {
            return false;
        }
        match terms.get(term) {
            TermData::Not(inner) => walk(terms, *inner, visited),
            TermData::App(Symbol::Named(name), args) => {
                matches!(name.as_str(), "to_real" | "to_int" | "is_int")
                    || args.iter().any(|&a| walk(terms, a, visited))
            }
            TermData::App(_, args) => args.iter().any(|&a| walk(terms, a, visited)),
            TermData::Ite(c, t, e) => {
                walk(terms, *c, visited) || walk(terms, *t, visited) || walk(terms, *e, visited)
            }
            _ => false,
        }
    }
    let mut visited: std::collections::HashSet<TermId> = std::collections::HashSet::new();
    walk(terms, term, &mut visited)
}

fn conflict_involves_int_sort(terms: &TermStore, term: TermId) -> bool {
    let mut t = term;
    while let TermData::Not(inner) = terms.get(t) {
        t = *inner;
    }
    match terms.get(t) {
        TermData::App(_, args) => args.iter().any(|&a| matches!(terms.sort(a), Sort::Int)),
        _ => false,
    }
}

/// Check if a term or its operands involve Sort::Real.
fn conflict_involves_real_sort(terms: &TermStore, term: TermId) -> bool {
    let mut t = term;
    while let TermData::Not(inner) = terms.get(t) {
        t = *inner;
    }
    match terms.get(t) {
        TermData::App(_, args) => args.iter().any(|&a| matches!(terms.sort(a), Sort::Real)),
        _ => false,
    }
}

/// Which fresh solver, if any, can re-solve a mixed-domain literal set.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum MixedVerifiability {
    /// Every literal is Arithmetic / EUF / Array (or a UF-arithmetic equality),
    /// and at least one is recognizable: the Nelson-Oppen verification combiner
    /// can re-solve it.
    Combined,
    /// At least one native String-domain term and no immediately-unverifiable
    /// literal. The downstream QF_SLIA gate performs the final no-Array,
    /// no-Real, linear-fragment checks before treating `Sat` as definitive.
    StringsCombined,
    /// A BitVec or truly-unknown literal is present — no fresh solver in this
    /// module reproduces the conflict. Still accepted, but COUNTED.
    Unverifiable,
}

/// Classify which fresh solver can re-verify a mixed-domain literal set.
///
/// BEFORE (#mixed-string-verify-gap): a single boolean, where any String
/// literal collapsed to "unverifiable" on the rationale that String conflicts
/// "have their own dedicated verifiers". That rationale holds only for
/// conflicts classifying PURELY into the String domain — the string gate is
/// reached via `TheoryDomain::String`, which a mixed string+arithmetic conflict
/// never classifies as. So mixed conflicts hit no gate at all. Splitting the
/// verdict three ways routes them to the QF_SLIA adapter instead.
fn classify_mixed_verifiability(
    terms: &TermStore,
    lits: impl Iterator<Item = TermId>,
) -> MixedVerifiability {
    let mut has_recognizable = false;
    let mut has_string = false;
    for term in lits {
        // Arithmetic atoms and UF-arithmetic equalities can hide a native
        // String->Int operation below their top-level operator. Treat that as
        // String content even when `classify_term_domain` returns Arithmetic
        // or Unknown; otherwise a support-only `str.len` bridge can be sent to
        // UF+LIA and its unconstrained value can make a `Sat` verdict look
        // definitive.
        has_string |= term_mentions_native_string_content(terms, term);
        match classify_term_domain(terms, term) {
            TheoryDomain::Arithmetic | TheoryDomain::Euf | TheoryDomain::Array => {
                has_recognizable = true;
            }
            TheoryDomain::Unknown if is_verifiable_uf_arith_equality(terms, term) => {
                has_recognizable = true;
            }
            TheoryDomain::String => {
                has_string = true;
            }
            TheoryDomain::BitVec | TheoryDomain::Unknown => {
                // BV and truly-unknown domains cannot be verified with either
                // combined solver; BV has its own structural verifier (#4535).
                return MixedVerifiability::Unverifiable;
            }
        }
    }
    if has_string {
        // Note: a set of ONLY String literals is dispatched to the dedicated
        // string gate by `classify_conflict_domain`, so it does not reach here;
        // routing it to the SLIA adapter anyway would still be sound (the
        // adapter subsumes the bare StringSolver).
        return MixedVerifiability::StringsCombined;
    }
    if has_recognizable {
        MixedVerifiability::Combined
    } else {
        MixedVerifiability::Unverifiable
    }
}

/// Check whether a set of literals involves only theory domains the
/// Nelson-Oppen verification combiner handles (Arithmetic, EUF, Array) and at
/// least one recognizable theory.
///
/// Semantics unchanged: `true` exactly when
/// [`classify_mixed_verifiability`] says `Combined`. The propagation-side
/// verifier still uses this narrow predicate (there is no SLIA propagation
/// verifier — see `verify_mixed_propagation_semantic`).
fn is_verifiable_mixed_domain(terms: &TermStore, lits: impl Iterator<Item = TermId>) -> bool {
    matches!(
        classify_mixed_verifiability(terms, lits),
        MixedVerifiability::Combined
    )
}

fn is_verifiable_uf_arith_equality(terms: &TermStore, term: TermId) -> bool {
    is_uf_int_equality(terms, term).is_some() || is_uf_real_equality(terms, term).is_some()
}

/// Whether any subterm of `term` is a `store` application.
///
/// Used by [`is_array_extensionality_literal`] to recognize the store-chain
/// read-back / commutativity shape (`select(store(...), i)`) that the isolated
/// combiner cannot reprove without eager ROW preprocessing.
fn term_mentions_store(terms: &TermStore, term: TermId) -> bool {
    let mut visited: std::collections::HashSet<TermId> = std::collections::HashSet::new();
    let mut stack = vec![term];
    while let Some(t) = stack.pop() {
        if !visited.insert(t) {
            continue;
        }
        match terms.get(t) {
            TermData::App(Symbol::Named(name), args) => {
                if name == "store" {
                    return true;
                }
                stack.extend(args.iter().copied());
            }
            TermData::App(_, args) => stack.extend(args.iter().copied()),
            TermData::Not(inner) => stack.push(*inner),
            TermData::Ite(c, a, b) => {
                stack.push(*c);
                stack.push(*a);
                stack.push(*b);
            }
            TermData::Let(bindings, body) => {
                for (_, v) in bindings {
                    stack.push(*v);
                }
                stack.push(*body);
            }
            TermData::Forall(_, body, _) | TermData::Exists(_, body, _) => stack.push(*body),
            _ => {}
        }
    }
    false
}

/// Whether a single conflict literal has the array-extensionality / read-over-
/// write conflict SHAPE that the isolated verification combiner is known to be
/// incomplete on: an `=` / `distinct` atom that is either
///
///   (a) over `Array`-sorted operands (an array (dis)equality — the
///       store-commutativity / extensionality shape
///       `store(store(a,i,v),j,v) != store(store(a,j,v),i,v)`), or
///   (b) over operands whose term tree contains a `store` (a store-chain
///       read-back equality such as `select(store(store(a,i,v),j,w),i) = v`).
///
/// Everything else — an arithmetic inequality (`<=`,`<`,`>=`,`>`) that merely
/// mentions a `select`, or an `=` over a `select` of a *bare* array variable
/// (no store, decidable by plain congruence) — is deliberately NOT this shape.
/// Those are exactly the mixed array+arith literals the adversarial review
/// flagged: if such a literal were the only "array context" in a conflict whose
/// arithmetic projection is standalone-SAT, the old
/// `term_has_array_context`-based predicate would launder a genuinely-spurious
/// `ConflictIsSat` into a WRONG UNSAT. Requiring the load-bearing array
/// (dis)equality shape closes that path (fail-closed to Unknown instead).
fn is_array_extensionality_literal(terms: &TermStore, term: TermId) -> bool {
    // Strip leading NOT layers to reach the atom.
    let mut atom = term;
    while let TermData::Not(inner) = terms.get(atom) {
        atom = *inner;
    }
    match terms.get(atom) {
        TermData::App(Symbol::Named(name), args) if name == "=" || name == "distinct" => {
            args.iter().any(|&arg| {
                matches!(terms.sort(arg), Sort::Array(_)) || term_mentions_store(terms, arg)
            })
        }
        _ => false,
    }
}

/// Whether a conflict carries a genuine array-extensionality / read-over-write
/// (dis)equality literal (see [`is_array_extensionality_literal`]).
///
/// Used by the eager `TheoryExtension` (check.rs) to scope its ONLY
/// accept-optimistic carve-out to array-context `ConflictIsSat` verdicts. The
/// isolated Nelson-Oppen verification combiner runs `verify_only` without the
/// eager ROW1/ROW2 + extensionality lemma preprocessing the production array
/// solver drives, so it cannot reprove array-extensionality tautologies such as
/// store-commutativity `store(store(a,i,v),j,v) = store(store(a,j,v),i,v)`. Its
/// `Sat` verdict on such a conflict is therefore a KNOWN false positive, not a
/// spuriousness proof — the same class of known-incomplete-verifier skip as the
/// nonlinear (#7978) and LIRA int/real (#6853) skips inside
/// [`verify_conflict_semantic`]. This is intentionally scoped to the eager path:
/// the shared verifier keeps rejecting array `ConflictIsSat` so the fail-closed
/// pipeline gates (6b7a57f921 / 472d9c23df) still catch genuinely-spurious,
/// ROW-verifiable array conflicts.
///
/// NARROWED (adversarial review): the predicate now requires the conflict to
/// contain a literal with the actual array (dis)equality / store-chain
/// extensionality shape, rather than accepting when ANY literal merely *mentions*
/// a `select`/`store`/array term anywhere in its tree. The old test over-matched
/// mixed array+arithmetic conflicts, so a spurious `ConflictIsSat` whose array
/// term only appeared inside an arithmetic literal (arith projection
/// standalone-SAT, no load-bearing array reasoning) could be laundered into a
/// wrong UNSAT. This is a pure RESTRICTION of an optimistic accept: strictly
/// more conflicts now fail closed to Unknown, never fewer.
pub(crate) fn conflict_has_array_context(terms: &TermStore, conflict: &[TheoryLit]) -> bool {
    conflict
        .iter()
        .any(|lit| is_array_extensionality_literal(terms, lit.term))
}

/// Classify the theory domain of a conflict's literals.
pub(super) fn classify_conflict_domain(terms: &TermStore, conflict: &[TheoryLit]) -> TheoryDomain {
    let mut result = TheoryDomain::Unknown;
    let mut saw_unknown_literal = false;
    for lit in conflict {
        let domain = classify_term_domain(terms, lit.term);
        match (result, domain) {
            (TheoryDomain::Unknown, TheoryDomain::Unknown) => {
                saw_unknown_literal = true;
            }
            (TheoryDomain::Unknown, d) => {
                if saw_unknown_literal {
                    return TheoryDomain::Unknown;
                }
                result = d;
            }
            (_, TheoryDomain::Unknown) => return TheoryDomain::Unknown,
            (a, b) if a == b => {}
            _ => return TheoryDomain::Unknown,
        }
    }
    result
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum VerificationCombinerKind {
    UfLia,
    UfLra,
    AufLia,
    AufLra,
    ArrayEuf,
}

fn verification_combiner_kind(
    terms: &TermStore,
    atoms: impl Iterator<Item = TermId>,
) -> VerificationCombinerKind {
    let mut has_int = false;
    let mut has_real = false;
    let mut has_array = false;

    for term in atoms {
        has_int |= conflict_involves_int_sort(terms, term);
        has_real |= conflict_involves_real_sort(terms, term);
        has_array |= term_has_array_context(terms, term);
    }

    if has_int {
        if has_array {
            VerificationCombinerKind::AufLia
        } else {
            VerificationCombinerKind::UfLia
        }
    } else if has_real {
        if has_array {
            VerificationCombinerKind::AufLra
        } else {
            VerificationCombinerKind::UfLra
        }
    } else if has_array {
        VerificationCombinerKind::ArrayEuf
    } else {
        // Default to UF+LIA for mixed uninterpreted/other domains.
        VerificationCombinerKind::UfLia
    }
}

pub(crate) fn make_verification_combiner(
    terms: &TermStore,
    atoms: impl Iterator<Item = TermId>,
) -> crate::combined_solvers::combiner::TheoryCombiner<'_> {
    use crate::combined_solvers::combiner::TheoryCombiner;

    let mut combiner = match verification_combiner_kind(terms, atoms) {
        VerificationCombinerKind::UfLia => TheoryCombiner::uf_lia(terms),
        VerificationCombinerKind::UfLra => TheoryCombiner::uf_lra(terms),
        VerificationCombinerKind::AufLia => TheoryCombiner::auf_lia(terms),
        VerificationCombinerKind::AufLra => TheoryCombiner::auf_lra(terms),
        VerificationCombinerKind::ArrayEuf => TheoryCombiner::array_euf(terms),
    };
    // #uflia-verify-only: every caller of this factory is a fail-closed
    // verification re-check that pattern-matches only the `TheoryResult`
    // variant. Skip the LIA post-verdict conflict augmentation (probe loop) —
    // verdicts are byte-identical, and the payload is discarded.
    combiner.set_verify_only(true);
    combiner
}

/// Verify a mixed-domain theory propagation using the Nelson-Oppen combined
/// solver (#8123).
///
/// For propagations involving literals from multiple theory domains (e.g.,
/// arithmetic reason literals implying an EUF equality), individual theory
/// solvers cannot validate the propagation in isolation. Use TheoryCombiner
/// to check that reason ∧ ¬propagated is UNSAT under the combined theory.
// #8529: Used in all builds (verify_propagation_semantic is now release-enabled).
fn verify_mixed_propagation_semantic(
    propagation: &TheoryPropagation,
    terms: &TermStore,
) -> Result<(), VerificationError> {
    use ay_core::{TheoryResult, TheorySolver};

    verify_theory_propagation(propagation)?;

    // Only attempt combined verification when all literals belong to
    // recognizable theory domains. Skip for Bool, BitVec, String, etc.
    let all_terms = propagation
        .reason
        .iter()
        .map(|l| l.term)
        .chain(std::iter::once(propagation.literal.term));
    if !is_verifiable_mixed_domain(terms, all_terms) {
        return Ok(());
    }

    let all_terms = propagation
        .reason
        .iter()
        .map(|l| l.term)
        .chain(std::iter::once(propagation.literal.term));
    let mut combiner = make_verification_combiner(terms, all_terms);

    for lit in &propagation.reason {
        combiner.register_atom(lit.term);
    }
    combiner.register_atom(propagation.literal.term);

    for lit in &propagation.reason {
        combiner.assert_literal(lit.term, lit.value);
    }
    combiner.assert_literal(propagation.literal.term, !propagation.literal.value);

    match combiner.check() {
        TheoryResult::Unsat(_) | TheoryResult::UnsatWithFarkas(_) => Ok(()),
        TheoryResult::Sat => Err(VerificationError::PropagationNotImplied {
            term: propagation.literal.term,
            value: propagation.literal.value,
        }),
        // Unknown / split: accept optimistically.
        _ => Ok(()),
    }
}

/// Verify a theory propagation semantically by dispatching to the appropriate
/// theory-specific verifier.
///
/// Called at both propagation acceptance sites (eager and lazy).
/// Determines the theory domain from term structure, then verifies:
/// - Arithmetic propagations via LRA solver (reason ∧ ¬propagated → ⊥)
/// - EUF propagations via congruence closure (reason ∧ ¬propagated → ⊥)
/// - Array propagations via combined ArrayEuf solver (reason ∧ ¬propagated → ⊥)
/// - Mixed/unknown domain: verified via Nelson-Oppen combined solver (#8123)
pub(crate) fn verify_propagation_semantic(
    propagation: &TheoryPropagation,
    terms: &TermStore,
) -> Result<(), VerificationError> {
    let domain = classify_propagation_domain(terms, propagation);

    match domain {
        TheoryDomain::Arithmetic if propagation_is_int_linear(propagation, terms) => {
            verify_lia_propagation(propagation, terms)
        }
        TheoryDomain::Arithmetic => verify_lra_propagation(propagation, terms),
        TheoryDomain::Euf => verify_euf_propagation(propagation, terms),
        TheoryDomain::Array => verify_array_propagation(propagation, terms),
        TheoryDomain::BitVec => verify_bv_propagation(propagation, terms),
        TheoryDomain::String => verify_string_propagation(propagation, terms),
        TheoryDomain::Unknown => {
            // #4535: delegated (not skipped) — see the conflict-side arm.
            tracing::debug!(
                term = ?propagation.literal.term,
                value = propagation.literal.value,
                reason_count = propagation.reason.len(),
                "Unknown-domain theory propagation delegated to Nelson-Oppen \
                 combined verifier (#4535)"
            );
            verify_mixed_propagation_semantic(propagation, terms)
        }
    }
}

/// Log conflict details for debugging (only in debug builds with AY_DEBUG_VERIFY)
#[cfg(debug_assertions)]
pub(crate) fn log_conflict_debug(conflict: &[TheoryLit], context: &str) {
    if crate::theory_debug_flags::debug_verify() {
        safe_eprintln!(
            "[verify_theory_conflict] {}: {} literals",
            context,
            conflict.len()
        );
        for (i, lit) in conflict.iter().enumerate() {
            safe_eprintln!("  [{i}] term={:?} value={}", lit.term, lit.value);
        }
    }
}

/// Log conflict details WITH term data for debugging (#8012 diagnosis).
/// Only in debug builds with AY_DEBUG_VERIFY.
#[cfg(debug_assertions)]
pub(crate) fn log_conflict_debug_with_terms(
    conflict: &[TheoryLit],
    context: &str,
    terms: &TermStore,
) {
    if crate::theory_debug_flags::debug_verify() {
        safe_eprintln!(
            "[verify_theory_conflict] {}: {} literals",
            context,
            conflict.len()
        );
        for (i, lit) in conflict.iter().enumerate() {
            let expr = format_term_recursive(terms, lit.term, 4);
            safe_eprintln!(
                "  [{i}] term={:?} value={} expr={}",
                lit.term,
                lit.value,
                expr
            );
        }
    }
}

#[cfg(not(debug_assertions))]
pub(crate) fn log_conflict_debug_with_terms(
    _conflict: &[TheoryLit],
    _context: &str,
    _terms: &TermStore,
) {
}

#[cfg(not(debug_assertions))]
/// No-op in release builds.
pub(crate) fn log_conflict_debug(_conflict: &[TheoryLit], _context: &str) {
    // No-op in release builds
}

/// Log propagation details for debugging (only in debug builds with AY_DEBUG_VERIFY)
#[cfg(debug_assertions)]
pub(crate) fn log_propagation_debug(propagation: &TheoryPropagation, context: &str) {
    if crate::theory_debug_flags::debug_verify() {
        tracing::debug!(
            context,
            term = ?propagation.literal.term,
            value = propagation.literal.value,
            reason_count = propagation.reason.len(),
            "verify_theory_propagation"
        );
    }
}

#[cfg(not(debug_assertions))]
/// No-op in release builds.
pub(crate) fn log_propagation_debug(_propagation: &TheoryPropagation, _context: &str) {
    // No-op in release builds
}

#[cfg(test)]
mod mixed_string_conflict_gate_tests {
    //! Pins the mixed string+arithmetic conflict gate
    //! (#mixed-string-verify-gap).
    //!
    //! BEFORE: `classify_conflict_domain` returns `Unknown` for a conflict that
    //! mixes `(= x "ab")` (String domain) with `(>= (str.len x) 2)`
    //! (Arithmetic domain — the `str.len` sits inside an arithmetic atom), so
    //! it dispatched to `verify_mixed_conflict_semantic`, whose
    //! `is_verifiable_mixed_domain` bail returned `Ok(())` on sight of the
    //! String literal. The conflict was accepted with NO semantic verification
    //! by ANY gate. These tests prove the gate now (a) fires, (b) REJECTS a
    //! provably-spurious mixed conflict, and (c) does NOT reject a valid one.
    use super::*;
    use ay_core::TheoryLit;

    /// `(= x "ab")` — String-domain literal.
    fn str_eq_const(terms: &mut TermStore, name: &str, value: &str) -> (TermId, TermId) {
        let x = terms.mk_var(name, Sort::String);
        let c = terms.mk_string(value.to_string());
        (x, terms.mk_eq(x, c))
    }

    /// `(>= (str.len x) k)` — Arithmetic-domain literal mentioning a string.
    fn str_len_ge(terms: &mut TermStore, x: TermId, k: i64) -> TermId {
        let len = terms.mk_app(Symbol::named("str.len"), vec![x], Sort::Int);
        let kk = terms.mk_int(num_bigint::BigInt::from(k));
        terms.mk_ge(len, kk)
    }

    /// The literal shapes really do straddle the domain classifier the way the
    /// gap description claims — this is the precondition for everything below.
    #[test]
    fn mixed_string_arith_conflict_classifies_unknown_and_routes_to_slia() {
        let mut terms = TermStore::new();
        let (x, eq) = str_eq_const(&mut terms, "x", "ab");
        let ge = str_len_ge(&mut terms, x, 2);
        assert_eq!(classify_term_domain(&terms, eq), TheoryDomain::String);
        assert_eq!(classify_term_domain(&terms, ge), TheoryDomain::Arithmetic);
        let conflict = vec![TheoryLit::new(eq, true), TheoryLit::new(ge, true)];
        // The dispatcher sends this to verify_mixed_conflict_semantic...
        assert_eq!(
            classify_conflict_domain(&terms, &conflict),
            TheoryDomain::Unknown
        );
        // ...which BEFORE the fix bailed out (`is_verifiable_mixed_domain` ==
        // false) and accepted unverified; now it routes to the SLIA adapter.
        assert!(
            !is_verifiable_mixed_domain(&terms, conflict.iter().map(|l| l.term)),
            "the Nelson-Oppen combiner still cannot take this conflict"
        );
        assert_eq!(
            classify_mixed_verifiability(&terms, conflict.iter().map(|l| l.term)),
            MixedVerifiability::StringsCombined,
            "mixed string+arith conflicts must route to the QF_SLIA verifier"
        );
    }

    /// THE POINT OF THE GATE: a SPURIOUS mixed string+arith conflict —
    /// `{(= x "ab"), (>= (str.len x) 2)}` is jointly SATISFIABLE (x = "ab" has
    /// length 2), so a theory claiming it is a conflict would learn the unsound
    /// blocking clause `¬(= x "ab") ∨ ¬(>= (str.len x) 2)` and can produce a
    /// wrong UNSAT. BEFORE the fix this was accepted silently. It MUST now be
    /// rejected.
    #[test]
    fn spurious_mixed_string_arith_conflict_is_rejected() {
        let mut terms = TermStore::new();
        let (x, eq) = str_eq_const(&mut terms, "x", "ab");
        let ge = str_len_ge(&mut terms, x, 2);
        let conflict = vec![TheoryLit::new(eq, true), TheoryLit::new(ge, true)];

        let before = mixed_string_verify_counts();
        let result = verify_conflict_semantic(&conflict, &terms, &[]);
        let after = mixed_string_verify_counts();

        assert!(
            result.is_err(),
            "a provably-satisfiable mixed string+arith conflict must be REJECTED \
             (fresh QF_SLIA re-solve proves x=\"ab\" ∧ len(x)>=2 satisfiable); got {result:?}"
        );
        assert!(
            matches!(result, Err(VerificationError::ConflictIsSat)),
            "rejection must be ConflictIsSat so the caller degrades to Unknown; got {result:?}"
        );
        // Observability: the rejection is counted, never silent.
        assert!(
            after.verified > before.verified,
            "the gate must record that it ran the re-solve"
        );
        assert!(
            after.rejected_sat > before.rejected_sat,
            "the rejection must be counted"
        );
    }

    /// The completeness half of the contract: a VALID mixed conflict —
    /// `{(= x "ab"), (>= (str.len x) 3)}` is jointly UNSAT (len("ab") = 2) —
    /// must NOT be rejected. Rejecting valid conflicts is exactly the failure
    /// mode the naive "reject all mixed string conflicts" fix would have had.
    #[test]
    fn valid_mixed_string_arith_conflict_is_accepted() {
        let mut terms = TermStore::new();
        let (x, eq) = str_eq_const(&mut terms, "x", "ab");
        let ge = str_len_ge(&mut terms, x, 3);
        let conflict = vec![TheoryLit::new(eq, true), TheoryLit::new(ge, true)];
        assert!(
            verify_conflict_semantic(&conflict, &terms, &[]).is_ok(),
            "a genuinely-unsatisfiable mixed string+arith conflict must be ACCEPTED"
        );
    }

    /// The dropped-coupling guard: `{(= x "ab"), (<= (+ (str.len x) n) 1),
    /// (>= n 0)}` is a VALID conflict (len(x) = 2 forces n <= -1, contradicting
    /// n >= 0), but the isolated adapter has no `str.len` axioms so LIA picks
    /// `len_x = 1` and reports `Sat`. The literal mentioning the pinned length
    /// still has a free `n`, so the verdict is `Unfaithful` and the conflict is
    /// ACCEPTED — counted, not silently.
    #[test]
    fn unpinnable_length_arithmetic_is_accepted_as_unfaithful() {
        let mut terms = TermStore::new();
        let (x, eq) = str_eq_const(&mut terms, "x", "ab");
        let len = terms.mk_app(Symbol::named("str.len"), vec![x], Sort::Int);
        let n = terms.mk_var("n", Sort::Int);
        let sum = terms.mk_add(vec![len, n]);
        let one = terms.mk_int(num_bigint::BigInt::from(1));
        let zero = terms.mk_int(num_bigint::BigInt::from(0));
        let le = terms.mk_le(sum, one);
        let ge = terms.mk_ge(n, zero);
        let conflict = vec![
            TheoryLit::new(eq, true),
            TheoryLit::new(le, true),
            TheoryLit::new(ge, true),
        ];
        assert_eq!(
            assess_slia_sat_trust(&terms, &conflict),
            SliaSatTrust::Unfaithful,
            "an arithmetic literal mixing a pinned length with a free Int leaves \
             LIA free to choose the length, so its Sat proves nothing"
        );
        assert!(
            verify_conflict_semantic(&conflict, &terms, &[]).is_ok(),
            "a valid conflict whose Sat verdict is an artifact of the dropped \
             str.len coupling must be ACCEPTED"
        );
    }

    /// When NO string->int bridge term appears, the fresh QF_SLIA solve drops
    /// no coupling at all, so a `Sat` verdict is a genuine satisfiability proof
    /// and the spurious conflict `{(= x "ab"), (>= n 5)}` is rejected.
    #[test]
    fn bridge_free_spurious_mixed_conflict_is_rejected() {
        let mut terms = TermStore::new();
        let (_x, eq) = str_eq_const(&mut terms, "x", "ab");
        let n = terms.mk_var("n", Sort::Int);
        let five = terms.mk_int(num_bigint::BigInt::from(5));
        let ge = terms.mk_ge(n, five);
        let conflict = vec![TheoryLit::new(eq, true), TheoryLit::new(ge, true)];
        assert_eq!(
            assess_slia_sat_trust(&terms, &conflict),
            SliaSatTrust::Trustworthy
        );
        assert!(
            matches!(
                verify_conflict_semantic(&conflict, &terms, &[]),
                Err(VerificationError::ConflictIsSat)
            ),
            "x = \"ab\" ∧ n >= 5 is plainly satisfiable — this conflict is spurious"
        );
    }

    /// The ground-refutation escape hatch is exercised by the valid conflict
    /// above: `{(= x "ab"), (>= (str.len x) 3)}` pins len(x)=2, and `2 >= 3`
    /// evaluates FALSE against its asserted `true` polarity.
    #[test]
    fn valid_length_conflict_is_ground_refuted_not_rejected() {
        let mut terms = TermStore::new();
        let (x, eq) = str_eq_const(&mut terms, "x", "ab");
        let ge = str_len_ge(&mut terms, x, 3);
        let conflict = vec![TheoryLit::new(eq, true), TheoryLit::new(ge, true)];
        assert_eq!(
            assess_slia_sat_trust(&terms, &conflict),
            SliaSatTrust::GroundRefuted
        );
    }

    /// Fail-closed size cap, mirroring `e40292e686`: a mixed string conflict
    /// larger than the cap is REJECTED, not trusted. A cost cap that fails open
    /// trusts precisely the largest, least-verifiable conflicts.
    #[test]
    fn oversized_mixed_string_conflict_fails_closed() {
        let mut terms = TermStore::new();
        let (x, eq) = str_eq_const(&mut terms, "x", "ab");
        let mut conflict = vec![TheoryLit::new(eq, true)];
        // Distinct arithmetic literals over distinct Int vars, so the
        // duplicate/tautology pre-checks do not short-circuit.
        for i in 0..MAX_MIXED_STRING_CONFLICT_LITS {
            let v = terms.mk_var(format!("n{i}"), Sort::Int);
            let k = terms.mk_int(num_bigint::BigInt::from(i as i64));
            let atom = terms.mk_ge(v, k);
            conflict.push(TheoryLit::new(atom, true));
        }
        let _ = x;
        assert!(conflict.len() > MAX_MIXED_STRING_CONFLICT_LITS);
        let before = mixed_string_verify_counts();
        let result = verify_conflict_semantic(&conflict, &terms, &[]);
        let after = mixed_string_verify_counts();
        assert!(
            matches!(result, Err(VerificationError::ConflictIsSat)),
            "over-cap mixed string conflict must fail CLOSED; got {result:?}"
        );
        assert!(after.rejected_over_cap > before.rejected_over_cap);
    }

    /// Routing guard: a BitVec literal still bails (BV has its own structural
    /// verifier and neither combined solver reads it) — but the bail is now
    /// COUNTED instead of being an invisible `Ok(())`.
    #[test]
    fn bitvec_mixed_conflict_still_bails_but_is_counted() {
        let mut terms = TermStore::new();
        let (_x, eq) = str_eq_const(&mut terms, "x", "ab");
        let bvs = Sort::BitVec(ay_core::BitVecSort::new(8));
        let bv = terms.mk_var("b", bvs.clone());
        let bv2 = terms.mk_var("c", bvs);
        let bv_eq = terms.mk_eq(bv, bv2);
        let conflict = vec![TheoryLit::new(eq, true), TheoryLit::new(bv_eq, true)];
        assert_eq!(
            classify_mixed_verifiability(&terms, conflict.iter().map(|l| l.term)),
            MixedVerifiability::Unverifiable
        );
        let before = mixed_string_verify_counts();
        assert!(verify_conflict_semantic(&conflict, &terms, &[]).is_ok());
        let after = mixed_string_verify_counts();
        assert!(
            after.skipped_unverifiable > before.skipped_unverifiable,
            "a remaining skip must be observable (counter), never silent"
        );
    }

    /// Pure arithmetic + EUF still routes to the Nelson-Oppen combiner — the
    /// refactor of `is_verifiable_mixed_domain` is semantics-preserving there.
    #[test]
    fn arith_euf_mix_still_routes_to_nelson_oppen() {
        let mut terms = TermStore::new();
        let a = terms.mk_var("a", Sort::Int);
        let b = terms.mk_var("b", Sort::Int);
        let f_a = terms.mk_app(Symbol::named("f"), vec![a], Sort::Int);
        let f_b = terms.mk_app(Symbol::named("f"), vec![b], Sort::Int);
        let euf_eq = terms.mk_eq(f_a, f_b);
        let five = terms.mk_int(num_bigint::BigInt::from(5));
        let arith = terms.mk_le(a, five);
        let lits = [euf_eq, arith];
        assert_eq!(
            classify_mixed_verifiability(&terms, lits.iter().copied()),
            MixedVerifiability::Combined
        );
        assert!(is_verifiable_mixed_domain(&terms, lits.iter().copied()));
    }
}

#[cfg(test)]
mod array_context_predicate_tests {
    //! Pins the NARROWED `conflict_has_array_context` predicate: it accepts an
    //! optimistic array `ConflictIsSat` verdict on the eager path ONLY when the
    //! conflict carries a genuine array (dis)equality / store-chain
    //! extensionality literal — not when an array term is merely *mentioned*
    //! inside an arithmetic literal. See the adversarial-review narrowing on
    //! [`conflict_has_array_context`].
    use super::*;
    use ay_core::{ArraySort, TheoryLit};

    fn int_array_sort() -> Sort {
        Sort::Array(Box::new(ArraySort::new(Sort::Int, Sort::Int)))
    }

    fn lit(term: TermId) -> TheoryLit {
        // Polarity is irrelevant to the predicate; it strips leading NOTs.
        TheoryLit::new(term, false)
    }

    /// Store-commutativity disequality `(distinct (store(store a i v) j v)
    /// (store(store a j v) i v))` is over Array-sorted operands — the shape the
    /// carve-out exists for. MUST be recognized (else the storecomm regressions
    /// degrade to Unknown).
    #[test]
    fn store_commutativity_array_diseq_is_recognized() {
        let mut terms = TermStore::new();
        let a = terms.mk_var("a", int_array_sort());
        let i = terms.mk_var("i", Sort::Int);
        let j = terms.mk_var("j", Sort::Int);
        let v = terms.mk_var("v", Sort::Int);
        let lhs = {
            let s1 = terms.mk_store(a, i, v);
            terms.mk_store(s1, j, v)
        };
        let rhs = {
            let s1 = terms.mk_store(a, j, v);
            terms.mk_store(s1, i, v)
        };
        let eq = terms.mk_eq(lhs, rhs);
        assert!(
            is_array_extensionality_literal(&terms, eq),
            "array-sorted (dis)equality must be recognized as extensionality shape"
        );
        assert!(conflict_has_array_context(&terms, &[lit(eq)]));
    }

    /// Read-back equality `(= (select (store(store a i v) j w) i) v)` is over
    /// Int operands but one side reads from a store chain — the ROW read-back
    /// shape. MUST be recognized (else the readback regression degrades to
    /// Unknown).
    #[test]
    fn store_chain_readback_eq_is_recognized() {
        let mut terms = TermStore::new();
        let a = terms.mk_var("a", int_array_sort());
        let i = terms.mk_var("i", Sort::Int);
        let j = terms.mk_var("j", Sort::Int);
        let v = terms.mk_var("v", Sort::Int);
        let w = terms.mk_var("w", Sort::Int);
        let chain = {
            let s1 = terms.mk_store(a, i, v);
            terms.mk_store(s1, j, w)
        };
        let sel = terms.mk_select(chain, i);
        let eq = terms.mk_eq(sel, v);
        assert!(
            is_array_extensionality_literal(&terms, eq),
            "(dis)equality over a select of a store chain must be recognized"
        );
        assert!(conflict_has_array_context(&terms, &[lit(eq)]));
    }

    /// The adversarial-review case: an ARITHMETIC INEQUALITY that merely mentions
    /// `select` (over a bare array variable). The old predicate returned true
    /// here (it saw a `select` anywhere in the tree); the narrowed predicate MUST
    /// return false so a spurious mixed conflict fail-closes to Unknown.
    #[test]
    fn select_in_arith_inequality_is_not_array_context() {
        let mut terms = TermStore::new();
        let a = terms.mk_var("a", int_array_sort());
        let i = terms.mk_var("i", Sort::Int);
        let sel = terms.mk_select(a, i);
        let five = terms.mk_int(5.into());
        // (<= (select a i) 5)
        let le = terms.mk_le(sel, five);
        // BEFORE (over-matching predicate): term_has_array_context saw the
        // `select` anywhere in the tree and returned true, laundering this into
        // the carve-out. AFTER (narrowed): it must NOT be recognized.
        assert!(
            term_has_array_context(&terms, le),
            "sanity: the OLD predicate DID match this arith literal (regression guard)"
        );
        assert!(
            !is_array_extensionality_literal(&terms, le),
            "an arithmetic inequality that only mentions select must NOT be treated \
             as an array-extensionality literal"
        );
        assert!(
            !conflict_has_array_context(&terms, &[lit(le)]),
            "conflict with only an arith-literal array mention must fail closed"
        );
    }

    /// An `=` over a `select` of a *bare* array variable (no store) is decidable
    /// by plain congruence — the isolated combiner handles it, so the carve-out
    /// is NOT needed. MUST return false (narrowed): store-free select equalities
    /// no longer launder a `ConflictIsSat`.
    #[test]
    fn select_over_bare_variable_eq_is_not_array_context() {
        let mut terms = TermStore::new();
        let a = terms.mk_var("a", int_array_sort());
        let i = terms.mk_var("i", Sort::Int);
        let sel = terms.mk_select(a, i);
        let five = terms.mk_int(5.into());
        // (= (select a i) 5), no store
        let eq = terms.mk_eq(sel, five);
        // BEFORE: over-matched (mentions select). AFTER: narrowed out.
        assert!(
            term_has_array_context(&terms, eq),
            "sanity: the OLD predicate DID match this bare-select equality"
        );
        assert!(
            !is_array_extensionality_literal(&terms, eq),
            "a store-free select equality is not the extensionality carve-out shape"
        );
        assert!(!conflict_has_array_context(&terms, &[lit(eq)]));
    }

    /// A genuinely-spurious MIXED conflict — a store-free select equality plus a
    /// pure-arithmetic inequality, no array (dis)equality anywhere — must fail
    /// closed. This is the exact class the review said the old predicate would
    /// launder into a wrong UNSAT.
    #[test]
    fn mixed_arith_and_bare_select_conflict_fails_closed() {
        let mut terms = TermStore::new();
        let a = terms.mk_var("a", int_array_sort());
        let i = terms.mk_var("i", Sort::Int);
        let x = terms.mk_var("x", Sort::Int);
        let sel = terms.mk_select(a, i);
        let five = terms.mk_int(5.into());
        let ten = terms.mk_int(10.into());
        let eq = terms.mk_eq(sel, five); // (= (select a i) 5)
        let le = terms.mk_le(x, ten); // (<= x 10)
        assert!(
            !conflict_has_array_context(&terms, &[lit(eq), lit(le)]),
            "mixed arith + bare-select conflict (no array (dis)equality) must fail closed"
        );
    }

    /// Adding a load-bearing array (dis)equality to the same mixed conflict flips
    /// the predicate back to true — the carve-out still fires when the genuine
    /// extensionality shape is present.
    #[test]
    fn mixed_conflict_with_array_diseq_is_recognized() {
        let mut terms = TermStore::new();
        let a = terms.mk_var("a", int_array_sort());
        let b = terms.mk_var("b", int_array_sort());
        let i = terms.mk_var("i", Sort::Int);
        let x = terms.mk_var("x", Sort::Int);
        let sel = terms.mk_select(a, i);
        let five = terms.mk_int(5.into());
        let ten = terms.mk_int(10.into());
        let eq = terms.mk_eq(sel, five);
        let le = terms.mk_le(x, ten);
        let arr_eq = terms.mk_eq(a, b); // (= a b) over Array-sorted vars
        assert!(conflict_has_array_context(
            &terms,
            &[lit(eq), lit(le), lit(arr_eq)]
        ));
    }
}
