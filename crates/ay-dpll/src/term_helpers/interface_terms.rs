// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use ay_core::kani_compat::DetHashMap as HashMap;
use ay_core::term::{Symbol, TermData};
use ay_core::{Sort, TermId, TermStore};

use super::arithmetic::{
    has_arithmetic_structure, is_pure_arithmetic_term, TERM_ANALYSIS_STACK_RED_ZONE,
    TERM_ANALYSIS_STACK_SIZE,
};
use super::euf_patterns::decode_non_bool_eq;

/// Check if a term involves an uninterpreted function application (#1893).
///
/// Uses `stacker::maybe_grow` for stack safety on deeply nested terms (#8414).
pub(super) fn involves_uninterpreted_function(terms: &TermStore, term: TermId) -> bool {
    // Hash-consed DAG: a subterm shared by many parents would otherwise be
    // re-walked once per path (super-linear on the deep diamond terms seen on
    // QF_ALIA/cs_fib-2). The result is a pure function of the immutable term
    // DAG, so a per-call result-memo is byte-identical to the naive walk (same
    // short-circuit order; each visited term's bool is just cached). The memo
    // (`DetHashMap`) allocates lazily — a leaf-only top-level call inserts
    // nothing, so shallow callers keep their prior cost.
    let mut memo: HashMap<TermId, bool> = HashMap::default();
    involves_uninterpreted_function_memo(terms, term, &mut memo)
}

fn involves_uninterpreted_function_memo(
    terms: &TermStore,
    term: TermId,
    memo: &mut HashMap<TermId, bool>,
) -> bool {
    if let Some(&cached) = memo.get(&term) {
        return cached;
    }
    let result = stacker::maybe_grow(
        TERM_ANALYSIS_STACK_RED_ZONE,
        TERM_ANALYSIS_STACK_SIZE,
        || match terms.get(term) {
            TermData::Const(_) | TermData::Var(_, _) => false,
            TermData::App(Symbol::Named(name), args) => {
                if matches!(
                    name.as_str(),
                    "+" | "-"
                        | "*"
                        | "/"
                        | "div"
                        | "mod"
                        | "abs"
                        | "to_real"
                        | "to_int"
                        | "<"
                        | "<="
                        | ">"
                        | ">="
                        | "="
                        | "distinct"
                        | "and"
                        | "or"
                        | "not"
                        | "=>"
                        | "ite"
                        | "select"
                        | "store"
                ) {
                    args.iter()
                        .any(|&arg| involves_uninterpreted_function_memo(terms, arg, memo))
                } else {
                    true
                }
            }
            TermData::Not(inner) => involves_uninterpreted_function_memo(terms, *inner, memo),
            TermData::Ite(c, t, e) => {
                involves_uninterpreted_function_memo(terms, *c, memo)
                    || involves_uninterpreted_function_memo(terms, *t, memo)
                    || involves_uninterpreted_function_memo(terms, *e, memo)
            }
            _ => false,
        },
    ); // stacker::maybe_grow
       // Only compound terms can be revisited via a shared sub-DAG; caching leaves
       // (which return in O(1)) would add allocation without avoiding any walk.
    if !matches!(terms.get(term), TermData::Const(_) | TermData::Var(_, _)) {
        memo.insert(term, result);
    }
    result
}

/// Extract interface arithmetic term from an equality between UF and arithmetic.
pub(crate) fn extract_interface_arith_term(terms: &TermStore, literal: TermId) -> Option<TermId> {
    let inner = match terms.get(literal) {
        TermData::Not(inner) => *inner,
        _ => literal,
    };
    let (lhs, rhs) = decode_non_bool_eq(terms, inner)?;

    let lhs_pure_arith = is_pure_arithmetic_term(terms, lhs);
    let rhs_pure_arith = is_pure_arithmetic_term(terms, rhs);
    let lhs_involves_uf = involves_uninterpreted_function(terms, lhs);
    let rhs_involves_uf = involves_uninterpreted_function(terms, rhs);

    if lhs_pure_arith && rhs_involves_uf {
        Some(lhs)
    } else if rhs_pure_arith && lhs_involves_uf {
        Some(rhs)
    } else {
        None
    }
}

/// Extract BOTH interface terms from a UF-arithmetic equality (#4767).
pub(crate) fn extract_uf_mixed_interface_term(
    terms: &TermStore,
    literal: TermId,
) -> Option<TermId> {
    let inner = match terms.get(literal) {
        TermData::Not(inner) => *inner,
        _ => literal,
    };
    let (lhs, rhs) = decode_non_bool_eq(terms, inner)?;

    let lhs_pure_arith = is_pure_arithmetic_term(terms, lhs);
    let rhs_pure_arith = is_pure_arithmetic_term(terms, rhs);
    let lhs_involves_uf = involves_uninterpreted_function(terms, lhs);
    let rhs_involves_uf = involves_uninterpreted_function(terms, rhs);

    if rhs_involves_uf && lhs_pure_arith && !rhs_pure_arith && has_arithmetic_structure(terms, rhs)
    {
        return Some(rhs);
    }
    if lhs_involves_uf && rhs_pure_arith && !lhs_pure_arith && has_arithmetic_structure(terms, lhs)
    {
        return Some(lhs);
    }
    None
}

/// Extract UF-mixed arithmetic operands from a (possibly negated) non-Bool
/// equality atom, regardless of the OTHER side's shape (#uflia-hard-mixed-eq).
///
/// `extract_uf_mixed_interface_term` requires one side to be PURE arithmetic.
/// An equality between a UF application and a UF-mixed compound — the mathsat
/// EufLaArithmetic hard* shape `(= (Sum a b) (+ (Sum c d) y x))` — has no pure
/// side, so the compound was never registered as a Nelson-Oppen interface
/// term. The bridge then never evaluates it, never proposes the
/// `compound = constant` interface equality, and when SAT asserts the atom
/// FALSE the EUF congruence refutation (`UF-app ~ c ~ compound` contradicting
/// the asserted disequality) is unreachable: the combined search accepts a
/// model the strict ite_uf_definition gate must reject, degrading a provable
/// UNSAT to unknown.
///
/// Returns each Int/Real-sorted side that combines arithmetic structure with
/// a UF subterm. Pure-arith sides stay with `extract_interface_arith_term`,
/// and bare UF applications are already registered by `track_uf_arith_args`.
pub(crate) fn extract_uf_mixed_eq_operands(
    terms: &TermStore,
    literal: TermId,
) -> (Option<TermId>, Option<TermId>) {
    let inner = match terms.get(literal) {
        TermData::Not(inner) => *inner,
        _ => literal,
    };
    let Some((lhs, rhs)) = decode_non_bool_eq(terms, inner) else {
        return (None, None);
    };
    let qualifies = |side: TermId| {
        // Int/Real-sorted sides ONLY (#seq-replace-mixed-eq regression): a
        // Seq/String/datatype-sorted equality operand can still "have
        // arithmetic structure" through its integer ARGUMENTS (e.g. the
        // `(seq.extract src 0 (- (seq.len src) 1))` terms minted by the
        // seq.replace/seq.indexof decomposition axioms). Registering such a
        // term as a Nelson-Oppen interface ARITHMETIC term makes EUF
        // propagate disequalities between Seq-sorted terms into LIA, whose
        // simplex model then requests an expression split on the Seq-sorted
        // equality — a split the executor cannot encode (`<`/`>` atoms are
        // meaningless for Seq), so the solve fail-closed to `unknown` on
        // satisfiable QF_SEQLIA instances.
        matches!(*terms.sort(side), Sort::Int | Sort::Real)
            && involves_uninterpreted_function(terms, side)
            && !is_pure_arithmetic_term(terms, side)
            && has_arithmetic_structure(terms, side)
    };
    (qualifies(lhs).then_some(lhs), qualifies(rhs).then_some(rhs))
}
