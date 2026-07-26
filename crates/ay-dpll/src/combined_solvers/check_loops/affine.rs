// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use std::collections::BTreeMap;

use ay_core::term::{Constant, Symbol, TermData, TermStore};
use ay_core::{Sort, TermId, TheoryLit};
use ay_euf::EufSolver;
use num_bigint::BigInt;
use num_traits::Zero;

type AffineIntExpr = (BTreeMap<TermId, BigInt>, BigInt);

fn merge_affine_terms(
    lhs: &mut BTreeMap<TermId, BigInt>,
    rhs: BTreeMap<TermId, BigInt>,
    sign: i32,
) {
    for (term, coeff) in rhs {
        let signed = if sign >= 0 { coeff } else { -coeff };
        let entry = lhs.entry(term).or_insert_with(|| BigInt::from(0));
        *entry += signed;
        if *entry == BigInt::from(0) {
            lhs.remove(&term);
        }
    }
    // Postcondition: no zero-coefficient entries remain after merging.
    debug_assert!(
        lhs.values().all(|c| !c.is_zero()),
        "BUG: merge_affine_terms left zero-coefficient entries"
    );
}

fn scale_affine(expr: &mut AffineIntExpr, factor: &BigInt) {
    expr.1 *= factor;
    for coeff in expr.0.values_mut() {
        *coeff *= factor;
    }
    expr.0.retain(|_, coeff| *coeff != BigInt::from(0));
    // Postcondition: scaling by zero must zero-out all terms.
    debug_assert!(
        !factor.is_zero() || (expr.0.is_empty() && expr.1.is_zero()),
        "BUG: scale_affine by 0 left non-zero terms: {} vars, constant={}",
        expr.0.len(),
        expr.1
    );
    // Postcondition: no zero-coefficient entries survive (retain cleaned them).
    debug_assert!(
        expr.0.values().all(|c| !c.is_zero()),
        "BUG: scale_affine left zero-coefficient entries after retain"
    );
}

fn parse_affine_int_expr(terms: &TermStore, term: TermId) -> Option<AffineIntExpr> {
    match terms.get(term) {
        TermData::Const(Constant::Int(n)) => Some((BTreeMap::new(), n.clone())),
        TermData::Var(_, _) if matches!(terms.sort(term), Sort::Int) => {
            let mut vars = BTreeMap::new();
            vars.insert(term, BigInt::from(1));
            Some((vars, BigInt::from(0)))
        }
        TermData::App(Symbol::Named(name), args) => match name.as_str() {
            "+" => {
                let mut vars = BTreeMap::new();
                let mut constant = BigInt::from(0);
                for &arg in args {
                    let (arg_vars, arg_const) = parse_affine_int_expr(terms, arg)?;
                    merge_affine_terms(&mut vars, arg_vars, 1);
                    constant += arg_const;
                }
                Some((vars, constant))
            }
            "-" if args.len() == 1 => {
                let mut expr = parse_affine_int_expr(terms, args[0])?;
                scale_affine(&mut expr, &BigInt::from(-1));
                Some(expr)
            }
            "-" if args.len() >= 2 => {
                let mut expr = parse_affine_int_expr(terms, args[0])?;
                for &arg in &args[1..] {
                    let (arg_vars, arg_const) = parse_affine_int_expr(terms, arg)?;
                    merge_affine_terms(&mut expr.0, arg_vars, -1);
                    expr.1 -= arg_const;
                }
                Some((expr.0, expr.1))
            }
            "*" => {
                let mut const_factor = BigInt::from(1);
                let mut non_constant: Option<AffineIntExpr> = None;
                for &arg in args {
                    let parsed = parse_affine_int_expr(terms, arg)?;
                    if parsed.0.is_empty() {
                        const_factor *= parsed.1;
                    } else if non_constant.is_none() {
                        non_constant = Some(parsed);
                    } else {
                        return None;
                    }
                }
                let mut expr = non_constant.unwrap_or((BTreeMap::new(), BigInt::from(1)));
                scale_affine(&mut expr, &const_factor);
                Some(expr)
            }
            // An Int-valued uninterpreted application is an affine atom.  It
            // must not be rejected merely because its arguments belong to
            // another theory: `f(a) + 1` is linear in the opaque atom `f(a)`.
            // Keeping the whole TermId as the atom prevents any accidental
            // identification of applications that EUF has not proved equal.
            _ if matches!(terms.sort(term), Sort::Int) => {
                let mut vars = BTreeMap::new();
                vars.insert(term, BigInt::from(1));
                Some((vars, BigInt::from(0)))
            }
            _ => None,
        },
        _ => None,
    }
}

fn canonical_affine(expr: &AffineIntExpr, euf: &EufSolver<'_>) -> (BTreeMap<u32, BigInt>, BigInt) {
    let mut vars = BTreeMap::new();
    for (&term, coeff) in &expr.0 {
        let rep = euf.enode_find_const(term.0);
        *vars.entry(rep).or_insert_with(|| BigInt::from(0)) += coeff;
    }
    vars.retain(|_, coeff| !coeff.is_zero());
    (vars, expr.1.clone())
}

/// Explain an affine index equality induced by EUF congruence.
///
/// Array indices such as `(+ (seq_offset final) 1)` and
/// `(+ (seq_offset current) 1)` are equal when EUF has proved the two opaque
/// `seq_offset` applications equal.  LIA need not assign either application a
/// concrete value, so model-value propagation alone cannot expose this fact to
/// the array solver.  This helper normalizes linear expressions by their EUF
/// representatives and returns the SAT-visible explanations for every
/// representative substitution.  `None` means equality was not proved.
pub(super) fn affine_euf_equality_reasons(
    terms: &TermStore,
    euf: &mut EufSolver<'_>,
    lhs: TermId,
    rhs: TermId,
) -> Option<Vec<TheoryLit>> {
    if lhs == rhs {
        return Some(Vec::new());
    }

    let lhs_expr = parse_affine_int_expr(terms, lhs);
    let rhs_expr = parse_affine_int_expr(terms, rhs);

    // Algebraically identical source expressions need no theory premise.
    // Every other equality must remain guarded by SAT-visible evidence:
    // inserting an unguarded array edge for an unexplained EUF merge is
    // unsound and can survive backtracking as a false equality.
    if lhs_expr
        .as_ref()
        .zip(rhs_expr.as_ref())
        .is_some_and(|(lhs, rhs)| lhs == rhs)
    {
        return Some(Vec::new());
    }

    if let (Some(lhs_expr), Some(rhs_expr)) = (&lhs_expr, &rhs_expr) {
        if canonical_affine(lhs_expr, euf) == canonical_affine(rhs_expr, euf) {
            let mut reasons = Vec::new();
            for atom in lhs_expr.0.keys().chain(rhs_expr.0.keys()) {
                let representative = TermId(euf.enode_find_const(atom.0));
                if *atom != representative {
                    let explanation = euf.explain(*atom, representative);
                    if explanation.is_empty() {
                        return None;
                    }
                    reasons.extend(explanation);
                }
            }
            reasons.sort_unstable_by_key(|lit| (lit.term.0, lit.value));
            reasons.dedup_by_key(|lit| (lit.term, lit.value));
            return (!reasons.is_empty()).then_some(reasons);
        }
    }

    // A directly proved equality between otherwise non-equivalent affine
    // forms (or non-affine terms) is still usable, but never without a
    // SAT-visible explanation.
    if euf.are_equal(lhs, rhs) {
        let mut reasons = euf.explain(lhs, rhs);
        reasons.sort_unstable_by_key(|lit| (lit.term.0, lit.value));
        reasons.dedup_by_key(|lit| (lit.term, lit.value));
        return (!reasons.is_empty()).then_some(reasons);
    }

    None
}

/// Returns true if two arithmetic terms are provably distinct due to a
/// non-zero constant offset: same variable coefficients, different constant.
pub(super) fn distinct_by_affine_offset(terms: &TermStore, lhs: TermId, rhs: TermId) -> bool {
    let Some(lhs_expr) = parse_affine_int_expr(terms, lhs) else {
        return false;
    };
    let Some(rhs_expr) = parse_affine_int_expr(terms, rhs) else {
        return false;
    };
    let result = lhs_expr.0 == rhs_expr.0 && lhs_expr.1 != rhs_expr.1;
    // Self-comparison must never yield distinct: a term has offset 0 from itself.
    debug_assert!(
        lhs != rhs || !result,
        "BUG: distinct_by_affine_offset returned true for self-comparison ({lhs:?})"
    );
    result
}
