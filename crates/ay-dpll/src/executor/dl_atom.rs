// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Pure difference-logic atom recognition, shared by the DPLL(T)
//! difference-logic theory ([`super::dl_theory`]) and the QF_RDL/QF_IDL
//! routes in `theories/rdl.rs`.
//!
//! Recognition is fail-closed: [`collect_comparison`] returns `None` for any
//! shape that is not exactly `x − y ⋈ c` or `x ⋈ c` over unit coefficients,
//! so a caller never approximates a non-DL atom.

use ay_core::kani_compat::DetHashMap as HashMap;
use ay_core::term::{Constant, Symbol, TermData, TermStore};
use ay_core::{Sort, TermId};
use ay_diff_logic::atom::Op;
use num_rational::BigRational;
use num_traits::{One, Zero};

/// One difference-logic atom in a sort-agnostic rational normal form
/// (`lhs − rhs ⋈ c`, with `rhs = None` for var-vs-const). Coefficients have
/// already been validated to be exactly unit / opposite-unit.
pub(super) struct CollectedAtom {
    pub(super) lhs: TermId,
    pub(super) rhs: Option<TermId>,
    pub(super) op: Op,
    /// Constant `c` as an exact rational (integer when the sort is Int).
    pub(super) c: BigRational,
}

/// Negate a comparison operator (used for `not (atom)`).
pub(super) fn negate_op(op: Op) -> Op {
    match op {
        Op::Le => Op::Gt,
        Op::Lt => Op::Ge,
        Op::Ge => Op::Lt,
        Op::Gt => Op::Le,
        // `not (a = b)` is `a != b`, which is a *disjunction* (`a < b ∨ a > b`),
        // NOT a difference-logic atom. Handled by the caller (it rejects).
        Op::Eq => Op::Eq,
    }
}

/// Parse a comparison application `(op A B)` (op ∈ {<,<=,=,>,>=}) into a
/// normalized DL atom by linearizing `A − B`.
pub(super) fn collect_comparison(terms: &TermStore, term: TermId) -> Option<CollectedAtom> {
    let TermData::App(Symbol::Named(name), args) = terms.get(term) else {
        return None;
    };
    if args.len() != 2 {
        return None;
    }
    let op = match name.as_str() {
        "<=" => Op::Le,
        "<" => Op::Lt,
        "=" => Op::Eq,
        ">=" => Op::Ge,
        ">" => Op::Gt,
        _ => return None,
    };
    let (a, b) = (args[0], args[1]);
    // `=` is only a difference atom when both sides are arithmetic (Int/Real).
    // A Bool `(= p q)` must NOT be treated as a DL atom.
    if !matches!(terms.sort(a), Sort::Int | Sort::Real)
        || !matches!(terms.sort(b), Sort::Int | Sort::Real)
    {
        return None;
    }

    // Linearize A − B into a coefficient map plus a constant. `A op B` is then
    // `(A − B) op 0`, i.e. (vars) op (−const).
    let mut coeffs: HashMap<TermId, BigRational> = HashMap::default();
    let mut constant = BigRational::zero();
    linearize(terms, a, BigRational::one(), &mut coeffs, &mut constant)?;
    linearize(terms, b, -BigRational::one(), &mut coeffs, &mut constant)?;

    // Drop zero coefficients.
    coeffs.retain(|_, c| !c.is_zero());

    // The DL constant is `c` such that `lhs − rhs ⋈ c`, where `lhs − rhs`
    // is the variable part and `c = −constant`.
    let c = -constant;

    // Classify the variable part: it must be `x` (unit), `−y` (opposite),
    // or `x − y` (one unit + one opposite). Anything else is not DL.
    let mut pos: Option<TermId> = None; // coeff +1
    let mut neg: Option<TermId> = None; // coeff −1
    for (t, coeff) in &coeffs {
        if coeff.is_one() {
            if pos.is_some() {
                return None; // two +1 vars ⇒ not DL
            }
            pos = Some(*t);
        } else if (-coeff).is_one() {
            if neg.is_some() {
                return None; // two −1 vars ⇒ not DL
            }
            neg = Some(*t);
        } else {
            return None; // non-unit coefficient ⇒ not DL
        }
    }

    match (pos, neg) {
        // x − y ⋈ c
        (Some(x), Some(y)) => Some(CollectedAtom {
            lhs: x,
            rhs: Some(y),
            op,
            c,
        }),
        // x ⋈ c
        (Some(x), None) => Some(CollectedAtom {
            lhs: x,
            rhs: None,
            op,
            c,
        }),
        // −y ⋈ c  ⇔  y ⋈ −c, with the operator flipped (multiply by −1).
        (None, Some(y)) => Some(CollectedAtom {
            lhs: y,
            rhs: None,
            op: flip_op_for_negation(op),
            c: -c,
        }),
        // 0 ⋈ c — a constant predicate with no variables. Not a DL atom in
        // the engine's variable space; fall through (the normal solver folds
        // it). This keeps the engine's `from_atoms` happy (it needs ≥1 var).
        (None, None) => None,
    }
}

/// Linearize an Int/Real term into `coeffs` (per-leaf coefficient) and a
/// running `constant`, scaled by `scale`. Returns `None` on any shape that is
/// not a linear combination over atomic arithmetic leaves (e.g. nonlinear
/// `*`, division by a variable, ITE, etc.) — fail-closed.
fn linearize(
    terms: &TermStore,
    term: TermId,
    scale: BigRational,
    coeffs: &mut HashMap<TermId, BigRational>,
    constant: &mut BigRational,
) -> Option<()> {
    match terms.get(term) {
        TermData::Const(Constant::Int(n)) => {
            *constant += &scale * BigRational::from(n.clone());
            Some(())
        }
        TermData::Const(Constant::Rational(r)) => {
            *constant += &scale * &r.0;
            Some(())
        }
        TermData::App(Symbol::Named(name), args) => match name.as_str() {
            "+" => {
                for &arg in args {
                    linearize(terms, arg, scale.clone(), coeffs, constant)?;
                }
                Some(())
            }
            "-" if args.len() == 1 => linearize(terms, args[0], -scale, coeffs, constant),
            "-" if args.len() >= 2 => {
                linearize(terms, args[0], scale.clone(), coeffs, constant)?;
                for &arg in &args[1..] {
                    linearize(terms, arg, -scale.clone(), coeffs, constant)?;
                }
                Some(())
            }
            "*" => {
                // Linear only: at most one non-constant factor; all other
                // factors must be numeric constants.
                let mut const_factor = BigRational::one();
                let mut var_arg: Option<TermId> = None;
                for &arg in args {
                    if let Some(k) = numeric_constant(terms, arg) {
                        const_factor *= k;
                    } else if var_arg.is_none() {
                        var_arg = Some(arg);
                    } else {
                        return None; // ≥2 variable factors ⇒ nonlinear
                    }
                }
                match var_arg {
                    Some(v) => linearize(terms, v, &scale * const_factor, coeffs, constant),
                    None => {
                        *constant += &scale * const_factor;
                        Some(())
                    }
                }
            }
            // Any other function symbol applied to args is treated as an
            // atomic arithmetic leaf ONLY if it is genuinely a variable-like
            // term. Reject interpreted ops we do not model (div, mod, abs,
            // to_int, ...) so we never mis-linearize them.
            _ => try_atomic_leaf(terms, term, scale, coeffs),
        },
        // A bare variable (or any other atomic term) is a leaf.
        _ => try_atomic_leaf(terms, term, scale, coeffs),
    }
}

/// Accept `term` as an atomic difference-logic variable leaf: add `scale` to
/// its coefficient. Only Int/Real-sorted, non-constant terms qualify.
fn try_atomic_leaf(
    terms: &TermStore,
    term: TermId,
    scale: BigRational,
    coeffs: &mut HashMap<TermId, BigRational>,
) -> Option<()> {
    // Must be arithmetic-sorted to be a DL variable.
    if !matches!(terms.sort(term), Sort::Int | Sort::Real) {
        return None;
    }
    // Reject interpreted arithmetic operators we cannot model as a single
    // variable (they would silently become opaque variables and could make a
    // non-DL instance look like DL). Only un-interpreted leaves are allowed:
    // a `Var`, or an uninterpreted function application (e.g. `(f x)` in
    // QF_UFIDL is a legitimate atomic Int term). Constants are not leaves.
    match terms.get(term) {
        TermData::Const(_) => None,
        TermData::App(Symbol::Named(name), _)
            if matches!(
                name.as_str(),
                "+" | "-" | "*" | "/" | "div" | "mod" | "abs" | "to_int" | "to_real"
            ) =>
        {
            // Interpreted arithmetic op that we did not destructure above ⇒
            // not a pure atomic leaf; reject.
            None
        }
        _ => {
            *coeffs.entry(term).or_insert_with(BigRational::zero) += scale;
            Some(())
        }
    }
}

/// A numeric (Int / integral-or-fractional Rational) constant value of a
/// term, including unary minus over a constant. `None` if not a constant.
fn numeric_constant(terms: &TermStore, term: TermId) -> Option<BigRational> {
    match terms.get(term) {
        TermData::Const(Constant::Int(n)) => Some(BigRational::from(n.clone())),
        TermData::Const(Constant::Rational(r)) => Some(r.0.clone()),
        TermData::App(Symbol::Named(name), args) if name == "-" && args.len() == 1 => {
            numeric_constant(terms, args[0]).map(|v| -v)
        }
        _ => None,
    }
}

/// Flip a comparison operator under multiplication by −1 (`−y ⋈ c ⇔ y ⋈′ −c`).
fn flip_op_for_negation(op: Op) -> Op {
    match op {
        Op::Le => Op::Ge,
        Op::Lt => Op::Gt,
        Op::Ge => Op::Le,
        Op::Gt => Op::Lt,
        Op::Eq => Op::Eq,
    }
}
