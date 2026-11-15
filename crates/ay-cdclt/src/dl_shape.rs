// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Which arithmetic atoms are difference atoms, and the integer tightening
//! that makes integer difference logic exact (`dl.rs` is the plug-in).

use ay_core::{Sort, TermData, TermId, TermStore};
use ay_diff_logic::{IStar, Op};
use num_rational::BigRational;
use num_traits::{One, Zero};

use crate::content::is_uf_app;
use crate::linear::{is_arith_var, Linearizer};

/// What an arithmetic atom is, to difference logic.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum DiffShape {
    /// `x − y ⋈ c`, or `x ⋈ c` when `y` is `None`.
    Diff {
        x: TermId,
        y: Option<TermId>,
        op: Op,
        c: BigRational,
    },
    /// An equality `a = b` whose difference is a difference atom with
    /// constant `c`; the plug-in defines it by `a ≤ b` and `b ≤ a`.
    Equality(TermId, TermId, BigRational),
    /// A comparison of constants, with its truth value.
    Ground(bool),
}

fn comparison(name: &str) -> Option<Op> {
    Some(match name {
        "<=" => Op::Le,
        "<" => Op::Lt,
        "=" => Op::Eq,
        ">=" => Op::Ge,
        ">" => Op::Gt,
        _ => return None,
    })
}

fn holds(op: Op, lhs: &BigRational, c: &BigRational) -> bool {
    match op {
        Op::Le => lhs <= c,
        Op::Lt => lhs < c,
        Op::Eq => lhs == c,
        Op::Ge => lhs >= c,
        Op::Gt => lhs > c,
    }
}

/// `−v ⋈ c` is `v ⋈' −c`.
const fn flip(op: Op) -> Op {
    match op {
        Op::Le => Op::Ge,
        Op::Lt => Op::Gt,
        Op::Ge => Op::Le,
        Op::Gt => Op::Lt,
        Op::Eq => Op::Eq,
    }
}

/// `¬(a ⋈ c)` as one comparison (never called on `=`).
pub(crate) const fn negate(op: Op) -> Op {
    match op {
        Op::Le => Op::Gt,
        Op::Lt => Op::Ge,
        Op::Ge => Op::Lt,
        Op::Gt => Op::Le,
        Op::Eq => Op::Eq,
    }
}

/// The difference-logic shape of an atom, or `None` when it is not one
/// (a non-unit coefficient, three leaves, or a leaf that is not a variable).
pub(crate) fn diff_shape(
    terms: &TermStore,
    lin: &mut Linearizer,
    atom: TermId,
) -> Option<DiffShape> {
    let TermData::App(sym, args) = terms.get(atom) else {
        return None;
    };
    let op = comparison(sym.name())?;
    let &[a, b] = args.as_slice() else {
        return None;
    };
    if !matches!(terms.sort(a), Sort::Int | Sort::Real) {
        return None;
    }
    let mut form = lin.linearize(terms, a).ok()?;
    let rhs = lin.linearize(terms, b).ok()?;
    form.add_scaled(&rhs, &-BigRational::one());
    let c = -form.constant.clone();
    let mut pos = None;
    let mut neg = None;
    for (&leaf, coeff) in &form.coeffs {
        // An uninterpreted application is a vertex like a variable: the hub
        // decides its equalities (design H1).
        if !is_arith_var(terms, leaf) && !is_uf_app(terms, leaf) {
            return None;
        }
        if coeff.is_one() && pos.is_none() {
            pos = Some(leaf);
        } else if (-coeff).is_one() && neg.is_none() {
            neg = Some(leaf);
        } else {
            return None;
        }
    }
    let shape = match (pos, neg) {
        (None, None) => return Some(DiffShape::Ground(holds(op, &BigRational::zero(), &c))),
        (Some(x), y) => DiffShape::Diff { x, y, op, c },
        (None, Some(y)) => DiffShape::Diff {
            x: y,
            y: None,
            op: flip(op),
            c: -c,
        },
    };
    if op == Op::Eq {
        let DiffShape::Diff { c, .. } = shape else {
            return None;
        };
        return Some(DiffShape::Equality(a, b, c));
    }
    Some(shape)
}

/// Whether a term the hub shares with arithmetic is a vertex plus a
/// constant (or a constant), which the difference-logic plug-in can carry.
pub(crate) fn shared_fits(terms: &TermStore, lin: &mut Linearizer, term: TermId) -> bool {
    let Ok(form) = lin.linearize(terms, term) else {
        return false;
    };
    let mut leaves = form.coeffs.iter();
    match (leaves.next(), leaves.next()) {
        (None, _) => true,
        (Some((&leaf, coeff)), None) => {
            coeff.is_one() && (is_arith_var(terms, leaf) || is_uf_app(terms, leaf))
        }
        _ => false,
    }
}

/// Integer tightening: every bound as an exactly equivalent non-strict one
/// (the lane's `tighten_int`, `executor/dl_theory.rs`).
pub(crate) fn tighten_int(op: Op, c: &BigRational) -> (Op, BigRational) {
    let one = BigRational::one();
    match op {
        Op::Le => (Op::Le, c.floor()),
        Op::Lt => (Op::Le, c.ceil() - one),
        Op::Ge => (Op::Ge, c.ceil()),
        Op::Gt => (Op::Ge, c.floor() + one),
        Op::Eq => (Op::Eq, c.clone()),
    }
}

/// Whether every constant the atoms lower to fits the `i128` weight lane
/// ([`IStar`]); otherwise the plug-in runs on exact rationals.
pub(crate) fn fits_fast_lane(shapes: &[DiffShape], integer: bool) -> bool {
    shapes.iter().all(|shape| match shape {
        DiffShape::Diff { op, c, .. } => {
            let (_, pos) = if integer {
                tighten_int(*op, c)
            } else {
                (*op, c.clone())
            };
            let (_, neg) = if integer {
                tighten_int(negate(*op), c)
            } else {
                (*op, c.clone())
            };
            IStar::fits_fast_lane(&pos).is_some() && IStar::fits_fast_lane(&neg).is_some()
        }
        // The definition's `a ≤ b` and `b ≤ a` carry `c` and `−c` (tightened
        // over Int they keep an integral `c` as it is).
        DiffShape::Equality(_, _, c) => {
            IStar::fits_fast_lane(c).is_some() && IStar::fits_fast_lane(&-c.clone()).is_some()
        }
        DiffShape::Ground(_) => true,
    })
}
