// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The exact clause the certificate proves, recognized in AY's term store.
//!
//! Recognition rebuilds [`Row`] — the same builder the certificate is
//! generated from — over four placeholder limbs and compares it node by node
//! with the clause's single equality. So whatever the strict checker accepts
//! under [`ay_core::TheoryLemmaKind::BvMulOverflowDivision`] is, term for
//! term, what the printed certificate concludes.

use super::row::Row;
use super::signed::Signed;
use super::term::{Op, Terms, T};
use ay_core::kani_compat::DetHashMap;
use ay_core::{Constant, Sort, Symbol, TermData, TermId, TermStore};

/// Widest limb the certificate is emitted for: `m = 64` is external-codegen's u128
/// `checked_mul`, and the pinned checker's normalizer budget is calibrated
/// there.
const MAX_LIMB: u32 = 64;

/// A recognized clause: the limb width, the limbs `[a_lo, a_hi, b_lo, b_hi]`
/// and whether it is the signed identity ([`Signed`]) or the unsigned one ([`Row`]).
pub(super) struct Shape {
    pub(super) m: u32,
    pub(super) leaves: [TermId; 4],
    pub(super) signed: bool,
}

/// The shape of `clause`, or `None` unless it is exactly the unit
/// `(cl (= L R))` of [`Row`] or of [`Signed`] over four distinct `m`-bit
/// variables with `m` even and `4 <= m <= 64`.
pub(super) fn shape(terms: &TermStore, clause: &[TermId]) -> Option<Shape> {
    let [eq] = clause else {
        return None;
    };
    let (l, r) = app2(terms, *eq, "=")?;
    let TermData::Ite(cond, _, _) = terms.get(r) else {
        return None;
    };
    let TermData::App(head, conj) = terms.get(*cond) else {
        return None;
    };
    if conj.len() != 2 {
        return None;
    }
    // unsigned: `(and (not (= A Z)) (not (= Q B)))`;
    // signed: `(or (and ..) (and (= A MIN) (= B -1)))`
    let (a, b, signed) = if named(head, "and") {
        let (a, _) = app2(terms, negated(terms, conj[0])?, "=")?;
        let (_, b) = app2(terms, negated(terms, conj[1])?, "=")?;
        (a, b, false)
    } else if named(head, "or") {
        let TermData::App(and, spec) = terms.get(conj[1]) else {
            return None;
        };
        if !named(and, "and") || spec.len() != 2 {
            return None;
        }
        let (a, _) = app2(terms, spec[0], "=")?;
        let (b, _) = app2(terms, spec[1], "=")?;
        (a, b, true)
    } else {
        return None;
    };
    let (a_hi, a_lo) = app2(terms, a, "concat")?;
    let (b_hi, b_lo) = app2(terms, b, "concat")?;
    let leaves = [a_lo, a_hi, b_lo, b_hi];
    let m = var_width(terms, a_lo)?;
    if m < 4 || m % 2 != 0 || m > MAX_LIMB {
        return None;
    }
    for (k, &leaf) in leaves.iter().enumerate() {
        if var_width(terms, leaf)? != m || leaves[..k].contains(&leaf) {
            return None;
        }
    }
    let mut t = Terms::new();
    let placeholders = Row::leaves(&mut t, m, ["0", "1", "2", "3"]);
    let (gl, gr) = if signed {
        let (sg, _) = Signed::new(&mut t, m, placeholders);
        (sg.l, sg.r)
    } else {
        let row = Row::new(&mut t, m, placeholders);
        (row.l, row.r)
    };
    let mut matcher = Matcher {
        terms,
        t: &t,
        leaves: placeholders.into_iter().zip(leaves).collect(),
        memo: DetHashMap::default(),
    };
    (matcher.same(gl, l) && matcher.same(gr, r)).then_some(Shape { m, leaves, signed })
}

fn named(symbol: &Symbol, name: &str) -> bool {
    matches!(symbol, Symbol::Named(n) if &**n == name)
}

fn app2(terms: &TermStore, t: TermId, name: &str) -> Option<(TermId, TermId)> {
    match terms.get(t) {
        TermData::App(symbol, args) if named(symbol, name) && args.len() == 2 => {
            Some((args[0], args[1]))
        }
        _ => None,
    }
}

fn negated(terms: &TermStore, t: TermId) -> Option<TermId> {
    match terms.get(t) {
        TermData::Not(x) => Some(*x),
        TermData::App(symbol, args) if named(symbol, "not") && args.len() == 1 => Some(args[0]),
        _ => None,
    }
}

fn var_width(terms: &TermStore, t: TermId) -> Option<u32> {
    match (terms.get(t), terms.sort(t)) {
        (TermData::Var(..), Sort::BitVec(sort)) => Some(sort.width),
        _ => None,
    }
}

struct Matcher<'a> {
    terms: &'a TermStore,
    t: &'a Terms,
    leaves: DetHashMap<T, TermId>,
    memo: DetHashMap<(T, TermId), bool>,
}

impl Matcher<'_> {
    fn same(&mut self, g: T, a: TermId) -> bool {
        if let Some(&known) = self.memo.get(&(g, a)) {
            return known;
        }
        let verdict = self.same_uncached(g, a);
        self.memo.insert((g, a), verdict);
        verdict
    }

    fn same_uncached(&mut self, g: T, a: TermId) -> bool {
        let (t, terms) = (self.t, self.terms);
        let gargs = t.args(g);
        match (t.op(g), terms.get(a)) {
            (Op::Var(_), _) => self.leaves.get(&g) == Some(&a),
            (Op::Lit(bits), TermData::Const(Constant::BitVec { value, width })) => {
                *width as usize == bits.len()
                    && value.sign() != num_bigint::Sign::Minus
                    && value.bits() <= u64::from(*width)
                    && bits
                        .iter()
                        .enumerate()
                        .all(|(i, &b)| value.bit(i as u64) == b)
            }
            (Op::True, TermData::Const(Constant::Bool(true)))
            | (Op::False, TermData::Const(Constant::Bool(false))) => true,
            (Op::Not, TermData::Not(x)) => self.same(gargs[0], *x),
            (Op::Ite, TermData::Ite(c, x, y)) => {
                let (c, x, y) = (*c, *x, *y);
                self.same(gargs[0], c) && self.same(gargs[1], x) && self.same(gargs[2], y)
            }
            (op, TermData::App(symbol, args)) => {
                if !Self::head_matches(op, symbol) || args.len() != gargs.len() {
                    return false;
                }
                gargs
                    .iter()
                    .zip(args.iter())
                    .all(|(&g, &a)| self.same(g, a))
            }
            _ => false,
        }
    }

    fn head_matches(op: &Op, symbol: &Symbol) -> bool {
        let name = match op {
            Op::Not => "not",
            Op::And => "and",
            Op::Or => "or",
            Op::Eq => "=",
            Op::Ite => "ite",
            Op::Add => "bvadd",
            Op::Mul => "bvmul",
            Op::Neg => "bvneg",
            Op::Ult => "bvult",
            Op::Concat => "concat",
            Op::Udiv => "bvudiv",
            Op::Shl => "bvshl",
            Op::Extract(hi, lo) => {
                return matches!(symbol, Symbol::Indexed(n, ix) if &**n == "extract" && ix[..] == [*hi, *lo]);
            }
            Op::ZeroExt(k) => {
                return matches!(symbol, Symbol::Indexed(n, ix) if &**n == "zero_extend" && ix[..] == [*k]);
            }
            _ => return false,
        };
        named(symbol, name)
    }
}
