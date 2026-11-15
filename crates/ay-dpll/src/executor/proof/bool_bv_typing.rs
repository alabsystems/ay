// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Positive typing of TOTAL builtin Bool/BV expressions; no UF/theory guessing.

use ay_core::{Constant, Sort, Symbol, TermData, TermId};
use ay_frontend::Context;

#[derive(Clone, Copy, Eq, PartialEq)]
pub(super) enum Scalar {
    Bool,
    Word(u32),
}

pub(super) fn scalar(ctx: &Context, term: TermId) -> Option<Scalar> {
    ctx.terms.entry_stamp(term)?;
    match ctx.terms.sort(term) {
        Sort::Bool => Some(Scalar::Bool),
        Sort::BitVec(word) if (1..=4096).contains(&word.width) => Some(Scalar::Word(word.width)),
        _ => None,
    }
}

pub(super) enum Children<'a> {
    None,
    One(TermId),
    Three([TermId; 3]),
    Slice(&'a [TermId]),
}

impl Children<'_> {
    pub(super) fn len(&self) -> usize {
        match self {
            Self::None => 0,
            Self::One(_) => 1,
            Self::Three(_) => 3,
            Self::Slice(a) => a.len(),
        }
    }

    pub(super) fn push_reversed(&self, pending: &mut Vec<(TermId, bool)>) {
        match self {
            Self::None => {}
            Self::One(a) => pending.push((*a, false)),
            Self::Three(a) => pending.extend(a.iter().rev().map(|&x| (x, false))),
            Self::Slice(a) => pending.extend(a.iter().rev().map(|&x| (x, false))),
        }
    }
}

pub(super) fn payload(ctx: &Context, term: TermId) -> Option<usize> {
    Some(match ctx.terms.get(term) {
        TermData::Var(name, _) => name.len(),
        TermData::App(symbol, _) => symbol.name().len(),
        TermData::Const(Constant::BitVec { width, .. }) => {
            usize::try_from(*width).ok()?.checked_add(7)? / 8
        }
        _ => 1,
    })
}

pub(super) fn children(ctx: &Context, term: TermId) -> Option<Children<'_>> {
    let sort = scalar(ctx, term)?;
    match ctx.terms.get(term) {
        TermData::Const(Constant::Bool(_)) if sort == Scalar::Bool => Some(Children::None),
        TermData::Const(Constant::BitVec { value, width })
            if sort == Scalar::Word(*width)
                && value.sign() != num_bigint::Sign::Minus
                && value.bits() <= u64::from(*width) =>
        {
            Some(Children::None)
        }
        TermData::Var(..) => Some(Children::None),
        TermData::Not(inner) if sort == Scalar::Bool && scalar(ctx, *inner)? == Scalar::Bool => {
            Some(Children::One(*inner))
        }
        TermData::Ite(c, t, e)
            if scalar(ctx, *c)? == Scalar::Bool
                && scalar(ctx, *t)? == sort
                && scalar(ctx, *e)? == sort =>
        {
            Some(Children::Three([*c, *t, *e]))
        }
        TermData::App(symbol, args) if builtin(ctx, symbol, args, sort) => {
            Some(Children::Slice(args))
        }
        _ => None,
    }
}

fn builtin(ctx: &Context, symbol: &Symbol, args: &[TermId], result: Scalar) -> bool {
    if ctx.has_symbol_binding(symbol.name()) {
        return false;
    }
    match symbol {
        Symbol::Named(name) => named(ctx, name, args, result),
        Symbol::Indexed(name, indices) => {
            indexed(ctx, name, indices, args, result).unwrap_or(false)
        }
        _ => false,
    }
}

fn all(ctx: &Context, args: &[TermId], sort: Scalar) -> bool {
    args.iter().all(|&term| scalar(ctx, term) == Some(sort))
}

fn named(ctx: &Context, name: &str, args: &[TermId], result: Scalar) -> bool {
    match name {
        "and" | "or" => result == Scalar::Bool && all(ctx, args, Scalar::Bool),
        "xor" | "=>" => args.len() >= 2 && result == Scalar::Bool && all(ctx, args, Scalar::Bool),
        "not" => args.len() == 1 && result == Scalar::Bool && all(ctx, args, Scalar::Bool),
        "=" | "distinct" => {
            args.len() >= 2
                && result == Scalar::Bool
                && args
                    .first()
                    .and_then(|&x| scalar(ctx, x))
                    .is_some_and(|s| all(ctx, args, s))
        }
        "ite" => match args {
            [c, t, e] => {
                scalar(ctx, *c) == Some(Scalar::Bool)
                    && scalar(ctx, *t) == Some(result)
                    && scalar(ctx, *e) == Some(result)
            }
            _ => false,
        },
        _ => word(ctx, name, args, result),
    }
}

fn word(ctx: &Context, name: &str, args: &[TermId], result: Scalar) -> bool {
    match name {
        "bvneg" | "bvnot" => {
            args.len() == 1 && matches!(result, Scalar::Word(_)) && all(ctx, args, result)
        }
        "bvadd" | "bvmul" | "bvand" | "bvor" | "bvxor" => {
            args.len() >= 2 && matches!(result, Scalar::Word(_)) && all(ctx, args, result)
        }
        "bvsub" | "bvudiv" | "bvurem" | "bvsdiv" | "bvsrem" | "bvsmod" | "bvnand" | "bvnor"
        | "bvxnor" | "bvshl" | "bvlshr" | "bvashr" => {
            args.len() == 2 && matches!(result, Scalar::Word(_)) && all(ctx, args, result)
        }
        "bvult" | "bvule" | "bvugt" | "bvuge" | "bvslt" | "bvsle" | "bvsgt" | "bvsge" => {
            args.len() == 2
                && result == Scalar::Bool
                && args
                    .first()
                    .and_then(|&x| scalar(ctx, x))
                    .is_some_and(|s| matches!(s, Scalar::Word(_)) && all(ctx, args, s))
        }
        "mkbv" => {
            !args.is_empty()
                && u32::try_from(args.len()).is_ok_and(|width| result == Scalar::Word(width))
                && all(ctx, args, Scalar::Bool)
        }
        "concat" => concatenation(ctx, args, result).unwrap_or(false),
        "bvcomp" => {
            args.len() == 2
                && result == Scalar::Word(1)
                && args
                    .first()
                    .and_then(|&x| scalar(ctx, x))
                    .is_some_and(|s| matches!(s, Scalar::Word(_)) && all(ctx, args, s))
        }
        _ => false,
    }
}

fn concatenation(ctx: &Context, args: &[TermId], result: Scalar) -> Option<bool> {
    let [left, right] = args else {
        return Some(false);
    };
    let (Scalar::Word(a), Scalar::Word(b)) = (scalar(ctx, *left)?, scalar(ctx, *right)?) else {
        return Some(false);
    };
    Some(result == Scalar::Word(a.checked_add(b)?))
}

fn indexed(
    ctx: &Context,
    name: &str,
    indices: &[u32],
    args: &[TermId],
    result: Scalar,
) -> Option<bool> {
    let [argument] = args else { return Some(false) };
    let Scalar::Word(width) = scalar(ctx, *argument)? else {
        return Some(false);
    };
    Some(match (name, indices) {
        ("extract", [high, low]) if low <= high && *high < width => {
            result == Scalar::Word(high.checked_sub(*low)?.checked_add(1)?)
        }
        ("zero_extend" | "sign_extend", [extra]) => {
            result == Scalar::Word(width.checked_add(*extra)?)
        }
        ("repeat", [count]) if *count > 0 => result == Scalar::Word(width.checked_mul(*count)?),
        ("rotate_left" | "rotate_right", [_]) => result == Scalar::Word(width),
        _ => false,
    })
}
