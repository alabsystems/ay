// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

#[derive(Clone, Copy, PartialEq, Eq)]
enum Ty {
    Bool,
    Bv(u32),
}

fn ty(terms: &TermStore, id: TermId) -> Result<Ty> {
    if id.index() >= terms.len() {
        return Err(CountedBvError::Invalid);
    }
    match terms.sort(id) {
        Sort::Bool => Ok(Ty::Bool),
        Sort::BitVec(sort) if sort.width != 0 => Ok(Ty::Bv(sort.width)),
        _ => Err(CountedBvError::Unsupported("source is not scalar Bool/BV")),
    }
}

pub(super) fn validate(terms: &TermStore, id: TermId, owner: &CountedAdmission) -> Result<()> {
    owner.admit(1, 0)?;
    let actual = ty(terms, id)?;
    let expected = match terms.get(id) {
        TermData::Const(Constant::Bool(_)) => Ty::Bool,
        TermData::Const(Constant::BitVec { value, width }) => {
            let limbs =
                usize::try_from(value.bits().div_ceil(32)).map_err(|_| CountedBvError::Invalid)?;
            owner.admit(limbs.checked_add(1).ok_or(CountedBvError::Invalid)?, 0)?;
            if *width == 0
                || value.sign() == num_bigint::Sign::Minus
                || value.bits() > u64::from(*width)
            {
                return Err(CountedBvError::Invalid);
            }
            Ty::Bv(*width)
        }
        TermData::Var(name, _) => {
            owner.admit(name.len(), 0)?;
            actual
        }
        TermData::Not(child) if ty(terms, *child)? == Ty::Bool => Ty::Bool,
        TermData::Ite(c, t, e)
            if ty(terms, *c)? == Ty::Bool && ty(terms, *t)? == ty(terms, *e)? =>
        {
            ty(terms, *t)?
        }
        TermData::App(symbol, args) => application(terms, symbol, args, owner)?,
        _ => return Err(CountedBvError::Unsupported("unaccounted term form")),
    };
    if actual != expected {
        return Err(CountedBvError::Invalid);
    }
    Ok(())
}

fn application(
    terms: &TermStore,
    symbol: &Symbol,
    args: &[TermId],
    owner: &CountedAdmission,
) -> Result<Ty> {
    let work = symbol
        .name()
        .len()
        .checked_add(args.len())
        .ok_or(CountedBvError::Invalid)?;
    owner.admit(work, 0)?;
    if terms.is_declared_function(symbol.name()) {
        return Err(CountedBvError::Unsupported("declared function"));
    }
    match symbol {
        Symbol::Named(name) => match name.as_ref() {
            "and" | "or" | "xor" => {
                for &arg in args {
                    if ty(terms, arg)? != Ty::Bool {
                        return Err(CountedBvError::Invalid);
                    }
                }
                Ok(Ty::Bool)
            }
            "=>" if args.len() == 2
                && ty(terms, args[0])? == Ty::Bool
                && ty(terms, args[1])? == Ty::Bool =>
            {
                Ok(Ty::Bool)
            }
            "=" | "distinct" if args.len() == 2 && ty(terms, args[0])? == ty(terms, args[1])? => {
                Ok(Ty::Bool)
            }
            "concat" if args.len() == 2 => {
                let (Ty::Bv(a), Ty::Bv(b)) = (ty(terms, args[0])?, ty(terms, args[1])?) else {
                    return Err(CountedBvError::Invalid);
                };
                a.checked_add(b).map(Ty::Bv).ok_or(CountedBvError::Invalid)
            }
            name => named_bv(terms, name, args),
        },
        Symbol::Indexed(name, indices) => {
            owner.admit(indices.len(), 0)?;
            indexed_bv(terms, name.as_ref(), indices, args)
        }
        _ => Err(CountedBvError::Unsupported("unaccounted symbol form")),
    }
}

fn named_bv(terms: &TermStore, name: &str, args: &[TermId]) -> Result<Ty> {
    let Some(&first) = args.first() else {
        return Err(CountedBvError::Invalid);
    };
    let Ty::Bv(width) = ty(terms, first)? else {
        return Err(CountedBvError::Invalid);
    };
    match name {
        "bvnot" | "bvneg" if args.len() == 1 => Ok(Ty::Bv(width)),
        "bvadd" | "bvsub" | "bvmul" | "bvudiv" | "bvurem" | "bvsdiv" | "bvsrem" | "bvsmod"
        | "bvand" | "bvor" | "bvxor" | "bvnand" | "bvnor" | "bvxnor" | "bvshl" | "bvlshr"
        | "bvashr"
            if args.len() == 2 && ty(terms, args[1])? == Ty::Bv(width) =>
        {
            Ok(Ty::Bv(width))
        }
        "bvult" | "bvule" | "bvugt" | "bvuge" | "bvslt" | "bvsle" | "bvsgt" | "bvsge"
            if args.len() == 2 && ty(terms, args[1])? == Ty::Bv(width) =>
        {
            Ok(Ty::Bool)
        }
        "bvcomp" if args.len() == 2 && ty(terms, args[1])? == Ty::Bv(width) => Ok(Ty::Bv(1)),
        _ => Err(CountedBvError::Unsupported(
            "unaccounted builtin or signature",
        )),
    }
}

fn indexed_bv(terms: &TermStore, name: &str, indices: &[u32], args: &[TermId]) -> Result<Ty> {
    let [arg] = args else {
        return Err(CountedBvError::Invalid);
    };
    let Ty::Bv(width) = ty(terms, *arg)? else {
        return Err(CountedBvError::Invalid);
    };
    match (name, indices) {
        ("extract", [high, low]) if high >= low && *high < width => Ok(Ty::Bv(high - low + 1)),
        ("zero_extend" | "sign_extend", [extra]) => width
            .checked_add(*extra)
            .map(Ty::Bv)
            .ok_or(CountedBvError::Invalid),
        ("rotate_left" | "rotate_right", [_]) => Ok(Ty::Bv(width)),
        ("repeat", [count]) if *count > 0 => width
            .checked_mul(*count)
            .map(Ty::Bv)
            .ok_or(CountedBvError::Invalid),
        _ => Err(CountedBvError::Unsupported("unaccounted indexed builtin")),
    }
}
