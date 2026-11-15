// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
use super::*;

fn width(terms: &TermStore, id: TermId) -> Result<u32> {
    match terms.sort(id) {
        Sort::BitVec(bits) => Ok(bits.width),
        _ => Err(Error::Invalid),
    }
}
fn result(sort: &Sort, width: u32) -> Result<Kind> {
    if width > 0 && sort == &Sort::bitvec(width) {
        Ok(Kind::Value)
    } else {
        Err(Error::Invalid)
    }
}

pub(super) fn named(terms: &TermStore, name: &str, args: &[TermId], sort: &Sort) -> Result<Kind> {
    match (name, args) {
        ("bvnot" | "bvneg", [a]) => result(sort, width(terms, *a)?),
        ("mkbv", bits) => {
            for &bit in bits {
                boolean(terms.sort(bit))?;
            }
            result(sort, u32::try_from(bits.len()).map_err(|_| Error::Invalid)?)
        }
        ("concat", [a, b]) => result(
            sort,
            width(terms, *a)?
                .checked_add(width(terms, *b)?)
                .ok_or(Error::Invalid)?,
        ),
        (
            "bvadd" | "bvsub" | "bvmul" | "bvudiv" | "bvurem" | "bvsdiv" | "bvsrem" | "bvsmod"
            | "bvand" | "bvor" | "bvxor" | "bvnand" | "bvnor" | "bvxnor" | "bvshl" | "bvlshr"
            | "bvashr" | "bvcomp" | "bvult" | "bvule" | "bvugt" | "bvuge" | "bvslt" | "bvsle"
            | "bvsgt" | "bvsge",
            [a, b],
        ) => {
            let bits = width(terms, *a)?;
            if bits != width(terms, *b)? {
                return Err(Error::Invalid);
            }
            match name {
                "bvult" | "bvule" | "bvugt" | "bvuge" | "bvslt" | "bvsle" | "bvsgt" | "bvsge" => {
                    boolean(sort)?;
                    Ok(Kind::Atom)
                }
                "bvcomp" => result(sort, 1),
                _ => result(sort, bits),
            }
        }
        _ => Err(Error::Unsupported),
    }
}

pub(super) fn indexed(
    terms: &TermStore,
    symbol: &Symbol,
    args: &[TermId],
    sort: &Sort,
) -> Result<Kind> {
    let (Symbol::Indexed(name, indices), [arg]) = (symbol, args) else {
        return Err(Error::Unsupported);
    };
    let bits = width(terms, *arg)?;
    let output = match (name.as_ref(), indices.as_slice()) {
        ("extract", [high, low]) if high >= low && *high < bits => high - low + 1,
        ("zero_extend" | "sign_extend", [extra]) => {
            bits.checked_add(*extra).ok_or(Error::Invalid)?
        }
        ("rotate_left" | "rotate_right", [_]) => bits,
        ("repeat", [count]) if *count > 0 => bits.checked_mul(*count).ok_or(Error::Invalid)?,
        _ => return Err(Error::Unsupported),
    };
    result(sort, output)
}
