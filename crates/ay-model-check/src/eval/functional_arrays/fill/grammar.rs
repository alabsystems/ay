// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Exact bounded Bool/BV/array metadata; unknown or indexed heads decline.

use super::*;

fn width(sort: &Sort) -> Option<u32> {
    match sort {
        Sort::BitVec(bits) if bits.width > 0 && bits.width <= 128 => Some(bits.width),
        _ => None,
    }
}

fn scalar(sort: &Sort) -> bool {
    sort == &Sort::Bool || width(sort).is_some()
}

fn array(sort: &Sort) -> bool {
    matches!(sort, Sort::Array(array) if matches!(&array.index_sort, Sort::BitVec(key) if key.width == 64) && scalar(&array.element_sort))
}

pub(super) fn scalar_value(value: &ModelValue, sort: &Sort) -> EvalResult<()> {
    let valid = match (value, sort) {
        (ModelValue::Bool(_), Sort::Bool) => true,
        (
            ModelValue::BitVec {
                value,
                width: actual,
            },
            Sort::BitVec(expected),
        ) => {
            *actual == expected.width
                && width(sort).is_some()
                && !value.is_negative()
                && value.bits() <= u64::from(*actual)
        }
        _ => false,
    };
    if valid {
        Ok(())
    } else {
        Err("fill scalar model value differs from exact sort".into())
    }
}

pub(super) fn node(terms: &TermStore, term: TermId, root: TermId, bound: TermId) -> EvalResult<()> {
    let sort = terms.sort(term);
    if !scalar(sort) && !array(sort) {
        return Err("unsupported fill sort".into());
    }
    let mut small = [term; 3];
    let children = children(terms, term, &mut small);
    if children
        .iter()
        .any(|child| (child.0 as usize) >= terms.len())
    {
        return Err("invalid fill child".into());
    }
    let valid = match terms.get(term) {
        TermData::Const(Constant::Bool(_)) => sort == &Sort::Bool,
        TermData::Const(Constant::BitVec {
            value,
            width: actual,
        }) => {
            width(sort) == Some(*actual)
                && !value.is_negative()
                && value.bits() <= u64::from(*actual)
        }
        TermData::Var(name, _) => name.len() <= 16_384,
        TermData::Not(inner) => sort == &Sort::Bool && terms.sort(*inner) == &Sort::Bool,
        TermData::Ite(condition, positive, negative) => {
            terms.sort(*condition) == &Sort::Bool
                && terms.sort(*positive) == sort
                && terms.sort(*negative) == sort
        }
        TermData::App(Symbol::Named(name), args) => {
            application(terms, term, root, bound, name, args)
        }
        _ => false,
    };
    if valid {
        Ok(())
    } else {
        Err("unsupported or malformed fill grammar".into())
    }
}

pub(super) fn children<'a>(
    terms: &'a TermStore,
    term: TermId,
    small: &'a mut [TermId; 3],
) -> &'a [TermId] {
    match terms.get(term) {
        TermData::App(_, args) => args,
        TermData::Not(inner) => {
            small[0] = *inner;
            &small[..1]
        }
        TermData::Ite(condition, positive, negative) => {
            *small = [*condition, *positive, *negative];
            small
        }
        _ => &[],
    }
}

fn application(
    terms: &TermStore,
    term: TermId,
    root: TermId,
    bound: TermId,
    name: &str,
    args: &[TermId],
) -> bool {
    let sort = terms.sort(term);
    if name == "lambda-array" {
        return term == root
            && args.len() == 2
            && args[0] == bound
            && matches!(sort, Sort::Array(array) if terms.sort(bound) == &array.index_sort && terms.sort(args[1]) == &array.element_sort);
    }
    boolean(terms, sort, name, args)
        .or_else(|| bitvector(terms, sort, name, args))
        .or_else(|| array_application(terms, sort, name, args))
        .unwrap_or(false)
}

fn boolean(terms: &TermStore, sort: &Sort, name: &str, args: &[TermId]) -> Option<bool> {
    let all_bool = || args.iter().all(|arg| terms.sort(*arg) == &Sort::Bool);
    Some(match name {
        "and" | "or" => sort == &Sort::Bool && all_bool(),
        "=>" | "xor" => args.len() == 2 && sort == &Sort::Bool && all_bool(),
        "not" => args.len() == 1 && sort == &Sort::Bool && all_bool(),
        "ite" => {
            args.len() == 3
                && terms.sort(args[0]) == &Sort::Bool
                && terms.sort(args[1]) == sort
                && terms.sort(args[2]) == sort
        }
        "=" | "distinct" => {
            args.len() >= 2
                && sort == &Sort::Bool
                && same(terms, args)
                && scalar(terms.sort(args[0]))
        }
        _ => return None,
    })
}

fn same(terms: &TermStore, args: &[TermId]) -> bool {
    args.first().is_some_and(|first| {
        args.iter()
            .all(|arg| terms.sort(*arg) == terms.sort(*first))
    })
}

fn bitvector(terms: &TermStore, sort: &Sort, name: &str, args: &[TermId]) -> Option<bool> {
    let bv_binary = || args.len() == 2 && same(terms, args) && width(terms.sort(args[0])).is_some();
    Some(match name {
        "bvnot" | "bvneg" => {
            args.len() == 1 && width(sort).is_some() && terms.sort(args[0]) == sort
        }
        "bvadd" | "bvsub" | "bvmul" | "bvand" | "bvor" | "bvxor" | "bvshl" | "bvlshr"
        | "bvashr" | "bvudiv" | "bvurem" | "bvsdiv" | "bvsrem" | "bvsmod" => {
            bv_binary() && terms.sort(args[0]) == sort
        }
        "bvult" | "bvule" | "bvugt" | "bvuge" | "bvslt" | "bvsle" | "bvsgt" | "bvsge" => {
            bv_binary() && sort == &Sort::Bool
        }
        "bvcomp" => bv_binary() && width(sort) == Some(1),
        "concat" => {
            args.len() == 2
                && match (
                    width(terms.sort(args[0])),
                    width(terms.sort(args[1])),
                    width(sort),
                ) {
                    (Some(left), Some(right), Some(result)) => {
                        left.checked_add(right) == Some(result)
                    }
                    _ => false,
                }
        }
        _ => return None,
    })
}

fn array_application(terms: &TermStore, sort: &Sort, name: &str, args: &[TermId]) -> Option<bool> {
    Some(match name {
        "select" => {
            args.len() == 2
                && matches!(terms.sort(args[0]), Sort::Array(array)
            if terms.sort(args[1]) == &array.index_sort && sort == &array.element_sort)
        }
        "const-array" => {
            args.len() == 1
                && matches!(sort, Sort::Array(array) if terms.sort(args[0]) == &array.element_sort)
        }
        "store" => {
            args.len() == 3
                && terms.sort(args[0]) == sort
                && matches!(sort, Sort::Array(array)
            if terms.sort(args[1]) == &array.index_sort && terms.sort(args[2]) == &array.element_sort)
        }
        _ => return None,
    })
}
