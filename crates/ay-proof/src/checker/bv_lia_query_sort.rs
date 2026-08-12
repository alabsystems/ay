// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Sort validation for the independently checked Bool/Int/BV query fragment.

use ay_core::{Constant, Sort, Symbol, TermData, TermId, TermStore};
use num_traits::{Signed, ToPrimitive};

use super::MAX_INTEGER_BITS;

pub(super) fn node_is_well_sorted(terms: &TermStore, term: TermId) -> bool {
    let sort = terms.sort(term);
    match terms.get(term) {
        TermData::Const(Constant::Bool(_)) => sort == &Sort::Bool,
        TermData::Const(Constant::Int(value)) => {
            sort == &Sort::Int && value.bits() <= MAX_INTEGER_BITS
        }
        TermData::Const(Constant::BitVec { value, width }) => {
            valid_bv_sort(sort).is_some_and(|actual| {
                actual == *width
                    && !value.is_negative()
                    && value.to_u64().is_some()
                    && value < &(num_bigint::BigInt::from(1_u8) << *width)
            })
        }
        TermData::Const(_) => false,
        TermData::Var(..) => supported_value_sort(sort),
        TermData::Not(inner) => sort == &Sort::Bool && terms.sort(*inner) == &Sort::Bool,
        TermData::Ite(condition, then_term, else_term) => {
            terms.sort(*condition) == &Sort::Bool
                && terms.sort(*then_term) == terms.sort(*else_term)
                && sort == terms.sort(*then_term)
                && supported_value_sort(sort)
        }
        TermData::App(symbol, args) => app_is_well_sorted(terms, sort, symbol, args),
        _ => false,
    }
}

fn app_is_well_sorted(terms: &TermStore, sort: &Sort, symbol: &Symbol, args: &[TermId]) -> bool {
    match symbol {
        Symbol::Named(name) => named_app_is_well_sorted(terms, sort, name, args),
        Symbol::Indexed(name, indices) => {
            indexed_app_is_well_sorted(terms, sort, name, indices, args)
        }
        _ => false,
    }
}

fn named_app_is_well_sorted(terms: &TermStore, sort: &Sort, name: &str, args: &[TermId]) -> bool {
    match name {
        "and" | "or" => sort == &Sort::Bool && all_sort(terms, args, &Sort::Bool),
        "not" => sort == &Sort::Bool && args.len() == 1 && terms.sort(args[0]) == &Sort::Bool,
        "=>" | "implies" | "xor" => {
            sort == &Sort::Bool && args.len() == 2 && all_sort(terms, args, &Sort::Bool)
        }
        "=" | "distinct" => {
            sort == &Sort::Bool
                && args.len() == 2
                && terms.sort(args[0]) == terms.sort(args[1])
                && supported_value_sort(terms.sort(args[0]))
        }
        "<" | "<=" | ">" | ">=" => {
            sort == &Sort::Bool && args.len() == 2 && all_sort(terms, args, &Sort::Int)
        }
        "bvult" | "bvule" | "bvugt" | "bvuge" | "bvslt" | "bvsle" | "bvsgt" | "bvsge" => {
            sort == &Sort::Bool && args.len() == 2 && same_valid_bv_args(terms, args).is_some()
        }
        "+" | "*" => sort == &Sort::Int && all_sort(terms, args, &Sort::Int),
        "-" => sort == &Sort::Int && !args.is_empty() && all_sort(terms, args, &Sort::Int),
        "mod" => sort == &Sort::Int && args.len() == 2 && all_sort(terms, args, &Sort::Int),
        "abs" => sort == &Sort::Int && args.len() == 1 && terms.sort(args[0]) == &Sort::Int,
        "bv2nat" => {
            sort == &Sort::Int && args.len() == 1 && valid_bv_sort(terms.sort(args[0])).is_some()
        }
        "bvnot" | "bvneg" => {
            args.len() == 1
                && valid_bv_sort(sort)
                    .is_some_and(|width| valid_bv_sort(terms.sort(args[0])) == Some(width))
        }
        "concat" => {
            args.len() == 2
                && valid_bv_sort(sort).is_some_and(|width| {
                    valid_bv_sort(terms.sort(args[0]))
                        .zip(valid_bv_sort(terms.sort(args[1])))
                        .and_then(|(left, right)| left.checked_add(right))
                        == Some(width)
                })
        }
        "bvadd" | "bvsub" | "bvmul" | "bvand" | "bvor" | "bvxor" | "bvnand" | "bvnor"
        | "bvxnor" | "bvshl" | "bvlshr" | "bvashr" => {
            args.len() == 2
                && valid_bv_sort(sort)
                    .is_some_and(|width| same_valid_bv_args(terms, args) == Some(width))
        }
        _ => false,
    }
}

fn indexed_app_is_well_sorted(
    terms: &TermStore,
    sort: &Sort,
    name: &str,
    indices: &[u32],
    args: &[TermId],
) -> bool {
    match (name, indices, args) {
        ("int2bv", [width], [arg]) => {
            valid_bv_sort(sort) == Some(*width) && terms.sort(*arg) == &Sort::Int
        }
        ("extract", [high, low], [arg]) => {
            high >= low
                && valid_bv_sort(terms.sort(*arg)).is_some_and(|input| *high < input)
                && valid_bv_sort(sort)
                    == high.checked_sub(*low).and_then(|span| span.checked_add(1))
        }
        ("zero_extend" | "sign_extend", [added], [arg]) => {
            valid_bv_sort(terms.sort(*arg)).and_then(|input| input.checked_add(*added))
                == valid_bv_sort(sort)
        }
        _ => false,
    }
}

fn all_sort(terms: &TermStore, args: &[TermId], expected: &Sort) -> bool {
    args.iter().all(|&arg| terms.sort(arg) == expected)
}

fn same_valid_bv_args(terms: &TermStore, args: &[TermId]) -> Option<u32> {
    (args.len() == 2)
        .then(|| valid_bv_sort(terms.sort(args[0])).zip(valid_bv_sort(terms.sort(args[1]))))
        .flatten()
        .and_then(|(left, right)| (left == right).then_some(left))
}

fn supported_value_sort(sort: &Sort) -> bool {
    matches!(sort, Sort::Bool | Sort::Int) || valid_bv_sort(sort).is_some()
}

fn valid_bv_sort(sort: &Sort) -> Option<u32> {
    let Sort::BitVec(width) = sort else {
        return None;
    };
    (width.width > 0 && width.width <= 64).then_some(width.width)
}
