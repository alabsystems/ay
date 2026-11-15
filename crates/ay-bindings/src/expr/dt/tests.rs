// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

#![cfg(test)]

use super::*;
use crate::SortError;
use num_bigint::BigInt;

mod definitions;
mod folding;
mod recursive_refs;
mod resources;
mod sibling_refs;
mod signatures;
mod store_coercion;

fn raw(value: ExprValue, sort: Sort) -> Expr {
    Expr {
        sort,
        value: Arc::new(value),
    }
}

fn raw_constructor(datatype: &str, constructor: &str, args: Vec<Expr>, sort: Sort) -> Expr {
    raw(
        ExprValue::DatatypeConstructor {
            datatype_name: datatype.to_owned(),
            constructor_name: constructor.to_owned(),
            args,
        },
        sort,
    )
}

fn raw_ite(cond: Expr, then_expr: Expr, else_expr: Expr, sort: Sort) -> Expr {
    raw(
        ExprValue::Ite {
            cond,
            then_expr,
            else_expr,
        },
        sort,
    )
}

fn pair_sort(width: u32) -> Sort {
    Sort::struct_type(
        "Pair",
        [("flag", Sort::bool()), ("word", Sort::bitvec(width))],
    )
}

fn pair(flag: Expr, word: Expr) -> Expr {
    let sort = pair_sort(word.sort().bitvec_width().expect("test word"));
    Expr::datatype_constructor("Pair", "Pair_mk", vec![flag, word], sort)
}

fn assert_error(result: Result<Expr, SortError>) {
    assert!(
        matches!(result, Err(SortError::Mismatch { .. })),
        "{result:?}"
    );
}
