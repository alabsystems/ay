// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Complete local types; no name/sort clones or indexed/unsupported heads.

use super::*;
use ay_core::Constant;
use num_traits::ToPrimitive;

#[derive(Clone, Copy)]
pub(super) enum Operation {
    Atom,
    Unary,
    Binary { extra: usize, address: bool },
    Balanced,
    Array,
    Select,
}
#[derive(Clone, Copy, PartialEq, Eq)]
struct Shape {
    index: u32,
    width: u32,
    boolean: bool,
}

fn scalar(sort: &Sort) -> Option<Shape> {
    match sort {
        Sort::Bool => Some(Shape {
            index: 0,
            width: 1,
            boolean: true,
        }),
        Sort::BitVec(w) if (1..=128).contains(&w.width) => Some(Shape {
            index: 0,
            width: w.width,
            boolean: false,
        }),
        _ => None,
    }
}
fn shape(sort: &Sort) -> Option<Shape> {
    if let Sort::Array(array) = sort {
        let Sort::BitVec(index) = &array.index_sort else {
            return None;
        };
        let cell = scalar(&array.element_sort)?;
        (9..=128).contains(&index.width).then_some(Shape {
            index: index.width,
            ..cell
        })
    } else {
        scalar(sort)
    }
}
fn child(terms: &TermStore, id: TermId) -> Option<Shape> {
    terms.entry_stamp(id)?;
    shape(terms.sort(id))
}

pub(super) fn inspect(terms: &TermStore, term: TermId) -> Option<(Operation, &[TermId])> {
    let actual = child(terms, term)?;
    match terms.get(term) {
        TermData::Var(..) => Some((
            if actual.index == 0 {
                Operation::Atom
            } else {
                Operation::Array
            },
            &[],
        )),
        TermData::Const(Constant::Bool(_)) if actual.index == 0 && actual.boolean => {
            Some((Operation::Atom, &[]))
        }
        TermData::Const(Constant::BitVec { value, width })
            if actual.index == 0
                && !actual.boolean
                && actual.width == *width
                && value
                    .to_u128()
                    .is_some_and(|v| *width == 128 || v < (1u128 << *width)) =>
        {
            Some((Operation::Atom, &[]))
        }
        TermData::Not(inner)
            if actual.index == 0 && actual.boolean && child(terms, *inner) == Some(actual) =>
        {
            Some((Operation::Unary, std::slice::from_ref(inner)))
        }
        TermData::App(Symbol::Named(name), args) if name.len() <= 32 && args.len() <= 128 => {
            application(terms, actual, name, args).map(|op| (op, args.as_slice()))
        }
        _ => None,
    }
}

fn application(terms: &TermStore, actual: Shape, name: &str, args: &[TermId]) -> Option<Operation> {
    if actual.index != 0 {
        return match (name, args) {
            ("const-array", [fill])
                if child(terms, *fill) == Some(Shape { index: 0, ..actual }) =>
            {
                Some(Operation::Array)
            }
            ("store", [base, index, value])
                if child(terms, *base) == Some(actual)
                    && child(terms, *index)
                        == Some(Shape {
                            index: 0,
                            width: actual.index,
                            boolean: false,
                        })
                    && child(terms, *value) == Some(Shape { index: 0, ..actual }) =>
            {
                Some(Operation::Array)
            }
            _ => None,
        };
    }
    if let ("select", [array, key]) = (name, args) {
        let array = child(terms, *array)?;
        return (array.index != 0
            && Shape { index: 0, ..array } == actual
            && child(terms, *key)
                == Some(Shape {
                    index: 0,
                    width: array.index,
                    boolean: false,
                }))
        .then_some(Operation::Select);
    }
    let bools = || {
        args.iter().all(|&id| {
            child(terms, id)
                == Some(Shape {
                    index: 0,
                    width: 1,
                    boolean: true,
                })
        })
    };
    let same = || {
        let [a, b] = args else {
            return None;
        };
        let a = child(terms, *a)?;
        (a.index == 0 && child(terms, *b) == Some(a)).then_some(a)
    };
    let binary = |extra, address| Some(Operation::Binary { extra, address });
    match name {
        "not" if actual.boolean && args.len() == 1 && bools() => Some(Operation::Unary),
        "and" | "or" if actual.boolean && bools() => Some(Operation::Balanced),
        "xor" if actual.boolean && args.len() == 2 && bools() => binary(1, false),
        "=>" | "implies" if actual.boolean && args.len() == 2 && bools() => binary(2, false),
        "=" | "distinct" if actual.boolean => {
            same()?;
            binary(if name == "=" { 1 } else { 2 }, false)
        }
        "bvadd" | "bvsub" | "bvand" | "bvor" | "bvxor"
            if !actual.boolean && same() == Some(actual) =>
        {
            binary(1, matches!(name, "bvadd" | "bvsub"))
        }
        "bvult" | "bvugt" if actual.boolean && !same()?.boolean => binary(1, false),
        "bvule" | "bvuge" if actual.boolean && !same()?.boolean => binary(2, false),
        _ => None,
    }
}
