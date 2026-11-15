// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Exact scalar operator signatures; no elaboration, rewriting or UF fallback.

use super::*;

const BOOLEAN: &[&str] = &["not", "and", "or", "xor", "=>", "=", "distinct", "ite"];
const UNARY: &[&str] = &["bvnot", "bvneg"];
const BINARY: &[&str] = &[
    "bvadd", "bvsub", "bvmul", "bvudiv", "bvurem", "bvsdiv", "bvsrem", "bvsmod", "bvand", "bvor",
    "bvxor", "bvnand", "bvnor", "bvxnor", "bvshl", "bvlshr", "bvashr",
];
const COMPARE: &[&str] = &[
    "bvult", "bvule", "bvugt", "bvuge", "bvslt", "bvsle", "bvsgt", "bvsge",
];

pub(super) fn write_head(head: &SExpr, budget: &mut Budget, text: &mut String) -> Option<()> {
    if let Some(name) = head.as_symbol() {
        if !BOOLEAN.contains(&name)
            && !UNARY.contains(&name)
            && !BINARY.contains(&name)
            && !COMPARE.contains(&name)
            && !matches!(name, "concat" | "bvcomp")
        {
            return None;
        }
        return budget.push(text, name);
    }
    let (name, first, second) = indexed(head)?;
    budget.charge(1, 96)?;
    let text_head = match second {
        Some(second) => format!("(_ {name} {first} {second})"),
        None => format!("(_ {name} {first})"),
    };
    budget.push(text, &text_head)
}

fn indexed(head: &SExpr) -> Option<(&str, u32, Option<u32>)> {
    match head.as_list()? {
        [marker, name, high, low] if marker.is_symbol("_") && name.is_symbol("extract") => {
            Some(("extract", natural(high)?, Some(natural(low)?)))
        }
        [marker, name, count] if marker.is_symbol("_") => {
            let name = name.as_symbol()?;
            matches!(
                name,
                "zero_extend" | "sign_extend" | "repeat" | "rotate_left" | "rotate_right"
            )
            .then_some((name, natural(count)?, None))
        }
        _ => None,
    }
}

pub(super) fn result(head: &SExpr, args: &[Scalar]) -> Option<Scalar> {
    let Some(name) = head.as_symbol() else {
        let [Scalar::Bv(width)] = args else {
            return None;
        };
        let (name, first, second) = indexed(head)?;
        let width = match name {
            "extract" => {
                let low = second?;
                if first < low || first >= *width {
                    return None;
                }
                first.checked_sub(low)?.checked_add(1)?
            }
            "zero_extend" | "sign_extend" => width.checked_add(first)?,
            "repeat" if first != 0 => width.checked_mul(first)?,
            "rotate_left" | "rotate_right" => *width,
            _ => return None,
        };
        return bounded(width);
    };
    if name == "ite" {
        let [Scalar::Bool, left, right] = args else {
            return None;
        };
        return (left == right).then_some(*left);
    }
    if matches!(name, "=" | "distinct") {
        let [left, right] = args else {
            return None;
        };
        return (left == right).then_some(Scalar::Bool);
    }
    if BOOLEAN.contains(&name) {
        let arity = match name {
            "not" => args.len() == 1,
            "xor" | "=>" => args.len() == 2,
            "and" | "or" => args.len() >= 2,
            _ => false,
        };
        return (arity && args.iter().all(|sort| *sort == Scalar::Bool)).then_some(Scalar::Bool);
    }
    if UNARY.contains(&name) {
        let [sort @ Scalar::Bv(_)] = args else {
            return None;
        };
        return Some(*sort);
    }
    let [Scalar::Bv(left), Scalar::Bv(right)] = args else {
        return None;
    };
    if name == "concat" {
        return bounded(left.checked_add(*right)?);
    }
    if left != right {
        return None;
    }
    if BINARY.contains(&name) {
        Some(Scalar::Bv(*left))
    } else if COMPARE.contains(&name) {
        Some(Scalar::Bool)
    } else if name == "bvcomp" {
        Some(Scalar::Bv(1))
    } else {
        None
    }
}

fn bounded(width: u32) -> Option<Scalar> {
    (1..=crate::api::MAX_API_BITVECTOR_WIDTH)
        .contains(&width)
        .then_some(Scalar::Bv(width))
}
