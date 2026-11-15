// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Cancellation-aware conjunction and bit-vector scans.

use super::*;

pub(super) fn contains_any_checked(
    set: &FxHashSet<&ChcExpr>,
    terms: &[std::sync::Arc<ChcExpr>],
    stop: &mut dyn FnMut() -> bool,
) -> Option<bool> {
    for term in terms {
        if stop() {
            return None;
        }
        if set.contains(term.as_ref()) {
            return Some(true);
        }
    }
    Some(false)
}

pub(super) fn contains_all_checked(
    set: &FxHashSet<&ChcExpr>,
    terms: &[std::sync::Arc<ChcExpr>],
    stop: &mut dyn FnMut() -> bool,
) -> Option<bool> {
    for term in terms {
        if stop() {
            return None;
        }
        if !set.contains(term.as_ref()) {
            return Some(false);
        }
    }
    Some(true)
}

pub(super) fn has_bv2nat_constant_contradiction_checked(
    conjuncts: &[ChcExpr],
    stop: &mut dyn FnMut() -> bool,
) -> Option<bool> {
    let mut bv_equalities: FxHashMap<ChcVar, u128> = FxHashMap::default();

    for conjunct in conjuncts {
        if stop() {
            return None;
        }
        if let Some((var, bits)) = extract_bv_var_const_equality(conjunct) {
            if let Some(previous) = bv_equalities.insert(var, bits) {
                if previous != bits {
                    return Some(true);
                }
            }
        }
    }

    for conjunct in conjuncts {
        if stop() {
            return None;
        }
        let Some((var, int_value, is_equality)) = extract_bv2nat_int_literal(conjunct) else {
            continue;
        };
        let Some(&bits) = bv_equalities.get(&var) else {
            continue;
        };
        let Some(int_bits) = non_negative_int_to_u128(int_value) else {
            if is_equality {
                return Some(true);
            }
            continue;
        };

        let equal = bits == int_bits;
        if (is_equality && !equal) || (!is_equality && equal) {
            return Some(true);
        }
    }

    Some(false)
}

fn extract_bv_var_const_equality(expr: &ChcExpr) -> Option<(ChcVar, u128)> {
    let ChcExpr::Op(ChcOp::Eq, args) = expr else {
        return None;
    };
    if args.len() != 2 {
        return None;
    }
    bv_var_const_pair(args[0].as_ref(), args[1].as_ref())
        .or_else(|| bv_var_const_pair(args[1].as_ref(), args[0].as_ref()))
}

fn bv_var_const_pair(lhs: &ChcExpr, rhs: &ChcExpr) -> Option<(ChcVar, u128)> {
    let ChcExpr::Var(var) = lhs else {
        return None;
    };
    let ChcSort::BitVec(var_width) = var.sort else {
        return None;
    };
    let ChcExpr::BitVec(bits, value_width) = rhs else {
        return None;
    };
    if var_width != *value_width {
        return None;
    }
    Some((var.clone(), *bits))
}

fn extract_bv2nat_int_literal(expr: &ChcExpr) -> Option<(ChcVar, i128, bool)> {
    match expr {
        ChcExpr::Op(ChcOp::Eq, args) if args.len() == 2 => {
            bv2nat_int_pair(args[0].as_ref(), args[1].as_ref(), true)
                .or_else(|| bv2nat_int_pair(args[1].as_ref(), args[0].as_ref(), true))
        }
        ChcExpr::Op(ChcOp::Ne, args) if args.len() == 2 => {
            bv2nat_int_pair(args[0].as_ref(), args[1].as_ref(), false)
                .or_else(|| bv2nat_int_pair(args[1].as_ref(), args[0].as_ref(), false))
        }
        ChcExpr::Op(ChcOp::Not, args) if args.len() == 1 => match args[0].as_ref() {
            ChcExpr::Op(ChcOp::Eq, eq_args) if eq_args.len() == 2 => {
                bv2nat_int_pair(eq_args[0].as_ref(), eq_args[1].as_ref(), false)
                    .or_else(|| bv2nat_int_pair(eq_args[1].as_ref(), eq_args[0].as_ref(), false))
            }
            ChcExpr::Op(ChcOp::Ne, ne_args) if ne_args.len() == 2 => {
                bv2nat_int_pair(ne_args[0].as_ref(), ne_args[1].as_ref(), true)
                    .or_else(|| bv2nat_int_pair(ne_args[1].as_ref(), ne_args[0].as_ref(), true))
            }
            _ => None,
        },
        _ => None,
    }
}

fn bv2nat_int_pair(
    lhs: &ChcExpr,
    rhs: &ChcExpr,
    is_equality: bool,
) -> Option<(ChcVar, i128, bool)> {
    let ChcExpr::Op(ChcOp::Bv2Nat, args) = lhs else {
        return None;
    };
    if args.len() != 1 {
        return None;
    }
    let ChcExpr::Var(var) = args[0].as_ref() else {
        return None;
    };
    if !matches!(var.sort, ChcSort::BitVec(_)) {
        return None;
    }
    let ChcExpr::Int(value) = rhs else {
        return None;
    };
    Some((var.clone(), *value, is_equality))
}

fn non_negative_int_to_u128(value: i128) -> Option<u128> {
    if value < 0 {
        None
    } else {
        Some(value as u128)
    }
}
