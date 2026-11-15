// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Preserve input DAG sharing in the existing BMC selector and BV rewrites.
//!
//! Only the traversal is memoized. In particular, the BV pass still runs
//! `simplify_constants` at each operator before its local identity rules;
//! this is not a claim that the complete simplification pipeline is O(DAG).

use std::sync::Arc;

use ay_core::kani_compat::DetHashMap as FxHashMap;

use crate::{ChcExpr, ChcOp, ChcSort};

#[derive(Clone, Copy)]
enum Pass {
    DatatypeSelectors,
    BitVectorIdentities,
}

type Memo = FxHashMap<*const ChcExpr, Arc<ChcExpr>>;

pub(super) fn datatype_selectors(expr: ChcExpr) -> ChcExpr {
    rewrite(expr, Pass::DatatypeSelectors)
}

pub(super) fn bitvector_identities(expr: ChcExpr) -> ChcExpr {
    rewrite(expr, Pass::BitVectorIdentities)
}

fn rewrite(expr: ChcExpr, pass: Pass) -> ChcExpr {
    // Keep every input Arc alive until the pointer-keyed memo is discarded.
    // Generated expressions never enter this memo: extract re-entry below
    // starts a separate root-scoped rewrite, just as the old helper recursed.
    let root = Arc::new(expr);
    let mut memo = Memo::default();
    let result = rewrite_arg(&root, pass, &mut memo);
    drop(memo);
    Arc::unwrap_or_clone(result)
}

fn rewrite_arg(expr: &Arc<ChcExpr>, pass: Pass, memo: &mut Memo) -> Arc<ChcExpr> {
    let key = Arc::as_ptr(expr);
    if let Some(result) = memo.get(&key) {
        return Arc::clone(result);
    }
    let rewritten = match expr.as_ref() {
        ChcExpr::Op(op, args) => {
            let args = args
                .iter()
                .map(|arg| rewrite_arg(arg, pass, memo))
                .collect();
            let rebuilt = ChcExpr::Op(*op, args);
            match pass {
                Pass::DatatypeSelectors => rebuilt,
                Pass::BitVectorIdentities => bv_identity(rebuilt.simplify_constants()),
            }
        }
        ChcExpr::PredicateApp(name, pred, args) => ChcExpr::PredicateApp(
            name.clone(),
            *pred,
            args.iter()
                .map(|arg| rewrite_arg(arg, pass, memo))
                .collect(),
        ),
        ChcExpr::FuncApp(name, sort, args) => {
            let args = args
                .iter()
                .map(|arg| rewrite_arg(arg, pass, memo))
                .collect();
            match pass {
                Pass::DatatypeSelectors => datatype_selector(name, sort, args),
                Pass::BitVectorIdentities => ChcExpr::FuncApp(name.clone(), sort.clone(), args),
            }
        }
        ChcExpr::ConstArray(key_sort, value) => {
            ChcExpr::ConstArray(key_sort.clone(), rewrite_arg(value, pass, memo))
        }
        ChcExpr::ArrayLambda(lambda) => ChcExpr::ArrayLambda(
            lambda.with_captures(
                lambda
                    .captures()
                    .iter()
                    .map(|value| rewrite_arg(value, pass, memo))
                    .collect(),
            ),
        ),
        other => other.clone(),
    };
    let result = Arc::new(rewritten);
    memo.insert(key, Arc::clone(&result));
    result
}

fn datatype_selector(name: &str, sort: &ChcSort, args: Vec<Arc<ChcExpr>>) -> ChcExpr {
    if args.len() == 1 {
        if let ChcExpr::FuncApp(ctor_name, ChcSort::Datatype { constructors, .. }, ctor_args) =
            args[0].as_ref()
        {
            for ctor in constructors.iter() {
                if ctor.name != *ctor_name {
                    continue;
                }
                for (selector_idx, selector) in ctor.selectors.iter().enumerate() {
                    if selector.name == name {
                        if let Some(value) = ctor_args.get(selector_idx) {
                            return value.as_ref().clone();
                        }
                    }
                }
            }
        }
    }
    ChcExpr::FuncApp(name.to_owned(), sort.clone(), args)
}

fn bv_identity(expr: ChcExpr) -> ChcExpr {
    let ChcExpr::Op(op, args) = &expr else {
        return expr;
    };
    match op {
        ChcOp::BvAdd if args.len() == 2 => {
            if is_bv_zero(args[0].as_ref()) {
                return args[1].as_ref().clone();
            }
            if is_bv_zero(args[1].as_ref()) {
                return args[0].as_ref().clone();
            }
        }
        ChcOp::BvSub if args.len() == 2 => {
            if is_bv_zero(args[1].as_ref()) {
                return args[0].as_ref().clone();
            }
            if args[0] == args[1] {
                if let Some(width) = bv_width(args[0].as_ref()) {
                    return ChcExpr::BitVec(0, width);
                }
            }
            if let Some(stripped) = strip_matching_bv_add_const(args[0].as_ref(), args[1].as_ref())
            {
                return stripped;
            }
        }
        ChcOp::BvMul if args.len() == 2 => {
            if is_bv_zero(args[0].as_ref()) {
                return args[0].as_ref().clone();
            }
            if is_bv_zero(args[1].as_ref()) {
                if let Some(width) = bv_width(args[0].as_ref()) {
                    return ChcExpr::BitVec(0, width);
                }
            }
            if is_bv_one(args[0].as_ref()) {
                return args[1].as_ref().clone();
            }
            if is_bv_one(args[1].as_ref()) {
                return args[0].as_ref().clone();
            }
        }
        ChcOp::BvUDiv | ChcOp::BvSDiv if args.len() == 2 && is_bv_one(args[1].as_ref()) => {
            return args[0].as_ref().clone();
        }
        ChcOp::BvExtract(hi, lo) if args.len() == 1 => {
            if let Some(extracted) = extract_from_bv_concat(args[0].as_ref(), *hi, *lo) {
                return extracted;
            }
        }
        _ => {}
    }
    ChcExpr::Op(*op, args.clone())
}

fn strip_matching_bv_add_const(sum: &ChcExpr, subtrahend: &ChcExpr) -> Option<ChcExpr> {
    let ChcExpr::Op(ChcOp::BvAdd, args) = sum else {
        return None;
    };
    if args.len() != 2 {
        return None;
    }
    if args[0].as_ref() == subtrahend {
        return Some(args[1].as_ref().clone());
    }
    if args[1].as_ref() == subtrahend {
        return Some(args[0].as_ref().clone());
    }
    None
}

fn extract_from_bv_concat(expr: &ChcExpr, hi: u32, lo: u32) -> Option<ChcExpr> {
    let ChcExpr::Op(ChcOp::BvConcat, args) = expr else {
        return None;
    };
    if args.len() != 2 || hi < lo {
        return None;
    }
    let high = args[0].as_ref();
    let low = args[1].as_ref();
    let high_width = bv_width(high)?;
    let low_width = bv_width(low)?;
    let total_width = high_width.checked_add(low_width)?;
    if hi >= total_width {
        return None;
    }
    if hi < low_width {
        return Some(extract_or_identity(low.clone(), hi, lo));
    }
    if lo >= low_width {
        return Some(extract_or_identity(
            high.clone(),
            hi - low_width,
            lo - low_width,
        ));
    }
    None
}

fn extract_or_identity(expr: ChcExpr, hi: u32, lo: u32) -> ChcExpr {
    if let Some(width) = bv_width(&expr) {
        if lo == 0 && hi + 1 == width {
            return expr;
        }
    }
    // This expression is generated, not part of the borrowed input DAG.
    // Give it its own memo so temporary addresses cannot alias an old key.
    bitvector_identities(ChcExpr::Op(ChcOp::BvExtract(hi, lo), vec![Arc::new(expr)]))
        .simplify_constants()
}

fn bv_width(expr: &ChcExpr) -> Option<u32> {
    match expr.sort() {
        ChcSort::BitVec(width) => Some(width),
        _ => None,
    }
}

fn is_bv_zero(expr: &ChcExpr) -> bool {
    matches!(expr, ChcExpr::BitVec(value, _) if *value == 0)
}

fn is_bv_one(expr: &ChcExpr) -> bool {
    matches!(expr, ChcExpr::BitVec(value, _) if *value == 1)
}

#[cfg(test)]
mod tests;
