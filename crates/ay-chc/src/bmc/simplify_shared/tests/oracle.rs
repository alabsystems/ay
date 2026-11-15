// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Frozen pre-sharing helpers from 51d3e6a2af3803bd8906100e023e73701f96bb3e.
//! Keep recursive calls inside this oracle, independent of the new traversal.
//! Only use on shallow inputs: the original helpers expand shared DAGs as trees.

use crate::{ChcExpr, ChcOp, ChcSort};
use std::sync::Arc;

pub(super) struct Frozen;

impl Frozen {
    pub(super) fn simplify_bv_identities(expr: ChcExpr) -> ChcExpr {
        match &expr {
            ChcExpr::Op(op, args) => {
                let args: Vec<_> = args
                    .iter()
                    .map(|arg| Arc::new(Self::simplify_bv_identities(arg.as_ref().clone())))
                    .collect();
                let expr = ChcExpr::Op(*op, args).simplify_constants();
                let ChcExpr::Op(op, args) = &expr else {
                    return expr;
                };

                match op {
                    ChcOp::BvAdd if args.len() == 2 => {
                        if Self::is_bv_zero(args[0].as_ref()) {
                            return args[1].as_ref().clone();
                        }
                        if Self::is_bv_zero(args[1].as_ref()) {
                            return args[0].as_ref().clone();
                        }
                    }
                    ChcOp::BvSub if args.len() == 2 => {
                        if Self::is_bv_zero(args[1].as_ref()) {
                            return args[0].as_ref().clone();
                        }
                        if args[0] == args[1] {
                            if let Some(width) = Self::bv_width(args[0].as_ref()) {
                                return ChcExpr::BitVec(0, width);
                            }
                        }
                        if let Some(stripped) =
                            Self::strip_matching_bv_add_const(args[0].as_ref(), args[1].as_ref())
                        {
                            return stripped;
                        }
                    }
                    ChcOp::BvMul if args.len() == 2 => {
                        if Self::is_bv_zero(args[0].as_ref()) {
                            return args[0].as_ref().clone();
                        }
                        if Self::is_bv_zero(args[1].as_ref()) {
                            if let Some(width) = Self::bv_width(args[0].as_ref()) {
                                return ChcExpr::BitVec(0, width);
                            }
                        }
                        if Self::is_bv_one(args[0].as_ref()) {
                            return args[1].as_ref().clone();
                        }
                        if Self::is_bv_one(args[1].as_ref()) {
                            return args[0].as_ref().clone();
                        }
                    }
                    ChcOp::BvUDiv | ChcOp::BvSDiv
                        if args.len() == 2 && Self::is_bv_one(args[1].as_ref()) =>
                    {
                        return args[0].as_ref().clone();
                    }
                    ChcOp::BvExtract(hi, lo) if args.len() == 1 => {
                        if let Some(extracted) =
                            Self::extract_from_bv_concat(args[0].as_ref(), *hi, *lo)
                        {
                            return extracted;
                        }
                    }
                    _ => {}
                }

                ChcExpr::Op(*op, args.clone())
            }
            ChcExpr::PredicateApp(name, pred, args) => ChcExpr::PredicateApp(
                name.clone(),
                *pred,
                args.iter()
                    .map(|arg| Arc::new(Self::simplify_bv_identities(arg.as_ref().clone())))
                    .collect(),
            ),
            ChcExpr::FuncApp(name, sort, args) => ChcExpr::FuncApp(
                name.clone(),
                sort.clone(),
                args.iter()
                    .map(|arg| Arc::new(Self::simplify_bv_identities(arg.as_ref().clone())))
                    .collect(),
            ),
            ChcExpr::ConstArray(key_sort, value) => ChcExpr::ConstArray(
                key_sort.clone(),
                Arc::new(Self::simplify_bv_identities(value.as_ref().clone())),
            ),
            other => other.clone(),
        }
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
        let high_width = Self::bv_width(high)?;
        let low_width = Self::bv_width(low)?;
        let total_width = high_width.checked_add(low_width)?;
        if hi >= total_width {
            return None;
        }

        if hi < low_width {
            return Some(Self::extract_or_identity(low.clone(), hi, lo));
        }
        if lo >= low_width {
            return Some(Self::extract_or_identity(
                high.clone(),
                hi - low_width,
                lo - low_width,
            ));
        }
        None
    }

    fn extract_or_identity(expr: ChcExpr, hi: u32, lo: u32) -> ChcExpr {
        if let Some(width) = Self::bv_width(&expr) {
            if lo == 0 && hi + 1 == width {
                return expr;
            }
        }
        Self::simplify_bv_identities(ChcExpr::Op(ChcOp::BvExtract(hi, lo), vec![Arc::new(expr)]))
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

    pub(super) fn simplify_dt_selector_apps(expr: ChcExpr) -> ChcExpr {
        match &expr {
            ChcExpr::Op(op, args) => ChcExpr::Op(
                *op,
                args.iter()
                    .map(|arg| Arc::new(Self::simplify_dt_selector_apps(arg.as_ref().clone())))
                    .collect(),
            ),
            ChcExpr::PredicateApp(name, pred, args) => ChcExpr::PredicateApp(
                name.clone(),
                *pred,
                args.iter()
                    .map(|arg| Arc::new(Self::simplify_dt_selector_apps(arg.as_ref().clone())))
                    .collect(),
            ),
            ChcExpr::FuncApp(name, sort, args) => {
                let simplified_args: Vec<_> = args
                    .iter()
                    .map(|arg| Arc::new(Self::simplify_dt_selector_apps(arg.as_ref().clone())))
                    .collect();
                if simplified_args.len() == 1 {
                    if let ChcExpr::FuncApp(
                        ctor_name,
                        ChcSort::Datatype { constructors, .. },
                        ctor_args,
                    ) = simplified_args[0].as_ref()
                    {
                        for ctor in constructors.iter() {
                            if ctor.name != *ctor_name {
                                continue;
                            }
                            for (selector_idx, selector) in ctor.selectors.iter().enumerate() {
                                if selector.name == *name {
                                    if let Some(value) = ctor_args.get(selector_idx) {
                                        return value.as_ref().clone();
                                    }
                                }
                            }
                        }
                    }
                }
                ChcExpr::FuncApp(name.clone(), sort.clone(), simplified_args)
            }
            ChcExpr::ConstArray(key_sort, value) => ChcExpr::ConstArray(
                key_sort.clone(),
                Arc::new(Self::simplify_dt_selector_apps(value.as_ref().clone())),
            ),
            other => other.clone(),
        }
    }
}
