// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Expression sort computation.

use std::sync::Arc;

use crate::expr::{maybe_grow_expr_stack, ChcExpr, ChcOp, ChcSort};

impl ChcExpr {
    /// Get the sort of this expression.
    pub fn sort(&self) -> ChcSort {
        // Intentionally no depth bail-out: callers require exact sort results.
        // `maybe_grow_expr_stack` bounds stack usage for deep trees.
        maybe_grow_expr_stack(|| match self {
            Self::Bool(_) => ChcSort::Bool,
            Self::Int(_) => ChcSort::Int,
            Self::Real(_, _) => ChcSort::Real,
            Self::BitVec(_, width) => ChcSort::BitVec(*width),
            Self::Var(v) => v.sort.clone(),
            Self::PredicateApp(_, _, _) => ChcSort::Bool,
            Self::FuncApp(_, sort, _) => sort.clone(),
            Self::Op(op, args) => Self::op_sort(op, args),
            Self::ConstArrayMarker(_) | Self::IsTesterMarker(_) => ChcSort::Bool,
            Self::ConstArray(key_sort, val) => {
                ChcSort::Array(Box::new(key_sort.clone()), Box::new(val.sort()))
            }
        })
    }

    fn op_sort(op: &ChcOp, args: &[Arc<Self>]) -> ChcSort {
        match op {
            ChcOp::Not | ChcOp::And | ChcOp::Or | ChcOp::Implies | ChcOp::Iff => ChcSort::Bool,
            ChcOp::Eq | ChcOp::Ne | ChcOp::Lt | ChcOp::Le | ChcOp::Gt | ChcOp::Ge => ChcSort::Bool,
            ChcOp::Add | ChcOp::Sub | ChcOp::Mul | ChcOp::Div | ChcOp::Mod | ChcOp::Neg => {
                Self::first_arg_sort(args)
            }
            ChcOp::Ite => Self::ite_sort(args),
            ChcOp::Select => Self::select_sort(args),
            ChcOp::Store => Self::first_arg_sort(args),
            ChcOp::BvULt
            | ChcOp::BvULe
            | ChcOp::BvUGt
            | ChcOp::BvUGe
            | ChcOp::BvSLt
            | ChcOp::BvSLe
            | ChcOp::BvSGt
            | ChcOp::BvSGe => ChcSort::Bool,
            ChcOp::BvComp => ChcSort::BitVec(1),
            ChcOp::Bv2Nat => ChcSort::Int,
            ChcOp::BvAdd
            | ChcOp::BvSub
            | ChcOp::BvMul
            | ChcOp::BvUDiv
            | ChcOp::BvURem
            | ChcOp::BvSDiv
            | ChcOp::BvSRem
            | ChcOp::BvSMod
            | ChcOp::BvAnd
            | ChcOp::BvOr
            | ChcOp::BvXor
            | ChcOp::BvNand
            | ChcOp::BvNor
            | ChcOp::BvXnor
            | ChcOp::BvNot
            | ChcOp::BvNeg
            | ChcOp::BvShl
            | ChcOp::BvLShr
            | ChcOp::BvAShr => Self::bv_value_sort(args),
            ChcOp::BvConcat => Self::bv_concat_sort(args),
            ChcOp::BvExtract(hi, lo) => {
                if hi >= lo {
                    ChcSort::BitVec(
                        hi.checked_sub(*lo)
                            .and_then(|width| width.checked_add(1))
                            .unwrap_or(u32::MAX),
                    )
                } else {
                    ChcSort::BitVec(1)
                }
            }
            ChcOp::BvZeroExtend(n) | ChcOp::BvSignExtend(n) => Self::bv_extend_sort(args, *n),
            ChcOp::BvRotateLeft(_) | ChcOp::BvRotateRight(_) => Self::bv_rotate_sort(args),
            ChcOp::BvRepeat(n) => Self::bv_repeat_sort(args, *n),
            ChcOp::Int2Bv(width) => ChcSort::BitVec(*width),
        }
    }

    fn first_arg_sort(args: &[Arc<Self>]) -> ChcSort {
        args.first().map_or(ChcSort::Int, |arg| arg.sort())
    }

    fn ite_sort(args: &[Arc<Self>]) -> ChcSort {
        // Follow the then-branch iteratively to avoid stack overflow on deep ITE chains.
        let mut current = args.get(1).map(AsRef::as_ref);
        loop {
            match current {
                Some(Self::Op(ChcOp::Ite, inner_args)) => {
                    current = inner_args.get(1).map(AsRef::as_ref);
                }
                Some(other) => return other.sort(),
                None => return ChcSort::Bool,
            }
        }
    }

    fn select_sort(args: &[Arc<Self>]) -> ChcSort {
        if let Some(array) = args.first() {
            if let ChcSort::Array(_, value_sort) = array.sort() {
                return (*value_sort).clone();
            }
        }
        ChcSort::Int
    }

    fn bv_value_sort(args: &[Arc<Self>]) -> ChcSort {
        debug_assert!(
            !args.is_empty(),
            "BUG: BV arithmetic/bitwise/shift op has no arguments"
        );
        Self::first_arg_sort(args)
    }

    fn bv_concat_sort(args: &[Arc<Self>]) -> ChcSort {
        if let (Some(a), Some(b)) = (args.first(), args.get(1)) {
            if let (ChcSort::BitVec(w1), ChcSort::BitVec(w2)) = (a.sort(), b.sort()) {
                return ChcSort::BitVec(w1.checked_add(w2).unwrap_or(u32::MAX));
            }
        }
        debug_assert!(
            false,
            "BUG: BvConcat has malformed args (expected 2 BitVec args)"
        );
        Self::first_arg_sort(args)
    }

    fn bv_extend_sort(args: &[Arc<Self>], extension: u32) -> ChcSort {
        if let Some(arg) = args.first() {
            if let ChcSort::BitVec(width) = arg.sort() {
                return ChcSort::BitVec(width.checked_add(extension).unwrap_or(u32::MAX));
            }
        }
        debug_assert!(
            false,
            "BUG: BvZeroExtend/BvSignExtend has malformed args (expected BitVec arg)"
        );
        Self::first_arg_sort(args)
    }

    fn bv_rotate_sort(args: &[Arc<Self>]) -> ChcSort {
        debug_assert!(!args.is_empty(), "BUG: BvRotate op has no arguments");
        Self::first_arg_sort(args)
    }

    fn bv_repeat_sort(args: &[Arc<Self>], repetitions: u32) -> ChcSort {
        if let Some(arg) = args.first() {
            if let ChcSort::BitVec(width) = arg.sort() {
                return ChcSort::BitVec(width.checked_mul(repetitions).unwrap_or(u32::MAX));
            }
        }
        debug_assert!(
            false,
            "BUG: BvRepeat has malformed args (expected BitVec arg)"
        );
        Self::first_arg_sort(args)
    }
}
