// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Tests for lemma clustering (Global Guidance #716).

#![allow(clippy::unwrap_used)]

pub(crate) use super::*;

mod analysis;
mod cluster;
mod pattern;

pub(super) fn make_var(name: &str) -> ChcExpr {
    ChcExpr::Var(ChcVar::new(name, ChcSort::Int))
}

pub(super) fn make_gt(left: ChcExpr, right: ChcExpr) -> ChcExpr {
    ChcExpr::Op(ChcOp::Gt, vec![Arc::new(left), Arc::new(right)])
}

pub(super) fn make_and(a: ChcExpr, b: ChcExpr) -> ChcExpr {
    ChcExpr::Op(ChcOp::And, vec![Arc::new(a), Arc::new(b)])
}

pub(super) fn contains_int(expr: &ChcExpr, n: i128) -> bool {
    match expr {
        ChcExpr::Int(v) => *v == n,
        ChcExpr::Op(_, args) => args.iter().any(|a| contains_int(a.as_ref(), n)),
        ChcExpr::PredicateApp(_, _, args) => args.iter().any(|a| contains_int(a.as_ref(), n)),
        ChcExpr::FuncApp(_, _, args) => args.iter().any(|a| contains_int(a.as_ref(), n)),
        ChcExpr::ConstArray(_ks, v) => contains_int(v.as_ref(), n),
        _ => false,
    }
}
