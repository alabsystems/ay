// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// PDR solver tests - extracted from solver.rs
// Author: Andrew Yates

use super::{cube, ChcExpr, ChcOp, ChcParser, ChcSort, ChcVar, Lemma, PdrConfig, PdrSolver};
use crate::lemma_hints::{HintStage, LemmaHint};
use crate::smt::{SmtContext, SmtResult, SmtValue};
use ay_core::kani_compat::DetHashMap as FxHashMap;

mod chain_safety;
mod construction;
mod contradiction_hints;
mod entry_and_cube;
mod propagation;

fn contains_or(expr: &ChcExpr) -> bool {
    match expr {
        ChcExpr::Op(ChcOp::Or, _) => true,
        ChcExpr::Op(_, args) => args.iter().any(|a| contains_or(a.as_ref())),
        ChcExpr::PredicateApp(_, _, args) => args.iter().any(|a| contains_or(a.as_ref())),
        _ => false,
    }
}

fn make_exponential_conjunction(var: &ChcVar, depth: usize) -> ChcExpr {
    let mut expr = ChcExpr::gt(ChcExpr::var(var.clone()), ChcExpr::int(0));
    for _ in 0..depth {
        expr = ChcExpr::and(expr.clone(), expr);
    }
    expr
}

fn make_exponential_unsafe_ite(var: &ChcVar, depth: usize) -> ChcExpr {
    let mut expr = ChcExpr::gt(ChcExpr::var(var.clone()), ChcExpr::int(0));
    for i in 0..depth {
        let cond = ChcExpr::ge(ChcExpr::var(var.clone()), ChcExpr::int(i as i64));
        expr = ChcExpr::ite(cond, expr.clone(), ChcExpr::not(expr));
    }
    expr
}

const SIMPLE_ENTRY_TIMEOUT_SMT2: &str = r#"
(set-logic HORN)

(declare-fun SRC ( Int ) Bool)
(declare-fun DST ( Int ) Bool)

(assert
  (forall ( (x Int) )
(=>
  (= x 0)
  (SRC x)
)
  )
)
(assert
  (forall ( (x Int) (y Int) )
(=>
  (and (SRC x) (= y 7))
  (DST y)
)
  )
)

(check-sat)
"#;
