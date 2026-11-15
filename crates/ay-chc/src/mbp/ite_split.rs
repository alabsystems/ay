// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Model-based splitting of arithmetic ITE terms (Workstream B R2,
//! `DESIGN_spacer_pob_lemma_pipeline.md` §4.1.4; Spacer `mbp_arith.cpp`
//! ite handling done syntactically).
//!
//! A literal `L[ite(c, a, b)]` whose ITE is arithmetic-sorted and whose guard
//! `c` the model decides is replaced by `L[a]` together with the implicant of
//! `c` (or `L[b]` with the implicant of `¬c`). The replacement implies the
//! original literal and the model satisfies it, so an implicant stays an
//! implicant; the eliminated variables inside the ITE become projectable.

use crate::{ChcExpr, ChcOp, ChcSort, SmtValue};
use ay_core::kani_compat::DetHashMap as FxHashMap;
use std::collections::VecDeque;
use std::sync::Arc;

use super::Mbp;

impl Mbp {
    /// Split the model-decided arithmetic ITEs of every literal for which
    /// `relevant` holds, to a fixed point bounded by `8 × |lits|` splits.
    /// `splits` counts the rewrites.
    pub(crate) fn split_term_ites(
        &self,
        lits: Vec<ChcExpr>,
        model: &FxHashMap<String, SmtValue>,
        relevant: &dyn Fn(&ChcExpr) -> bool,
        splits: &mut usize,
    ) -> Vec<ChcExpr> {
        let budget = 8 * lits.len().max(1);
        let mut work: VecDeque<ChcExpr> = lits.into();
        let mut out: Vec<ChcExpr> = Vec::with_capacity(work.len());
        let mut used = 0usize;
        while let Some(lit) = work.pop_front() {
            if used < budget && relevant(&lit) {
                if let Some((rewritten, guard)) = self.split_first_ite(&lit, model) {
                    used += 1;
                    *splits += 1;
                    work.push_back(rewritten.simplify_constants());
                    for g in self.get_implicant(&guard, model) {
                        work.push_back(g.to_expr());
                    }
                    continue;
                }
            }
            out.push(lit);
        }
        out
    }

    /// Replace the first (pre-order) arithmetic ITE whose guard the model
    /// decides; returns the rewritten expression and the guard literal taken.
    fn split_first_ite(
        &self,
        e: &ChcExpr,
        model: &FxHashMap<String, SmtValue>,
    ) -> Option<(ChcExpr, ChcExpr)> {
        crate::expr::maybe_grow_expr_stack(|| {
            let _g = crate::expr::ExprDepthGuard::check()?;
            let ChcExpr::Op(op, args) = e else {
                return None;
            };
            if *op == ChcOp::Ite && args.len() == 3 && e.sort() != ChcSort::Bool {
                match self.eval_bool(&args[0], model) {
                    Some(true) => {
                        return Some((args[1].as_ref().clone(), args[0].as_ref().clone()))
                    }
                    Some(false) => {
                        return Some((
                            args[2].as_ref().clone(),
                            ChcExpr::not(args[0].as_ref().clone()),
                        ))
                    }
                    None => {}
                }
            }
            for (i, a) in args.iter().enumerate() {
                if let Some((na, guard)) = self.split_first_ite(a, model) {
                    let mut new_args = args.clone();
                    new_args[i] = Arc::new(na);
                    return Some((ChcExpr::Op(*op, new_args), guard));
                }
            }
            None
        })
    }
}
