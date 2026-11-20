// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! `LitCube` — a cube over one predicate's canonical variables as a literal
//! vector plus its cached conjunction (the development design notes at `9598c4206`
//! §3.1, contract C1).
//!
//! Owner: **WP-B1-L** (lemma core). Declared in the skeleton commit with the
//! frozen API; P and S consume it (`ProofObligation::cube`,
//! `PredecessorState.lits`, telemetry). `state: ChcExpr` stays the source of
//! truth for every existing reader; a `LitCube` is a literal-indexed VIEW of
//! the same conjunction (`expr() == ChcExpr::and_all(lits)`).

#![allow(dead_code, unused)]

use crate::{ChcExpr, ChcOp, ChcVar};

/// A cube over one predicate's canonical variables as a literal vector plus its cached `and_all`.
///
/// Invariants: no `Bool(true)` literal, no structural duplicate, literal
/// order preserved from construction (the implicant walk / the POB state's
/// top-level conjunct order); `expr == ChcExpr::and_all(lits)`; the empty cube
/// is `true`.
#[derive(Debug, Clone)]
pub(crate) struct LitCube {
    lits: Vec<ChcExpr>,
    expr: ChcExpr,
}

impl LitCube {
    /// Build from literals; order preserved, `Bool(true)` and structural duplicates dropped.
    pub(crate) fn from_lits(lits: Vec<ChcExpr>) -> Self {
        let mut out: Vec<ChcExpr> = Vec::with_capacity(lits.len());
        for lit in lits {
            if matches!(lit, ChcExpr::Bool(true)) {
                continue;
            }
            if out.iter().any(|l| *l == lit) {
                continue;
            }
            out.push(lit);
        }
        let expr = ChcExpr::and_all(out.iter().cloned());
        Self { lits: out, expr }
    }

    /// Build from a state formula: `collect_conjuncts_nontrivial()` (`expr/methods/conjuncts.rs:107`).
    pub(crate) fn from_expr(state: &ChcExpr) -> Self {
        Self::from_lits(state.collect_conjuncts_nontrivial())
    }

    /// The literals, in cube order.
    pub(crate) fn lits(&self) -> &[ChcExpr] {
        &self.lits
    }

    /// `== ChcExpr::and_all(lits)`.
    pub(crate) fn expr(&self) -> &ChcExpr {
        &self.expr
    }

    /// Number of literals.
    pub(crate) fn len(&self) -> usize {
        self.lits.len()
    }

    /// Empty == cube `true`.
    pub(crate) fn is_empty(&self) -> bool {
        self.lits.is_empty()
    }

    /// Sub-cube keeping literal `i` iff `keep[i]`. `keep.len() == len()`.
    pub(crate) fn subset(&self, keep: &[bool]) -> LitCube {
        debug_assert_eq!(
            keep.len(),
            self.lits.len(),
            "BUG: LitCube::subset mask length"
        );
        let lits = self
            .lits
            .iter()
            .zip(keep.iter())
            .filter(|(_, k)| **k)
            .map(|(l, _)| l.clone())
            .collect();
        Self::from_lits(lits)
    }

    /// Sub-cube without literal `idx`.
    pub(crate) fn without(&self, idx: usize) -> LitCube {
        let lits = self
            .lits
            .iter()
            .enumerate()
            .filter(|(i, _)| *i != idx)
            .map(|(_, l)| l.clone())
            .collect();
        Self::from_lits(lits)
    }

    /// Invariant form of the lemma = `Not(expr)`; keeps the `Not(cube)` shape that
    /// `strengthen.rs` (point-block detection) and `push_lemmas.rs` read.
    ///
    /// The empty cube (`true`) yields the explicit `Bool(false)` lemma so the
    /// readers that special-case `false` by name (`frame_hyp` keeps it, model
    /// extraction filters it, `DESIGN` §7.5) see it as such rather than as
    /// `Not(Bool(true))`.
    pub(crate) fn lemma_formula(&self) -> ChcExpr {
        if self.lits.is_empty() {
            return ChcExpr::Bool(false);
        }
        ChcExpr::not(self.expr.clone())
    }

    /// Telemetry: every canonical variable is grounded to a constant
    /// (`pdr/cube/equality.rs::is_point_cube_for_vars`).
    pub(crate) fn is_point_cube(&self, canon: &[ChcVar]) -> bool {
        if canon.is_empty() {
            return false;
        }
        super::is_point_cube_for_vars(&self.expr, canon)
    }

    /// Literals of shape `canon = const` (either side), plus Boolean pins `v` / `¬v`.
    pub(crate) fn pin_count(&self) -> usize {
        self.lits.iter().filter(|l| is_pin_literal(l)).count()
    }

    /// Number of canonical variables mentioned by at least one literal (for `free_var_ratio`).
    pub(crate) fn mentioned_canon(&self, canon: &[ChcVar]) -> usize {
        if canon.is_empty() {
            return 0;
        }
        let mentioned: std::collections::HashSet<String> = self
            .lits
            .iter()
            .flat_map(|l| l.vars())
            .map(|v| v.name)
            .collect();
        canon.iter().filter(|v| mentioned.contains(&v.name)).count()
    }

    /// Structural hash of the conjunction.
    pub(crate) fn structural_hash(&self) -> u64 {
        self.expr.structural_hash()
    }

    /// Telemetry: literals that are disequalities (`Not(Eq ..)` / `Ne`).
    pub(crate) fn diseq_count(&self) -> usize {
        self.lits
            .iter()
            .filter(|l| match l {
                ChcExpr::Op(ChcOp::Not, args) => {
                    args.len() == 1 && matches!(&*args[0], ChcExpr::Op(ChcOp::Eq, _))
                }
                ChcExpr::Op(ChcOp::Ne, _) => true,
                _ => false,
            })
            .count()
    }
}

fn is_const(e: &ChcExpr) -> bool {
    matches!(
        e,
        ChcExpr::Int(_) | ChcExpr::Real(_, _) | ChcExpr::Bool(_) | ChcExpr::BitVec(_, _)
    )
}

/// `v = c`, `c = v`, `v`, `¬v`.
fn is_pin_literal(l: &ChcExpr) -> bool {
    match l {
        ChcExpr::Var(_) => true,
        ChcExpr::Op(ChcOp::Not, args) => args.len() == 1 && matches!(&*args[0], ChcExpr::Var(_)),
        ChcExpr::Op(ChcOp::Eq, args) => {
            args.len() == 2
                && ((matches!(&*args[0], ChcExpr::Var(_)) && is_const(&args[1]))
                    || (matches!(&*args[1], ChcExpr::Var(_)) && is_const(&args[0])))
        }
        _ => false,
    }
}
