// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Disequality->strict literal-swap repair for discovered safety lemmas.
//!
//! A safety lemma whose disjuncts include a disequality `a != b` (= `a < b OR
//! a > b`) is frequently too weak to be self-inductive even when one of the two
//! strict halves is exactly the missing inductive invariant. Example (mult):
//! `(x2 != x1) OR (x1 <= x0)` is entry-inductive but not self-inductive, while
//! `(x1 > x2) OR (x1 <= x0)` is z3-spacer's complete inductive proof. This
//! module produces the strict refinements; callers re-validate every candidate
//! through the UNCHANGED admission / self-inductiveness oracle (which rejects on
//! SMT Unknown), so the repair can only admit a genuinely inductive lemma.

use crate::{ChcExpr, ChcOp};

/// `AY_CHC_DISEQ_SWAP` kill-switch (default ON; only the literal "0" disables).
pub(in crate::pdr::solver) fn diseq_swap_enabled() -> bool {
    // B15: typed A/B switch (`ab_switches`); the never-set env read is gone.
    crate::ab_switches::get().diseq_swap
}

/// Strict refinements of any disequality disjunct in `formula`.
///
/// Decomposes the lemma into OR-normal disjuncts — handling both the explicit
/// `Or(..)` form and the negated-error `Not(And(..))` form via De Morgan
/// (`ChcExpr::not` already eliminates double negation) — and, for each
/// disequality disjunct (`Ne(a,b)` or `Not(Eq(a,b))`), emits the two strict
/// variants (`a < b` and `a > b`). Pure and bounded (<= 4 disequality disjuncts
/// x 2 candidates). Returns empty when `formula` is not an OR-shaped lemma or
/// has no disequality disjunct (so re-running it on a produced strict candidate
/// yields nothing — callers cannot recurse indefinitely).
pub(in crate::pdr::solver) fn strict_disequality_repairs(formula: &ChcExpr) -> Vec<ChcExpr> {
    let disjuncts: Vec<ChcExpr> = match formula {
        ChcExpr::Op(ChcOp::Or, args) => args.iter().map(|a| (**a).clone()).collect(),
        ChcExpr::Op(ChcOp::Not, nargs) if nargs.len() == 1 => match &*nargs[0] {
            ChcExpr::Op(ChcOp::And, cargs) => {
                cargs.iter().map(|c| ChcExpr::not((**c).clone())).collect()
            }
            _ => return Vec::new(),
        },
        _ => return Vec::new(),
    };
    if disjuncts.len() < 2 {
        return Vec::new();
    }

    fn as_diseq(d: &ChcExpr) -> Option<(ChcExpr, ChcExpr)> {
        match d {
            ChcExpr::Op(ChcOp::Ne, a) if a.len() == 2 => Some(((*a[0]).clone(), (*a[1]).clone())),
            ChcExpr::Op(ChcOp::Not, a) if a.len() == 1 => {
                if let ChcExpr::Op(ChcOp::Eq, e) = &*a[0] {
                    if e.len() == 2 {
                        return Some(((*e[0]).clone(), (*e[1]).clone()));
                    }
                }
                None
            }
            _ => None,
        }
    }

    let mut out = Vec::new();
    let mut diseq_count = 0;
    for (i, d) in disjuncts.iter().enumerate() {
        if let Some((a, b)) = as_diseq(d) {
            diseq_count += 1;
            if diseq_count > 4 {
                break;
            }
            for strict in [
                ChcExpr::lt(a.clone(), b.clone()),
                ChcExpr::gt(a.clone(), b.clone()),
            ] {
                let mut nd = disjuncts.clone();
                nd[i] = strict;
                out.push(ChcExpr::or_all(nd));
            }
        }
    }
    out
}
