// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Equality solving across an interpolation cut (`A | B`, shared `S`).
//!
//! An IMC query `A = init(x0) ∧ T(x0,x1)`, `B = T(x1,x2) ∧ … ∧ bad(xk)` over
//! a sally / cav12 transition system is easy once equalities are solved
//! (`smt::solve_eqs`): the init constants select one disjunct of `T@0`, whose
//! frame equalities pin most of `x1`, which in turn selects one disjunct of
//! `T@1`, and so on. A proof-producing solve cannot substitute across the
//! cut, so it searches the disjunctions of `B` blind (om1_with_relays k = 3:
//! the proof solve exceeds its 5 s budget where the plain check takes 0.6 s).
//!
//! [`simplify_partition`] makes the cut explicit instead:
//!
//! 1. `A'` = `A` with its equalities solved, shared variables substituted but
//!    kept (`solve_eqs` with `S` protected), so `A ≡ ∃X_A. A'`.
//! 2. `U` = the conjuncts of `A'` that are equalities (or Bool literals) over
//!    `S` only — consequences of `A` over the shared vocabulary.
//! 3. `B'` = `B ∧ U` with its equalities solved (`S` protected), so
//!    `B ∧ U ≡ ∃X_B. B'`.
//!
//! If `I'` interpolates `(A', B')` then `I = I' ∧ U` interpolates `(A, B)`:
//! `A ⊨ A' ⊨ I'` and `A ⊨ U`; `I ∧ B = I' ∧ U ∧ B ⊨ I' ∧ B'`, which is
//! UNSAT; `vars(I) ⊆ S`. If `B'` is already `false`, `I = U`.
//!
//! The interpolant is stronger than one of `(A, B)` would be (it keeps the
//! exact shared constants `A` forces), which is the price of never searching
//! across the cut. The consumers re-validate everything they conclude from it
//! (IMC's Safe is re-checked on the Verification lane on the original clauses).

use std::sync::Arc;

use ay_core::kani_compat::DetHashSet as FxHashSet;

use crate::smt::solve_eqs::solve_eqs;
use crate::{ChcExpr, ChcOp, ChcSort};

/// The simplified partition.
#[derive(Debug, Clone)]
pub(crate) enum Transfer {
    /// `B ∧ U` is already refuted: `and(units)` interpolates `(A, B)`.
    Units(Vec<ChcExpr>),
    /// Interpolate `(a, b)` and conjoin `units` to the result.
    Split {
        a: Vec<ChcExpr>,
        b: Vec<ChcExpr>,
        units: Vec<ChcExpr>,
    },
}

/// Solve equalities on both sides of the cut and move `A`'s shared
/// equalities into `B`. `None` when neither side changes, or when `A` alone
/// is refuted (the caller then runs its unsimplified path).
///
/// `facts`: move every conjunct of `A'` over shared variables only (the
/// constants, equalities AND relations `A` forces on the cut — IMC, whose
/// next image is then as precise as this one), instead of only its shared
/// equalities (the generalising engines).
pub(crate) fn simplify_partition(
    a: &[ChcExpr],
    b: &[ChcExpr],
    shared: &FxHashSet<String>,
    facts: bool,
) -> Option<Transfer> {
    let a_expr = conjoin(a);
    let a_solved = solve_eqs(&a_expr, shared);
    let a_residual = a_solved.map_or(a_expr, |s| s.residual);
    if matches!(a_residual, ChcExpr::Bool(false)) {
        return None;
    }
    let a_parts = a_residual.collect_conjuncts_nontrivial();
    let units: Vec<ChcExpr> = a_parts
        .iter()
        .filter(|c| {
            if facts {
                c.vars().iter().all(|v| shared.contains(&v.name))
            } else {
                is_shared_unit(c, shared)
            }
        })
        .cloned()
        .collect();
    let b_expr = conjoin(&[b, units.as_slice()].concat());
    let b_solved = solve_eqs(&b_expr, shared);
    let changed = !units.is_empty() || b_solved.is_some();
    let b_residual = b_solved.map_or(b_expr, |s| s.residual);
    if matches!(b_residual, ChcExpr::Bool(false)) {
        return (!units.is_empty()).then_some(Transfer::Units(units));
    }
    if !changed && a_parts.len() == a.len() {
        return None;
    }
    Some(Transfer::Split {
        a: a_parts,
        b: b_residual.collect_conjuncts_nontrivial(),
        units,
    })
}

/// An equality between a shared variable and a constant or another shared
/// variable, or a shared Bool literal.
fn is_shared_unit(c: &ChcExpr, shared: &FxHashSet<String>) -> bool {
    let shared_var = |e: &ChcExpr| matches!(e, ChcExpr::Var(v) if shared.contains(&v.name));
    let constant =
        |e: &ChcExpr| matches!(e, ChcExpr::Int(_) | ChcExpr::Real(..) | ChcExpr::Bool(_));
    match c {
        ChcExpr::Var(_) => is_shared_bool(c, shared),
        ChcExpr::Op(ChcOp::Not, args) if args.len() == 1 => is_shared_bool(&args[0], shared),
        ChcExpr::Op(ChcOp::Eq | ChcOp::Iff, args) if args.len() == 2 => {
            let (l, r) = (args[0].as_ref(), args[1].as_ref());
            (shared_var(l) && (constant(r) || shared_var(r))) || (shared_var(r) && constant(l))
        }
        _ => false,
    }
}

fn is_shared_bool(e: &ChcExpr, shared: &FxHashSet<String>) -> bool {
    match e {
        ChcExpr::Var(v) => v.sort == ChcSort::Bool && shared.contains(&v.name),
        _ => false,
    }
}

/// `and(parts)` without the constructor's deduplicating walk.
pub(crate) fn conjoin(parts: &[ChcExpr]) -> ChcExpr {
    match parts.len() {
        0 => ChcExpr::Bool(true),
        1 => parts[0].clone(),
        _ => ChcExpr::Op(ChcOp::And, parts.iter().cloned().map(Arc::new).collect()),
    }
}

#[cfg(test)]
#[path = "unit_transfer_tests.rs"]
mod tests;
