// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Root POBs of the nonlinear Spacer lane without the query's local variables.
//!
//! A root POB is the query constraint on the query predicate's canonical
//! variables; the query clause's other variables stay in it as existentials
//! (`__query{i}_B`). A lemma derived from such a POB mentions them free, and
//! a frame lemma with a free variable reads existentially in every later
//! query and model check: the fixed point it builds fails the query clause
//! (`hopv/mc91_99`: `B ≠ 0 ∧ ((B = 0) ≠ (n ≤ 99))`, `D = 0 ∧ …`). Spacer's
//! roots are MBP-projected onto the predicate; here the EXACT cases are
//! eliminated before the root is queued:
//!
//! * `v = t` with `v` local and not in `t`: `∃v. v = t ∧ φ(v) ≡ φ(t)`;
//! * a conjunct `A` / `¬A` whose variables are all local fixes the atom `A`
//!   in every other conjunct (`A ∧ φ(A) ≡ A ∧ φ(true)`);
//! * what is left over locals only is a closed side condition: dropped when
//!   satisfiable, the root is `false` when not (`∃L. ψ(L) ∧ φ(x) ≡ (∃L. ψ) ∧ φ`).
//!
//! When a local survives in a conjunct with canonical variables the
//! (equivalent) simplified state is kept as it is.

use super::super::*;
use crate::ChcVar;
use ay_core::kani_compat::DetHashSet as FxHashSet;

/// `expr` with every occurrence of `target` replaced by `by`.
fn replace_subterm(expr: &ChcExpr, target: &ChcExpr, by: &ChcExpr) -> ChcExpr {
    crate::expr::maybe_grow_expr_stack(|| {
        if expr == target {
            return by.clone();
        }
        match expr {
            ChcExpr::Op(op, args) => ChcExpr::Op(
                op.clone(),
                args.iter()
                    .map(|a| std::sync::Arc::new(replace_subterm(a, target, by)))
                    .collect(),
            ),
            other => other.clone(),
        }
    })
}

/// The flattened, constant-simplified conjuncts of `exprs` (`None`: `false`).
fn normalize(exprs: Vec<ChcExpr>) -> Option<Vec<ChcExpr>> {
    let mut out = Vec::with_capacity(exprs.len());
    for e in exprs {
        for c in e.simplify_constants().collect_conjuncts() {
            match c {
                ChcExpr::Bool(true) => {}
                ChcExpr::Bool(false) => return None,
                c => out.push(c),
            }
        }
    }
    Some(out)
}

/// A local `v = t` conjunct with `v ∉ vars(t)`: `(v, t)`.
fn local_definition(c: &ChcExpr, is_local: &dyn Fn(&ChcVar) -> bool) -> Option<(ChcVar, ChcExpr)> {
    let ChcExpr::Op(ChcOp::Eq, args) = c else {
        return None;
    };
    if args.len() != 2 {
        return None;
    }
    for (lhs, rhs) in [(&args[0], &args[1]), (&args[1], &args[0])] {
        if let ChcExpr::Var(v) = lhs.as_ref() {
            if is_local(v) && !rhs.vars().iter().any(|w| w.name == v.name) {
                return Some((v.clone(), rhs.as_ref().clone()));
            }
        }
    }
    None
}

/// Rules 1 and 2 of the module docs on the conjuncts `conj` (no solver
/// call): the result is equivalent to `∃locals` of the input exactly when the
/// eliminated locals are gone, and equivalent to the input otherwise. `None`:
/// the conjunction is `false`.
pub(super) fn eliminate_locals(
    conj: Vec<ChcExpr>,
    is_local: &dyn Fn(&ChcVar) -> bool,
) -> Option<Vec<ChcExpr>> {
    let only_locals = |c: &ChcExpr| c.vars().iter().all(|v| is_local(v));
    let mut conj = normalize(conj)?;
    for _ in 0..16 {
        let mut changed = false;
        if let Some((i, (v, t))) = conj
            .iter()
            .enumerate()
            .find_map(|(i, c)| local_definition(c, is_local).map(|d| (i, d)))
        {
            conj.remove(i);
            let subst = [(v, t)];
            conj = conj.iter().map(|c| c.substitute(&subst)).collect();
            changed = true;
        } else if let Some((i, atom, value)) = conj.iter().enumerate().find_map(|(i, c)| {
            if !only_locals(c) || matches!(c, ChcExpr::Op(ChcOp::And, _)) {
                return None;
            }
            let (atom, value) = match c {
                ChcExpr::Op(ChcOp::Not, a) if a.len() == 1 => (a[0].as_ref().clone(), false),
                c => (c.clone(), true),
            };
            let used = conj
                .iter()
                .enumerate()
                .any(|(j, d)| j != i && replace_subterm(d, &atom, &ChcExpr::Bool(value)) != *d);
            used.then_some((i, atom, value))
        }) {
            let by = ChcExpr::Bool(value);
            conj = conj
                .iter()
                .enumerate()
                .map(|(j, d)| {
                    if j == i {
                        d.clone()
                    } else {
                        replace_subterm(d, &atom, &by)
                    }
                })
                .collect();
            changed = true;
        }
        if !changed {
            break;
        }
        conj = normalize(conj)?;
    }
    Some(conj)
}

impl PdrSolver {
    /// The root POB state of `pred` with the query's local variables
    /// eliminated where that is exact (module docs).
    pub(in crate::pdr::solver) fn nl_root_state(
        &mut self,
        pred: PredicateId,
        state: ChcExpr,
    ) -> ChcExpr {
        let Some(canon) = self.canonical_vars(pred) else {
            return state;
        };
        let canon: FxHashSet<String> = canon.iter().map(|v| v.name.clone()).collect();
        let is_local = |v: &ChcVar| !canon.contains(&v.name);
        let only_locals = |c: &ChcExpr| c.vars().iter().all(|v| is_local(v));
        let Some(conj) = eliminate_locals(vec![state], &is_local) else {
            return ChcExpr::Bool(false);
        };
        let (side, rest): (Vec<ChcExpr>, Vec<ChcExpr>) =
            conj.into_iter().partition(|c| only_locals(c));
        if rest.iter().any(|c| c.vars().iter().any(|v| is_local(v))) || side.is_empty() {
            return ChcExpr::and_all(side.into_iter().chain(rest));
        }
        // A closed side condition over locals only.
        let side_query = self.bound_int_vars(ChcExpr::and_all(side.clone()));
        self.smt.reset();
        match self.smt.check_sat(&side_query) {
            SmtResult::Sat(_) => ChcExpr::and_all(rest),
            SmtResult::Unsat | SmtResult::UnsatWithCore(_) | SmtResult::UnsatWithFarkas(_) => {
                ChcExpr::Bool(false)
            }
            SmtResult::Unknown => ChcExpr::and_all(side.into_iter().chain(rest)),
        }
    }
}
