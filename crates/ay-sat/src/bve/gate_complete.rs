// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! When gate-restricted elimination is sound, proved per candidate.
//!
//! Gate-restricted elimination of `x` (Eén and Biere, SAT 2005) resolves only
//! gate × non-gate pairs (plus gate × gate pairs for a semantic definition)
//! and pushes only the gate clauses on the reconstruction stack. Write the gate
//! clauses as `x ∨ E_j` and `¬x ∨ D_i`. The step is sound when
//!
//! 1. every gate × gate pair is resolved or its resolvent is satisfied in every
//!    model (a clashing literal, or a root-true one), and
//! 2. the gate *completely* defines `x`: the `E_j` and `D_i` together are
//!    unsatisfiable, so every assignment falsifies some `E_j` (forcing `x`
//!    true) or some `D_i` (forcing `x` false).
//!
//! Given a model of the simplified formula, reconstruction sets `x` by the
//! gate clauses. If `E_j` is false, (1) makes every `D_i` true, and every
//! non-gate clause `¬x ∨ F` has its resolvent `E_j ∨ F`, so `F` is true: all
//! clauses of `x` hold with `x` true, and symmetrically for a false `D_i`. (2)
//! excludes the third case, where no gate clause is falsified, `x` keeps an
//! arbitrary value, and a deleted non-gate clause can be left false; an
//! incomplete gate also loses the non-gate × non-gate resolvents the formula
//! needs. That lost constraint made AY answer SAT on the UNSAT braun-9/13 and
//! barrel6 in June 2026. Both conditions are checked here, not assumed from
//! the extractor. Condition 2 is decided by a small DPLL search over the gate
//! clauses under a node budget; out of budget counts as not proved. Root
//! assignments hold in every model reconstruction starts from (BVE never
//! eliminates an assigned variable, and reconstruction only flips eliminated
//! ones), so a root-satisfied gate clause is dropped and a root-false literal
//! is removed: an AND gate read through a root-false literal is complete.

use crate::clause_arena::ClauseArena;
use crate::literal::{Literal, Variable};

/// Gate clauses beyond this are not checked (the restriction is not used).
const GATE_CHECK_MAX_CLAUSES: usize = 256;
/// DPLL nodes one completeness check may visit.
const GATE_CHECK_NODE_BUDGET: u32 = 4_096;

/// Outcome of the soundness check of one gate.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum GateVerdict {
    /// Both conditions hold (or condition 2 is not needed): restrict.
    Sound,
    /// Not a gate shape: empty, too many clauses, a dead clause, a clause
    /// without the pivot or with both polarities, or one side empty.
    Shape,
    /// Condition 1 fails: an unresolved gate pair is not tautological.
    Pairs,
    /// Condition 2 fails: the gate clauses without the pivot are satisfiable.
    Incomplete,
    /// Condition 2 not decided within the node budget.
    Budget,
}

/// Whether gate-restricted resolution with gate-only witnesses is sound for
/// eliminating `var` with gate clauses `defining` (see the module docs).
/// `pure` is true when every live clause of `var` is a gate clause, where
/// condition 2 is not needed: with (1), restricted resolution is full
/// resolution and the witnesses are all the clauses.
pub(super) fn gate_restriction_is_sound(
    var: Variable,
    clauses: &ClauseArena,
    defining: &[usize],
    resolve_gate_pairs: bool,
    vals: &[i8],
    pure: bool,
) -> GateVerdict {
    if defining.is_empty() || defining.len() > GATE_CHECK_MAX_CLAUSES {
        return GateVerdict::Shape;
    }
    let pos = Literal::positive(var);
    let neg = Literal::negative(var);
    let mut pos_side: Vec<&[Literal]> = Vec::with_capacity(defining.len());
    let mut neg_side: Vec<&[Literal]> = Vec::with_capacity(defining.len());
    for &idx in defining {
        if idx >= clauses.len() || clauses.is_dead(idx) {
            return GateVerdict::Shape;
        }
        let lits = clauses.literals(idx);
        match (lits.contains(&pos), lits.contains(&neg)) {
            (true, false) => pos_side.push(lits),
            (false, true) => neg_side.push(lits),
            _ => return GateVerdict::Shape,
        }
    }
    if pos_side.is_empty() || neg_side.is_empty() {
        return GateVerdict::Shape;
    }
    let root_true = |lit: Literal| vals.get(lit.index()).copied().unwrap_or(0) > 0;
    if !resolve_gate_pairs {
        for &p in &pos_side {
            for &n in &neg_side {
                let clash = p
                    .iter()
                    .any(|&l| l.variable() != var && n.contains(&l.negated()));
                let satisfied = p
                    .iter()
                    .chain(n)
                    .any(|&l| l.variable() != var && root_true(l));
                if !clash && !satisfied {
                    return GateVerdict::Pairs;
                }
            }
        }
    }
    if pure {
        return GateVerdict::Sound;
    }
    // Condition 2 on the gate clauses without `var` under the root
    // assignment: a root-satisfied clause is dropped (it forces nothing), a
    // root-false literal removed (an emptied clause forces `var` by itself).
    let mut local_of: Vec<(Variable, u32)> = Vec::new();
    let mut local = Vec::with_capacity(defining.len());
    for lits in pos_side.iter().chain(&neg_side) {
        if lits.iter().any(|&l| l.variable() != var && root_true(l)) {
            continue;
        }
        let mut clause = Vec::with_capacity(lits.len());
        let root_false = |lit: Literal| vals.get(lit.index()).copied().unwrap_or(0) < 0;
        for &l in lits
            .iter()
            .filter(|&&l| l.variable() != var && !root_false(l))
        {
            let id = match local_of.iter().find(|(v, _)| *v == l.variable()) {
                Some(&(_, id)) => id,
                None => {
                    let id = local_of.len() as u32;
                    local_of.push((l.variable(), id));
                    id
                }
            };
            clause.push(2 * id + u32::from(!l.is_positive()));
        }
        local.push(clause);
    }
    let mut budget = GATE_CHECK_NODE_BUDGET;
    let mut assignment = vec![0i8; local_of.len()];
    match dpll_refutes(&local, &mut assignment, &mut budget) {
        Some(true) => GateVerdict::Sound,
        Some(false) => GateVerdict::Incomplete,
        None => GateVerdict::Budget,
    }
}

/// `Some(true)` when `clauses` (literal `2v + negated`) have no model extending
/// `assignment`, `Some(false)` when they have one, `None` out of budget.
/// `assignment` is restored before returning.
fn dpll_refutes(clauses: &[Vec<u32>], assignment: &mut [i8], budget: &mut u32) -> Option<bool> {
    if *budget == 0 {
        return None;
    }
    *budget -= 1;
    let value = |assignment: &[i8], lit: u32| {
        let v = assignment[(lit / 2) as usize];
        if lit & 1 == 1 {
            -v
        } else {
            v
        }
    };
    let mut trail: Vec<usize> = Vec::new();
    let outcome = 'search: loop {
        let mut branch = None;
        let mut progress = false;
        for clause in clauses {
            let mut open = None;
            let mut open_count = 0;
            let mut satisfied = false;
            for &lit in clause {
                match value(assignment, lit) {
                    1 => {
                        satisfied = true;
                        break;
                    }
                    0 => {
                        open_count += 1;
                        open = Some(lit);
                    }
                    _ => {}
                }
            }
            if satisfied {
                continue;
            }
            match (open_count, open) {
                (0, _) => break 'search Some(true),
                (1, Some(lit)) => {
                    let v = (lit / 2) as usize;
                    assignment[v] = if lit & 1 == 1 { -1 } else { 1 };
                    trail.push(v);
                    progress = true;
                }
                (_, Some(lit)) => branch = branch.or(Some(lit)),
                _ => {}
            }
        }
        if progress {
            continue;
        }
        let Some(lit) = branch else {
            break Some(false);
        };
        let v = (lit / 2) as usize;
        let mut result = Some(true);
        for sign in [1i8, -1] {
            assignment[v] = sign;
            let branch_result = dpll_refutes(clauses, assignment, budget);
            assignment[v] = 0;
            match branch_result {
                Some(true) => {}
                other => {
                    result = other;
                    break;
                }
            }
        }
        break result;
    };
    for v in trail {
        assignment[v] = 0;
    }
    outcome
}

#[cfg(test)]
#[path = "gate_complete_tests.rs"]
mod tests;
