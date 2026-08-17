// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Multi-predicate affine-relation Houdini for the catamorphism-abstracted LIA
//! problem ("CATA v2", CHC-COMP agenda #7).
//!
//! # Why this exists
//!
//! The catamorphism abstraction (see [`super`]) turns a recursive-ADT CHC
//! system into a datatype-free LIA CHC system whose predicate arguments are
//! catamorphism values (list length, tree size, element sum, …). The invariant
//! that proves the abstract system safe is almost always a **conjunction of
//! affine (in)equalities** among those catamorphism columns — e.g.
//! `size(append(x,y)) = size(x) + size(y) − 1`, `size(rev(x)) = size(x)`,
//! `len(x) = size(x) − 1`.
//!
//! These abstract problems are *multi-relation* Horn systems (a `len`, an
//! `append`, a `rev`, …, joined by a many-body query hyperedge). Empirically
//! neither AY's PDR/portfolio nor z3-Spacer converge on them within a
//! competition budget: CEGAR/PDR are poor at synthesizing exact equalities
//! across several mutually-constraining relations. ChocoCatalia wins this track
//! precisely because its `Choco` backend is an ICE/decision-tree LIA learner,
//! not a PDR engine.
//!
//! This module is the ICE-learner analogue: classic **Houdini** (greatest
//! fixpoint over a conjunctive candidate lattice) over a mined pool of affine
//! relations, generalized from the single-predicate transition-system Houdini
//! in `adaptive_houdini.rs` to the *multi-predicate* abstract problem.
//!
//! # Soundness
//!
//! This engine is a **candidate generator only**. Its output is an
//! [`InvariantModel`] over the abstract problem that the caller
//! (`adaptive_cata.rs`) still runs through the full v1 certification stack:
//!  1. the per-clause implication obligations `θ ⇒ θ#` (already discharged),
//!  2. a fresh full re-verification of the abstract model against EVERY
//!     abstract clause (`validate_external_invariant_model`),
//!  3. composition with the reserved catamorphism symbols and the original
//!     query-clause gate (`cata_model_excludes_error`).
//!
//! A wrong or non-inductive Houdini result therefore fails step (2)/(3) and
//! yields NO verdict — never a wrong Safe. That safety net is what lets the
//! candidate mining below be heuristic.

use std::time::Duration;

use ay_core::kani_compat::DetHashMap as FxHashMap;
use ay_core::time::Instant;

use crate::expr::evaluate_expr;
use crate::smt::{PdrExecutorBackend, SmtResult, SmtValue};
use crate::{
    ChcExpr, ChcProblem, ChcSort, ChcVar, ClauseHead, InvariantModel, PredicateId,
    PredicateInterpretation,
};

use super::{CataKind, ColumnTag};

/// Per-predicate cap on candidate atoms (ordered strongest/most-valuable
/// first; the tail is truncated). Generous so the high-value triple-sum
/// equalities are never truncated for typical (≤ 8-column) abstract preds.
const MAX_CANDS_PER_PRED: usize = 512;
/// Raised cap for element/ordering-carrying predicates (those with a `Min`
/// column). Their pools additionally hold the depth-1 GUARDED families plus
/// the same affine ties, so the cap is lifted to keep BOTH the exact
/// equalities and the guarded atoms from being truncated. Only preds that
/// actually gain guarded atoms use this — non-element preds keep the 512 cap
/// and their pool is byte-identical to today.
const MAX_CANDS_PER_ELEM_PRED: usize = 3072;
/// Per-SMT-query timeout inside the Houdini loop (LIA, few variables — fast).
const HOUDINI_QUERY_TIMEOUT: Duration = Duration::from_millis(400);
/// Hard cap on Houdini refinement rounds (fixpoint is monotone; this only
/// guards pathological candidate churn).
const MAX_ROUNDS: usize = 64;

/// Run multi-predicate affine Houdini on a datatype-free abstract LIA problem.
///
/// Returns an inductive-by-construction [`InvariantModel`] that excludes every
/// query clause, or `None` when the candidate lattice cannot prove safety
/// within `deadline`. The result is NOT trusted: the caller re-certifies it.
pub(crate) fn solve_abstract_affine(
    problem: &ChcProblem,
    tags: &FxHashMap<PredicateId, Vec<ColumnTag>>,
    deadline: Instant,
) -> Option<InvariantModel> {
    debug_assert!(!problem.has_datatype_sorts());
    let preds = problem.predicates();
    if preds.is_empty() {
        return None;
    }

    let constants = harvest_constants(problem);

    // Candidate pool per predicate, over that predicate's canonical arg vars.
    // An EMPTY `tags` map (or a missing entry) makes `candidate_pool` emit the
    // legacy conjunctive pool byte-for-byte — the guarded families are purely
    // additive and gated on the presence of `Min`-tagged columns.
    let mut inv: FxHashMap<PredicateId, Vec<ChcExpr>> = FxHashMap::default();
    for pred in preds {
        let pred_tags = tags.get(&pred.id).map(Vec::as_slice).unwrap_or(&[]);
        inv.insert(
            pred.id,
            candidate_pool(pred.id, &pred.arg_sorts, &constants, pred_tags),
        );
    }

    // Partition clauses once: rule clauses (predicate head) vs query clauses
    // (False head). Facts (empty body) are rule clauses with an empty body.
    let mut rule_clauses = Vec::new();
    let mut query_clauses = Vec::new();
    for clause in problem.clauses() {
        match &clause.head {
            ClauseHead::Predicate(..) => rule_clauses.push(clause),
            ClauseHead::False => query_clauses.push(clause),
        }
    }

    let mut backend = PdrExecutorBackend::new();

    // ── Houdini fixpoint over the rule clauses ──────────────────────────────
    for _round in 0..MAX_ROUNDS {
        if Instant::now() >= deadline {
            return None;
        }
        let mut changed = false;
        for &clause in &rule_clauses {
            if Instant::now() >= deadline {
                return None;
            }
            let ClauseHead::Predicate(hpid, hargs) = &clause.head else {
                continue;
            };
            // Assumption A = ⋀ body-predicate invariants (instantiated) ∧ φ.
            let assumption = instantiate_body(clause, &inv);
            let hsubst = canonical_subst(*hpid, hargs, problem);

            while let Some(head_cands) = inv.get(hpid) {
                if head_cands.is_empty() {
                    break;
                }
                let head_conj = ChcExpr::and_all(head_cands.iter().map(|c| c.substitute(&hsubst)));
                let query = ChcExpr::and(assumption.clone(), ChcExpr::not(head_conj));
                // Ground shortcut: `¬head_conj` is often a constant-false term
                // (every candidate already implied at this clause) that a
                // theory backend can return Unknown on — which would wrongly
                // trigger dropping. Fold it first.
                if let Some(b) = ground_bool(&query) {
                    if !b {
                        break; // query is constant-false ⇒ all candidates implied
                    }
                }
                match backend.check_sat(&query, HOUDINI_QUERY_TIMEOUT) {
                    r if r.is_unsat() => break, // every head candidate is implied
                    SmtResult::Sat(model) => {
                        // Drop every head candidate the model falsifies.
                        let dropped = drop_falsified(&mut inv, *hpid, &hsubst, &model);
                        if dropped > 0 {
                            changed = true;
                            continue;
                        }
                        // Model gave no droppable candidate (indeterminate):
                        // fall back to a definitive per-candidate sweep.
                        if per_candidate_sweep(&mut backend, &assumption, &mut inv, *hpid, &hsubst)
                        {
                            changed = true;
                        }
                        break;
                    }
                    _ => {
                        // Unknown: a definitive per-candidate sweep keeps only
                        // candidates provably implied (fail-closed dropping).
                        if per_candidate_sweep(&mut backend, &assumption, &mut inv, *hpid, &hsubst)
                        {
                            changed = true;
                        }
                        break;
                    }
                }
            }
        }
        if !changed {
            break;
        }
    }

    // Diagnostic: the fixpoint invariant per predicate. Env-gated (like
    // --chc-cata-dump-obligations) so it costs nothing on the hot path.
    if ay_core::misc_cli_flags().chc_cata_trace {
        for pred in preds {
            let cands = inv.get(&pred.id).map(Vec::as_slice).unwrap_or(&[]);
            let f = ChcExpr::and_all(cands.iter().cloned());
            tracing::debug!(
                pred = %pred.name,
                n = cands.len(),
                inv = %crate::InvariantModel::expr_to_smtlib(&f),
                "cata-v2 affine houdini: fixpoint invariant"
            );
        }
    }

    // ── Query check: every error clause must be excluded ────────────────────
    for (qi, &clause) in query_clauses.iter().enumerate() {
        if Instant::now() >= deadline {
            return None;
        }
        let assumption = instantiate_body(clause, &inv);
        if !robust_unsat(&mut backend, &assumption) {
            // The strongest lattice invariant does not exclude this error:
            // Houdini cannot prove safety here.
            tracing::debug!(query = qi, "cata-v2 affine houdini: query not excluded");
            return None;
        }
    }
    tracing::debug!(
        preds = preds.len(),
        "cata-v2 affine houdini: found a safety invariant"
    );

    // ── Build the abstract invariant model ──────────────────────────────────
    let mut model = InvariantModel::new();
    for pred in preds {
        let vars: Vec<ChcVar> = pred
            .arg_sorts
            .iter()
            .enumerate()
            .map(|(i, s)| canonical_var(pred.id, i, s))
            .collect();
        let cands = inv.remove(&pred.id).unwrap_or_default();
        let formula = if cands.is_empty() {
            ChcExpr::Bool(true)
        } else {
            ChcExpr::and_all(cands)
        };
        model.set(pred.id, PredicateInterpretation::new(vars, formula));
    }
    Some(model)
}

/// Drop head candidates of `hpid` that `model` evaluates to false at the
/// clause's head-argument terms. Returns how many were dropped.
fn drop_falsified(
    inv: &mut FxHashMap<PredicateId, Vec<ChcExpr>>,
    hpid: PredicateId,
    hsubst: &[(ChcVar, ChcExpr)],
    model: &FxHashMap<String, SmtValue>,
) -> usize {
    let Some(cands) = inv.get_mut(&hpid) else {
        return 0;
    };
    let before = cands.len();
    cands.retain(|c| {
        // Keep unless the model definitively falsifies the instantiated atom.
        !matches!(
            evaluate_expr(&c.substitute(hsubst), model),
            Some(SmtValue::Bool(false))
        )
    });
    before - cands.len()
}

/// Definitive per-candidate inductiveness sweep: drop every head candidate `c`
/// for which `assumption ⇒ c_inst` does not provably hold. Returns whether any
/// candidate was dropped. Dropping only weakens, so this is sound; a surviving
/// candidate is guaranteed implied under `assumption`.
fn per_candidate_sweep(
    backend: &mut PdrExecutorBackend,
    assumption: &ChcExpr,
    inv: &mut FxHashMap<PredicateId, Vec<ChcExpr>>,
    hpid: PredicateId,
    hsubst: &[(ChcVar, ChcExpr)],
) -> bool {
    let snapshot = match inv.get(&hpid) {
        Some(v) => v.clone(),
        None => return false,
    };
    let mut survivors = Vec::with_capacity(snapshot.len());
    let mut dropped = false;
    for cand in snapshot {
        let query = ChcExpr::and(assumption.clone(), ChcExpr::not(cand.substitute(hsubst)));
        if robust_unsat(backend, &query) {
            survivors.push(cand);
        } else {
            dropped = true;
        }
    }
    inv.insert(hpid, survivors);
    dropped
}

/// Constant-fold `e` to a Boolean if it is ground (no free variables).
fn ground_bool(e: &ChcExpr) -> Option<bool> {
    match evaluate_expr(e, &FxHashMap::default()) {
        Some(SmtValue::Bool(b)) => Some(b),
        _ => None,
    }
}

/// Robust UNSAT check: constant-fold ground formulas first (a theory backend
/// can return `Unknown` on a trivially-false conjunction, and treating that as
/// "not unsat" would wrongly drop an implied candidate), else ask the backend.
fn robust_unsat(backend: &mut PdrExecutorBackend, e: &ChcExpr) -> bool {
    match ground_bool(e) {
        Some(b) => !b,
        None => backend.check_sat(e, HOUDINI_QUERY_TIMEOUT).is_unsat(),
    }
}

/// Assumption formula for a clause: `⋀ body-predicate invariants (instantiated
/// at their argument terms) ∧ clause constraint`.
fn instantiate_body(
    clause: &crate::HornClause,
    inv: &FxHashMap<PredicateId, Vec<ChcExpr>>,
) -> ChcExpr {
    let mut parts: Vec<ChcExpr> = Vec::new();
    if let Some(c) = &clause.body.constraint {
        parts.push(c.clone());
    }
    for (bpid, bargs) in &clause.body.predicates {
        if let Some(cands) = inv.get(bpid) {
            let subst = canonical_subst_raw(*bpid, bargs);
            for cand in cands {
                parts.push(cand.substitute(&subst));
            }
        }
    }
    match parts.len() {
        0 => ChcExpr::Bool(true),
        1 => parts.remove(0),
        _ => ChcExpr::and_all(parts),
    }
}

/// Substitution mapping predicate `pid`'s canonical arg vars onto the argument
/// terms of one application (sorts read from `problem`).
fn canonical_subst(
    pid: PredicateId,
    args: &[ChcExpr],
    problem: &ChcProblem,
) -> Vec<(ChcVar, ChcExpr)> {
    let sorts = &problem.predicates()[pid.index()].arg_sorts;
    args.iter()
        .enumerate()
        .map(|(i, a)| {
            let sort = sorts.get(i).cloned().unwrap_or(ChcSort::Int);
            (canonical_var(pid, i, &sort), a.clone())
        })
        .collect()
}

/// Like [`canonical_subst`] but reads the sort from the argument expression
/// (no `&ChcProblem` needed — used on the hot body-instantiation path).
fn canonical_subst_raw(pid: PredicateId, args: &[ChcExpr]) -> Vec<(ChcVar, ChcExpr)> {
    args.iter()
        .enumerate()
        .map(|(i, a)| (canonical_var(pid, i, &a.sort()), a.clone()))
        .collect()
}

/// Canonical argument variable for predicate `pid`, column `i`. The name is
/// reserved and collision-free with user/abstraction variables.
fn canonical_var(pid: PredicateId, i: usize, sort: &ChcSort) -> ChcVar {
    ChcVar::new(format!("__cxh{}_{}", pid.index(), i), sort.clone())
}

/// Harvest the integer constants that seed affine candidates: every literal
/// appearing anywhere in the problem plus the small fixed ladder
/// `{-2,-1,0,1,2}` (covers the `±1` node-counting offsets and `±2`
/// two-element-list constants that dominate the abstracted pool).
fn harvest_constants(problem: &ChcProblem) -> Vec<i64> {
    let mut set: Vec<i64> = vec![-2, -1, 0, 1, 2];
    let push = |n: i128, set: &mut Vec<i64>| {
        if let Ok(v) = i64::try_from(n) {
            if v.abs() <= 1_000_000 && !set.contains(&v) {
                set.push(v);
            }
        }
    };
    fn walk(e: &ChcExpr, out: &mut Vec<i128>) {
        match e {
            ChcExpr::Int(n) => out.push(*n),
            ChcExpr::Op(_, args)
            | ChcExpr::FuncApp(_, _, args)
            | ChcExpr::PredicateApp(_, _, args) => {
                for a in args {
                    walk(a, out);
                }
            }
            ChcExpr::ConstArray(_, v) => walk(v, out),
            _ => {}
        }
    }
    let mut lits: Vec<i128> = Vec::new();
    for clause in problem.clauses() {
        if let Some(c) = &clause.body.constraint {
            walk(c, &mut lits);
        }
        for (_, args) in &clause.body.predicates {
            for a in args {
                walk(a, &mut lits);
            }
        }
        if let ClauseHead::Predicate(_, args) = &clause.head {
            for a in args {
                walk(a, &mut lits);
            }
        }
    }
    for n in lits {
        push(n, &mut set);
    }
    // Deterministic, bounded: keep the small-magnitude constants first.
    set.sort_by_key(|c| (c.unsigned_abs(), *c));
    set.truncate(16);
    set
}

/// Build the ordered candidate pool for one predicate. Strongest / most useful
/// atoms first (`false`, then equalities with small constants, then
/// inequalities), truncated to [`MAX_CANDS_PER_PRED`].
fn candidate_pool(
    pid: PredicateId,
    arg_sorts: &[ChcSort],
    constants: &[i64],
    tags: &[ColumnTag],
) -> Vec<ChcExpr> {
    let var = |i: usize| -> ChcExpr { ChcExpr::var(canonical_var(pid, i, &arg_sorts[i])) };
    let int_cols: Vec<usize> = arg_sorts
        .iter()
        .enumerate()
        .filter(|(_, s)| matches!(s, ChcSort::Int))
        .map(|(i, _)| i)
        .collect();
    let bool_cols: Vec<usize> = arg_sorts
        .iter()
        .enumerate()
        .filter(|(_, s)| matches!(s, ChcSort::Bool))
        .map(|(i, _)| i)
        .collect();

    // Small constants get priority in equalities (node-counting offsets).
    let small: Vec<i64> = constants.iter().copied().filter(|c| c.abs() <= 2).collect();

    // ── Tag-derived column classes for the depth-1 GUARDED families ─────────
    // Tags are trusted ONLY when index-aligned with the abstract signature;
    // otherwise (or when empty) they are ignored, the guarded section below is
    // a strict no-op, and the pool is byte-identical to the legacy conjunctive
    // pool. `element_pred` (a `Min` column exists) is the single switch that
    // both enables the guarded atoms AND raises the truncation cap — so a
    // size-family predicate (no `Min`) is provably unaffected.
    let tags: &[ColumnTag] = if tags.len() == arg_sorts.len() {
        tags
    } else {
        &[]
    };
    let min_cols: Vec<usize> = tags
        .iter()
        .enumerate()
        .filter(|(_, t)| matches!(t.kind, Some(CataKind::Min)))
        .map(|(i, _)| i)
        .collect();
    let flag_cols: Vec<usize> = tags
        .iter()
        .enumerate()
        .filter(|(_, t)| matches!(t.kind, Some(CataKind::Sorted) | Some(CataKind::RootDisc)))
        .map(|(i, _)| i)
        .collect();
    let scalar_int_cols: Vec<usize> = tags
        .iter()
        .enumerate()
        .filter(|(_, t)| t.scalar_int)
        .map(|(i, _)| i)
        .collect();
    let element_pred = !min_cols.is_empty();

    let mut pool: Vec<ChcExpr> = Vec::new();

    // (0) `false` — the error-flag invariant. Houdini drops it the moment the
    // predicate is shown reachable; it survives only for genuinely-unreachable
    // predicates (the `ff` safety flag in the clam/leon encoding).
    pool.push(ChcExpr::Bool(false));

    // (1) Bool-column literals and their negations.
    for &i in &bool_cols {
        pool.push(var(i));
        pool.push(ChcExpr::not(var(i)));
    }

    // (2) Triple-sum equalities `a_i + a_j − a_k = c` (small constants) — the
    // `append`-style `size(z) = size(x) + size(y) − 1` family. Placed BEFORE
    // the larger pair-equality block so it survives truncation.
    for a in 0..int_cols.len() {
        for b in (a + 1)..int_cols.len() {
            for k in 0..int_cols.len() {
                if k == a || k == b {
                    continue;
                }
                let (i, j, kk) = (int_cols[a], int_cols[b], int_cols[k]);
                for &c in &small {
                    pool.push(ChcExpr::eq(
                        ChcExpr::sub(ChcExpr::add(var(i), var(j)), var(kk)),
                        ChcExpr::int(c),
                    ));
                }
            }
        }
    }

    // (3) Pair equalities `a_i − a_j = c` — small constants first (the
    // measure-preserving `rev`/`len` ties), then the remaining constants.
    for pass_small in [true, false] {
        for a in 0..int_cols.len() {
            for b in 0..int_cols.len() {
                if a == b {
                    continue;
                }
                let (i, j) = (int_cols[a], int_cols[b]);
                for &c in constants {
                    if (c.abs() <= 2) != pass_small {
                        continue;
                    }
                    pool.push(ChcExpr::eq(ChcExpr::sub(var(i), var(j)), ChcExpr::int(c)));
                }
            }
        }
    }

    // ── Depth-1 GUARDED families (element / ordering catamorphisms) ─────────
    // Placed AFTER the exact-equality classes (2)/(3) — so the size-family
    // triple-sum and pair equalities are never truncated in their favour — and
    // BEFORE the low-value single-column bounds. EMPTY for a predicate without
    // a `Min` column, so the size family's pool is unchanged. Every atom here
    // is a candidate GENERATOR ONLY: a non-inductive one is dropped by the
    // fail-closed Houdini sweep, and any surviving model is re-certified by the
    // caller's gate — enlarging this pool can turn Unknown into a re-verified
    // Safe but can NEVER manufacture a false Safe.
    if element_pred {
        // Base ordering atoms that reference a `Min` column: the non-affine
        // core of the sort family (`head ≤ min_tail`, `min ≤ min`). Computed
        // once, then guarded by every flag column below.
        let mut min_atoms: Vec<ChcExpr> = Vec::new();
        // Min ↔ Min orderings (both directions) and equalities.
        for &a in &min_cols {
            for &b in &min_cols {
                if a != b {
                    min_atoms.push(ChcExpr::le(var(a), var(b)));
                }
            }
        }
        for x in 0..min_cols.len() {
            for y in (x + 1)..min_cols.len() {
                min_atoms.push(ChcExpr::eq(var(min_cols[x]), var(min_cols[y])));
            }
        }
        // Scalar element ↔ Min orderings: the `element ≤ min(list)` fact that a
        // flag guard turns into `sorted ⇒ head ≤ min_tail`.
        for &m in &min_cols {
            for &s in &scalar_int_cols {
                min_atoms.push(ChcExpr::le(var(s), var(m)));
                min_atoms.push(ChcExpr::le(var(m), var(s)));
                min_atoms.push(ChcExpr::eq(var(s), var(m)));
            }
        }

        // (G1) FLAG-GUARDED family. For every Sorted/RootDisc flag column `g`
        // and guard bit v ∈ {1,0}: guard each Min-referencing base atom, and
        // pin every OTHER flag column to 0/1 (the `sorted_in ⇒ sorted_out`,
        // `ordered_flag ⇔ sorted` propagation the query needs).
        for &g in &flag_cols {
            for v in [1i64, 0] {
                let guard = ChcExpr::eq(var(g), ChcExpr::int(v));
                for p in &min_atoms {
                    pool.push(ChcExpr::implies(guard.clone(), p.clone()));
                }
                for &f in &flag_cols {
                    if f != g {
                        pool.push(ChcExpr::implies(
                            guard.clone(),
                            ChcExpr::eq(var(f), ChcExpr::int(1)),
                        ));
                        pool.push(ChcExpr::implies(
                            guard.clone(),
                            ChcExpr::eq(var(f), ChcExpr::int(0)),
                        ));
                    }
                }
            }
        }

        // (G2) GUARDED-MIN recurrence. For every `Min` column `m` and every
        // ordered pair (x, y) of DISTINCT operands drawn from {scalar_int
        // columns, OTHER Min columns}, the non-convex min selection
        // `m = ite(x ≤ y, x, y)` (proven inexpressible affine-only) plus its
        // convex companions `m ≤ x`. Sentinel constants (±1e9) are never
        // operands here — operands are columns, and the harvest cap keeps the
        // sentinels out of `constants` entirely.
        for &m in &min_cols {
            let mut operands: Vec<usize> = scalar_int_cols.clone();
            for &om in &min_cols {
                if om != m {
                    operands.push(om);
                }
            }
            for &x in &operands {
                pool.push(ChcExpr::le(var(m), var(x)));
                for &y in &operands {
                    if x != y {
                        pool.push(ChcExpr::eq(
                            var(m),
                            ChcExpr::ite(ChcExpr::le(var(x), var(y)), var(x), var(y)),
                        ));
                    }
                }
            }
        }
    }

    // (4) Pair difference bounds `a_i − a_j ⋈ c` for small c (monotone
    // measure relations like `len(take) ≤ len`).
    for a in 0..int_cols.len() {
        for b in 0..int_cols.len() {
            if a == b {
                continue;
            }
            let (i, j) = (int_cols[a], int_cols[b]);
            for &c in &small {
                pool.push(ChcExpr::ge(ChcExpr::sub(var(i), var(j)), ChcExpr::int(c)));
                pool.push(ChcExpr::le(ChcExpr::sub(var(i), var(j)), ChcExpr::int(c)));
            }
        }
    }

    // (5) Single-column bounds `a_i ⋈ c` for small c (base measures ≥ 0/1).
    for &i in &int_cols {
        for &c in &small {
            pool.push(ChcExpr::ge(var(i), ChcExpr::int(c)));
            pool.push(ChcExpr::le(var(i), ChcExpr::int(c)));
        }
    }

    // Element-carrying predicates use the raised cap so neither the exact
    // equalities nor the guarded families are truncated; every other predicate
    // keeps the legacy cap (and a byte-identical pool).
    let cap = if element_pred {
        MAX_CANDS_PER_ELEM_PRED
    } else {
        MAX_CANDS_PER_PRED
    };
    pool.truncate(cap);
    pool
}

#[allow(clippy::unwrap_used, clippy::panic)]
#[cfg(test)]
#[path = "affine_houdini_tests.rs"]
mod tests;
