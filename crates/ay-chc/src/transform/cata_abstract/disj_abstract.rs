// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Disjunctive abstract-invariant learner for the catamorphism-abstracted LIA
//! problem ("CATA v3 ICE lane", CHC-COMP agenda #7).
//!
//! # Why this exists
//!
//! [`super::affine_houdini`] synthesizes a *conjunction* of affine relations per
//! predicate (greatest fixpoint over a conjunctive candidate lattice). That
//! suffices for the size-family abstractions, but the element/ordering levels
//! (`Min` + `Sorted` columns — the sortedness fold) provably require a
//! **disjunctive** invariant. Example (z3-Spacer's certificate for the
//! `tip2015_sort_ISortSorts` L5 abstraction):
//!
//! ```text
//! ordered_13 := (l1_rootdisc >= 1 OR l2_sorted <= 0)
//!             AND (l2_rootdisc >= 1 OR l1_rootdisc = 1)
//! ```
//!
//! A conjunction of atoms cannot express `(a OR b)`, so affine Houdini returns
//! `None` on these levels and the whole route falls through to Unknown.
//!
//! This module computes the **least fixpoint of the exact Boolean abstract
//! post** over a small, tag-derived atom set per predicate. The result is the
//! *strongest* invariant expressible as an arbitrary Boolean combination of
//! those atoms (a disjunction of conjunctive minterms — a decision-tree region),
//! which is genuinely disjunctive. Concretely: for every rule clause
//! `body ∧ φ ⇒ head`, and every reachable minterm-combination of the body
//! predicates, it enumerates (via blocking-clause AllSAT) every head-atom
//! truth-assignment consistent with `body ∧ φ` and adds it to the head's
//! reachable set. Iterating to a fixpoint yields an invariant that is inductive
//! **by construction**; the query clauses are then checked for exclusion.
//!
//! # Soundness
//!
//! Candidate generator only — identical discipline to affine Houdini. The
//! caller (`adaptive_cata.rs`) re-certifies the returned [`InvariantModel`]
//! against EVERY abstract clause with a fresh verifier, discharges the
//! per-clause implication obligations, and gates the original query. A wrong or
//! non-inductive result therefore yields NO verdict — never a wrong Safe. Every
//! loop is bounded (atom cap, minterm cap, body-combo cap, round cap, wall
//! deadline) and fails closed to `None`.

use std::collections::HashSet;
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

/// Per-SMT-query timeout inside the fixpoint (LIA, few variables — fast).
const QUERY_TIMEOUT: Duration = Duration::from_millis(400);
/// Hard cap on atoms per predicate. A minterm is a `u64` bitmask, so this must
/// stay ≤ 64; kept lower to bound the reachable-minterm blow-up.
const MAX_ATOMS_PER_PRED: usize = 40;
/// Hard cap on reachable minterms per predicate (bounds the DNF size).
const MAX_MINTERMS_PER_PRED: usize = 6000;
/// Hard cap on head-minterm enumeration per body-combination.
const MAX_ENUM_PER_COMBO: usize = 2048;
/// Hard cap on the body-combination product for one clause.
const MAX_BODY_COMBOS: usize = 40_000;
/// Hard cap on fixpoint refinement rounds.
const MAX_ROUNDS: usize = 128;

/// Run the disjunctive (exact predicate-abstraction least-fixpoint) learner.
///
/// Returns an inductive-by-construction [`InvariantModel`] that excludes every
/// query clause, or `None` when the atom lattice cannot prove safety within the
/// caps / `deadline`. NOT trusted: the caller re-certifies it.
pub(crate) fn solve_abstract_disjunctive(
    problem: &ChcProblem,
    tags: &FxHashMap<PredicateId, Vec<ColumnTag>>,
    deadline: Instant,
) -> Option<InvariantModel> {
    debug_assert!(!problem.has_datatype_sorts());
    let preds = problem.predicates();
    if preds.is_empty() {
        return None;
    }

    // Atom set per predicate over its canonical arg vars.
    let mut atoms: FxHashMap<PredicateId, Vec<ChcExpr>> = FxHashMap::default();
    for pred in preds {
        let pred_tags = tags.get(&pred.id).map(Vec::as_slice).unwrap_or(&[]);
        let a = build_atoms(pred.id, &pred.arg_sorts, pred_tags);
        if a.len() > MAX_ATOMS_PER_PRED {
            // Too many atoms ⇒ minterm blow-up risk; fail closed.
            return None;
        }
        atoms.insert(pred.id, a);
    }

    // Partition clauses.
    let mut rule_clauses = Vec::new();
    let mut query_clauses = Vec::new();
    for clause in problem.clauses() {
        match &clause.head {
            ClauseHead::Predicate(..) => rule_clauses.push(clause),
            ClauseHead::False => query_clauses.push(clause),
        }
    }

    // Reachable minterm set per predicate (bitmask: bit i ⟺ atom i TRUE).
    let mut reach: FxHashMap<PredicateId, Vec<u64>> = FxHashMap::default();
    let mut reach_set: FxHashMap<PredicateId, HashSet<u64>> = FxHashMap::default();
    for pred in preds {
        reach.insert(pred.id, Vec::new());
        reach_set.insert(pred.id, HashSet::new());
    }

    let mut backend = PdrExecutorBackend::new();

    // ── Least-fixpoint of the exact abstract post ───────────────────────────
    for _round in 0..MAX_ROUNDS {
        if Instant::now() >= deadline {
            return None;
        }
        let mut changed = false;
        for &clause in &rule_clauses {
            let ClauseHead::Predicate(hpid, hargs) = &clause.head else {
                continue;
            };
            let head_atoms = atoms.get(hpid)?;
            let head_subst = canonical_subst(*hpid, hargs, problem);
            let head_atoms_inst: Vec<ChcExpr> = head_atoms
                .iter()
                .map(|a| a.substitute(&head_subst))
                .collect();

            // Enumerate reachable body-minterm combinations.
            let body = &clause.body.predicates;
            let mut sizes: Vec<usize> = Vec::with_capacity(body.len());
            let mut product: usize = 1;
            for (bpid, _) in body {
                let n = reach.get(bpid).map(Vec::len).unwrap_or(0);
                sizes.push(n);
                product = product.saturating_mul(n);
            }
            if body
                .iter()
                .any(|(bpid, _)| reach.get(bpid).map(Vec::is_empty).unwrap_or(true))
            {
                // Some body predicate has no reachable minterm yet ⇒ nothing to
                // propagate this round.
                continue;
            }
            if product > MAX_BODY_COMBOS {
                return None;
            }

            let mut idx = vec![0usize; body.len()];
            loop {
                if Instant::now() >= deadline {
                    return None;
                }
                // Build the body formula for this combination.
                let mut parts: Vec<ChcExpr> = Vec::new();
                if let Some(c) = &clause.body.constraint {
                    parts.push(c.clone());
                }
                for (k, (bpid, bargs)) in body.iter().enumerate() {
                    let mask = reach[bpid][idx[k]];
                    let batoms = &atoms[bpid];
                    let subst = canonical_subst(*bpid, bargs, problem);
                    parts.push(minterm_expr(batoms, mask).substitute(&subst));
                }
                let body_formula = ChcExpr::and_all(parts);

                let masks =
                    enum_head_minterms(&mut backend, &body_formula, &head_atoms_inst, deadline)?;
                for m in masks {
                    let set = reach_set.get_mut(hpid).unwrap();
                    if set.insert(m) {
                        let v = reach.get_mut(hpid).unwrap();
                        v.push(m);
                        changed = true;
                        if v.len() > MAX_MINTERMS_PER_PRED {
                            return None;
                        }
                    }
                }

                // Advance the mixed-radix body index.
                if body.is_empty() {
                    break;
                }
                let mut k = 0;
                loop {
                    idx[k] += 1;
                    if idx[k] < sizes[k] {
                        break;
                    }
                    idx[k] = 0;
                    k += 1;
                    if k == body.len() {
                        break;
                    }
                }
                if k == body.len() {
                    break;
                }
            }
        }
        if !changed {
            break;
        }
    }

    if std::env::var_os("AY_CATA_TRACE").is_some() {
        for pred in preds {
            let masks = &reach[&pred.id];
            let f = build_pred_invariant(&atoms[&pred.id], masks);
            tracing::debug!(
                pred = %pred.name,
                minterms = masks.len(),
                inv = %InvariantModel::expr_to_smtlib(&f),
                "cata-disj: fixpoint invariant"
            );
        }
    }

    // ── Query check: no reachable body-combo may satisfy an error clause ────
    for &clause in &query_clauses {
        let body = &clause.body.predicates;
        if body
            .iter()
            .any(|(bpid, _)| reach.get(bpid).map(Vec::is_empty).unwrap_or(true))
        {
            // A body predicate is unreachable ⇒ clause vacuously excluded.
            continue;
        }
        let mut sizes: Vec<usize> = Vec::with_capacity(body.len());
        let mut product: usize = 1;
        for (bpid, _) in body {
            let n = reach[bpid].len();
            sizes.push(n);
            product = product.saturating_mul(n);
        }
        if product > MAX_BODY_COMBOS {
            return None;
        }
        let mut idx = vec![0usize; body.len()];
        loop {
            if Instant::now() >= deadline {
                return None;
            }
            let mut parts: Vec<ChcExpr> = Vec::new();
            if let Some(c) = &clause.body.constraint {
                parts.push(c.clone());
            }
            for (k, (bpid, bargs)) in body.iter().enumerate() {
                let mask = reach[bpid][idx[k]];
                let subst = canonical_subst(*bpid, bargs, problem);
                parts.push(minterm_expr(&atoms[bpid], mask).substitute(&subst));
            }
            let body_formula = ChcExpr::and_all(parts);
            match backend.check_sat(&body_formula, QUERY_TIMEOUT) {
                r if r.is_unsat() => {}
                SmtResult::Sat(_) => {
                    // Least fixpoint reaches the error ⇒ no atom-expressible
                    // invariant proves safety here.
                    tracing::debug!("cata-disj: query reachable in least fixpoint");
                    return None;
                }
                _ => return None, // Unknown ⇒ fail closed.
            }
            if body.is_empty() {
                break;
            }
            let mut k = 0;
            loop {
                idx[k] += 1;
                if idx[k] < sizes[k] {
                    break;
                }
                idx[k] = 0;
                k += 1;
                if k == body.len() {
                    break;
                }
            }
            if k == body.len() {
                break;
            }
        }
    }
    tracing::debug!(
        preds = preds.len(),
        "cata-disj: found a disjunctive safety invariant"
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
        let formula = build_pred_invariant(&atoms[&pred.id], &reach[&pred.id]);
        model.set(pred.id, PredicateInterpretation::new(vars, formula));
    }
    Some(model)
}

/// Enumerate every head-atom truth-assignment consistent with `body_formula`
/// via blocking-clause AllSAT. Returns the reachable head minterms, or `None`
/// on Unknown / indeterminate evaluation / cap / deadline (fail closed).
fn enum_head_minterms(
    backend: &mut PdrExecutorBackend,
    body_formula: &ChcExpr,
    head_atoms_inst: &[ChcExpr],
    deadline: Instant,
) -> Option<Vec<u64>> {
    debug_assert!(head_atoms_inst.len() <= 64);
    // Ground shortcut: a constant-false body contributes nothing.
    if let Some(SmtValue::Bool(false)) = evaluate_expr(body_formula, &FxHashMap::default()) {
        return Some(Vec::new());
    }
    let mut result = Vec::new();
    let mut f = body_formula.clone();
    for _ in 0..MAX_ENUM_PER_COMBO {
        if Instant::now() >= deadline {
            return None;
        }
        match backend.check_sat(&f, QUERY_TIMEOUT) {
            SmtResult::Sat(model) => {
                let mut mask = 0u64;
                let mut block: Vec<ChcExpr> = Vec::with_capacity(head_atoms_inst.len());
                for (i, atom) in head_atoms_inst.iter().enumerate() {
                    let b = match evaluate_expr(atom, &model) {
                        Some(SmtValue::Bool(v)) => v,
                        _ => return None, // indeterminate ⇒ fail closed.
                    };
                    if b {
                        mask |= 1u64 << i;
                        block.push(ChcExpr::not(atom.clone()));
                    } else {
                        block.push(atom.clone());
                    }
                }
                result.push(mask);
                // Block this exact head-atom assignment and continue.
                let blocking = if block.is_empty() {
                    ChcExpr::Bool(false)
                } else {
                    ChcExpr::or_all(block)
                };
                f = ChcExpr::and(f, blocking);
            }
            r if r.is_unsat() => return Some(result),
            _ => return None, // Unknown ⇒ fail closed.
        }
    }
    None // enumeration cap hit ⇒ fail closed.
}

/// Conjunctive expression for one minterm over `atoms` (atom i asserted
/// positively when bit i is set, negated otherwise).
fn minterm_expr(atoms: &[ChcExpr], mask: u64) -> ChcExpr {
    let mut parts: Vec<ChcExpr> = Vec::with_capacity(atoms.len());
    for (i, a) in atoms.iter().enumerate() {
        if mask & (1u64 << i) != 0 {
            parts.push(a.clone());
        } else {
            parts.push(ChcExpr::not(a.clone()));
        }
    }
    match parts.len() {
        0 => ChcExpr::Bool(true),
        1 => parts.remove(0),
        _ => ChcExpr::and_all(parts),
    }
}

/// DNF invariant for a predicate: disjunction of its reachable minterms.
/// Empty reachable set ⇒ `false` (unreachable predicate).
fn build_pred_invariant(atoms: &[ChcExpr], masks: &[u64]) -> ChcExpr {
    if masks.is_empty() {
        return ChcExpr::Bool(false);
    }
    let mut sorted: Vec<u64> = masks.to_vec();
    sorted.sort_unstable();
    sorted.dedup();
    let disjuncts: Vec<ChcExpr> = sorted.iter().map(|&m| minterm_expr(atoms, m)).collect();
    if disjuncts.len() == 1 {
        disjuncts.into_iter().next().unwrap()
    } else {
        ChcExpr::or_all(disjuncts)
    }
}

/// Substitution mapping predicate `pid`'s canonical arg vars onto the argument
/// terms of one application.
pub(super) fn canonical_subst(
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

/// Canonical argument variable for predicate `pid`, column `i`. Reserved,
/// collision-free with user/abstraction/affine-Houdini (`__cxh…`) variables.
pub(super) fn canonical_var(pid: PredicateId, i: usize, sort: &ChcSort) -> ChcVar {
    ChcVar::new(format!("__cxd{}_{}", pid.index(), i), sort.clone())
}

/// Atom-vocabulary profile for [`build_atoms_profiled`].
///
/// The wide sortedness abstracts (`BSortSorts` and family — 9+ predicates, 3
/// list-groups per predicate) blow the full vocabulary past every tractable
/// wall in TWO independent ways, both MEASURED on the dumped abstracts:
///   * the ~21 SIZE pairwise-difference atoms per wide predicate push the atom
///     count to 39 (→ up to 2³⁹ minterms) and, worse, make every AllSAT
///     head-enumeration SMT call cost ~200 ms, so even round 0 (facts) exhausts
///     the budget; and
///   * the MIN/element ordering (`min_i ≤ min_j`) atoms, combined with the
///     `ite(<= elt min) … sorted` recurrence and the AllSAT blocking clauses,
///     drive the `ay-dpll` LIA backend to a genuine `Unknown` on the `ordered`
///     self-recurrence (fast Unknown, not a timeout) — the learner then fails
///     closed.
///
/// [`AtomProfile::FlagsOnly`] drops BOTH families, keeping the RootDisc/Sorted
/// flag atoms and the nil-discriminator `size = 1` atoms. The certifying
/// disjunctive invariant of the sortedness fold lives in that flag lattice (see
/// the module-level `ordered_13` example), so this compact vocabulary converts
/// the wide family where the full one cannot — while the full profile still
/// converts the narrow family (`ISortSorts`, `nat_ISortSorts`) whose invariant
/// genuinely needs the min atoms. The two profiles are therefore complementary;
/// the wired route tries `Full` first and `FlagsOnly` as an additive fallback,
/// each independently re-certified by the caller (candidate generators only).
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(super) enum AtomProfile {
    /// The full tag-derived vocabulary (flags + size + min + untagged).
    Full,
    /// Flags + nil-discriminator only: drop the size pairwise-difference atoms
    /// and the min/element ordering atoms.
    FlagsOnly,
    /// [`AtomProfile::Full`] PLUS `size_i <= size_j` (and size↔scalar) leq-split
    /// atoms — the piecewise-linear vocabulary the ELEMENT-FREE nat-peano family
    /// needs (min/max/leq/minus-clamp laws over Peano sizes are disjunctions
    /// split on a size ordering, which `Full`'s unit-difference equalities alone
    /// cannot express). Used ONLY by the nonsort nat lane
    /// ([`super::ice_dt::solve_abstract_ice_dt_nat`]); the wide sortedness Full /
    /// FlagsOnly profiles must NOT grow (their atom count is already at the
    /// ay-dpll `Unknown` / SMT-latency wall — see this enum's other variants).
    NatSize,
}

/// Build the tag-derived atom set for one predicate. The atoms are chosen to be
/// bounded in count and RELATIONAL for unbounded columns (`Min`, element
/// scalars) so the reachable-minterm set cannot blow up on element values:
/// only the finitely-many ordering relationships among columns are tracked.
pub(super) fn build_atoms(
    pid: PredicateId,
    arg_sorts: &[ChcSort],
    tags: &[ColumnTag],
) -> Vec<ChcExpr> {
    build_atoms_profiled(pid, arg_sorts, tags, AtomProfile::Full)
}

/// [`build_atoms`] under an explicit [`AtomProfile`] — see that enum for why the
/// wide sortedness family needs the compact [`AtomProfile::FlagsOnly`] vocabulary.
pub(super) fn build_atoms_profiled(
    pid: PredicateId,
    arg_sorts: &[ChcSort],
    tags: &[ColumnTag],
    profile: AtomProfile,
) -> Vec<ChcExpr> {
    let flags_only = matches!(profile, AtomProfile::FlagsOnly);
    let var = |i: usize| -> ChcExpr { ChcExpr::var(canonical_var(pid, i, &arg_sorts[i])) };
    let int_cols: Vec<usize> = arg_sorts
        .iter()
        .enumerate()
        .filter(|(_, s)| matches!(s, ChcSort::Int))
        .map(|(i, _)| i)
        .collect();

    // Trust tags only when index-aligned with the signature.
    let tags: &[ColumnTag] = if tags.len() == arg_sorts.len() {
        tags
    } else {
        &[]
    };
    let tag_kind = |i: usize| -> Option<&CataKind> { tags.get(i).and_then(|t| t.kind.as_ref()) };
    let is_scalar_int = |i: usize| -> bool { tags.get(i).map(|t| t.scalar_int).unwrap_or(false) };

    let size_cols: Vec<usize> = int_cols
        .iter()
        .copied()
        .filter(|&i| matches!(tag_kind(i), Some(CataKind::Size)))
        .collect();
    let flag_cols: Vec<usize> = int_cols
        .iter()
        .copied()
        .filter(|&i| {
            matches!(
                tag_kind(i),
                Some(CataKind::RootDisc) | Some(CataKind::Sorted)
            )
        })
        .collect();
    let min_cols: Vec<usize> = int_cols
        .iter()
        .copied()
        .filter(|&i| matches!(tag_kind(i), Some(CataKind::Min) | Some(CataKind::Max)))
        .collect();
    let scalar_cols: Vec<usize> = int_cols
        .iter()
        .copied()
        .filter(|&i| is_scalar_int(i))
        .collect();
    // Columns with no usable tag (e.g. the le/gt scalar relations): fall back to
    // pairwise ordering atoms among them.
    let untagged: Vec<usize> = int_cols
        .iter()
        .copied()
        .filter(|&i| tag_kind(i).is_none() && !is_scalar_int(i))
        .collect();

    let mut pool: Vec<ChcExpr> = Vec::new();
    let push = |e: ChcExpr, pool: &mut Vec<ChcExpr>| {
        if !pool.iter().any(|p| *p == e) {
            pool.push(e);
        }
    };

    // (1) Flag columns (RootDisc / Sorted ∈ {0,1}): pin to 0 and to 1.
    for &i in &flag_cols {
        push(ChcExpr::eq(var(i), ChcExpr::int(0)), &mut pool);
        push(ChcExpr::eq(var(i), ChcExpr::int(1)), &mut pool);
    }

    // (2) Size columns: `= 1` (nil vs non-nil) and pairwise unit differences.
    // The `= 1` nil-discriminator is kept under every profile; the pairwise
    // differences are the dominant atom-count / SMT-latency contributor and are
    // dropped under `FlagsOnly` (see [`AtomProfile`]).
    for &i in &size_cols {
        push(ChcExpr::eq(var(i), ChcExpr::int(1)), &mut pool);
    }
    if !flags_only {
        for a in 0..size_cols.len() {
            for b in 0..size_cols.len() {
                if a == b {
                    continue;
                }
                let (i, j) = (size_cols[a], size_cols[b]);
                for c in [-1i64, 0, 1] {
                    push(
                        ChcExpr::eq(ChcExpr::sub(var(i), var(j)), ChcExpr::int(c)),
                        &mut pool,
                    );
                }
            }
        }
    }

    // (2b) NAT leq-splits: `size_i <= size_j` for every ordered size pair, plus
    // `size <= scalar` / `scalar <= size`. These are the piecewise-linear split
    // atoms the element-free nat-peano family needs — `min(a,b)=c`,
    // `max(a,b)=c`, `leq`, `minus`-clamp abstract to a DISJUNCTION guarded by a
    // size ordering (e.g. `(a<=b ∧ c=a) ∨ (a>b ∧ c=b)`), which the `Full`
    // unit-difference EQUALITIES alone cannot express. Emitted ONLY under
    // `NatSize`, so the sortedness `Full`/`FlagsOnly` vocabularies are byte-
    // identical (no wide-family regression).
    if matches!(profile, AtomProfile::NatSize) {
        for a in 0..size_cols.len() {
            for b in 0..size_cols.len() {
                if a == b {
                    continue;
                }
                push(ChcExpr::le(var(size_cols[a]), var(size_cols[b])), &mut pool);
            }
        }
        for &i in &size_cols {
            for &s in &scalar_cols {
                push(ChcExpr::le(var(i), var(s)), &mut pool);
                push(ChcExpr::le(var(s), var(i)), &mut pool);
            }
        }
    }

    // (3) Min/element ordering atoms (relational — bounded count, no blow-up on
    // unbounded element values). Min ↔ Min, Min ↔ scalar element. Dropped under
    // `FlagsOnly`: these atoms drive the ay-dpll backend to `Unknown` on the
    // `ordered` recurrence for the wide family (see [`AtomProfile`]).
    if !flags_only {
        let mut ord_left: Vec<usize> = min_cols.clone();
        for &s in &scalar_cols {
            ord_left.push(s);
        }
        for a in 0..ord_left.len() {
            for b in 0..ord_left.len() {
                if a == b {
                    continue;
                }
                let (i, j) = (ord_left[a], ord_left[b]);
                // Only emit `i <= j` once per ordered pair; equality via both dirs.
                push(ChcExpr::le(var(i), var(j)), &mut pool);
            }
        }
    }

    // (4) Untagged scalar relations (le/gt-style predicates): pairwise ordering.
    for a in 0..untagged.len() {
        for b in 0..untagged.len() {
            if a == b {
                continue;
            }
            push(ChcExpr::le(var(untagged[a]), var(untagged[b])), &mut pool);
        }
    }

    pool
}
