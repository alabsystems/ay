// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Clause-local array store-to-load forwarding + dead-store elimination.
//!
//! Threaded-memory CHC encodings (e.g. model-checker-consumer's type-indexed memory
//! relations) cut every relation hop with fresh array variables defined by
//! `a' = (store a i v)` equality conjuncts, so a `(select a' j)` downstream in
//! the SAME clause never sees the store it reads from and the SMT backend pays
//! the full eager select×store axiom cross-product. This pass, within each
//! clause constraint:
//!
//! 1. **Forwarding:** substitutes definitional array equalities
//!    (`a' = store-chain / const-array / array-var alias`, first binding wins,
//!    occurs-checked) into the OTHER conjuncts and folds the resulting
//!    `select(store(...))` chains with [`ChcExpr::simplify_array_ops`]
//!    (ROW1 on syntactically identical indices, ROW2 skip-over-store only on
//!    provably distinct constant indices — anything else is NOT rewritten).
//!    A rewritten conjunct is kept only when it did not grow (node count), so
//!    unfoldable symbolic-index chains never inflate the clause.
//! 2. **Dead-store elimination:** drops inner writes of a store chain whose
//!    index is syntactically identical to a LATER (outer) write in the same
//!    chain — `store(store(b, i, v1), i, v2) = store(b, i, v2)` is a pointwise
//!    array-theory identity, valid in every model regardless of context.
//! 3. **Local def cleanup:** drops a definitional equality whose defined array
//!    variable is clause-local (not a predicate/head argument) and no longer
//!    occurs in any other conjunct — the same local existential projection
//!    `LocalVarEliminator` performs (`∀v. R ∧ v=t ⇒ H  ⟺  R ⇒ H` when
//!    `v ∉ R, H, t`), restricted to array definitions.
//!
//! Once the reads are forwarded to scalars and the local store temporaries
//! are gone, the memory arrays stop appearing in clause constraints, and the
//! existing trailing [`super::DeadParamEliminator`] can slice the dead array
//! argument positions — the relation-arity collapse that turns the
//! "235-relation" heavy-memory class from >120s Unknowns into seconds.
//!
//! Every rewrite is equivalence-preserving on the clause (congruence under a
//! kept top-level equality, pointwise store identities, or local existential
//! projection), so verdicts cannot flip; the transform still reports
//! original-clause validation obligations fail-closed like its siblings.
//!
//! Cost is strictly bounded per clause: one pass (no fixpoint), capped def
//! counts, capped resolved-definition and chain sizes, and the node budgets
//! of the shared expression rewriters.
//!
//! Kill switch: `AY_CHC_DISABLE_ARRAY_STORE_FORWARDING=1` disables the pass
//! (also part of the condense-share cache env key).

use std::sync::Arc;

use crate::expr::{maybe_grow_expr_stack, MAX_EXPR_RECURSION_DEPTH};
use crate::{ChcExpr, ChcOp, ChcProblem, ChcSort, ChcVar, HornClause};
use ay_core::kani_compat::{DetHashMap as FxHashMap, DetHashSet as FxHashSet};

use super::{
    IdentityBackTranslator, MemoryBackTranslator, TransformMemoryReport, TransformObligation,
    TransformationResult, Transformer,
};

/// Kill switch: `AY_CHC_DISABLE_ARRAY_STORE_FORWARDING=1` (or any value other
/// than `0`) disables the pass. Default: enabled.
pub(crate) fn array_store_forwarding_enabled() -> bool {
    std::env::var("AY_CHC_DISABLE_ARRAY_STORE_FORWARDING")
        .map(|v| v == "0")
        .unwrap_or(true)
}

/// Definitional array equalities considered per clause (linear scan cap).
const MAX_DEFS_PER_CLAUSE: usize = 512;

/// A resolved (chain-expanded) definition larger than this many nodes falls
/// back to its unexpanded right-hand side, bounding substitution blowup.
const MAX_RESOLVED_DEF_NODES: usize = 4096;

/// Clauses whose constraint reaches this many nodes are skipped entirely, and
/// individual conjuncts at/above this size are never rewritten.
const MAX_CLAUSE_NODES: usize = 200_000;

/// Store-chain windows longer than this are absorbed per-window only.
const MAX_STORE_CHAIN_LEN: usize = 1024;

/// Clause-local constant-address store-to-load forwarding + dead-store
/// elimination (see module docs).
pub(crate) struct ArrayStoreForwarder {
    verbose: bool,
}

impl Default for ArrayStoreForwarder {
    fn default() -> Self {
        Self::new()
    }
}

impl ArrayStoreForwarder {
    pub(crate) fn new() -> Self {
        Self { verbose: false }
    }

    pub(crate) fn with_verbose(mut self, verbose: bool) -> Self {
        self.verbose = verbose;
        self
    }

    /// Apply the pass to every clause constraint. Returns `None` when no
    /// clause changed (identity), otherwise the rewritten problem.
    ///
    /// Constraints are rewritten in place on a clone of the problem, so all
    /// problem-level metadata (predicates, datatype defs, action tags, query
    /// evidence) is preserved exactly.
    pub(crate) fn apply(&self, problem: &ChcProblem) -> Option<ChcProblem> {
        let mut new_problem = problem.clone();
        let mut changed_clauses = 0usize;
        for clause in new_problem.clauses_mut() {
            if let Some(new_constraint) = forward_in_clause(clause) {
                clause.body.constraint = new_constraint;
                changed_clauses += 1;
            }
        }
        if changed_clauses == 0 {
            return None;
        }
        if self.verbose {
            safe_eprintln!(
                "CHC: array-store-forwarding: rewrote {} clause constraints",
                changed_clauses
            );
        }
        Some(new_problem)
    }
}

impl Transformer for ArrayStoreForwarder {
    fn transform(self: Box<Self>, problem: ChcProblem) -> TransformationResult {
        if !array_store_forwarding_enabled() {
            return TransformationResult {
                problem,
                back_translator: Box::new(IdentityBackTranslator),
            };
        }
        match self.apply(&problem) {
            Some(new_problem) => TransformationResult {
                problem: new_problem,
                back_translator: Box::new(
                    MemoryBackTranslator::new(
                        // Equivalence-preserving clause-constraint rewrites only
                        // (no signature change): witnesses pass through unchanged,
                        // and Safe/Unsafe answers still validate/replay against
                        // the ORIGINAL clauses fail-closed, mirroring
                        // LocalVarEliminator.
                        TransformMemoryReport::with_original_validation_obligations(
                            "array_store_forwarding",
                            [
                                TransformObligation::named("clause-local-store-forwarding"),
                                TransformObligation::named("original-validation-on-safe"),
                                TransformObligation::named("original-replay-on-unsafe"),
                            ],
                        ),
                    )
                    .with_ground_input("array-store-forwarding", &problem),
                ),
            },
            None => TransformationResult {
                problem,
                back_translator: Box::new(IdentityBackTranslator),
            },
        }
    }
}

/// Rewrite one clause constraint. Returns `Some(new_constraint)` when the
/// clause changed (`Some(None)` meaning the constraint simplified to `true`),
/// `None` when untouched.
fn forward_in_clause(clause: &HornClause) -> Option<Option<ChcExpr>> {
    let constraint = clause.body.constraint.as_ref()?;
    if !mentions_store_or_const_array(constraint) {
        return None;
    }
    if constraint.node_count(MAX_CLAUSE_NODES) >= MAX_CLAUSE_NODES {
        return None;
    }

    let conjuncts = constraint.collect_conjuncts_nontrivial();
    if conjuncts.is_empty() {
        return None;
    }

    // --- 1. Collect definitional array equalities (first binding wins). ---
    let mut defs: FxHashMap<ChcVar, ChcExpr> = FxHashMap::default();
    let mut def_conjunct_idx: FxHashMap<ChcVar, usize> = FxHashMap::default();
    let mut def_order: Vec<ChcVar> = Vec::new();
    for (idx, conj) in conjuncts.iter().enumerate() {
        if defs.len() >= MAX_DEFS_PER_CLAUSE {
            break;
        }
        if let Some((var, rhs)) = extract_array_definition(conj) {
            if !defs.contains_key(&var) {
                defs.insert(var.clone(), rhs.clone());
                def_conjunct_idx.insert(var.clone(), idx);
                def_order.push(var);
            }
        }
    }
    let def_indices: FxHashSet<usize> = def_conjunct_idx.values().copied().collect();

    // --- 2. Resolve definitions (expand chains through other defs). ---
    let resolved = resolve_defs(&defs, &def_order);
    let subst_map: FxHashMap<&ChcVar, &ChcExpr> = resolved.iter().collect();

    // --- 3. Rewrite conjuncts (forward + fold + absorb; never grow). ---
    let mut changed = false;
    let mut rewritten: Vec<ChcExpr> = Vec::with_capacity(conjuncts.len());
    for (idx, conj) in conjuncts.iter().enumerate() {
        let old_nodes = conj.node_count(MAX_CLAUSE_NODES);
        if old_nodes >= MAX_CLAUSE_NODES {
            rewritten.push(conj.clone());
            continue;
        }
        if def_indices.contains(&idx) {
            // Keep definitional conjuncts in definitional shape; only absorb
            // dead stores inside the RHS (a strict pointwise shrink).
            let absorbed = absorb_dead_stores(conj);
            if absorbed != *conj && absorbed.node_count(old_nodes + 1) <= old_nodes {
                changed = true;
                rewritten.push(absorbed);
            } else {
                rewritten.push(conj.clone());
            }
            continue;
        }

        let accepts = |cand: &ChcExpr| -> bool {
            cand != conj && cand.node_count(old_nodes + 1) <= old_nodes
        };

        // Substituted candidate (only when the conjunct mentions a defined
        // var), then the no-substitution fold as fallback.
        let mentions_def = !defs.is_empty() && mentions_any_var(conj, &defs);
        let subst_candidate = if mentions_def {
            let cand = absorb_dead_stores(&conj.substitute_map(&subst_map).simplify_array_ops());
            if accepts(&cand) {
                Some(cand)
            } else {
                None
            }
        } else {
            None
        };
        let chosen = subst_candidate.or_else(|| {
            let cand = absorb_dead_stores(&conj.simplify_array_ops());
            if accepts(&cand) {
                Some(cand)
            } else {
                None
            }
        });
        match chosen {
            Some(cand) => {
                changed = true;
                rewritten.push(cand);
            }
            None => rewritten.push(conj.clone()),
        }
    }

    // --- 4. Drop dead clause-local array definitions. ---
    let shared_vars = collect_shared_vars(clause);
    let mut kept: Vec<bool> = vec![true; rewritten.len()];
    // Variable sets of the final conjuncts (drops don't alter other entries).
    let conjunct_vars: Vec<FxHashSet<ChcVar>> = rewritten
        .iter()
        .map(|c| c.vars().into_iter().collect())
        .collect();
    // Bounded iteration: each round drops at least one def or terminates.
    // The round cap bounds worst-case cost on adversarial clauses (chains
    // deeper than the cap keep their remaining defs — sound, just less slim).
    for _ in 0..def_order.len().min(64) {
        let mut progressed = false;
        // Reverse order cleans an in-order def chain in a single round (the
        // last temp drops first, unblocking its predecessor within the round).
        for var in def_order.iter().rev() {
            let idx = def_conjunct_idx[var];
            if !kept[idx] || shared_vars.contains(var) {
                continue;
            }
            let used_elsewhere = conjunct_vars
                .iter()
                .enumerate()
                .any(|(j, vars)| j != idx && kept[j] && vars.contains(var));
            if !used_elsewhere {
                kept[idx] = false;
                changed = true;
                progressed = true;
            }
        }
        if !progressed {
            break;
        }
    }

    if !changed {
        return None;
    }

    let remaining: Vec<ChcExpr> = rewritten
        .into_iter()
        .zip(kept)
        .filter_map(|(c, keep)| keep.then_some(c))
        .collect();
    let new_constraint = ChcExpr::and_all(remaining).simplify_constants();
    Some(Some(new_constraint).filter(|c| !matches!(c, ChcExpr::Bool(true))))
}

/// Extract `v = rhs` / `rhs = v` where `v` is an array-sorted variable, `rhs`
/// is an array term (store chain, constant array, or array-var alias), and
/// `v` does not occur in `rhs` (occurs check — `v = store(v, i, x)` is a
/// constraint, not a definition).
fn extract_array_definition(conj: &ChcExpr) -> Option<(ChcVar, &ChcExpr)> {
    let ChcExpr::Op(ChcOp::Eq, args) = conj else {
        return None;
    };
    if args.len() != 2 {
        return None;
    }
    for (var_side, rhs_side) in [(&args[0], &args[1]), (&args[1], &args[0])] {
        if let ChcExpr::Var(v) = var_side.as_ref() {
            if matches!(v.sort, ChcSort::Array(_, _))
                && is_array_definition_term(rhs_side.as_ref())
                && !rhs_side.vars().contains(v)
            {
                return Some((v.clone(), rhs_side.as_ref()));
            }
        }
    }
    None
}

/// Root shapes accepted as array definition right-hand sides.
fn is_array_definition_term(expr: &ChcExpr) -> bool {
    match expr {
        ChcExpr::Op(ChcOp::Store, args) => args.len() == 3,
        ChcExpr::ConstArray(_, _) => true,
        ChcExpr::Var(v) => matches!(v.sort, ChcSort::Array(_, _)),
        _ => false,
    }
}

/// Resolve each definition by expanding other defined variables inside it
/// (DFS with cycle tolerance: an in-progress variable stays unexpanded, which
/// is still a valid one-level definition). Oversized expansions fall back to
/// the raw right-hand side.
fn resolve_defs(
    defs: &FxHashMap<ChcVar, ChcExpr>,
    def_order: &[ChcVar],
) -> FxHashMap<ChcVar, ChcExpr> {
    let mut resolved: FxHashMap<ChcVar, ChcExpr> = FxHashMap::default();
    let mut in_progress: FxHashSet<ChcVar> = FxHashSet::default();
    for var in def_order {
        resolve_one(var, defs, &mut resolved, &mut in_progress);
    }
    resolved
}

fn resolve_one(
    var: &ChcVar,
    defs: &FxHashMap<ChcVar, ChcExpr>,
    resolved: &mut FxHashMap<ChcVar, ChcExpr>,
    in_progress: &mut FxHashSet<ChcVar>,
) {
    if resolved.contains_key(var) || in_progress.contains(var) {
        return;
    }
    let Some(raw) = defs.get(var) else {
        return;
    };
    in_progress.insert(var.clone());
    let expanded = expand_defined_vars(raw, defs, resolved, in_progress, 0);
    let expanded = absorb_dead_stores(&expanded);
    let final_def = if expanded.node_count(MAX_RESOLVED_DEF_NODES + 1) > MAX_RESOLVED_DEF_NODES {
        raw.clone()
    } else {
        expanded
    };
    in_progress.remove(var);
    resolved.insert(var.clone(), final_def);
}

fn expand_defined_vars(
    expr: &ChcExpr,
    defs: &FxHashMap<ChcVar, ChcExpr>,
    resolved: &mut FxHashMap<ChcVar, ChcExpr>,
    in_progress: &mut FxHashSet<ChcVar>,
    depth: usize,
) -> ChcExpr {
    if depth >= MAX_EXPR_RECURSION_DEPTH {
        return expr.clone();
    }
    maybe_grow_expr_stack(|| match expr {
        ChcExpr::Var(v) => {
            if in_progress.contains(v) || !defs.contains_key(v) {
                return expr.clone();
            }
            resolve_one(v, defs, resolved, in_progress);
            match resolved.get(v) {
                Some(def) => def.clone(),
                None => expr.clone(),
            }
        }
        _ => expr.map_children_with(|child| {
            expand_defined_vars(child, defs, resolved, in_progress, depth + 1)
        }),
    })
}

/// Whether the conjunct mentions any defined variable (cheap tree scan).
fn mentions_any_var(expr: &ChcExpr, defs: &FxHashMap<ChcVar, ChcExpr>) -> bool {
    fn inner(expr: &ChcExpr, defs: &FxHashMap<ChcVar, ChcExpr>, depth: usize) -> bool {
        if depth >= MAX_EXPR_RECURSION_DEPTH {
            // Conservative: assume a mention so the (still budgeted)
            // substitution path decides.
            return true;
        }
        maybe_grow_expr_stack(|| match expr {
            ChcExpr::Var(v) => defs.contains_key(v),
            ChcExpr::Bool(_)
            | ChcExpr::Int(_)
            | ChcExpr::Real(_, _)
            | ChcExpr::BitVec(_, _)
            | ChcExpr::ConstArrayMarker(_)
            | ChcExpr::IsTesterMarker(_) => false,
            ChcExpr::ConstArray(_, val) => inner(val, defs, depth + 1),
            ChcExpr::Op(_, args)
            | ChcExpr::PredicateApp(_, _, args)
            | ChcExpr::FuncApp(_, _, args) => args.iter().any(|a| inner(a, defs, depth + 1)),
        })
    }
    inner(expr, defs, 0)
}

/// Cheap gate: does the constraint contain any `store` or constant array at
/// all? Without one, nothing can fold. Depth-cap hits answer `false` (the
/// clause-size gate skips such clauses anyway).
fn mentions_store_or_const_array(expr: &ChcExpr) -> bool {
    fn inner(expr: &ChcExpr, depth: usize) -> bool {
        if depth >= MAX_EXPR_RECURSION_DEPTH {
            return false;
        }
        maybe_grow_expr_stack(|| match expr {
            ChcExpr::Op(ChcOp::Store, _) | ChcExpr::ConstArray(_, _) => true,
            ChcExpr::Op(_, args)
            | ChcExpr::PredicateApp(_, _, args)
            | ChcExpr::FuncApp(_, _, args) => args.iter().any(|a| inner(a, depth + 1)),
            _ => false,
        })
    }
    inner(expr, 0)
}

/// Drop inner writes of store chains whose index is syntactically identical
/// to a later (outer) write in the same chain.
///
/// `store(store(b, i, v1), …, i, v2) = store(b, …, i, v2)` holds pointwise in
/// every model — the last write to an index wins regardless of intervening
/// writes to other indices — so this is a pure equivalence-preserving shrink,
/// valid anywhere in the formula (including under negations).
fn absorb_dead_stores(expr: &ChcExpr) -> ChcExpr {
    absorb_inner(expr, 0)
}

fn absorb_inner(expr: &ChcExpr, depth: usize) -> ChcExpr {
    if depth >= MAX_EXPR_RECURSION_DEPTH {
        return expr.clone();
    }
    maybe_grow_expr_stack(|| match expr {
        ChcExpr::Op(ChcOp::Store, args) if args.len() == 3 => absorb_store_chain(expr, depth),
        _ => expr.map_children_with(|child| absorb_inner(child, depth + 1)),
    })
}

fn absorb_store_chain(expr: &ChcExpr, depth: usize) -> ChcExpr {
    // Walk the chain outermost → innermost (bounded window).
    let mut writes: Vec<(&Arc<ChcExpr>, &Arc<ChcExpr>)> = Vec::new();
    let mut cur = expr;
    loop {
        match cur {
            ChcExpr::Op(ChcOp::Store, args)
                if args.len() == 3 && writes.len() < MAX_STORE_CHAIN_LEN =>
            {
                writes.push((&args[1], &args[2]));
                cur = args[0].as_ref();
            }
            _ => break,
        }
    }
    let base = absorb_inner(cur, depth + 1);
    let mut changed = base != *cur;

    // Keep only the first (outermost) write per syntactic index.
    let mut seen: Vec<&ChcExpr> = Vec::with_capacity(writes.len());
    let mut kept: Vec<(ChcExpr, ChcExpr)> = Vec::with_capacity(writes.len());
    for (idx, val) in &writes {
        if seen.iter().any(|s| *s == idx.as_ref()) {
            changed = true; // dead inner store: overwritten by an outer write
            continue;
        }
        seen.push(idx.as_ref());
        let new_idx = absorb_inner(idx, depth + 1);
        let new_val = absorb_inner(val, depth + 1);
        changed |= new_idx != *idx.as_ref() || new_val != *val.as_ref();
        kept.push((new_idx, new_val));
    }
    if !changed {
        return expr.clone();
    }
    // Rebuild innermost-first (kept is outermost → innermost).
    let mut result = base;
    for (idx, val) in kept.into_iter().rev() {
        result = ChcExpr::store(result, idx, val);
    }
    result
}

/// Variables appearing in body predicate arguments or the clause head — never
/// eligible for local def cleanup (mirrors `LocalVarEliminator`).
fn collect_shared_vars(clause: &HornClause) -> FxHashSet<ChcVar> {
    let mut vars = FxHashSet::default();
    for (_, args) in &clause.body.predicates {
        for arg in args {
            for v in arg.vars() {
                vars.insert(v);
            }
        }
    }
    for v in clause.head.vars() {
        vars.insert(v);
    }
    vars
}

#[allow(clippy::unwrap_used, clippy::panic)]
#[cfg(test)]
#[path = "array_store_forwarding_tests.rs"]
mod tests;
