// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Eldarica-style ghost index/value pairs for quantified array invariants
//! (CHC-COMP agenda item #16, FORALL-ARR ghost-pair prong).
//!
//! # Idea
//!
//! For every predicate argument of sort `(Array K V)`, where `K` is `Int` or
//! a 1..=64-bit bit-vector sort, append `n` ghost scalar pairs
//! `(idx_k : K, val_k : V)` to the predicate signature. The
//! intended (semantic) coupling is `val_k = select(arr, idx_k)`:
//!
//! - **Head occurrences** `P(args)` become `P(args, f_1, select(arr, f_1), ...)`
//!   where each `f_k` is a FRESH clause variable. Because CHC clause variables
//!   are implicitly universally quantified, the clause now proves the head
//!   interpretation for EVERY index — the ghost pair behaves like a universally
//!   quantified `(i, arr[i])` probe.
//! - **Body occurrences** `P(args)` are replaced by ONE *instantiated* copy
//!   `P(args, t, select(arr, t))` — the pass-through tuple (the head's fresh
//!   ghost variables) when available, otherwise the best trigger diagonal
//!   drawn from the clause's own select/store index terms. Eldarica emits
//!   several copies, but multiple body atoms of one predicate make the clause
//!   NONLINEAR, which this PDR core cannot push lemmas through; the richer
//!   multi-tuple instantiation still runs on the certification side, where
//!   instances are plain SMT conjuncts.
//!
//! PDR then discovers a QUANTIFIER-FREE invariant `I'(args, idx, val, ...)`
//! over the ghost scalars, which denotes the quantified original invariant
//!
//! ```text
//! Q_P(args)  :=  forall i_1 .. i_m .  I'(args, i_1, select(arr_1, i_1), ...)
//! ```
//!
//! # Equisatisfiability
//!
//! *Transformed SAT ⇒ original SAT*: given a solution `I'` of the transformed
//! system, `Q_P` above solves the original system. For any original clause and
//! any target indices, instantiate the transformed clause's fresh head ghosts
//! at those indices; every body instance `I'(args, t, arr[t])` follows from the
//! body atom's quantified interpretation, so the transformed clause yields the
//! head instance. *Original SAT ⇒ transformed SAT*: `I'(args, ghosts) :=
//! I(args)` (ignore the ghosts) satisfies every transformed clause. Hence the
//! transformation is verdict-exact in both directions, for ANY choice of
//! body instantiation terms — instantiation only affects completeness of the
//! search, never soundness.
//!
//! # Gating (G1)
//!
//! The back-translated model is genuinely quantified and `ChcExpr` has no
//! quantifier node, so it CANNOT be represented as a `PredicateInterpretation`.
//! Instead the route seals a [`GhostPairCertificate`] — the transformed model
//! plus the ghost layout — via [`GhostPairCertificate::certify_and_seal`],
//! which discharges every ORIGINAL clause under the quantified semantics:
//!
//! - the head `forall` is skolemized with fresh constants (sound + complete),
//! - each body `forall` hypothesis is instantiated at every index term
//!   occurring in the clause plus the fresh head symbols (sound weakening),
//! - if the quantifier-free instantiation check does not prove the clause, a
//!   full quantified SMT check (explicit `forall` bodies through the ay-dpll
//!   executor, which has e-matching/MBQI) runs as fallback,
//! - any remaining SAT/Unknown fails the certification ⇒ the route withholds
//!   the verdict (fail-closed, returns unknown).
//!
//! Certification is construction-sealed: a `GhostPairCertificate` can only be
//! obtained through `certify_and_seal`, which runs the full original-clause
//! discharge. Downstream gates re-run [`recheck_ghost_pair_certificate`]
//! (finalize: all clauses; the runner's excludes-error gate: query clauses).
//!
//! Source ideas: Eldarica `-arrayQuans:n` (HornReader.scala ghost pairs with
//! trigger-based body instantiation) — reimplemented from scratch; see
//! the development design notes (Eldarica #6).

mod candidate;
mod candidate_flow;
mod candidate_houdini;
mod candidate_model;
mod candidate_names;
mod candidate_pool;
mod candidate_query;
mod candidate_substitute;
mod candidate_support;
mod candidate_usage;
mod certify;
mod ghost_tuple_flow;

use crate::{
    ChcExpr, ChcOp, ChcProblem, ChcSort, ChcVar, ClauseBody, ClauseHead, HornClause,
    InvariantModel, PredicateId,
};
use ay_core::kani_compat::DetHashMap as FxHashMap;
use ay_core::kani_compat::DetHashSet as FxHashSet;

use crate::smt::executor_adapter::collect_uninterpreted_function_declarations_for_exprs;

use super::{
    BackTranslator, InvalidityWitness, TransformMemoryReport, TransformationResult, Transformer,
    ValidityWitness,
};

pub(crate) use candidate_houdini::{try_query_anchored_and_seal, QueryAnchoredSeal};
pub(crate) use certify::{
    ghost_pair_replay_obligations, recheck_ghost_pair_certificate, GhostPairCertificate,
};

/// Maximum ghost slots (index/value pairs) added to a single predicate.
const MAX_SLOTS_PER_PREDICATE: usize = 8;

/// Maximum number of instantiated copies of one body atom. Identity + seed +
/// one reserved alternate for every allowed slot must all fit.
const BODY_INSTANCE_CAP: usize = MAX_SLOTS_PER_PREDICATE + 2;

/// Maximum number of clause index terms considered as triggers. Two full
/// predicate layouts allow heterogeneous head/body key sorts to coexist.
const INDEX_TERM_CAP: usize = MAX_SLOTS_PER_PREDICATE * 2;

/// Ghost layout for one predicate.
#[derive(Debug, Clone)]
struct GhostPredSpec {
    /// Arity of the predicate BEFORE ghost extension.
    original_arity: usize,
    /// Positions (into the original argument list) of `(Array K V)`
    /// arguments that received ghost pairs, in ascending order.
    array_positions: Vec<usize>,
    /// Index sort for each entry in `array_positions`.
    index_sorts: Vec<ChcSort>,
}

impl GhostPredSpec {
    /// Number of ghost slots (index/value pairs) with `n` pairs per array.
    fn slots(&self, n: usize) -> usize {
        self.array_positions.len() * n
    }

    /// Original argument position of the array probed by ghost slot `s`.
    fn array_position_of_slot(&self, s: usize, n: usize) -> Option<usize> {
        self.array_positions.get(s.checked_div(n)?).copied()
    }

    /// Index sort of ghost slot `s` when there are `n` pairs per array.
    fn index_sort_of_slot(&self, s: usize, n: usize) -> Option<&ChcSort> {
        self.index_sorts.get(s.checked_div(n)?)
    }

    /// Index sorts of all ghost slots in transformed argument order.
    fn slot_index_sorts(&self, n: usize) -> Vec<ChcSort> {
        self.index_sorts
            .iter()
            .flat_map(|sort| std::iter::repeat_n(sort.clone(), n))
            .collect()
    }
}

/// Ghost layout for a whole problem: which predicates carry ghosts and how.
///
/// Transformed argument layout for a predicate `p` in `preds`:
/// `orig_args ++ [idx_0, val_0, idx_1, val_1, ...]` with one `(idx, val)` pair
/// per slot, slots ordered by `(array_position, pair_index)`.
#[derive(Debug, Clone, Default)]
pub(crate) struct GhostPairSpec {
    /// Ghost pairs per array argument.
    n: usize,
    /// Per-predicate ghost layout. Predicates without supported-index array
    /// arguments are absent and keep their original signature.
    preds: FxHashMap<PredicateId, GhostPredSpec>,
}

impl GhostPairSpec {
    /// Compute the ghost layout for `problem` with `n` pairs per array arg.
    ///
    /// Only `(Array K V)` arguments with `K = Int | BitVec(1..=64)` and a
    /// non-array, non-datatype value sort are instrumented. Predicates whose
    /// ghost slot count would exceed [`MAX_SLOTS_PER_PREDICATE`] are left
    /// uninstrumented.
    pub(crate) fn analyze(problem: &ChcProblem, n: usize) -> Self {
        let n = n.max(1);
        let mut preds = FxHashMap::default();
        for pred in problem.predicates() {
            let arrays: Vec<(usize, ChcSort)> = pred
                .arg_sorts
                .iter()
                .enumerate()
                .filter_map(|(i, sort)| match sort {
                    ChcSort::Array(key, value)
                        if is_supported_index_sort(key)
                            && !matches!(
                                **value,
                                ChcSort::Array(_, _) | ChcSort::Datatype { .. }
                            ) =>
                    {
                        Some((i, (**key).clone()))
                    }
                    _ => None,
                })
                .collect();
            let (array_positions, index_sorts): (Vec<_>, Vec<_>) = arrays.into_iter().unzip();
            let Some(slot_count) = array_positions.len().checked_mul(n) else {
                continue;
            };
            if array_positions.is_empty() || slot_count > MAX_SLOTS_PER_PREDICATE {
                continue;
            }
            preds.insert(
                pred.id,
                GhostPredSpec {
                    original_arity: pred.arity(),
                    array_positions,
                    index_sorts,
                },
            );
        }
        Self { n, preds }
    }

    /// True when no predicate receives ghosts (transform would be identity).
    pub(crate) fn is_empty(&self) -> bool {
        self.preds.is_empty()
    }

    /// Extended argument sorts for predicate `pred_id` (original sorts plus
    /// one `(key_sort, value_sort)` pair per ghost slot).
    fn extended_sorts(&self, pred_id: PredicateId, orig_sorts: &[ChcSort]) -> Option<Vec<ChcSort>> {
        let Some(spec) = self.preds.get(&pred_id) else {
            return Some(orig_sorts.to_vec());
        };
        if orig_sorts.len() != spec.original_arity {
            return None;
        }
        let mut sorts = orig_sorts.to_vec();
        for (array_index, &pos) in spec.array_positions.iter().enumerate() {
            let expected_index_sort = spec.index_sorts.get(array_index)?;
            let (key_sort, value_sort) = match orig_sorts.get(pos) {
                Some(ChcSort::Array(key, value)) if key.as_ref() == expected_index_sort => {
                    ((**key).clone(), (**value).clone())
                }
                _ => return None,
            };
            for _ in 0..self.n {
                sorts.push(key_sort.clone());
                sorts.push(value_sort.clone());
            }
        }
        Some(sorts)
    }

    /// Extend a predicate application's arguments with ghost pairs probed at
    /// `idx_terms` (one per slot): `args ++ [t_s, select(arr_s, t_s), ...]`.
    fn extend_args(
        &self,
        pred_id: PredicateId,
        args: &[ChcExpr],
        idx_terms: &[ChcExpr],
    ) -> Option<Vec<ChcExpr>> {
        let Some(spec) = self.preds.get(&pred_id) else {
            return Some(args.to_vec());
        };
        if args.len() != spec.original_arity || idx_terms.len() != spec.slots(self.n) {
            return None;
        }
        let mut out = args.to_vec();
        for (s, idx) in idx_terms.iter().enumerate() {
            let array_pos = spec.array_position_of_slot(s, self.n)?;
            let expected_index_sort = spec.index_sort_of_slot(s, self.n)?;
            if &idx.sort() != expected_index_sort {
                return None;
            }
            let array = args.get(array_pos)?.clone();
            let ChcSort::Array(key_sort, _) = array.sort() else {
                return None;
            };
            if key_sort.as_ref() != expected_index_sort {
                return None;
            }
            out.push(idx.clone());
            out.push(ChcExpr::select(array, idx.clone()));
        }
        Some(out)
    }
}

fn is_supported_index_sort(sort: &ChcSort) -> bool {
    matches!(sort, ChcSort::Int | ChcSort::BitVec(1..=64))
}

/// Collect candidate trigger terms: the supported index expressions of every
/// `select`/`store` occurring in the clause (constraint + all atom arguments).
pub(crate) fn collect_index_terms(clause: &HornClause, cap: usize) -> Vec<ChcExpr> {
    let mut terms: Vec<ChcExpr> = Vec::new();
    let mut visit = |expr: &ChcExpr| {
        collect_index_terms_in(expr, &mut terms, cap);
    };
    for (_, args) in &clause.body.predicates {
        for arg in args {
            visit(arg);
        }
    }
    if let Some(constraint) = &clause.body.constraint {
        visit(constraint);
    }
    if let ClauseHead::Predicate(_, args) = &clause.head {
        for arg in args {
            visit(arg);
        }
    }
    terms
}

/// Whether any array access in this clause uses a supported, non-literal key.
/// This is an existential admission check, so it deliberately scans past the
/// bounded candidate vocabulary used later by the transformer.
pub(crate) fn clause_has_symbolic_index(clause: &HornClause) -> bool {
    let mut expressions: Vec<&ChcExpr> = Vec::new();
    if let Some(constraint) = &clause.body.constraint {
        expressions.push(constraint);
    }
    for (_, args) in &clause.body.predicates {
        expressions.extend(args);
    }
    if let ClauseHead::Predicate(_, args) = &clause.head {
        expressions.extend(args);
    }
    expressions.into_iter().any(expr_has_symbolic_index)
}

fn expr_has_symbolic_index(expr: &ChcExpr) -> bool {
    crate::expr::maybe_grow_expr_stack(|| {
        if let ChcExpr::Op(ChcOp::Select | ChcOp::Store, args) = expr {
            if let Some(index) = args.get(1).map(AsRef::as_ref) {
                if is_supported_index_sort(&index.sort())
                    && !matches!(index, ChcExpr::Int(_) | ChcExpr::BitVec(_, _))
                {
                    return true;
                }
            }
        }
        match expr {
            ChcExpr::Op(_, args)
            | ChcExpr::PredicateApp(_, _, args)
            | ChcExpr::FuncApp(_, _, args) => args.iter().any(|arg| expr_has_symbolic_index(arg)),
            ChcExpr::ConstArray(_, value) => expr_has_symbolic_index(value),
            _ => false,
        }
    })
}

fn collect_index_terms_in(expr: &ChcExpr, out: &mut Vec<ChcExpr>, cap: usize) {
    crate::expr::maybe_grow_expr_stack(|| {
        if cap == 0 {
            return;
        }
        if let ChcExpr::Op(op, args) = expr {
            let idx_arg = match op {
                ChcOp::Select | ChcOp::Store => args.get(1),
                _ => None,
            };
            if let Some(idx) = idx_arg {
                if is_supported_index_sort(&idx.sort()) {
                    push_index_term_fair(out, idx, cap);
                }
            }
        }
        match expr {
            ChcExpr::Op(_, args)
            | ChcExpr::PredicateApp(_, _, args)
            | ChcExpr::FuncApp(_, _, args) => {
                for arg in args {
                    collect_index_terms_in(arg, out, cap);
                }
            }
            ChcExpr::ConstArray(_, value) => collect_index_terms_in(value, out, cap),
            _ => {}
        }
    });
}

/// Keep the bounded trigger vocabulary sort-fair: a later key sort may replace
/// a duplicate from an earlier sort, but never the sole representative of one.
fn push_index_term_fair(out: &mut Vec<ChcExpr>, term: &ChcExpr, cap: usize) {
    if out.contains(term) {
        return;
    }
    if out.len() < cap {
        out.push(term.clone());
        return;
    }
    let term_sort = term.sort();
    if out.iter().any(|existing| existing.sort() == term_sort) {
        return;
    }
    let replace = (0..out.len()).rev().find(|&candidate| {
        let candidate_sort = out[candidate].sort();
        out.iter()
            .filter(|existing| existing.sort() == candidate_sort)
            .count()
            > 1
    });
    if let Some(replace) = replace {
        out[replace] = term.clone();
    }
}

/// Instantiation tuples for a body atom with typed ghost index slots.
///
/// Tuple sources, in priority order:
/// 1. the identity tuple (the head's fresh ghost variables, pass-through) when
///    the slot sorts line up — this is the frame/transition instantiation,
/// 2. a typed seed assembled from the first compatible trigger for each slot
///    (or a typed zero when none exists),
/// 3. per-slot replacements in that seed, which cover heterogeneous tuples of
///    arbitrary arity without an exponential Cartesian product,
/// 4. homogeneous diagonals and, for two slots, ordered pairs retained for
///    same-index and adjacent-index relations.
///
/// Any choice here is sound (see module docs); the set only affects which
/// invariants become expressible/provable.
pub(crate) fn instantiation_tuples(
    slot_sorts: &[ChcSort],
    fresh: &[ChcExpr],
    cands: &[ChcExpr],
    cap: usize,
) -> Vec<Vec<ChcExpr>> {
    if slot_sorts.is_empty() || cap == 0 {
        return Vec::new();
    }
    let mut tuples: Vec<Vec<ChcExpr>> = Vec::new();
    let push = |tuple: Vec<ChcExpr>, tuples: &mut Vec<Vec<ChcExpr>>| {
        if tuples.len() < cap && !tuples.contains(&tuple) {
            tuples.push(tuple);
        }
    };
    if tuple_has_sorts(fresh, slot_sorts) {
        push(fresh.to_vec(), &mut tuples);
    }

    // Clause triggers take precedence in the seed: the exact fresh tuple is
    // already retained above, while the seed should expose observed accesses.
    let sources: Vec<&ChcExpr> = cands.iter().chain(fresh.iter()).collect();
    let Some(seed): Option<Vec<ChcExpr>> = slot_sorts
        .iter()
        .map(|sort| {
            sources
                .iter()
                .find(|term| term.sort() == *sort)
                .map(|term| (**term).clone())
                .or_else(|| zero_index(sort))
        })
        .collect()
    else {
        return Vec::new();
    };
    push(seed.clone(), &mut tuples);

    // Reserve one distinct, type-compatible alternate for every slot before
    // spending the remaining cap on the wider trigger vocabulary.
    for (slot, sort) in slot_sorts.iter().enumerate() {
        let mut alternate = None;
        for term in &sources {
            if term.sort() == *sort && *term != &seed[slot] {
                alternate = Some(*term);
                break;
            }
        }
        let Some(term) = alternate else {
            continue;
        };
        let mut tuple = seed.clone();
        tuple[slot] = term.clone();
        push(tuple, &mut tuples);
    }

    // Vary one slot at a time around the fully typed seed. Iterating sources
    // first gives every compatible slot a bounded opportunity before moving
    // to the next trigger and avoids starving later slots of a shared sort.
    for term in &sources {
        for (slot, sort) in slot_sorts.iter().enumerate() {
            if term.sort() != *sort {
                continue;
            }
            let mut tuple = seed.clone();
            let Some(entry) = tuple.get_mut(slot) else {
                continue;
            };
            *entry = (**term).clone();
            push(tuple, &mut tuples);
        }
    }

    for t in &sources {
        if slot_sorts.iter().all(|sort| t.sort() == *sort) {
            push(vec![(**t).clone(); slot_sorts.len()], &mut tuples);
        }
    }
    if let [first_sort, second_sort] = slot_sorts {
        for a in &sources {
            if a.sort() != *first_sort {
                continue;
            }
            for b in &sources {
                if b.sort() == *second_sort && a != b {
                    push(vec![(**a).clone(), (**b).clone()], &mut tuples);
                }
            }
        }
    }
    tuples
}

fn tuple_has_sorts(tuple: &[ChcExpr], sorts: &[ChcSort]) -> bool {
    tuple.len() == sorts.len()
        && tuple
            .iter()
            .zip(sorts)
            .all(|(term, sort)| term.sort() == *sort)
}

fn zero_index(sort: &ChcSort) -> Option<ChcExpr> {
    match sort {
        ChcSort::Int => Some(ChcExpr::Int(0)),
        ChcSort::BitVec(width @ 1..=64) => Some(ChcExpr::BitVec(0, *width)),
        _ => None,
    }
}

/// Build the trigger tuple that a false-head property clause actually
/// observes for one body atom.
///
/// A diagonal tuple is insufficient for cross-array properties such as
/// `c[bc + 4*i] = a[ba + 4*i] + b[bb + 4*i]`, and for `n=2` it misses
/// adjacent-cell properties such as `a[k - 1] <= a[k]`. Trigger-based array
/// encodings instantiate each array slot at the select/store terms that refer
/// to that specific array argument. Slots without an observed access receive
/// a type-correct zero without discarding accesses observed in other slots.
fn observed_access_tuple(
    pred_spec: &GhostPredSpec,
    n: usize,
    atom_args: &[ChcExpr],
    constraint: &ChcExpr,
) -> Option<Vec<ChcExpr>> {
    let mut tuple = Vec::with_capacity(pred_spec.slots(n));
    for (array_index, &array_position) in pred_spec.array_positions.iter().enumerate() {
        let array = atom_args.get(array_position)?;
        let index_sort = pred_spec.index_sorts.get(array_index)?;
        let mut indices = Vec::new();
        collect_access_indices_for_array(
            constraint,
            array,
            index_sort,
            &mut indices,
            INDEX_TERM_CAP,
        );
        for slot in 0..n {
            tuple.push(
                indices
                    .get(slot)
                    .cloned()
                    .or_else(|| zero_index(index_sort))?,
            );
        }
    }
    Some(tuple)
}

fn collect_access_indices_for_array(
    expr: &ChcExpr,
    array: &ChcExpr,
    index_sort: &ChcSort,
    out: &mut Vec<ChcExpr>,
    cap: usize,
) {
    crate::expr::maybe_grow_expr_stack(|| {
        if out.len() >= cap {
            return;
        }
        if let ChcExpr::Op(op, args) = expr {
            if matches!(op, ChcOp::Select | ChcOp::Store)
                && args
                    .first()
                    .is_some_and(|candidate| candidate.as_ref() == array)
            {
                if let Some(index) = args.get(1).map(|index| index.as_ref()) {
                    if index.sort() == *index_sort && !out.contains(index) {
                        out.push(index.clone());
                    }
                }
            }
        }
        match expr {
            ChcExpr::Op(_, args)
            | ChcExpr::PredicateApp(_, _, args)
            | ChcExpr::FuncApp(_, _, args) => {
                for arg in args {
                    collect_access_indices_for_array(arg, array, index_sort, out, cap);
                }
            }
            ChcExpr::ConstArray(_, value) => {
                collect_access_indices_for_array(value, array, index_sort, out, cap);
            }
            _ => {}
        }
    });
}

/// Allocate one fresh variable of `sort` whose name collides with nothing in
/// `used` (which is extended with the new name).
fn fresh_var(prefix: &str, sort: ChcSort, used: &mut FxHashSet<String>) -> ChcVar {
    let mut counter = 0usize;
    loop {
        let name = format!("{prefix}{counter}");
        counter += 1;
        if used.contains(&name) {
            continue;
        }
        used.insert(name.clone());
        return ChcVar::new(name, sort);
    }
}

/// Allocate fresh variables of the requested sorts whose names collide with
/// nothing in `used` (which is extended with the new names).
pub(crate) fn fresh_index_vars(
    prefix: &str,
    sorts: &[ChcSort],
    used: &mut FxHashSet<String>,
) -> Vec<ChcVar> {
    let mut vars = Vec::with_capacity(sorts.len());
    let mut counter = 0usize;
    for sort in sorts {
        loop {
            let name = format!("{prefix}{counter}");
            counter += 1;
            if used.contains(&name) {
                continue;
            }
            used.insert(name.clone());
            vars.push(ChcVar::new(name, sort.clone()));
            break;
        }
    }
    vars
}

/// Reserve source UF symbols before allocating ghost variables. SMT-LIB uses
/// one term namespace for bound variables and nullary functions, so a fresh
/// ghost name must not shadow a source function application.
fn reserve_clause_function_names(clause: &HornClause, used: &mut FxHashSet<String>) -> Option<()> {
    let mut expressions = Vec::new();
    expressions.extend(clause.body.constraint.iter());
    expressions.extend(
        clause
            .body
            .predicates
            .iter()
            .flat_map(|(_, args)| args.iter()),
    );
    if let ClauseHead::Predicate(_, args) = &clause.head {
        expressions.extend(args);
    }
    let declarations = collect_uninterpreted_function_declarations_for_exprs(expressions).ok()?;
    used.extend(declarations.into_iter().map(|declaration| declaration.name));
    Some(())
}

/// Ghost index/value pair transformer (Eldarica `-arrayQuans:n` analog).
pub(crate) struct ArrayGhostPairTransformer {
    n: usize,
    verbose: bool,
}

impl ArrayGhostPairTransformer {
    pub(crate) fn new(n: usize) -> Self {
        Self {
            n: n.max(1),
            verbose: false,
        }
    }

    #[allow(dead_code)] // parity with sibling transformers' builder API
    pub(crate) fn with_verbose(mut self, verbose: bool) -> Self {
        self.verbose = verbose;
        self
    }

    fn rewrite_clause(&self, clause: &HornClause, spec: &GhostPairSpec) -> Option<HornClause> {
        let cands = collect_index_terms(clause, INDEX_TERM_CAP);
        let clause_vars = certify::exact_clause_vars(clause)?;
        let mut used: FxHashSet<String> = clause_vars.into_iter().map(|var| var.name).collect();
        reserve_clause_function_names(clause, &mut used)?;

        // Head: append fresh, implicitly-universal ghost probes. Head
        // arguments stay variables (`idx_s`, `val_s`); the semantic coupling
        // `val_s = select(arr, idx_s)` goes into the body constraint —
        // Eldarica's encoding, and friendlier to PDR's transition encoding
        // than select-expressions in head positions.
        let mut coupling: Vec<ChcExpr> = Vec::new();
        let (new_head, fresh_exprs) = match &clause.head {
            ClauseHead::Predicate(pred_id, args) => match spec.preds.get(pred_id) {
                Some(pred_spec) => {
                    if args.len() != pred_spec.original_arity {
                        return None;
                    }
                    let slot_sorts = pred_spec.slot_index_sorts(spec.n);
                    let fresh_idx = fresh_index_vars("__gpi", &slot_sorts, &mut used);
                    let fresh_exprs: Vec<ChcExpr> =
                        fresh_idx.iter().cloned().map(ChcExpr::var).collect();
                    let mut new_args = args.clone();
                    for (s, idx_expr) in fresh_exprs.iter().enumerate() {
                        let array_pos = pred_spec.array_position_of_slot(s, spec.n)?;
                        let array = args.get(array_pos)?.clone();
                        let ChcSort::Array(key_sort, value_sort) = array.sort() else {
                            return None;
                        };
                        if key_sort.as_ref() != pred_spec.index_sort_of_slot(s, spec.n)? {
                            return None;
                        }
                        let val_var = fresh_var("__gpv", *value_sort, &mut used);
                        coupling.push(ChcExpr::eq(
                            ChcExpr::var(val_var.clone()),
                            ChcExpr::select(array, idx_expr.clone()),
                        ));
                        new_args.push(idx_expr.clone());
                        new_args.push(ChcExpr::var(val_var));
                    }
                    (ClauseHead::Predicate(*pred_id, new_args), fresh_exprs)
                }
                None => (clause.head.clone(), Vec::new()),
            },
            ClauseHead::False => (ClauseHead::False, Vec::new()),
        };

        // Body: instantiate each ghost-carrying atom at exactly ONE tuple —
        // the pass-through tuple (the head's fresh ghost variables) when the
        // slot counts line up, otherwise the best typed trigger tuple. Emitting
        // multiple instantiated copies (Eldarica's encoding) would make the
        // clause NONLINEAR (several body atoms of the same predicate), which
        // this PDR core cannot push lemmas through — it stalls at frame 1.
        // A single instance keeps the clause linear; any instantiation choice
        // is sound (see module docs), and the richer multi-tuple instantiation
        // still runs on the CERTIFICATION side (certify.rs), where instances
        // are plain SMT conjuncts with no linearity constraint.
        let mut new_body_preds: Vec<(PredicateId, Vec<ChcExpr>)> = Vec::new();
        for (pred_id, args) in &clause.body.predicates {
            match spec.preds.get(pred_id) {
                Some(pred_spec) => {
                    let tuple = ghost_tuple_flow::preferred_body_ghost_indices(
                        clause,
                        spec,
                        pred_spec,
                        args,
                        &fresh_exprs,
                        &cands,
                    )?;
                    new_body_preds.push((*pred_id, spec.extend_args(*pred_id, args, &tuple)?));
                }
                None => new_body_preds.push((*pred_id, args.clone())),
            }
        }

        let new_constraint = if coupling.is_empty() {
            clause.body.constraint.clone()
        } else {
            let mut conjuncts = coupling;
            if let Some(constraint) = &clause.body.constraint {
                conjuncts.insert(0, constraint.clone());
            }
            Some(ChcExpr::and_all(conjuncts))
        };
        let mut new_clause =
            HornClause::new(ClauseBody::new(new_body_preds, new_constraint), new_head);
        new_clause.action_id = clause.action_id;
        Some(new_clause)
    }
}

impl Transformer for ArrayGhostPairTransformer {
    fn transform(self: Box<Self>, problem: ChcProblem) -> TransformationResult {
        let spec = GhostPairSpec::analyze(&problem, self.n);
        // Active datatype terms are outside this transform's semantic scope.
        // A declaration-only prelude is inert, however, and is common in
        // MODEL_CHECKER_CONSUMER output; preserving it must not suppress array ghosting.
        if spec.is_empty() || problem.uses_datatype_features() {
            return TransformationResult {
                problem,
                back_translator: Box::new(super::IdentityBackTranslator),
            };
        }

        let mut new_problem = ChcProblem::new();
        if problem.has_stripped_body_forall() {
            new_problem.mark_stripped_body_forall();
        }
        // Preserve the complete declaration tables before copying clauses:
        // action ids are positional, and later preprocessing/SMT contexts
        // expect even unused datatype prelude metadata to remain available.
        for name in problem.action_names() {
            new_problem.declare_action(name.clone());
        }
        for (name, constructors) in problem.datatype_defs() {
            new_problem.add_datatype_def(name.clone(), constructors.clone());
        }
        for pred in problem.predicates() {
            let Some(sorts) = spec.extended_sorts(pred.id, &pred.arg_sorts) else {
                return TransformationResult {
                    problem,
                    back_translator: Box::new(super::IdentityBackTranslator),
                };
            };
            let id = new_problem.declare_predicate(&pred.name, sorts);
            debug_assert_eq!(id, pred.id, "ghost transform must preserve predicate ids");
        }
        for clause in problem.clauses() {
            let Some(rewritten) = self.rewrite_clause(clause, &spec) else {
                return TransformationResult {
                    problem,
                    back_translator: Box::new(super::IdentityBackTranslator),
                };
            };
            new_problem.add_clause(rewritten);
        }
        if problem.is_fixedpoint_format() {
            new_problem.set_fixedpoint_format();
        }

        if self.verbose {
            tracing::info!(
                action = "ArrayGhostPairs",
                n = spec.n,
                instrumented_predicates = spec.preds.len(),
                "CHC: ghost-pair instrumentation added {} ghost pair(s) per array argument on {} predicate(s)",
                spec.n,
                spec.preds.len(),
            );
        }

        TransformationResult {
            problem: new_problem,
            back_translator: Box::new(ArrayGhostPairBackTranslator { spec }),
        }
    }
}

/// Back-translator for the ghost-pair transform.
pub(crate) struct ArrayGhostPairBackTranslator {
    spec: GhostPairSpec,
}

impl BackTranslator for ArrayGhostPairBackTranslator {
    fn translate_validity(&self, _witness: ValidityWitness) -> ValidityWitness {
        // The true back-translated model is `forall i. I'(args, i, arr[i])`,
        // which has NO quantifier-free `ChcExpr` representation. Returning an
        // empty model is fail-closed: an empty model never passes the final
        // Safe gates on its own. The ghost-pair route instead seals the
        // quantified model as a `GhostPairCertificate` (full per-rule
        // discharge on the ORIGINAL clauses) and attaches it to the model.
        InvariantModel::new()
    }

    fn translate_invalidity(&self, witness: InvalidityWitness) -> InvalidityWitness {
        // Drop ghost-argument assignments (canonical arg names beyond the
        // original arity); the derivation witness refers to transformed
        // clause shapes, so it is stripped. The route/finalize boundary
        // replays the trace against the ORIGINAL clauses before any Unsafe
        // verdict is exposed, so an imperfect translation can only demote to
        // unknown, never flip a verdict.
        let mut witness = witness;
        witness.witness = None;
        for step in &mut witness.steps {
            let Some(pred_spec) = self.spec.preds.get(&step.predicate) else {
                continue;
            };
            let ghost_names: Vec<String> = (pred_spec.original_arity
                ..pred_spec.original_arity + 2 * pred_spec.slots(self.spec.n))
                .map(|j| format!("__p{}_a{}", step.predicate.index(), j))
                .collect();
            for name in ghost_names {
                step.assignments.remove(&name);
            }
        }
        witness
    }

    fn transform_memory(&self) -> TransformMemoryReport {
        TransformMemoryReport::with_original_validation_obligations(
            "array_ghost_pairs",
            Vec::<super::TransformObligation>::new(),
        )
        .with_fact("ghost_pairs_per_array", self.spec.n.to_string())
        .with_fact("instrumented_predicates", self.spec.preds.len().to_string())
    }
}

#[allow(clippy::unwrap_used, clippy::panic)]
#[cfg(test)]
#[path = "tests.rs"]
mod tests;
