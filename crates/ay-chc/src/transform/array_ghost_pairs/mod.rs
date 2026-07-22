// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Eldarica-style ghost index/value pairs for quantified array invariants
//! (CHC-COMP agenda item #16, FORALL-ARR ghost-pair prong).
//!
//! # Idea
//!
//! For every predicate argument of sort `(Array Int V)`, append `n` ghost
//! scalar pairs `(idx_k : Int, val_k : V)` to the predicate signature. The
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

mod certify;

use crate::{
    ChcExpr, ChcOp, ChcProblem, ChcSort, ChcVar, ClauseBody, ClauseHead, HornClause,
    InvariantModel, PredicateId,
};
use ay_core::kani_compat::DetHashMap as FxHashMap;
use ay_core::kani_compat::DetHashSet as FxHashSet;

use super::{
    BackTranslator, InvalidityWitness, TransformMemoryReport, TransformationResult, Transformer,
    ValidityWitness,
};

pub(crate) use certify::{
    ghost_pair_replay_obligations, recheck_ghost_pair_certificate, GhostPairCertificate,
};

/// Maximum number of instantiated copies of one body atom.
const BODY_INSTANCE_CAP: usize = 8;

/// Maximum number of clause index terms considered as triggers.
const INDEX_TERM_CAP: usize = 6;

/// Maximum ghost slots (index/value pairs) added to a single predicate.
const MAX_SLOTS_PER_PREDICATE: usize = 4;

/// Ghost layout for one predicate.
#[derive(Debug, Clone)]
pub(crate) struct GhostPredSpec {
    /// Arity of the predicate BEFORE ghost extension.
    pub(crate) original_arity: usize,
    /// Positions (into the original argument list) of `(Array Int V)`
    /// arguments that received ghost pairs, in ascending order.
    pub(crate) array_positions: Vec<usize>,
}

impl GhostPredSpec {
    /// Number of ghost slots (index/value pairs) with `n` pairs per array.
    pub(crate) fn slots(&self, n: usize) -> usize {
        self.array_positions.len() * n
    }

    /// Original argument position of the array probed by ghost slot `s`.
    pub(crate) fn array_position_of_slot(&self, s: usize, n: usize) -> usize {
        self.array_positions[s / n]
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
    pub(crate) n: usize,
    /// Per-predicate ghost layout. Predicates without Int-indexed array
    /// arguments are absent and keep their original signature.
    pub(crate) preds: FxHashMap<PredicateId, GhostPredSpec>,
}

impl GhostPairSpec {
    /// Compute the ghost layout for `problem` with `n` pairs per array arg.
    ///
    /// Only `(Array Int V)` arguments with a non-array, non-datatype value
    /// sort are instrumented. Predicates whose ghost slot count would exceed
    /// [`MAX_SLOTS_PER_PREDICATE`] are left uninstrumented.
    pub(crate) fn analyze(problem: &ChcProblem, n: usize) -> Self {
        let mut preds = FxHashMap::default();
        for pred in problem.predicates() {
            let array_positions: Vec<usize> = pred
                .arg_sorts
                .iter()
                .enumerate()
                .filter_map(|(i, sort)| match sort {
                    ChcSort::Array(key, value)
                        if **key == ChcSort::Int
                            && !matches!(
                                **value,
                                ChcSort::Array(_, _) | ChcSort::Datatype { .. }
                            ) =>
                    {
                        Some(i)
                    }
                    _ => None,
                })
                .collect();
            if array_positions.is_empty() || array_positions.len() * n > MAX_SLOTS_PER_PREDICATE {
                continue;
            }
            preds.insert(
                pred.id,
                GhostPredSpec {
                    original_arity: pred.arity(),
                    array_positions,
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
    /// one `(Int, value_sort)` pair per ghost slot).
    fn extended_sorts(&self, pred_id: PredicateId, orig_sorts: &[ChcSort]) -> Vec<ChcSort> {
        let Some(spec) = self.preds.get(&pred_id) else {
            return orig_sorts.to_vec();
        };
        let mut sorts = orig_sorts.to_vec();
        for &pos in &spec.array_positions {
            let value_sort = match &orig_sorts[pos] {
                ChcSort::Array(_, value) => (**value).clone(),
                // analyze() only records Array positions.
                other => other.clone(),
            };
            for _ in 0..self.n {
                sorts.push(ChcSort::Int);
                sorts.push(value_sort.clone());
            }
        }
        sorts
    }

    /// Extend a predicate application's arguments with ghost pairs probed at
    /// `idx_terms` (one per slot): `args ++ [t_s, select(arr_s, t_s), ...]`.
    fn extend_args(
        &self,
        pred_id: PredicateId,
        args: &[ChcExpr],
        idx_terms: &[ChcExpr],
    ) -> Vec<ChcExpr> {
        let Some(spec) = self.preds.get(&pred_id) else {
            return args.to_vec();
        };
        debug_assert_eq!(idx_terms.len(), spec.slots(self.n));
        let mut out = args.to_vec();
        for (s, idx) in idx_terms.iter().enumerate() {
            let array_pos = spec.array_position_of_slot(s, self.n);
            out.push(idx.clone());
            out.push(ChcExpr::select(args[array_pos].clone(), idx.clone()));
        }
        out
    }
}

/// Collect candidate trigger terms: the Int-sorted index expressions of every
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

fn collect_index_terms_in(expr: &ChcExpr, out: &mut Vec<ChcExpr>, cap: usize) {
    crate::expr::maybe_grow_expr_stack(|| {
        if out.len() >= cap {
            return;
        }
        if let ChcExpr::Op(op, args) = expr {
            let idx_arg = match op {
                ChcOp::Select | ChcOp::Store => args.get(1),
                _ => None,
            };
            if let Some(idx) = idx_arg {
                if idx.sort() == ChcSort::Int && !out.iter().any(|t| t == idx.as_ref()) {
                    out.push(idx.as_ref().clone());
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

/// Instantiation tuples for a body atom with `slots` ghost index slots.
///
/// Tuple sources, in priority order:
/// 1. the identity tuple (the head's fresh ghost variables, pass-through) when
///    the slot counts line up — this is the frame/transition instantiation,
/// 2. diagonal tuples `[t, t, ..]` for each fresh head ghost and each clause
///    index term — the "same cell in every probe" instantiation,
/// 3. for `slots == 2`, ordered pairs of distinct candidates — needed to relate
///    two probes at different indices (copy with offsets, sortedness, n=2).
///
/// Any choice here is sound (see module docs); the set only affects which
/// invariants become expressible/provable.
pub(crate) fn instantiation_tuples(
    slots: usize,
    fresh: &[ChcExpr],
    cands: &[ChcExpr],
    cap: usize,
) -> Vec<Vec<ChcExpr>> {
    if slots == 0 {
        return Vec::new();
    }
    let mut tuples: Vec<Vec<ChcExpr>> = Vec::new();
    let push = |tuple: Vec<ChcExpr>, tuples: &mut Vec<Vec<ChcExpr>>| {
        if tuples.len() < cap && !tuples.contains(&tuple) {
            tuples.push(tuple);
        }
    };
    if fresh.len() == slots {
        push(fresh.to_vec(), &mut tuples);
    }
    for t in fresh.iter().chain(cands.iter()) {
        push(vec![t.clone(); slots], &mut tuples);
    }
    if slots == 2 {
        let pool: Vec<&ChcExpr> = fresh.iter().chain(cands.iter()).collect();
        for a in &pool {
            for b in &pool {
                if a != b {
                    push(vec![(*a).clone(), (*b).clone()], &mut tuples);
                }
            }
        }
    }
    if tuples.is_empty() {
        // No triggers at all in this clause: probe an arbitrary constant cell.
        tuples.push(vec![ChcExpr::Int(0); slots]);
    }
    tuples
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

/// Allocate `count` fresh Int variables whose names collide with nothing in
/// `used` (which is extended with the new names).
pub(crate) fn fresh_int_vars(
    prefix: &str,
    count: usize,
    used: &mut FxHashSet<String>,
) -> Vec<ChcVar> {
    let mut vars = Vec::with_capacity(count);
    let mut counter = 0usize;
    while vars.len() < count {
        let name = format!("{prefix}{counter}");
        counter += 1;
        if used.contains(&name) {
            continue;
        }
        used.insert(name.clone());
        vars.push(ChcVar::new(name, ChcSort::Int));
    }
    vars
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

    fn rewrite_clause(&self, clause: &HornClause, spec: &GhostPairSpec) -> HornClause {
        let cands = collect_index_terms(clause, INDEX_TERM_CAP);
        let mut used: FxHashSet<String> = clause.vars().into_iter().map(|v| v.name).collect();

        // Head: append fresh, implicitly-universal ghost probes. Head
        // arguments stay variables (`idx_s`, `val_s`); the semantic coupling
        // `val_s = select(arr, idx_s)` goes into the body constraint —
        // Eldarica's encoding, and friendlier to PDR's transition encoding
        // than select-expressions in head positions.
        let mut coupling: Vec<ChcExpr> = Vec::new();
        let (new_head, fresh_exprs) = match &clause.head {
            ClauseHead::Predicate(pred_id, args) => match spec.preds.get(pred_id) {
                Some(pred_spec) => {
                    let slots = pred_spec.slots(spec.n);
                    let fresh_idx = fresh_int_vars("__gpi", slots, &mut used);
                    let fresh_exprs: Vec<ChcExpr> =
                        fresh_idx.iter().cloned().map(ChcExpr::var).collect();
                    let mut new_args = args.clone();
                    for (s, idx_expr) in fresh_exprs.iter().enumerate() {
                        let array_pos = pred_spec.array_position_of_slot(s, spec.n);
                        let value_sort = match args[array_pos].sort() {
                            ChcSort::Array(_, value) => *value,
                            other => other,
                        };
                        let val_var = fresh_var("__gpv", value_sort, &mut used);
                        coupling.push(ChcExpr::eq(
                            ChcExpr::var(val_var.clone()),
                            ChcExpr::select(args[array_pos].clone(), idx_expr.clone()),
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
        // slot counts line up, otherwise the best trigger diagonal. Emitting
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
                    let tuples = instantiation_tuples(
                        pred_spec.slots(spec.n),
                        &fresh_exprs,
                        &cands,
                        BODY_INSTANCE_CAP,
                    );
                    // instantiation_tuples orders the pass-through tuple first
                    // when available and never returns an empty set.
                    if let Some(tuple) = tuples.first() {
                        new_body_preds.push((*pred_id, spec.extend_args(*pred_id, args, tuple)));
                    }
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
        new_clause
    }
}

impl Transformer for ArrayGhostPairTransformer {
    fn transform(self: Box<Self>, problem: ChcProblem) -> TransformationResult {
        let spec = GhostPairSpec::analyze(&problem, self.n);
        // Datatype metadata is not carried over by the rebuild below; ghost
        // instrumentation is gated to datatype-free problems by the route.
        if spec.is_empty() || !problem.datatype_defs().is_empty() {
            return TransformationResult {
                problem,
                back_translator: Box::new(super::IdentityBackTranslator),
            };
        }

        let mut new_problem = ChcProblem::new();
        for pred in problem.predicates() {
            let id = new_problem
                .declare_predicate(&pred.name, spec.extended_sorts(pred.id, &pred.arg_sorts));
            debug_assert_eq!(id, pred.id, "ghost transform must preserve predicate ids");
        }
        for clause in problem.clauses() {
            new_problem.add_clause(self.rewrite_clause(clause, &spec));
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
