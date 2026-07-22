// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Array-content invariant synthesis.
//!
//! Two layers, each independently gated and sound:
//!
//! * **Increment 0 — frontier extraction + telemetry** (flag
//!   `AY_CHC_ARRAY_FRONTIER_TELEMETRY`, default OFF). Computes the per-predicate
//!   *index-term frontier* `T(pred)` and counts `>= 2`-array predicates. Emits
//!   nothing into frames; pure analysis. See spec §6 "Increment 0".
//! * **Increment 1 — single-array value-fact candidates** (flag `AY_CHC_ARRAY_INV`,
//!   default OFF). Turns the frontier into actual invariant *candidates* of the form
//!   `select(a, t) >= 0`, `select(a, t) = 0`, and (for `Bool`-element arrays)
//!   `(= (select a t) true/false)`, and feeds each to the **existing, unchanged**
//!   `add_discovered_invariant` admission gate. See spec §6 "Increment 1".
//!
//! ## Why this is sound by construction
//!
//! PDR today cannot synthesize any fact about array *contents* for predicates with
//! `>= 2` array-sorted parameters, so those problems return `Unknown`. Increment 1
//! does **not** weaken, bypass, or modify the admission/inductiveness pipeline — it
//! is *purely an additional candidate source*. Every synthesized atom is a
//! Bool-sorted, `select`-based formula (never an array-sorted equality), so it
//! passes the admission gate's array filters *legitimately* (admission.rs lines
//! 36/54), and is then subject — exactly like every LIA candidate — to init-validity,
//! entry-/self-inductiveness, the SCC-joint check, and the executor false-UNSAT
//! cross-check. A candidate that is not actually inductive is **rejected**, never
//! admitted as a false proof.
//!
//! ## Cost / behavior gates
//!
//! * Increment-0 telemetry is gated on `AY_CHC_ARRAY_FRONTIER_TELEMETRY`.
//! * Increment-1 candidate emission is gated on `AY_CHC_ARRAY_INV`. When that flag
//!   is OFF (the default, and the hot path) `discover_array_content_invariants`
//!   returns immediately after one cheap boolean check, proposing nothing — so the
//!   default solver verdict is **byte-for-byte unchanged** (still `Unknown` on the
//!   multi-array cases it cannot yet handle).
//! * Increment-1 is additionally cost-gated on `max_array_params >= 2` (the spec's
//!   dominant-UNKNOWN target) and budget-bounded.
//!
//! Frontier extraction itself ([`PdrSolver::index_term_frontier`]) is a pure
//! function with no side effects, callable from tests regardless of any flag.

use super::super::PdrSolver;
use crate::{ChcExpr, ChcOp, ChcSort, ChcVar, PredicateId};
use std::sync::OnceLock;
use std::time::Duration;

/// Upper bound on `|T(pred)|`. Matches the spec's `MAX_INDEX_TERMS` (§3.1: "start
/// at 4"). Keeps later increments' instantiation set — and this increment's
/// telemetry — small and decidable.
pub(in crate::pdr::solver) const MAX_INDEX_TERMS: usize = 4;

/// One array-sorted predicate parameter: its canonical position, its canonical
/// variable, and its element (value) sort.
///
/// Mirrors the spec's `ArrayParam` (§3.5). Used to enumerate compatible array
/// pairs and (in later increments) to build `select(var, t)` atoms.
#[derive(Debug, Clone)]
pub(in crate::pdr::solver) struct ArrayParam {
    /// Position of this parameter in the predicate's argument list.
    pub(in crate::pdr::solver) pos: usize,
    /// Canonical variable (`__p{pred}_a{pos}`) for this parameter.
    pub(in crate::pdr::solver) var: ChcVar,
    /// Element/value sort of the array (the `V` in `(Array K V)`).
    pub(in crate::pdr::solver) elem_sort: ChcSort,
}

/// A finite set of index terms used to instantiate array-content invariants for
/// one predicate.
///
/// All terms are expressed over the predicate's canonical vars (or are constants),
/// so they are legal to embed inside that predicate's frame invariant. Deduped
/// structurally; capped at [`MAX_INDEX_TERMS`].
///
/// Mirrors the spec's `IndexTermFrontier` (§3.5). In Increment 0 this is produced
/// and counted but never turned into a candidate atom.
#[derive(Debug, Clone, Default)]
pub(in crate::pdr::solver) struct IndexTermFrontier {
    /// `|terms| <= MAX_INDEX_TERMS`, structurally deduped.
    pub(in crate::pdr::solver) terms: Vec<ChcExpr>,
}

impl IndexTermFrontier {
    /// Push `term` if it is not already present (structural dedup) and the cap is
    /// not yet reached. Returns `true` if the term was added.
    fn try_push(&mut self, term: ChcExpr) -> bool {
        if self.terms.len() >= MAX_INDEX_TERMS {
            return false;
        }
        if self.terms.contains(&term) {
            return false;
        }
        self.terms.push(term);
        true
    }

    /// Whether the frontier collected any index term.
    pub(in crate::pdr::solver) fn is_empty(&self) -> bool {
        self.terms.is_empty()
    }

    /// Number of index terms collected.
    pub(in crate::pdr::solver) fn len(&self) -> usize {
        self.terms.len()
    }
}

/// Whether the array-frontier telemetry pass is enabled.
///
/// Reads `AY_CHC_ARRAY_FRONTIER_TELEMETRY` exactly once. The pass is **OFF** by
/// default; only an explicit truthy value (`1`, `true`, `yes`, `on`,
/// case-insensitive) enables it. Everything else — unset, empty, `0`, `false` —
/// keeps it off so the hot path is untouched.
pub(in crate::pdr::solver) fn array_frontier_telemetry_enabled() -> bool {
    static ENABLED: OnceLock<bool> = OnceLock::new();
    *ENABLED.get_or_init(|| {
        array_frontier_telemetry_enabled_for(
            std::env::var("AY_CHC_ARRAY_FRONTIER_TELEMETRY")
                .ok()
                .as_deref(),
        )
    })
}

/// Testable core of the flag parse: only explicit truthy values enable.
fn array_frontier_telemetry_enabled_for(value: Option<&str>) -> bool {
    matches!(
        value.map(str::trim).map(str::to_ascii_lowercase).as_deref(),
        Some("1" | "true" | "yes" | "on")
    )
}

/// Budget for the Increment-1 candidate-emission pass. Mirrors the spec's
/// `array_content_pass_timeout` (§3.6: "default 750ms"). Each candidate still goes
/// through the (independently bounded) admission gate; this only caps the pass's
/// own wall-clock so a wide problem cannot starve the rest of startup discovery.
const ARRAY_CONTENT_PASS_TIMEOUT: Duration = Duration::from_millis(750);

/// Whether the Increment-1 array-content invariant *candidate emission* pass is
/// enabled.
///
/// Reads `AY_CHC_ARRAY_INV` exactly once. The pass is **OFF** by default; only an
/// explicit truthy value (`1`, `true`, `yes`, `on`, case-insensitive) enables it.
/// Everything else — unset, empty, `0`, `false` — keeps it off so the default path
/// is byte-for-byte unchanged (still `Unknown` on the multi-array cases it targets).
///
/// This intentionally mirrors the Increment-0 telemetry flag plumbing
/// ([`array_frontier_telemetry_enabled`]); the two flags are independent so the
/// pure-analysis telemetry can stay enabled without emitting any candidate.
pub(in crate::pdr::solver) fn array_content_invariants_enabled() -> bool {
    static ENABLED: OnceLock<bool> = OnceLock::new();
    *ENABLED.get_or_init(|| {
        array_content_invariants_enabled_for(std::env::var("AY_CHC_ARRAY_INV").ok().as_deref())
    })
}

/// Testable core of the `AY_CHC_ARRAY_INV` flag parse: only explicit truthy values
/// enable. Shares the exact acceptance set with the telemetry flag.
fn array_content_invariants_enabled_for(value: Option<&str>) -> bool {
    matches!(
        value.map(str::trim).map(str::to_ascii_lowercase).as_deref(),
        Some("1" | "true" | "yes" | "on")
    )
}

impl PdrSolver {
    /// Collect the array-sorted canonical parameters of `pred`.
    ///
    /// Pure analysis; no side effects. Returns one [`ArrayParam`] per
    /// `(Array K V)`-sorted canonical variable, in parameter order.
    pub(in crate::pdr::solver) fn array_canonical_params(
        &self,
        pred: PredicateId,
    ) -> Vec<ArrayParam> {
        let mut params = Vec::new();
        let canonical_vars = match self.canonical_vars(pred) {
            Some(v) => v,
            None => return params,
        };
        for (pos, var) in canonical_vars.iter().enumerate() {
            if let ChcSort::Array(_key, val) = &var.sort {
                params.push(ArrayParam {
                    pos,
                    var: var.clone(),
                    elem_sort: (**val).clone(),
                });
            }
        }
        params
    }

    /// Compute the **index-term frontier** `T(pred)` for one predicate (spec §3.1).
    ///
    /// A finite, structurally-deduped set of cheap, syntactic index terms that are
    /// likely the relevant points of an array invariant. Sources, in priority
    /// order (the cap means earlier sources win):
    ///
    /// 1. **Constant `0`** — the dominant base index for heaps/Vecs.
    /// 2. **Property indices** — concrete indices appearing in `select(arr, idx)`
    ///    inside query clauses, reused verbatim from
    ///    [`crate::pdr::solver::blocking::PropertyArrayIndices`].
    /// 3. **Store/select indices in defining clauses** — every `idx` in
    ///    `store(_, idx, _)` / `select(_, idx)` across clauses defining `pred`,
    ///    translated from clause-local body args onto `pred`'s canonical vars so
    ///    the term is expressible in the frame invariant. Terms that cannot be so
    ///    translated (mention non-canonical locals) are dropped.
    /// 4. **Scalar canonical vars** of `Int`/`BitVec` sort — bare `i`, `n`, `p`.
    ///
    /// This is a **pure** function: it reads the problem and returns a frontier,
    /// with no mutation and no frame emission. It is the analysis core that
    /// Increment 0 ships; later increments consume `T` to build candidate atoms.
    pub(in crate::pdr::solver) fn index_term_frontier(
        &self,
        pred: PredicateId,
    ) -> IndexTermFrontier {
        let mut frontier = IndexTermFrontier::default();

        // (4 in the cap sense lives last, but constant 0 is the cheapest, highest-
        // value base index, so it is admitted first.)
        let _ = frontier.try_push(ChcExpr::Int(0));

        // Source 2: property indices (already concrete ChcExprs from the query).
        let array_params = self.array_canonical_params(pred);
        for ap in &array_params {
            for idx in self.property_array_indices.indices_for(pred, ap.pos) {
                if frontier.terms.len() >= MAX_INDEX_TERMS {
                    break;
                }
                let _ = frontier.try_push(idx.clone());
            }
        }

        // Source 3: store/select indices in defining clauses, translated to
        // canonical vars (dropped if not expressible over them).
        if frontier.terms.len() < MAX_INDEX_TERMS {
            for term in self.collect_canonical_store_select_indices(pred) {
                if frontier.terms.len() >= MAX_INDEX_TERMS {
                    break;
                }
                let _ = frontier.try_push(term);
            }
        }

        // Source 4: scalar (Int/BV) canonical vars as candidate indices.
        if frontier.terms.len() < MAX_INDEX_TERMS {
            if let Some(canonical_vars) = self.canonical_vars(pred) {
                for var in canonical_vars {
                    if frontier.terms.len() >= MAX_INDEX_TERMS {
                        break;
                    }
                    if matches!(var.sort, ChcSort::Int | ChcSort::BitVec(_)) {
                        let _ = frontier.try_push(ChcExpr::var(var.clone()));
                    }
                }
            }
        }

        frontier
    }

    /// **Increment-1 candidate generator.** Synthesize single-array value-fact
    /// candidates from the index-term frontier and feed them to the *existing,
    /// unchanged* admission gate.
    ///
    /// For every predicate with `>= 2` array-sorted canonical parameters, for every
    /// array param `a`, and every index term `t` in `T(pred)`, propose the
    /// element-sort-appropriate value facts (see [`Self::array_value_fact_candidates`]):
    ///
    /// * `Int` element: `select(a, t) >= 0` and `select(a, t) = 0`,
    /// * `Bool` element: `(= (select a t) true)` and `(= (select a t) false)`.
    ///
    /// Each candidate is handed to [`PdrSolver::add_discovered_invariant`] — the same
    /// gate every LIA candidate clears (init-validity, entry-/self-inductiveness,
    /// SCC-joint, executor false-UNSAT cross-check). **Nothing here weakens or
    /// bypasses that gate**; a non-inductive candidate is simply rejected.
    ///
    /// Fully gated:
    /// * returns immediately when `AY_CHC_ARRAY_INV` is not explicitly truthy
    ///   (default OFF ⇒ no candidates ⇒ default verdict unchanged),
    /// * skips predicates with `< 2` array params (cost gate, spec §3.2),
    /// * stops on cancellation or once the pass budget is spent.
    ///
    /// Returns the number of candidates that the gate *admitted* into a frame.
    pub(in crate::pdr::solver) fn discover_array_content_invariants(&mut self) -> usize {
        // Cheap flag check first: default-OFF keeps the hot path (and the default
        // verdict) byte-for-byte unchanged.
        if !array_content_invariants_enabled() {
            return 0;
        }
        self.discover_array_content_invariants_inner()
    }

    /// Flag-independent core of [`Self::discover_array_content_invariants`].
    ///
    /// Split out so unit tests can exercise the candidate-generation + admission
    /// path deterministically without depending on the process-global
    /// `AY_CHC_ARRAY_INV` `OnceLock`. The production entry point above is the only
    /// non-test caller and always guards this behind the flag, so the default path
    /// is byte-for-byte unchanged.
    pub(in crate::pdr::solver) fn discover_array_content_invariants_inner(&mut self) -> usize {
        if !self.uses_arrays {
            return 0;
        }
        // Cost gate: the dominant-UNKNOWN target is >=2 array params (spec §3.2).
        if self.max_array_params < 2 {
            return 0;
        }

        let deadline = ay_core::time::Instant::now() + ARRAY_CONTENT_PASS_TIMEOUT;
        let predicates: Vec<PredicateId> = self.problem.predicates().iter().map(|p| p.id).collect();

        let mut admitted = 0usize;
        let mut proposed = 0usize;

        for pred in predicates {
            let arrays = self.array_canonical_params(pred);
            if arrays.len() < 2 {
                continue;
            }
            let frontier = self.index_term_frontier(pred);
            if frontier.is_empty() {
                continue;
            }

            // Enumerate (array param, index term) candidate atoms.
            let mut candidates: Vec<ChcExpr> = Vec::new();
            for ap in &arrays {
                for t in &frontier.terms {
                    // An index term that itself mentions an array sort is not a
                    // legal index; the frontier never produces those, but guard
                    // anyway so a future frontier source cannot break this.
                    if expr_has_array_sort(t) {
                        continue;
                    }
                    array_value_fact_candidates(&ap.var, &ap.elem_sort, t, &mut candidates);
                }
            }
            proposed += candidates.len();

            for cand in candidates {
                if self.is_cancelled() || ay_core::time::Instant::now() >= deadline {
                    if self.config.verbose {
                        safe_eprintln!(
                            "PDR: array-content: stopping (cancelled/budget) after {} admitted of {} proposed",
                            admitted,
                            proposed
                        );
                    }
                    return admitted;
                }
                // The UNCHANGED admission gate. Soundness lives here, not in this pass.
                if self.add_discovered_invariant(pred, cand.clone(), 1) {
                    admitted += 1;
                    if self.config.verbose {
                        safe_eprintln!(
                            "PDR: array-content: ADMITTED inductive array value fact for pred {}: {}",
                            pred.index(),
                            cand
                        );
                    }
                }
            }
        }

        if self.config.verbose && proposed > 0 {
            safe_eprintln!(
                "PDR: array-content (Increment 1): {} candidate(s) proposed, {} admitted by the unchanged inductiveness gate",
                proposed,
                admitted
            );
        }

        admitted
    }

    /// Collect `store(_, idx, _)` / `select(_, idx)` index terms from every clause
    /// defining `pred`, translated from clause-local vars onto `pred`'s canonical
    /// vars. Terms not expressible over canonical vars (or over constants) are
    /// dropped, since they could not legally appear in `pred`'s frame invariant.
    fn collect_canonical_store_select_indices(&self, pred: PredicateId) -> Vec<ChcExpr> {
        let mut out: Vec<ChcExpr> = Vec::new();

        let canonical_vars = match self.canonical_vars(pred) {
            Some(v) => v,
            None => return out,
        };

        for clause in self.problem.clauses_defining(pred) {
            let constraint = match &clause.body.constraint {
                Some(c) => c,
                None => continue,
            };

            // Build a clause-local -> canonical substitution from the *head*
            // application of `pred` (head args occupy the canonical positions).
            let head_args = match &clause.head {
                crate::ClauseHead::Predicate(pid, args) if *pid == pred => args.as_slice(),
                _ => continue,
            };
            if head_args.len() != canonical_vars.len() {
                continue;
            }
            let mut subst: Vec<(ChcVar, ChcExpr)> = Vec::new();
            for (arg, canon) in head_args.iter().zip(canonical_vars.iter()) {
                if let ChcExpr::Var(v) = arg {
                    subst.push((v.clone(), ChcExpr::var(canon.clone())));
                }
            }

            let mut raw_indices: Vec<ChcExpr> = Vec::new();
            collect_array_index_terms(constraint, &mut raw_indices);

            // Allowed variable names in a translated term: the canonical vars.
            for idx in raw_indices {
                let translated = if subst.is_empty() {
                    idx.clone()
                } else {
                    idx.substitute(&subst)
                };
                if !expr_mentions_only_canonical(&translated, canonical_vars) {
                    continue;
                }
                if !out.contains(&translated) {
                    out.push(translated);
                }
            }
        }

        out
    }

    /// **Increment 0 telemetry pass.** Counts predicates with `>= 2` array params
    /// and (when verbose/telemetry-enabled) reports the per-predicate frontier.
    ///
    /// This emits **nothing** into any frame and proposes **no** invariant
    /// candidate — it is strict, no-behavior-change instrumentation. It is fully
    /// gated: when `AY_CHC_ARRAY_FRONTIER_TELEMETRY` is not explicitly truthy it
    /// returns `0` immediately, doing no frontier extraction. Returns the number of
    /// predicates with `>= 2` array params seen.
    pub(in crate::pdr::solver) fn run_array_frontier_telemetry(&self) -> usize {
        // Cheap flag check first: the default-OFF gate keeps the hot path untouched.
        if !array_frontier_telemetry_enabled() {
            return 0;
        }
        // Skip entirely on problems with no array sorts at all.
        if !self.uses_arrays {
            return 0;
        }

        let predicates: Vec<PredicateId> = self.problem.predicates().iter().map(|p| p.id).collect();

        let mut multi_array_predicates = 0usize;
        let mut total_frontier_terms = 0usize;

        for pred in predicates {
            let array_params = self.array_canonical_params(pred);
            if array_params.len() < 2 {
                continue;
            }
            multi_array_predicates += 1;

            let frontier = self.index_term_frontier(pred);
            total_frontier_terms += frontier.len();

            if self.config.verbose {
                safe_eprintln!(
                    "PDR: array-frontier: pred {} has {} array params, frontier |T|={} terms={:?}",
                    pred.index(),
                    array_params.len(),
                    frontier.len(),
                    frontier.terms,
                );
            }
        }

        if self.config.verbose && multi_array_predicates > 0 {
            safe_eprintln!(
                "PDR: array-frontier: {} predicate(s) with >=2 array params, {} total frontier index terms (telemetry only; no frames emitted)",
                multi_array_predicates,
                total_frontier_terms,
            );
        }

        multi_array_predicates
    }
}

/// Build the Increment-1 single-array value-fact candidate atoms for one array
/// parameter `arr` (with element sort `elem_sort`) at one index term `t`,
/// appending them to `out`.
///
/// Every produced atom is a **Bool-sorted, `select`-based** formula and is **not**
/// an array-sorted equality — i.e. it passes the admission gate's array filters
/// (admission.rs lines 36/54) legitimately, so the gate's inductiveness checks (not
/// a relaxed gate) decide admission. The shapes, by element sort:
///
/// * `Int`  → `select(arr, t) >= 0` and `select(arr, t) = 0` (the dominant
///   heap/Vec non-negativity / zero-init class).
/// * `Bool` → `(= (select arr t) true)` and `(= (select arr t) false)` (validity-
///   flag heaps; the `select` result is `Bool`-sorted so the `=` is Bool-sorted at
///   top level and never an *array*-sorted equality).
///
/// Other element sorts (BitVec, Real, datatypes, nested arrays) emit nothing in
/// Increment 1 — keeping the candidate stream small and the pass cheap. Adding
/// those is a later increment; their absence only loses completeness, never
/// soundness.
fn array_value_fact_candidates(
    arr: &ChcVar,
    elem_sort: &ChcSort,
    t: &ChcExpr,
    out: &mut Vec<ChcExpr>,
) {
    let sel = || ChcExpr::select(ChcExpr::var(arr.clone()), t.clone());
    match elem_sort {
        ChcSort::Int => {
            out.push(ChcExpr::ge(sel(), ChcExpr::int(0)));
            out.push(ChcExpr::eq(sel(), ChcExpr::int(0)));
        }
        ChcSort::Bool => {
            out.push(ChcExpr::eq(sel(), ChcExpr::bool_const(true)));
            out.push(ChcExpr::eq(sel(), ChcExpr::bool_const(false)));
        }
        // Increment 1 deliberately covers only Int/Bool element value facts.
        _ => {}
    }
}

/// Whether `expr` is, or syntactically contains, an array-sorted term. Used as a
/// defensive guard so an index term can never carry an array sort into a
/// `select(_, t)` atom.
fn expr_has_array_sort(expr: &ChcExpr) -> bool {
    if matches!(expr.sort(), ChcSort::Array(_, _)) {
        return true;
    }
    match expr {
        ChcExpr::Op(_, args) => args.iter().any(|a| expr_has_array_sort(a)),
        ChcExpr::PredicateApp(_, _, args) | ChcExpr::FuncApp(_, _, args) => {
            args.iter().any(|a| expr_has_array_sort(a))
        }
        _ => false,
    }
}

/// Recursively collect index terms `idx` from `store(_, idx, _)` and
/// `select(_, idx)` subexpressions of `expr`.
fn collect_array_index_terms(expr: &ChcExpr, out: &mut Vec<ChcExpr>) {
    match expr {
        ChcExpr::Op(ChcOp::Select, args) if args.len() == 2 => {
            collect_array_index_terms(args[0].as_ref(), out);
            push_index_term(args[1].as_ref(), out);
            collect_array_index_terms(args[1].as_ref(), out);
        }
        ChcExpr::Op(ChcOp::Store, args) if args.len() == 3 => {
            collect_array_index_terms(args[0].as_ref(), out);
            push_index_term(args[1].as_ref(), out);
            collect_array_index_terms(args[1].as_ref(), out);
            collect_array_index_terms(args[2].as_ref(), out);
        }
        ChcExpr::Op(_, args) => {
            for arg in args {
                collect_array_index_terms(arg.as_ref(), out);
            }
        }
        ChcExpr::PredicateApp(_, _, args) | ChcExpr::FuncApp(_, _, args) => {
            for arg in args {
                collect_array_index_terms(arg.as_ref(), out);
            }
        }
        ChcExpr::Bool(_)
        | ChcExpr::Int(_)
        | ChcExpr::Real(_, _)
        | ChcExpr::BitVec(_, _)
        | ChcExpr::Var(_)
        | ChcExpr::ConstArrayMarker(_)
        | ChcExpr::IsTesterMarker(_)
        | ChcExpr::ConstArray(_, _) => {}
    }
}

/// Push an index term if not already present (structural dedup).
fn push_index_term(idx: &ChcExpr, out: &mut Vec<ChcExpr>) {
    if !out.contains(idx) {
        out.push(idx.clone());
    }
}

/// Whether every variable mentioned by `expr` is one of `canonical_vars`.
/// Constants (no vars) trivially pass.
fn expr_mentions_only_canonical(expr: &ChcExpr, canonical_vars: &[ChcVar]) -> bool {
    expr.vars()
        .iter()
        .all(|v| canonical_vars.iter().any(|cv| cv.name == v.name))
}

#[cfg(test)]
mod tests;
