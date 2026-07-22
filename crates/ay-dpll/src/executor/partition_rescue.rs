// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Post-dispatch symbol-disjoint partition rescue (Wave C, P2-multitheory).
//!
//! # What this fixes
//!
//! Trivially-SAT (and trivially-UNSAT) multi-theory conjunctions like
//! `(> r 1.5) ∧ (= b #x0a)` — a Real atom beside a BitVec atom, with no
//! conversion op coupling them — have no combined solver lane, so the primary
//! dispatch returns `unknown(Incomplete)` even though each conjunct is
//! trivially decidable alone and z3 answers `sat`. This module repairs the
//! whole *class* at the dispatch boundary rather than adding one combined lane
//! per theory pair: when the primary returns `Unknown(Incomplete)`, it splits
//! the assertion conjunction into symbol-connectivity components, solves each
//! through the ordinary per-component routing, and combines the verdicts.
//!
//! # Soundness — the guarantee derives from the WALK, not from the model gates
//!
//! The primary-path SAT gates fail *open* on exactly the incompleteness this
//! rescue could produce, so we do NOT lean on them:
//!
//!   * In default (non `--self-check`) mode, `finalize_sat_model_validation`
//!     returns `Ok(Sat)` with `last_model_validated == true` even when some
//!     assertions were only accepted via a SAT-agrees fallback or were
//!     un-evaluable (`incomplete > 0`); the `incomplete > 0 → Unknown` degrade
//!     is gated on `self.self_check` (pipeline.rs). So finalize alone is NOT a
//!     strict acceptance test.
//!   * The outer `emit_sat_verdict` independent gate KEEPS a `Sat` on
//!     `CannotConfirm` for genuinely-incomplete fragments (independent_gate.rs),
//!     i.e. it also fails open on an un-evaluable coupling term.
//!
//! Therefore the SAT guarantee rests on TWO things that do not fail open:
//!
//!   1. **The connectivity walk + scalar eligibility gate.** For a QF formula
//!      partitioned by shared *uninterpreted* symbols, there is no cross-
//!      component assertion: every assertion lives wholly inside one component
//!      (a `=`/predicate over symbols of two would-be components forces them
//!      into one). Each assertion was therefore decided, with a model, by its
//!      own component solve. The merged model reproduces every component's value
//!      on its own symbols, so it satisfies every assertion. QF sentences are
//!      preserved under domain extension, so shared *uninterpreted sorts* across
//!      components cannot couple the verdict — and the scalar-only merge gate
//!      excludes uninterpreted sorts from the model anyway. The only QF-external
//!      coupler is quantified sort-cardinality, which the firing gate excludes.
//!   2. **A STRICT positive re-validation of the merged model**, used purely as
//!      defense-in-depth against a connectivity-walk *bug*: we require BOTH
//!      `finalize_sat_model_validation() == Ok(Sat)` with `last_model_validated`
//!      AND `confirm_sat_with_independent_gate() == ConfirmedSat` (every
//!      assertion PROVABLY evaluates true under the merged model). `ConfirmedSat`
//!      is the strict positive kernel — it is NOT the fail-open `Ok(Sat)` /
//!      `CannotConfirm` path — so an un-verifiable merged coupling atom yields
//!      `CannotConfirm` and we fail closed to `unknown`.
//!
//! The UNSAT direction needs neither the walk nor the gates: by monotonicity of
//! conjunction, any UNSAT subset of the asserted conjuncts refutes the whole.
//! Under `--self-check` the boundary additionally degrades any `unsat` whose
//! refutation proof does not self-certify (check_sat.rs), so the unsat lane is
//! sound even when a subset-window Alethe proof cannot self-certify (it becomes
//! an honest `unknown`).
//!
//! # Fail-closed at every step
//!
//! Anything unexpected — a component `Unknown`, a missing/ineligible connector,
//! an `EvalValue::Unknown`, a merged model the strict re-validation cannot
//! confirm — restores the primary's original `Unknown` verdict and reason.
//! A wrong SAT is the worst outcome; we never trade soundness for a decide.

use ay_core::term::TermData;
use ay_core::{Sort, TermId};

use super::model::{EvalValue, Model};
use crate::executor::Executor;
use crate::executor_types::{Result, SolveResult, UnknownReason};
use crate::features::is_builtin_symbol_name;

/// Snapshot of the verdict-shaping state the rescue mutates while solving
/// components, restored verbatim on every fail-closed exit so the primary's
/// original `Unknown` is byte-identical to a no-rescue run.
struct RescueStateGuard {
    last_unknown_reason: Option<UnknownReason>,
    skip_model_eval: bool,
    defer_model_validation: bool,
    qfax_refinement_clause: Option<Vec<(TermId, bool)>>,
    last_assumption_core: Option<Vec<TermId>>,
    last_model_validated: bool,
}

impl Executor {
    /// Wrap the primary dispatch result. Returns `primary` UNCHANGED unless the
    /// firing gate holds and the partition rescue reaches a definite verdict.
    ///
    /// Placement is deliberately POST-dispatch: zero behavior change on anything
    /// that already decides (`Sat`/`Unsat`/non-Incomplete `Unknown` short-
    /// circuit immediately), so there is no perf or verdict delta on the working
    /// paths — the cost is paid only on already-`unknown(Incomplete)` queries.
    pub(in crate::executor) fn try_partition_rescue(
        &mut self,
        primary: Result<SolveResult>,
        pre_dispatch_assertions: &[TermId],
    ) -> Result<SolveResult> {
        // Only a clean Incomplete-Unknown is a rescue candidate.
        if !matches!(primary, Ok(SolveResult::Unknown)) {
            return primary;
        }
        if !self.partition_rescue_firing_gate(pre_dispatch_assertions) {
            return primary;
        }

        // Build the symbol-connectivity partition + the connecting-symbol table.
        let Some((components, connectors)) =
            self.partition_symbol_disjoint(pre_dispatch_assertions)
        else {
            return primary;
        };
        if components.len() < 2 {
            return primary;
        }

        self.last_statistics
            .set_int("solver.partition_rescue.fired", 1);
        self.last_statistics.set_int(
            "solver.partition_rescue.components",
            components.len() as u64,
        );

        match self.run_partition_components(&components, &connectors, pre_dispatch_assertions) {
            Some(decided) => {
                let label = match &decided {
                    Ok(SolveResult::Sat) => "sat",
                    Ok(SolveResult::Unsat(_)) => "unsat",
                    _ => "restore-unknown",
                };
                self.last_statistics
                    .set_string("solver.partition_rescue.outcome", label);
                decided
            }
            None => {
                self.last_statistics
                    .set_string("solver.partition_rescue.outcome", "restore-unknown");
                primary
            }
        }
    }

    /// All firing conditions (§2.1). Any failure returns `false` → no rescue.
    fn partition_rescue_firing_gate(&self, pre_dispatch_assertions: &[TermId]) -> bool {
        // The measured reason on every live probe; excludes Timeout/Interrupted.
        if self.last_unknown_reason != Some(UnknownReason::Incomplete) {
            return false;
        }
        // Quantifiers can couple symbol-disjoint conjuncts via sort cardinality
        // (the classic partition-unsoundness) — fail-closed out, belt AND braces.
        if self.original_problem_had_quantifiers {
            return false;
        }
        if pre_dispatch_assertions
            .iter()
            .any(|&a| crate::ematching::contains_quantifier(&self.ctx.terms, a))
        {
            return false;
        }
        // Incremental sessions: a component-window solve would pollute persistent
        // SAT/theory state. One-shot CLI files and plain `add()+check()` keep
        // this false.
        if self.incremental_mode {
            return false;
        }
        // Optimization: a rescue-`sat` inside an objective-refinement loop would
        // bypass objective handling. Decline whenever objectives / soft
        // constraints are registered.
        if !self.ctx.objectives().is_empty() || !self.ctx.soft_constraints().is_empty() {
            return false;
        }
        // Unsat-core extraction redirects through check_sat_assuming and never
        // reaches this dispatch; double-gate anyway (core code is concurrently
        // edited).
        if self.produce_unsat_cores_enabled() {
            return false;
        }
        if self.external_stop_reason().is_some() || self.solve_deadline.expired() {
            return false;
        }
        true
    }

    /// Solve each component, combine verdicts, and (all-SAT) merge + strictly
    /// re-validate the merged model. `Some(Ok(..))` is a definite verdict;
    /// `None` means fail-closed → the caller restores the primary `Unknown`.
    fn run_partition_components(
        &mut self,
        components: &[Vec<TermId>],
        connectors: &[Connector],
        pre_dispatch_assertions: &[TermId],
    ) -> Option<Result<SolveResult>> {
        let guard = RescueStateGuard {
            last_unknown_reason: self.last_unknown_reason,
            skip_model_eval: self.skip_model_eval,
            defer_model_validation: self.defer_model_validation,
            qfax_refinement_clause: self.qfax_refinement_clause.clone(),
            last_assumption_core: self.last_assumption_core.clone(),
            last_model_validated: self.last_model_validated,
        };

        // Component index -> its Sat model (populated only if every component is
        // Sat; short-circuits to Unsat as soon as any component is Unsat).
        let mut component_models: Vec<Option<Model>> = Vec::with_capacity(components.len());
        let mut any_unknown = false;

        for component in components {
            if self.external_stop_reason().is_some() || self.solve_deadline.expired() {
                self.restore_after_rescue(&guard);
                return None;
            }
            let result = match self.solve_partition_component(component) {
                Ok(r) => r,
                Err(e) => {
                    // A hard solver error must not surface from a rescue: restore
                    // the sound original Unknown. (Errors on the primary path are
                    // the caller's; here we only ever downgrade to no-op.)
                    let _ = e;
                    self.restore_after_rescue(&guard);
                    return None;
                }
            };
            match result {
                SolveResult::Unsat(cert) => {
                    // Subset monotonicity: an UNSAT subset of the asserted
                    // conjuncts refutes the whole conjunction — sound with NO
                    // reliance on the disjointness analysis. Restore the FULL
                    // assertion set for the downstream boundary (proof build /
                    // self-check), keep the component's proof in `last_proof`.
                    self.ctx.assertions = pre_dispatch_assertions.to_vec();
                    self.last_unknown_reason = None;
                    self.last_model = None;
                    self.skip_model_eval = guard.skip_model_eval;
                    self.defer_model_validation = guard.defer_model_validation;
                    return Some(Ok(SolveResult::Unsat(cert)));
                }
                SolveResult::Unknown => {
                    // Keep hunting the remaining components for an UNSAT, but no
                    // SAT can be emitted once any component is Unknown.
                    any_unknown = true;
                    component_models.push(None);
                }
                SolveResult::Sat => {
                    // Clone the component's model out before the next solve
                    // overwrites `last_model`. A Sat with no usable model cannot
                    // contribute to the merge → fail closed (record it as None so
                    // an all-SAT merge is impossible).
                    if self.skip_model_eval || self.last_model.is_none() {
                        any_unknown = true;
                        component_models.push(None);
                    } else {
                        component_models.push(self.last_model.clone());
                    }
                }
            }
        }

        if any_unknown {
            self.restore_after_rescue(&guard);
            return None;
        }

        // All components SAT: attempt the scalar-only model merge.
        match self.merge_and_validate(connectors, &component_models, pre_dispatch_assertions) {
            Some(sat) => Some(Ok(sat)),
            None => {
                self.restore_after_rescue(&guard);
                None
            }
        }
    }

    /// Solve one component through the ORDINARY per-component routing, replaying
    /// the identical pre-dispatch soundness passes the primary dispatch runs
    /// before `route_to_solver` (so a component's SAT is never trusted at face
    /// value without the singleton/enum/const-array corrections). Snapshot/
    /// restore of `ctx.assertions` and `incr_theory_state` isolates the window;
    /// `last_model`/`last_proof` are left as the component solve set them.
    ///
    /// No recursion: this calls `route_to_solver` directly (one level); a
    /// still-mixed component simply returns `Unknown`.
    fn solve_partition_component(&mut self, component: &[TermId]) -> Result<SolveResult> {
        let saved_assertions = std::mem::replace(&mut self.ctx.assertions, component.to_vec());
        let saved_incr = self.incr_theory_state.take();
        self.last_model = None;

        let (category, features) = self.detect_logic_category(component);

        // IDENTICAL pre-dispatch soundness passes as the top-level dispatch
        // (check_sat.rs). They mutate the swapped-in `ctx.assertions`, discarded
        // on restore. Several exist specifically to correct wrong-SAT on
        // singleton/enum/const-array shapes; running them per component closes
        // the "component SAT trusted at face value" gap. (Belt: the scalar-only
        // merge eligibility already excludes array/datatype/enum connectors, so
        // any component whose SAT these passes would have to correct is merge-
        // ineligible anyway — but we replicate the passes rather than rely on
        // that argument.)
        self.add_singleton_array_sort_equalities();
        self.fold_singleton_sort_equalities();
        let pigeonhole_unsat = self.add_finite_enum_pigeonhole_conflict();
        if features.has_arrays {
            self.add_distinct_const_array_disequalities();
            self.add_finite_index_array_extensionality();
            self.add_finite_index_select_expansion();
        }

        let result = if pigeonhole_unsat {
            Ok(SolveResult::unsat())
        } else {
            self.route_to_solver(category, &features)
        };

        self.ctx.assertions = saved_assertions;
        self.incr_theory_state = saved_incr;
        result
    }

    /// Merge the per-component scalar models and strictly re-validate the merged
    /// model against the FULL assertion set. Returns `Some(Sat)` only on strict
    /// positive validation; `None` on any failure (caller fails closed).
    fn merge_and_validate(
        &mut self,
        connectors: &[Connector],
        component_models: &[Option<Model>],
        pre_dispatch_assertions: &[TermId],
    ) -> Option<SolveResult> {
        // Eligibility gate: EVERY connecting symbol (of ANY arity) must be a
        // nullary declared constant of scalar sort. An arity>0 UF, array,
        // datatype, sequence, uninterpreted-sort, RoundingMode, or RegLan
        // connector makes the whole merge ineligible → fail closed. This both
        // keeps v1 scope to the scalar theories AND (with the connectors table
        // covering every arity — see `partition_symbol_disjoint`) makes shapes
        // like `(= (f 0) 1)` unmergeable even in the impossible event they were
        // not already unioned into one component.
        for connector in connectors {
            if !self.connector_is_scalar_nullary_const(connector) {
                return None;
            }
        }

        // Build the merged model from each connector's value in its OWNING
        // component's model. By the disjointness walk each connector belongs to
        // exactly one component. Values live in `completed_values` — the
        // authoritative last-resort slot `evaluate_var`/printers/gates all read
        // (`#no-fabricated-model-values`), so `(get-model)`/`(get-value ..)`
        // cannot diverge.
        //
        // For Int/Real vars, `evaluate_var_theory` DEFAULTS a missing var to 0
        // (bypassing `completed_values`) UNLESS an arith model is present, in
        // which case a miss returns Unknown and the completion slot is consulted.
        // Install empty LIA/LRA models so every Int/Real connector routes through
        // `completed_values` exactly like BV/String/FP/Bool (which already miss
        // to Unknown on an absent sub-model). Empty (not value-bearing) so a
        // single scalar source of truth stays in `completed_values`.
        let mut merged = Model::empty();
        merged.lra_model = Some(ay_lra::LraModel {
            values: Default::default(),
        });
        merged.lia_model = Some(ay_lia::LiaModel {
            values: Default::default(),
        });
        for connector in connectors {
            let component_model = component_models.get(connector.component)?.as_ref()?;
            // Canonical TermId is the declared symbol's bound term — the SAME
            // term get-value/printers evaluate, so `(get-model)` and
            // `(get-value ..)` cannot diverge.
            let tid = self.ctx.symbol_info(&connector.name).and_then(|i| i.term)?;
            let value = self.evaluate_term(component_model, tid);
            if value == EvalValue::Unknown {
                return None;
            }
            merged.completed_values.insert(tid, value);
        }

        // Install the merged model against the FULL pre-dispatch assertion set
        // and force a strict positive re-validation. defer/skip forced OFF so
        // `finalize_sat_model_validation` cannot take its fail-open defer/skip
        // early return (which would return Ok(Sat) without full validation).
        self.ctx.assertions = pre_dispatch_assertions.to_vec();
        self.last_model = Some(merged);
        self.last_model_validated = false;
        self.last_unknown_reason = None;
        self.defer_model_validation = false;
        self.skip_model_eval = false;

        let finalize = self.finalize_sat_model_validation();

        // STRICT acceptance (§2.4.3, hardened per REVISE objections 1 & 2):
        // require BOTH the full pipeline's Ok(Sat)+validated AND the strict
        // positive independent-gate kernel `ConfirmedSat` (every assertion
        // PROVABLY true). `ConfirmedSat` is not the fail-open `Ok(Sat)` /
        // `CannotConfirm` path, so an un-verifiable merged coupling atom is
        // rejected here rather than slipping through as a wrong SAT.
        let finalize_ok = matches!(finalize, Ok(SolveResult::Sat)) && self.last_model_validated;
        if !finalize_ok {
            return None;
        }
        if !matches!(
            self.confirm_sat_with_independent_gate(),
            ay_model_check::GateVerdict::ConfirmedSat
        ) {
            return None;
        }

        // The verdict now re-enters the outer `emit_sat_verdict` funnel (in
        // check_sat_guarded), where the merged model faces the strict +
        // independent + authoritative-failclosed gates a second time exactly
        // like any other model. We do NOT rely on that funnel's fail-open
        // default; the ConfirmedSat above is the acceptance test.
        Some(SolveResult::Sat)
    }

    /// A connector is mergeable iff it is a nullary declared constant whose sort
    /// is one of the scalar theories the merge understands. Everything else
    /// (arity>0 UF, arrays, datatypes, sequences, uninterpreted sorts,
    /// RoundingMode, RegLan) is ineligible.
    fn connector_is_scalar_nullary_const(&self, connector: &Connector) -> bool {
        let Some(info) = self.ctx.symbol_info(&connector.name) else {
            return false;
        };
        if !info.arg_sorts.is_empty() || info.term.is_none() {
            return false;
        }
        matches!(
            info.sort,
            Sort::Bool
                | Sort::Int
                | Sort::Real
                | Sort::BitVec(_)
                | Sort::String
                | Sort::FloatingPoint(_, _)
        )
    }

    /// Restore the verdict-shaping state the rescue mutated, reproducing the
    /// primary's original `Unknown` verdict byte-for-byte.
    fn restore_after_rescue(&mut self, guard: &RescueStateGuard) {
        self.last_model = None;
        self.last_unknown_reason = guard.last_unknown_reason;
        self.skip_model_eval = guard.skip_model_eval;
        self.defer_model_validation = guard.defer_model_validation;
        self.qfax_refinement_clause = guard.qfax_refinement_clause.clone();
        self.last_assumption_core = guard.last_assumption_core.clone();
        self.last_model_validated = guard.last_model_validated;
    }

    /// Partition the assertion roots into symbol-connectivity components via
    /// union-find over shared non-builtin (uninterpreted) symbols. Returns the
    /// components (each a `Vec<TermId>` of assertion roots) AND the flat table
    /// of connecting symbols with their owning component index.
    ///
    /// Every non-builtin application symbol of ANY arity and every free
    /// variable is a connecting symbol, used BOTH for union-find AND for the
    /// merge-eligibility gate (REVISE objection 3): interpreted constants and
    /// operators never connect (they denote fixed values); a cross-theory
    /// coupler `(= (bv2nat b) i)` is one assertion containing both symbols, so
    /// it lands wholly in one component; a shared arity>0 UF like `(f 0)`
    /// unions its assertions into one component AND is scalar-ineligible.
    ///
    /// Returns `None` if a quantifier is encountered (the firing gate already
    /// excludes this, but the walk fails closed defensively).
    fn partition_symbol_disjoint(
        &self,
        assertions: &[TermId],
    ) -> Option<(Vec<Vec<TermId>>, Vec<Connector>)> {
        let n = assertions.len();
        if n == 0 {
            return None;
        }
        // Per-assertion set of connecting symbol names.
        let mut per_assertion: Vec<Vec<String>> = Vec::with_capacity(n);
        for &root in assertions {
            let mut names: Vec<String> = Vec::new();
            if !self.collect_connecting_symbols(root, &mut names) {
                return None; // quantifier encountered → fail closed
            }
            names.sort();
            names.dedup();
            per_assertion.push(names);
        }

        // Union-find over assertion indices, joined on shared symbol name.
        let mut parent: Vec<usize> = (0..n).collect();
        // first assertion index that introduced each symbol name
        let mut first_seen: std::collections::HashMap<&str, usize> =
            std::collections::HashMap::new();
        for (idx, names) in per_assertion.iter().enumerate() {
            for name in names {
                match first_seen.get(name.as_str()) {
                    Some(&other) => union(&mut parent, idx, other),
                    None => {
                        first_seen.insert(name.as_str(), idx);
                    }
                }
            }
        }

        // Materialize components keyed by union-find root, preserving input order.
        let mut order: Vec<usize> = Vec::new();
        let mut buckets: std::collections::HashMap<usize, Vec<TermId>> =
            std::collections::HashMap::new();
        for (idx, &root_term) in assertions.iter().enumerate() {
            let r = find(&mut parent, idx);
            buckets.entry(r).or_default().push(root_term);
            if !order.contains(&r) {
                order.push(r);
            }
        }
        // Component index by union-find root, in first-appearance order.
        let mut comp_index: std::collections::HashMap<usize, usize> =
            std::collections::HashMap::new();
        let mut components: Vec<Vec<TermId>> = Vec::with_capacity(order.len());
        for (ci, r) in order.iter().enumerate() {
            comp_index.insert(*r, ci);
            components.push(buckets.remove(r).unwrap_or_default());
        }

        // Flatten the connector table: each distinct symbol -> its component.
        let mut connectors: Vec<Connector> = Vec::new();
        let mut seen: std::collections::HashSet<String> = std::collections::HashSet::new();
        for (idx, names) in per_assertion.iter().enumerate() {
            let ci = comp_index[&find(&mut parent, idx)];
            for name in names {
                if seen.insert(name.clone()) {
                    connectors.push(Connector {
                        name: name.clone(),
                        component: ci,
                    });
                }
            }
        }

        Some((components, connectors))
    }

    /// DFS the term DAG collecting connecting symbol names into `out`. Returns
    /// `false` if a quantifier is encountered (fail-closed signal). A visited
    /// set bounds the walk on shared/hash-consed subterms.
    fn collect_connecting_symbols(&self, root: TermId, out: &mut Vec<String>) -> bool {
        let mut stack = vec![root];
        let mut visited: std::collections::HashSet<TermId> = std::collections::HashSet::new();
        while let Some(t) = stack.pop() {
            if !visited.insert(t) {
                continue;
            }
            match self.ctx.terms.get(t) {
                TermData::Const(_) => {}
                TermData::Var(name, _) => {
                    // A free variable = a declared scalar constant (bound vars
                    // cannot occur; quantifiers are gated + rejected below).
                    out.push(name.clone());
                }
                TermData::App(sym, args) => {
                    if !is_builtin_symbol_name(sym.name()) {
                        // Non-builtin application of ANY arity (UF, datatype
                        // ctor/sel, user const) connects and is recorded for the
                        // eligibility gate.
                        out.push(sym.name().to_string());
                    }
                    for &a in args {
                        stack.push(a);
                    }
                }
                TermData::Not(inner) => stack.push(*inner),
                TermData::Ite(c, th, el) => {
                    stack.push(*c);
                    stack.push(*th);
                    stack.push(*el);
                }
                TermData::Let(bindings, body) => {
                    for (_, rhs) in bindings {
                        stack.push(*rhs);
                    }
                    stack.push(*body);
                }
                TermData::Forall(_, _, _) | TermData::Exists(_, _, _) => {
                    // Cannot occur (firing gate excludes quantifiers); fail
                    // closed if it somehow does.
                    return false;
                }
                // `TermData` is #[non_exhaustive]: any unknown/new term kind is
                // treated as fail-closed (declines the partition entirely).
                _ => return false,
            }
        }
        true
    }
}

/// A connecting (uninterpreted) symbol and the index of the component it
/// belongs to (unique by the disjointness walk).
struct Connector {
    name: String,
    component: usize,
}

fn find(parent: &mut [usize], mut x: usize) -> usize {
    while parent[x] != x {
        parent[x] = parent[parent[x]];
        x = parent[x];
    }
    x
}

fn union(parent: &mut [usize], a: usize, b: usize) {
    let ra = find(parent, a);
    let rb = find(parent, b);
    if ra != rb {
        parent[ra] = rb;
    }
}
