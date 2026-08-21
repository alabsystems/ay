// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Model storage and proof building helpers.

// #8529: Use deterministic hash maps in all builds.
use ay_arrays::ArrayModel;
use ay_bv::BvModel;
use ay_core::kani_compat::DetHashMap as HashMap;
use ay_core::term::{Constant, TermData};
use ay_core::{Sort, TermId, TseitinResult};
use ay_euf::EufModel;
use ay_fp::FpModel;
use ay_lia::LiaModel;
use ay_lra::LraModel;
use ay_sat::{SatResult, SatUnknownReason};
use ay_strings::StringModel;

use crate::executor_types::{Result, SolveResult, UnknownOrigin, UnknownReason};

use super::super::model::Model;
use super::super::Executor;

impl Executor {
    /// Record SAT-side `Unknown` reason if one was reported by ay-sat.
    ///
    /// Takes a mutable reference to the `last_unknown_reason` field directly
    /// (rather than `&mut self`) so callers can invoke this while other fields
    /// of `Executor` (e.g. `ctx.terms`) are borrowed by a `DpllT` instance.
    pub(in crate::executor) fn record_sat_unknown_reason(
        target: &mut Option<UnknownReason>,
        reason: Option<SatUnknownReason>,
    ) {
        if let Some(reason) = reason {
            *target = Some(Self::map_sat_unknown_origin(reason).reason());
        }
    }

    pub(in crate::executor) fn map_sat_unknown_reason(reason: SatUnknownReason) -> UnknownReason {
        Self::map_sat_unknown_origin(reason).reason()
    }

    pub(in crate::executor) fn map_sat_unknown_origin(reason: SatUnknownReason) -> UnknownOrigin {
        match reason {
            SatUnknownReason::Interrupted => UnknownOrigin::InterruptFlag,
            SatUnknownReason::DeadlineExceeded => UnknownOrigin::SolveDeadline,
            SatUnknownReason::ResourceBudget => UnknownOrigin::DeterministicResourceBudget,
            SatUnknownReason::TheoryStop | SatUnknownReason::ExtensionUnknown => {
                UnknownOrigin::IncompleteSolverLane
            }
            SatUnknownReason::UnsupportedConfig => UnknownOrigin::UnsupportedFeature,
            SatUnknownReason::EmptyTheoryConflict
            | SatUnknownReason::Unspecified
            | SatUnknownReason::AssumptionUnknown
            | SatUnknownReason::InvalidSatModel => UnknownOrigin::UntaggedSolverUnknown,
            #[allow(unreachable_patterns)]
            _ => UnknownOrigin::UntaggedSolverUnknown,
        }
    }

    /// Process solve result and store model if SAT
    pub(in crate::executor) fn solve_and_store_model(
        &mut self,
        result: SatResult,
        tseitin_result: &TseitinResult,
        euf_model: Option<EufModel>,
        array_model: Option<ArrayModel>,
    ) -> Result<SolveResult> {
        self.solve_and_store_model_full(
            result,
            tseitin_result,
            euf_model,
            array_model,
            None,
            None,
            None,
            None,
            None,
            None,
        )
    }

    /// Process solve result and store model if SAT, taking a `TheoryModels`
    /// struct instead of individual model parameters.
    ///
    /// This is the preferred call site for pipeline macros — it avoids the
    /// 8-argument field-by-field expansion at every return point.
    pub(in crate::executor) fn solve_and_store_model_with_theories(
        &mut self,
        result: SatResult,
        tseitin_result: &TseitinResult,
        mut models: super::solve_harness::TheoryModels,
    ) -> Result<SolveResult> {
        // NRA irrational-root certificate (TARGET nra_irrational): the SAT was
        // proven by an exact Sturm/IVT argument and carries exact ALGEBRAIC
        // witnesses (e.g. `x*x = 2` ⇒ x = √2 as a `root-obj`). Store them so
        // variable lookup, polynomial evaluation, get-value/get-model printing
        // and FULL model validation compute with them exactly — validation is
        // NOT suppressed for this path; it runs and must confirm the model.
        // Any stale rational LRA value for an algebraic variable (e.g. a
        // leftover simplex assignment) is stripped: the exact algebraic
        // witness is authoritative.
        if matches!(result, SatResult::Sat(_)) && !models.nra_algebraic.is_empty() {
            if let Some(lra) = models.lra.as_mut() {
                for (var, _) in &models.nra_algebraic {
                    lra.values.remove(var);
                }
            }
            self.nra_algebraic_model.set(&mut models.nra_algebraic);
        }
        // DT e-graph model export (#mv-dt-single-source): stash it aside and
        // attach it only AFTER the verdict is stored and stands as Sat — the
        // validation gates inside `solve_and_store_model_full` must not (and do
        // not) read it, and a Sat the gates degrade to Unknown must not leave a
        // stale e-graph export behind. `solve_and_store_model_full` clears any
        // previous export up front, so a later lane's Sat without a DT export
        // (or an Unsat/Unknown) can never pair a fresh model with a stale
        // e-graph.
        let dt_model = models.dt.take();
        let mut outcome = self.solve_and_store_model_full(
            result,
            tseitin_result,
            models.euf,
            models.array,
            models.lra,
            models.lia,
            models.bv,
            models.fp,
            models.string,
            models.seq,
        );
        if dt_model.is_some() && matches!(self.last_result, Some(SolveResult::Sat)) {
            self.dt_theory_model = dt_model;
            self.dt_egraph_assignment.replace(None);
        } else if dt_model.is_some()
            && self.dt_validation_wants_egraph
            && matches!(outcome, Ok(SolveResult::Unknown))
            && self.last_model.is_some()
        {
            // (#dt-egraph-validation-retry, mv-rerun-20260718 regression):
            // in-loop validation degraded this Sat to Unknown on a DATATYPE
            // ground-assertion incompleteness gap while the e-graph export was
            // stashed aside. Attach the export now and re-run finalization
            // ONCE: the canonical validator stays blind to it (unchanged
            // evidence discipline), but the INDEPENDENT fail-closed gate's
            // handoff can now re-evaluate the witness against the committed
            // single-source per-class values — exactly what the emit-time gate
            // reads on the normal Sat path. A retry that still cannot confirm
            // falls into the same fail-closed arms and the export is dropped,
            // so no stale e-graph outlives a non-Sat verdict.
            self.dt_theory_model = dt_model;
            self.dt_validation_wants_egraph = false;
            self.dt_egraph_assignment.replace(None);
            self.last_result = Some(SolveResult::Sat);
            outcome = self.finalize_sat_model_validation();
            if matches!(outcome, Ok(SolveResult::Sat)) {
                // The failed first pass recorded unknown-diagnostic stats and
                // an unknown reason; the verdict is now a validated Sat.
                self.last_unknown_reason = None;
                for key in [
                    "unknown.reason",
                    "unknown.phase",
                    "unknown.cost_center",
                    "unknown.detail",
                ] {
                    self.last_statistics.extra.remove(key);
                }
                self.last_statistics
                    .set_int("model_validation.dt_egraph_retry", 1);
            } else {
                self.clear_dt_theory_model();
            }
        }
        outcome
    }

    /// Process solve result and store model if SAT (with all theory models)
    #[allow(clippy::too_many_arguments)]
    pub(in crate::executor) fn solve_and_store_model_full(
        &mut self,
        result: SatResult,
        tseitin_result: &TseitinResult,
        euf_model: Option<EufModel>,
        array_model: Option<ArrayModel>,
        lra_model: Option<LraModel>,
        lia_model: Option<LiaModel>,
        bv_model: Option<BvModel>,
        fp_model: Option<FpModel>,
        string_model: Option<StringModel>,
        seq_model: Option<ay_seq::SeqModel>,
    ) -> Result<SolveResult> {
        // Every stored verdict invalidates any previous DT e-graph export: the
        // export is only meaningful paired with the model of the SAME accepted
        // Sat, and `solve_and_store_model_with_theories` re-attaches it after
        // this call when this verdict is a DT-lane Sat (#mv-dt-single-source).
        self.clear_dt_theory_model();

        // Tseitin var_to_term must be consistent with term_to_var (#4661).
        // var_to_term may be larger because encode.rs creates auxiliary fresh vars
        // for true/false constant encoding (fresh_var()) without inserting into
        // term_to_var. Every term-backed var appears in both maps, but auxiliary
        // constant-encoding vars appear only in var_to_term.
        debug_assert!(
            tseitin_result.var_to_term.len() >= tseitin_result.term_to_var.len(),
            "BUG: Tseitin var_to_term ({}) has fewer entries than term_to_var ({})",
            tseitin_result.var_to_term.len(),
            tseitin_result.term_to_var.len()
        );

        match result {
            SatResult::Sat(model) => {
                // SAT model must be non-empty when assertions exist (#4714)
                debug_assert!(
                    !model.is_empty() || self.ctx.assertions.is_empty(),
                    "SAT result has empty model but {} assertions exist",
                    self.ctx.assertions.len()
                );

                // Store the model with mappings (convert from 1-indexed CNF vars to 0-indexed)
                let term_to_var: HashMap<TermId, u32> = tseitin_result
                    .term_to_var
                    .iter()
                    .map(|(&t, &v)| (t, v - 1))
                    .collect();

                // All mapped vars must be valid model indices (#4714)
                debug_assert!(
                    term_to_var.values().all(|&v| (v as usize) < model.len()),
                    "term_to_var contains index {} but model has only {} vars",
                    term_to_var.values().max().unwrap_or(&0),
                    model.len()
                );

                // Store the model first with original values
                let mut assembled_model = Model::empty();
                assembled_model.sat_model = model;
                assembled_model.term_to_var = term_to_var;
                assembled_model.euf_model = euf_model;
                assembled_model.array_model = array_model;
                assembled_model.lra_model = lra_model;
                assembled_model.lia_model = lia_model;
                assembled_model.bv_model = bv_model;
                assembled_model.fp_model = fp_model;
                assembled_model.string_model = string_model;
                assembled_model.seq_model = seq_model;
                self.last_model = Some(assembled_model);

                // #qf-auflia-final-index-reconcile: re-key Int-indexed array
                // interpretation cells under the FINAL assignment (extraction
                // keys them by theory-side term values, which are stale for
                // Bool-ITE composite indices — the LIA solver never sees the
                // SAT Bool assignment). Adds only cells forced by the model's
                // own committed read values; on committed-read disagreement
                // the model is internally inconsistent and must NOT be
                // emitted — fail closed to Unknown (never flips sat/unsat).
                // See executor/model/array_reconcile.rs.
                if !self.reconcile_array_select_entries_with_final_assignment() {
                    self.last_model = None;
                    if self.last_unknown_reason.is_none() {
                        self.last_unknown_reason = Some(UnknownReason::Incomplete);
                    }
                    self.last_result = Some(SolveResult::Unknown);
                    return Ok(SolveResult::Unknown);
                }

                // SAT-preserving minimization: try smaller values for each
                // variable and keep only those that pass assertion re-evaluation.
                // Skip when assumptions are active: minimization only checks
                // permanent assertions, not assumptions, so it can produce models
                // that violate assumption constraints (#5121).
                //
                // DEMAND (#model-demand): this is witness cosmetics, so it is
                // also skipped when nothing in the run can read a model. The
                // gates below are NOT skipped — they decide the verdict.
                if self.counterexample_minimization_demanded()
                    && self.last_assumptions.is_none()
                    && !self.defer_counterexample_minimization
                {
                    self.minimize_model_sat_preserving();
                }

                // Aggressive BV/LIA/LRA minimization (#8297): run additional
                // passes that specifically target pinning values to 0/1. This
                // gives inter-variable constraints more opportunity to converge
                // to a globally minimal counterexample.
                if self.aggressive_model_minimize
                    && self.model_output_is_demanded()
                    && self.last_assumptions.is_none()
                    && !self.defer_counterexample_minimization
                {
                    self.aggressive_minimize_model();
                }

                // Soundness guard for known string tautology patterns that should
                // never appear as SAT when negated.
                if self.has_negated_string_equivalence_tautology() {
                    self.last_model = None;
                    self.last_result = Some(SolveResult::Unknown);
                    return Ok(SolveResult::Unknown);
                }
                self.pending_sat_unknown_reason = None;
                self.last_result = Some(SolveResult::Sat);
                debug_assert!(
                    self.last_model.is_some(),
                    "BUG: SAT result must populate last_model before finalize_sat_model_validation"
                );

                // #8373: Fix ITE model values before validation.
                // The simplex model assigns values to individual variables without
                // respecting ITE branch constraints. This pass evaluates ITE conditions,
                // determines which branch is active, and patches the LRA model so that
                // active-branch equalities are satisfied. Without this, the model
                // validation pipeline sees false evaluations on ITE-containing
                // assertions and degrades SAT to Unknown.
                self.fix_ite_model_values();

                self.finalize_sat_model_validation()
            }
            SatResult::Unsat(_) => {
                // Build proof if proof production is enabled
                if self.produce_proofs_enabled() {
                    self.build_unsat_proof();
                    debug_assert!(
                        self.last_proof.is_some(),
                        "BUG: UNSAT with proofs enabled but build_unsat_proof did not populate last_proof"
                    );
                }
                self.pending_sat_unknown_reason = None;
                self.last_result = Some(SolveResult::unsat());
                Ok(SolveResult::unsat())
            }
            SatResult::Unknown => {
                // Map SAT-level unknown reason to DPLL-level reason if the
                // theory executor hasn't already set one (#4622).
                if self.last_unknown_reason.is_none() {
                    if let Some(sat_reason) = self.pending_sat_unknown_reason.take() {
                        self.last_unknown_reason = Some(Self::map_sat_unknown_reason(sat_reason));
                    } else {
                        self.last_unknown_reason = Some(UnknownReason::Incomplete);
                    }
                }
                self.last_result = Some(SolveResult::Unknown);
                Ok(SolveResult::Unknown)
            }
            #[allow(unreachable_patterns)]
            _ => unreachable!("BUG: SatResult variant not handled in check_sat dispatch"),
        }
    }

    // Proof functions moved to executor/proof.rs

    // get_info, format_statistics_smt2, get_option_value, get_assertions,
    // simplify, format_term moved to executor/commands.rs

    /// Detect `(not (= A B))` where `A` and `B` are structurally equivalent
    /// Boolean string predicates/equalities. These formulas are UNSAT by
    /// string semantics; returning SAT here is unsound.
    pub(super) fn has_negated_string_equivalence_tautology(&self) -> bool {
        if self.bypass_string_tautology_guard {
            return false;
        }
        self.ctx
            .assertions
            .iter()
            .any(|&a| self.is_negated_string_equivalence_tautology(a))
    }

    fn is_negated_string_equivalence_tautology(&self, assertion: TermId) -> bool {
        // Pattern 1: (not (= A B)) — direct negated equality.
        if let TermData::Not(inner) = self.ctx.terms.get(assertion) {
            if let TermData::App(sym, args) = self.ctx.terms.get(*inner) {
                if sym.name() == "="
                    && args.len() == 2
                    && *self.ctx.terms.sort(args[0]) == Sort::Bool
                    && *self.ctx.terms.sort(args[1]) == Sort::Bool
                    && self.bool_terms_structurally_equivalent(args[0], args[1])
                {
                    return true;
                }
            }
        }
        // Pattern 2: (ite A (not B) B) — term store may rewrite
        // (not (= A B)) into ITE form for Boolean sorts (#6688).
        if let TermData::Ite(cond, then_br, else_br) = self.ctx.terms.get(assertion) {
            if *self.ctx.terms.sort(*cond) == Sort::Bool
                && *self.ctx.terms.sort(*else_br) == Sort::Bool
            {
                // Check: then_br = (not else_br), i.e., (ite A (not B) B)
                if let TermData::Not(neg_inner) = self.ctx.terms.get(*then_br) {
                    if *neg_inner == *else_br {
                        return self.bool_terms_structurally_equivalent(*cond, *else_br);
                    }
                }
                // Also check: (ite A B (not B)) which is (= A B) — but as
                // a top-level assertion this is NOT a negated tautology.
                // And: (ite (not A) B (not B)) ≡ (not (= A B))
                if let TermData::Not(neg_cond) = self.ctx.terms.get(*cond) {
                    if let TermData::Not(neg_else) = self.ctx.terms.get(*else_br) {
                        if *neg_else == *then_br {
                            // (ite (not A) B (not B)) ≡ (not (= A B))
                            return self.bool_terms_structurally_equivalent(*neg_cond, *then_br);
                        }
                    }
                }
            }
        }
        false
    }

    /// Structural Boolean equivalence checks for string rewrite tautologies.
    fn bool_terms_structurally_equivalent(&self, lhs: TermId, rhs: TermId) -> bool {
        self.contains_equivalent_to_string_equality_term(lhs, rhs)
            || self.contains_equivalent_to_string_equality_term(rhs, lhs)
            || self.self_concat_equalities_equivalent_term(lhs, rhs)
    }

    /// Check equivalence: `str.contains(h, n)` ↔ `(= h n)` for structural cases.
    fn contains_equivalent_to_string_equality_term(
        &self,
        contains_term: TermId,
        eq_term: TermId,
    ) -> bool {
        let TermData::App(c_sym, c_args) = self.ctx.terms.get(contains_term) else {
            return false;
        };
        if c_sym.name() != "str.contains" || c_args.len() != 2 {
            return false;
        }
        let h = c_args[0];
        let n = c_args[1];

        let TermData::App(eq_sym, eq_args) = self.ctx.terms.get(eq_term) else {
            return false;
        };
        if eq_sym.name() != "=" || eq_args.len() != 2 {
            return false;
        }

        let eq_matches =
            (eq_args[0] == h && eq_args[1] == n) || (eq_args[1] == h && eq_args[0] == n);
        if !eq_matches {
            return false;
        }

        self.contains_has_equality_semantics_term(h, n)
    }

    /// Whether `str.contains(h, n)` is structurally equivalent to `h = n`.
    fn contains_has_equality_semantics_term(&self, h: TermId, n: TermId) -> bool {
        if h == n {
            return true;
        }
        if matches!(
            self.ctx.terms.get(h),
            TermData::Const(Constant::String(s)) if s.is_empty()
        ) {
            return true;
        }

        let mut components = Vec::new();
        self.flatten_concat_term(n, &mut components);
        components.len() >= 2 && components.contains(&h)
    }

    /// Check equivalence of self-concat equalities:
    /// `(= x (str.++ y x))` and `(= x (str.++ x y))`.
    fn self_concat_equalities_equivalent_term(&self, lhs: TermId, rhs: TermId) -> bool {
        let Some((lx, ly)) = self.extract_self_concat_pair_term(lhs) else {
            return false;
        };
        let Some((rx, ry)) = self.extract_self_concat_pair_term(rhs) else {
            return false;
        };
        lx == rx && ly == ry
    }

    /// Extract `(x, y)` from equality `x = str.++(x, y)` or `x = str.++(y, x)`.
    fn extract_self_concat_pair_term(&self, term: TermId) -> Option<(TermId, TermId)> {
        let TermData::App(eq_sym, eq_args) = self.ctx.terms.get(term) else {
            return None;
        };
        if eq_sym.name() != "=" || eq_args.len() != 2 {
            return None;
        }
        if *self.ctx.terms.sort(eq_args[0]) != Sort::String
            || *self.ctx.terms.sort(eq_args[1]) != Sort::String
        {
            return None;
        }

        for &(x, other) in &[(eq_args[0], eq_args[1]), (eq_args[1], eq_args[0])] {
            let mut components = Vec::new();
            self.flatten_concat_term(other, &mut components);
            if components.len() != 2 {
                continue;
            }
            if components[0] == x {
                return Some((x, components[1]));
            }
            if components[1] == x {
                return Some((x, components[0]));
            }
        }
        None
    }

    /// Flatten a concat term into syntactic leaf components.
    fn flatten_concat_term(&self, term: TermId, out: &mut Vec<TermId>) {
        let TermData::App(sym, args) = self.ctx.terms.get(term) else {
            out.push(term);
            return;
        };
        if sym.name() != "str.++" {
            out.push(term);
            return;
        }
        for &arg in args {
            self.flatten_concat_term(arg, out);
        }
    }
}

#[cfg(test)]
#[path = "model_helpers_tests.rs"]
mod tests;
