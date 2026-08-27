// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Producer-scoped pre-seal completion for a CERTIFIED constant-interpretation
//! witness, and the declaration-eligibility filter the two pre-seal
//! completions share.
//!
//! The formula-neutral pass in the parent module
//! ([`Executor::complete_quantified_output_model_before_seal`]) is the only
//! completion a SEARCH-produced quantified theorem model may receive, and its
//! occurrence skip is load-bearing there. A constant-interpretation
//! certificate is a different object with a stronger theorem, and this module
//! is where that difference — and ONLY that difference — is cashed in. The two
//! passes are deliberately identical in every other respect, which is why the
//! eligibility filter lives here as one shared predicate instead of being
//! restated on each side where it could drift.

use ay_core::kani_compat::DetHashSet as HashSet;
use ay_core::term::TermEntryStamp;
use ay_core::TermId;
use ay_frontend::DeclarationKind;

use super::super::{EvalValue, Model};
use crate::executor::Executor;

impl Executor {
    /// The declaration-eligibility filter both pre-seal completions share: an
    /// ORDINARY FREE PRIMARY declaration.
    ///
    /// Parsed and atomically allocated native-API declarations are
    /// completion-eligible, not projection authority; aliases,
    /// caller-supplied registrations, overloads, definitions, theory heads,
    /// and internals stay excluded. This prevents deductive-checks
    /// `Solver::declare_const` models from reaching `try_get_model` with "sat
    /// accepted without a total model"; positive-origin eligibility itself is
    /// centralized in `is_completion_eligible_declaration`.
    ///
    /// One predicate for both passes, so they can never drift on WHICH
    /// declarations may be touched. They differ only in WHEN occurrence
    /// withholds a default, which is the entire point of the split.
    pub(super) fn is_ordinary_free_primary_declaration(
        &self,
        surface_name: &str,
        info: &ay_frontend::SymbolInfo,
    ) -> bool {
        let identity = self.ctx.symbol_identity_name(surface_name, info);
        info.declaration_kind() == DeclarationKind::Uninterpreted
            && info.is_completion_eligible_declaration()
            && self.ctx.overloaded_surface_name(identity).is_none()
            && !self.ctx.is_internal_symbol(surface_name)
            && !self.ctx.is_defined_fun(surface_name)
            && self.ctx.adopted_macro_interp(surface_name).is_none()
    }

    /// Complete a CERTIFIED CONSTANT-INTERPRETATION witness before its
    /// producer seals it: the formula-neutral pass, then the residual free
    /// constants that pass deliberately withholds.
    ///
    /// [`Executor::complete_quantified_output_model_before_seal`] is the
    /// correct operation for a SEARCH-produced quantified theorem model, and
    /// it runs here first, unchanged. There, a declaration that OCCURS in an
    /// exact root is constrained by the very formula the theorem is about, so
    /// defaulting it could publish an under-constrained model — that skip is
    /// load-bearing and is not touched.
    ///
    /// A constant-interpretation certificate is a different object, and the
    /// difference is exactly what makes occurrence uninformative here. Every
    /// axiom and every ground conjunct was discharged, under the pinned
    /// interpretation `I`, by REFUTING ITS NEGATION as a standalone query in
    /// which the residual symbols are ordinary free uninterpreted symbols. An
    /// UNSAT there says the instance holds under EVERY interpretation of those
    /// residuals, so the certificate's theorem licenses `I ∪ J` for an
    /// ARBITRARY `J` — the same statement
    /// `install_const_interp_cert_witness` already makes about the entries it
    /// publishes. An occurring residual constant is, under THIS theorem, as
    /// unconstrained as an absent one: the assertions were discharged for
    /// every value it could take, so any one of them is a witness.
    ///
    /// Withholding those values made the const-interp witness PARTIAL BY
    /// CONSTRUCTION, and a certified SAT that the independent gate had already
    /// CONFIRMED was then discarded for having no total model — for every
    /// query whose assertions mention any uninterpreted-sorted constant.
    /// Measured at `b66957de35` on the two-binder AUFLIA control
    /// (`false_unsat_auflia_disjunct_forall::
    /// equivalent_single_universal_control_stays_sat`): the same fixture on the
    /// same binary answered `unknown (incomplete)` by default and `sat` with
    /// `:model_check_gate.result "confirmed-sat"` under
    /// `--no-const-interp-cert`; the minimal pair "constant declared but
    /// absent" / "same constant made to occur" answered `sat` / `unknown`.
    ///
    /// Scope discipline. This fills ONLY ordinary free 0-ary declarations that
    /// are neither substitution keys nor already valued, through the same
    /// eligibility filter, the same canonical defaults, the same semantic
    /// mutation primitive, and the same before/after root-currentness checks
    /// as the formula-neutral pass; every one of those failure modes still
    /// fails closed, and a `false` return discards the witness entirely.
    /// Functions are NOT widened: their residual freedom is just as real, but
    /// nothing needs it, and the narrow change is the one the certificate
    /// provably covers.
    #[must_use]
    pub(in crate::executor) fn complete_certified_const_interp_model_before_seal(
        &mut self,
        model: &mut Model,
        exact_roots: &[TermId],
    ) -> bool {
        if !self.complete_quantified_output_model_before_seal(model, exact_roots) {
            return false;
        }
        // Same isolation contract as the pass above: `model` is not installed
        // in `self.last_model`, so the TermId-keyed evaluator memo must not
        // carry ambient entries from the predecessor model into planning.
        super::super::with_isolated_eval_memo(|| {
            self.complete_certified_const_interp_residuals_isolated(model, exact_roots)
        })
    }

    fn complete_certified_const_interp_residuals_isolated(
        &mut self,
        model: &mut Model,
        exact_roots: &[TermId],
    ) -> bool {
        // Publish only after every check succeeds; a false return leaves the
        // caller's producer model byte-for-byte as the formula-neutral pass
        // left it.
        let mut completed = model.clone();
        let source_stamp = self.ctx.source_context_stamp();
        let Some(root_entries) = exact_roots
            .iter()
            .map(|&root| self.ctx.terms.entry_stamp(root))
            .collect::<Option<Vec<TermEntryStamp>>>()
        else {
            return false;
        };
        let roots_are_current = |executor: &Executor| {
            executor.ctx.source_context_stamp() == source_stamp
                && root_entries.iter().copied().map(Some).eq(exact_roots
                    .iter()
                    .map(|&root| executor.ctx.terms.entry_stamp(root)))
        };
        if !roots_are_current(self) {
            return false;
        }
        // Plan immutably.
        let substituted: HashSet<TermId> =
            self.recorded_var_substitutions.keys().copied().collect();
        let mut constant_defaults = Vec::new();
        for (surface_name, info) in self.ctx.symbol_iter() {
            if !info.arg_sorts.is_empty()
                || !self.is_ordinary_free_primary_declaration(surface_name, info)
            {
                continue;
            }
            let Some(term) = info.term else {
                return false;
            };
            // A substitution key is owned by substitution replay, and an
            // already-valued constant is owned by the certificate or by the
            // formula-neutral pass. Occurrence is NOT a reason here.
            if substituted.contains(&term)
                || !matches!(self.evaluate_term(&completed, term), EvalValue::Unknown)
            {
                continue;
            }
            if let Some(default) = self.unconstrained_default_value(&info.sort) {
                constant_defaults.push((term, default));
            }
        }
        constant_defaults.sort_by_key(|(term, _)| term.index());
        constant_defaults.dedup_by_key(|(term, _)| *term);
        if !roots_are_current(self) {
            return false;
        }
        let mut constants_filled = 0usize;
        for (term, default) in constant_defaults {
            if !Self::insert_completed_value(&self.ctx.terms, &mut completed, term, &default) {
                return false;
            }
            constants_filled += 1;
        }
        if !roots_are_current(self) {
            return false;
        }
        *model = completed;
        if constants_filled > 0 {
            self.last_statistics.set_int(
                "model_completion.const_interp_cert_residual_constants",
                constants_filled as u64,
            );
        }
        true
    }
}
