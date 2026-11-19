// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Model output entry points: `get-model`, `get-value`, `get-objectives`.
//!
//! Formatting helpers (function tables, array values, eval-value rendering)
//! live in sibling `output_format.rs`.

use ay_core::kani_compat::{DetHashMap, DetHashSet};
use ay_core::term::{TermConstructionAdmission as _, TermData};
use ay_core::{quote_symbol, string_literal, Sort, Symbol, TermId};

use crate::executor_format::{
    format_bigint, format_bitvec, format_model_atom_surface, format_real, format_sort_surface,
};
use crate::executor_types::SolveResult;

use super::construction_owner::{ModelConstructionRead, ModelRead};
use super::overloaded_ctor_surface::ValueSpelling;
use super::Executor;
use super::{debug_model, CertifiedConstInterpBody, EvalValue, LinearIntBody, Model};

mod aggregate_constants;
use aggregate_constants::{AggregateConstantValue, AggregateConstantValues};

/// Nesting bound of [`Executor::gv_printed_bool`].
const PRINTED_BOOL_DEPTH: u32 = 256;

#[cfg(test)]
thread_local! {
    /// The `c ay.model.partial` lines this thread wrote to stderr, in order.
    static PARTIAL_MODEL_REPORTS: std::cell::RefCell<Vec<String>> =
        const { std::cell::RefCell::new(Vec::new()) };
}

/// Test hook: the `c ay.model.partial` lines this thread wrote to stderr
/// since the last call, in order.
#[cfg(test)]
pub(super) fn take_partial_model_reports() -> Vec<String> {
    PARTIAL_MODEL_REPORTS.with(|reports| std::mem::take(&mut *reports.borrow_mut()))
}

/// A `(get-model)` response rendered in one spelling, and the symbols it
/// leaves out. [`Executor::surface_response`] can render a response in both
/// spellings and return either, so the omissions are reported by
/// [`Self::publish`], for the rendering returned, not by each rendering.
struct ModelResponse {
    text: String,
    /// Sorted, without duplicates.
    omitted: Vec<String>,
}

impl AsRef<str> for ModelResponse {
    fn as_ref(&self) -> &str {
        &self.text
    }
}

impl ModelResponse {
    /// The response text, once its omissions are reported on stderr as
    /// `c ay.model.partial omitted=<n> symbols=[<names>]`.
    ///
    /// Every fail-closed omission drops a symbol from an otherwise
    /// well-formed model. The result still prints `sat`, so the run scores
    /// ZERO in Model-Validation while the scoreboard reads `errors: 0`. The
    /// report is on stderr ONLY: stdout is piped verbatim into Dolmen and
    /// must stay a pure get-model response. The harness already captures
    /// `stderr_tail`, so this makes a partial model greppable in the run
    /// record instead of silently scoring zero.
    fn publish(self) -> String {
        // Not under `--z3-mode`, whose stderr stays empty as z3's does; the
        // response itself shows the omission.
        if !self.omitted.is_empty() && !ay_core::misc_cli_flags().z3_transcript {
            let line = format!(
                "c ay.model.partial omitted={} symbols=[{}]",
                self.omitted.len(),
                self.omitted.join(" ")
            );
            eprintln!("{line}");
            #[cfg(test)]
            PARTIAL_MODEL_REPORTS.with(|reports| reports.borrow_mut().push(line));
        }
        self.text
    }
}

impl Executor {
    /// The array constants `(get-model)` would print through the witness
    /// builder ([`Self::format_array_witness_value`]) rather than through the
    /// independent gate's own value, with the text it would print.
    ///
    /// Constants the printer takes from the gate (`completed_model_value`, the
    /// aggregate reconstruction) are left out: their text is the gate's value
    /// by construction. The witness builder assembles its text from direct
    /// reads and the array interpretation and can leave out what it cannot
    /// spell, so its text is the one that has to be checked against the
    /// validated model (AY-N9). A symbol the builder cannot render is left
    /// out too: `(get-model)` refuses it on its own.
    pub(in crate::executor) fn printed_array_witness_texts(
        &self,
        model: &Model,
    ) -> Result<Vec<(TermId, String)>, String> {
        let has_array_constant = self.ctx.symbol_iter().any(|(_, info)| {
            info.arg_sorts.is_empty() && info.term.is_some() && matches!(info.sort, Sort::Array(_))
        });
        if !has_array_constant || model.has_residual_arrays() {
            return Ok(Vec::new());
        }
        let aggregate_values = AggregateConstantValues::collect(self, model)?;
        let mut printed = Vec::new();
        for (name, info) in self.ctx.symbol_iter() {
            if !info.arg_sorts.is_empty() || !matches!(info.sort, Sort::Array(_)) {
                continue;
            }
            let Some(term_id) = info.term else {
                continue;
            };
            if self.is_exact_dt_internal_symbol(self.ctx.symbol_identity_name(name, info))
                || self.ctx.is_internal_symbol(name)
                || self.ctx.is_defined_fun(name)
                || self.ctx.adopted_macro_interp(name).is_some()
            {
                continue;
            }
            match self.completed_model_value(model, term_id) {
                Ok(None) => {}
                Ok(Some(_)) | Err(()) => continue,
            }
            match aggregate_values.resolve(self, model, term_id)? {
                AggregateConstantValue::Absent => {}
                AggregateConstantValue::Value(_) | AggregateConstantValue::Poisoned => continue,
            }
            if let Some(text) = self.format_array_witness_value(model, term_id, &info.sort) {
                printed.push((term_id, text));
            }
        }
        Ok(printed)
    }

    /// Generate model output for get-model command.
    pub(crate) fn model(&self) -> String {
        self.checked_evaluation_output(|| {
            self.surface_response(|spelling| self.model_response(spelling))
                .publish()
        })
    }

    /// [`Self::model`] in [`ValueSpelling::Sorted`], for a reader inside this
    /// process that holds the solver.
    pub(crate) fn model_for_decoder(&self) -> String {
        self.checked_evaluation_output(|| self.model_response(ValueSpelling::Sorted).publish())
    }

    /// The model rendered in `spelling`, with the symbols it leaves out.
    fn model_response(&self, spelling: ValueSpelling) -> ModelResponse {
        let mut omitted = Vec::new();
        let text = self.model_unstopped(spelling, &mut omitted);
        ModelResponse { text, omitted }
    }

    /// The model text in `spelling`; the symbols it leaves out go to
    /// `omissions`.
    fn model_unstopped(&self, spelling: ValueSpelling, omissions: &mut Vec<String>) -> String {
        if !self.produce_models_enabled() {
            return "(error \"model generation is not enabled\")".to_string();
        }

        // Check if we have a model.  Some SAT paths have no concrete theory
        // model because assertions were simplified away; every declared
        // constant is then unconstrained, so print the completed default
        // model (the values exist in a model, nothing is fabricated at print
        // time — #no-fabricated-model-values).
        let dummy_model;
        let published_candidate;
        let mut unvalidated_candidate = false;
        let model = match (&self.last_result, &self.last_model) {
            (Some(SolveResult::Sat), Some(m)) => m,
            (Some(SolveResult::Sat), None) => {
                dummy_model = self.completed_default_model();
                &dummy_model
            }
            _ => match self.publishable_candidate() {
                Some(candidate) => {
                    unvalidated_candidate = true;
                    published_candidate = candidate;
                    &published_candidate
                }
                None => return "(error \"model is not available\")".to_string(),
            },
        };
        if unvalidated_candidate {
            self.with_model_data_read(model, |read| {
                self.model_from_selected(read, true, spelling, omissions)
            })
        } else {
            self.with_model_construction_read(model, |read| {
                self.model_from_selected(read, false, spelling, omissions)
            })
        }
    }

    fn model_from_selected(
        &self,
        read: &dyn ModelRead,
        unvalidated_candidate: bool,
        spelling: ValueSpelling,
        omissions: &mut Vec<String>,
    ) -> String {
        let model = read.model();
        if !self.materialized_scalar_functions_current(model) {
            return "(error \"materialized scalar function model is stale\")".to_string();
        }
        if !model.residual_arrays_are_current(&self.ctx) {
            return "(error \"retained array model is stale\")".to_string();
        }

        // Collect model values for user-declared symbols.
        //
        // Datatype SELECTOR totalizations come first (#mv-total-selectors):
        // without them a model validator evaluating a selector applied to a
        // wrong-constructor value rejects the whole model as partial. Each
        // definition defers to the builtin selector on the owning constructor
        // and reproduces the internal model's committed value on every
        // constrained wrong-constructor case.
        // The constructors `overloaded_ctor_surface` may ascribe in
        // `spelling` (#overloaded-nil-surface).
        let overloaded = self.overloaded_ctors_for(spelling);
        let mut definitions = self.total_selector_definitions(model, &overloaded);
        // Every fail-closed omission below drops a symbol from an otherwise
        // well-formed model, invisibly to every downstream consumer of the
        // response. Record what was dropped: it goes to `omissions`, which
        // `ModelResponse::publish` reports on stderr.
        let mut omitted: Vec<String> = Vec::new();

        // Entailed reconstruction of datatype/array-sorted constants, shared with
        // the independent gate (`gate_emit_reconstructions`): the printer's own
        // per-leaf materialization can leave a datatype field leaf `Unknown` (an
        // unavailable marker) or pick per-leaf values that are mutually
        // incoherent, so the emitted model does not re-check. Where the gate's
        // entailed-alias resolution yields a concrete, marker-free value, prefer
        // it — that is the model the gate confirmed, so it round-trips. A leaf
        // the gate leaves unresolved is simply absent here and falls through to
        // the existing renderer (fail-closed, no fabrication).
        let aggregate_values = match AggregateConstantValues::collect(self, model) {
            Ok(values) => values,
            Err(error) => return format!("(error \"{error}\")"),
        };

        // Ground UF applications, collected once on first need and shared by
        // every symbol that reaches the fallback below. Lazy because the sweep
        // walks every assertion and the EUF lanes never need it.
        let mut ground_uf_apps: Option<DetHashMap<(String, usize), Vec<(TermId, Vec<TermId>)>>> =
            None;

        'symbols: for (name, info) in self.ctx.symbol_iter() {
            // A validated model prints whole or not at all. An unvalidated
            // candidate leaves out a symbol whose value cannot be rendered
            // (reported with the other omissions below) instead of failing the
            // whole command.
            macro_rules! unrenderable {
                ($symbols:lifetime, $error:expr) => {{
                    if unvalidated_candidate {
                        omitted.push(name.to_string());
                        continue $symbols;
                    }
                    return $error;
                }};
            }

            // Skip DT-internal symbols (constructors, testers, selectors) (#5412).
            if self.is_exact_dt_internal_symbol(self.ctx.symbol_identity_name(name, info)) {
                continue;
            }

            // Skip SOLVER-INTERNAL symbol registrations (fresh single-ctor
            // elimination field constants): not user-declared, so a validator
            // treats their definitions as garbage — the pinned 2025 Dolmen
            // silently stops reading the model at the first one, orphaning
            // every later user symbol (#mv-internal-symbol-suppression). The
            // flag is cleared on user (re)declaration, so no user-DECLARED
            // symbol is ever suppressed.
            if self.ctx.is_internal_symbol(name) {
                continue;
            }

            // Keep nullary output on the same typed ownership path as the
            // independent view, before any competing constant interpretation.
            if info.arg_sorts.is_empty() {
                if let Some(term_id) = info.term {
                    match self.completed_model_value(model, term_id) {
                        Ok(Some(value)) => {
                            let Some(value) = self.format_gate_model_value(&value, &info.sort)
                            else {
                                unrenderable!(
                                    'symbols,
                                    "(error \"completed model value cannot be rendered exactly\")"
                                        .to_string()
                                );
                            };
                            definitions.push(format!(
                                "  (define-fun {} () {} {value})",
                                quote_symbol(name),
                                format_sort_surface(&self.ctx, &info.sort)
                            ));
                            continue;
                        }
                        Ok(None) => {}
                        Err(()) => {
                            unrenderable!(
                                'symbols,
                                "(error \"retained array model value is unavailable\")".to_string()
                            );
                        }
                    }
                }
            }

            // A checked projection is the exact total interpretation of this
            // declaration, not a finite sample. Emit its lambda body directly
            // and do not consult or complete an ordinary EUF table for the
            // same head. The internal identity plus full signature prevents an
            // overloaded surface name from selecting the wrong definition.
            let identity = self.ctx.symbol_identity_name(name, info);
            let symbol = Symbol::named(identity);
            match model.projection_ufs.projected_argument_for_signature(
                &symbol,
                &info.arg_sorts,
                &info.sort,
            ) {
                Ok(Some(projected_argument)) => {
                    // A semantic projection token does not prove that this
                    // head is still a free UF in the CURRENT source context.
                    // In particular, an adopted definitional macro keeps its
                    // declaration in `symbol_iter`, so projection-first output
                    // would otherwise silently replace its authored body.
                    // Fail closed at the final output boundary. This negative
                    // check is defense in depth only; steering still requires
                    // positive, stable declaration-kind provenance.
                    let source_is_defined = self.ctx.is_defined_fun(name);
                    let source_is_adopted = self.ctx.adopted_macro_interp(name).is_some();
                    if source_is_defined || source_is_adopted {
                        tracing::error!(
                            surface_name = %name,
                            identity = %identity,
                            is_defined_fun = source_is_defined,
                            is_adopted_macro = source_is_adopted,
                            "refusing to format a projection model over a defined source head"
                        );
                        return "(error \"checked projection model conflicts with current source binding\")"
                            .to_string();
                    }
                    match self.format_projection_function(
                        name,
                        &info.arg_sorts,
                        &info.sort,
                        projected_argument,
                    ) {
                        Ok(definition) => definitions.push(definition),
                        Err(error) => {
                            tracing::error!(
                                %error,
                                "refusing to format a malformed checked projection model"
                            );
                            return "(error \"malformed checked projection model\")".to_string();
                        }
                    }
                    continue;
                }
                Ok(None) => {}
                Err(error) => {
                    tracing::error!(
                        %error,
                        surface_name = %name,
                        identity = %identity,
                        "refusing to read a checked projection model at a conflicting declaration signature"
                    );
                    return "(error \"checked projection model conflicts with current declaration signature\")"
                        .to_string();
                }
            }

            // A quantified SAT certificate may install an exact typed table
            // with an explicit else value.  Emit that interpretation directly
            // before consulting the lossy raw EUF table (whose legacy format
            // encodes the else branch as its last row and cannot faithfully
            // represent a carrier-free datatype domain).
            if let Some(total) = model.certified_total_ufs.by_symbol.get(identity) {
                let argument_sorts_match = total.arg_sorts == info.arg_sorts;
                let result_sort_matches = total.result_sort == info.sort;
                let signature_matches = argument_sorts_match && result_sort_matches;
                if self.ctx.is_defined_fun(name)
                    || self.ctx.adopted_macro_interp(name).is_some()
                    || !signature_matches
                {
                    tracing::error!(
                        surface_name = %name,
                        identity = %identity,
                        "refusing to format a certified total UF at a conflicting source declaration"
                    );
                    return "(error \"certified total UF conflicts with current source declaration\")"
                        .to_string();
                }
                match self.format_certified_total_function(
                    name,
                    &total.arg_sorts,
                    &total.result_sort,
                    &total.rendered_rows,
                    &total.rendered_default,
                ) {
                    Ok(definition) => definitions.push(definition),
                    Err(error) => {
                        tracing::error!(
                            %error,
                            surface_name = %name,
                            identity = %identity,
                            "refusing to format a malformed certified total UF"
                        );
                        return "(error \"malformed certified total UF model\")".to_string();
                    }
                }
                continue;
            }

            // CONSTANT-INTERPRETATION CERTIFICATE WITNESS. The certificate's
            // proof object is an interpretation `I` under which every axiom was
            // machine-checked, so `I` is the model and this is how it prints:
            // `I(f) = λ ȳ. c_f` renders as
            // `(define-fun f ((x!0 S) ..) T c_f)`, matching z3's output for the
            // same query.
            //
            // Emitted through a channel of its own rather than through
            // `adopted_macro_interp` above. That mechanism refuses any symbol a
            // constraint mentions, and its soundness rests on exactly that
            // refusal ("nothing constrains this symbol, so any interpretation
            // will do"); the symbols here are the opposite case — they occur in
            // the quantified constraint, and are publishable only because the
            // certificate checked every constraint AGAINST this interpretation.
            // Relaxing the frontend's refusal would have widened it for every
            // caller on the strength of an argument only this one can make.
            //
            // Non-empty only after a grant on the route where the certificate
            // supplied the entire model, so it can never displace a theory
            // model built by a real solve.
            if let Some(entry) = self
                .const_interp_cert_witness_entries(model)
                .iter()
                .find(|entry| entry.name() == Some(name.as_str()))
            {
                let params_str = entry
                    .parameter_sorts()
                    .iter()
                    .enumerate()
                    .map(|(index, sort)| {
                        let parameter = format!("x!{index}");
                        format!(
                            "({} {})",
                            quote_symbol(&parameter),
                            format_sort_surface(&self.ctx, sort)
                        )
                    })
                    .collect::<Vec<_>>()
                    .join(" ");
                // The printing channel has always been a TERM channel — the
                // body below is whatever the certified interpretation says,
                // and for a CONSTANT body that is the published constant.
                // A SYMBOLIC body carries no `TermId` to print, so it is
                // rendered from its coefficients against the same `x!i`
                // parameter spellings the signature above just emitted; a
                // rendering failure is an error, never a silently omitted or
                // guessed definition.
                let body = match entry.body() {
                    CertifiedConstInterpBody::Constant { value, .. } => self.format_term(*value),
                    CertifiedConstInterpBody::LinearInt(linear) => {
                        match format_linear_int_body(linear) {
                            Some(rendered) => rendered,
                            None => {
                                tracing::error!(
                                    surface_name = %name,
                                    "refusing to format a malformed certified linear interpretation"
                                );
                                return "(error \"malformed certified constant-interpretation model\")"
                                    .to_string();
                            }
                        }
                    }
                };
                definitions.push(format!(
                    "  (define-fun {} ({}) {}\n    {})",
                    quote_symbol(name),
                    params_str,
                    format_sort_surface(&self.ctx, &info.sort),
                    body
                ));
                continue;
            }

            // Canonical interpretations for declarations proved absent from a
            // quantified theorem live outside `EufModel`, so installing them
            // cannot change strict-gate `euf_backed` classification. Recheck
            // the exact declaration binding/signature at this final output
            // boundary and print the same constant body evaluation returns.
            let identity_symbol = Symbol::named(identity);
            if let Some(entry) = model
                .formula_neutral_function_default_entries()
                .iter()
                .find(|entry| entry.symbol() == &identity_symbol)
            {
                if !entry.is_current(&self.ctx)
                    || entry.parameter_sorts() != info.arg_sorts
                    || entry.result_sort() != &info.sort
                    || self.unconstrained_default_value(&info.sort).as_ref() != Some(entry.value())
                {
                    tracing::error!(
                        surface_name = %name,
                        identity = %identity,
                        "refusing to format a stale formula-neutral function default"
                    );
                    return "(error \"formula-neutral function default conflicts with current declaration\")"
                        .to_string();
                }
                let params_str = entry
                    .parameter_sorts()
                    .iter()
                    .enumerate()
                    .map(|(index, sort)| {
                        format!(
                            "({} {})",
                            quote_symbol(&format!("x!{index}")),
                            format_sort_surface(&self.ctx, sort)
                        )
                    })
                    .collect::<Vec<_>>()
                    .join(" ");
                definitions.push(format!(
                    "  (define-fun {} ({}) {}\n    {})",
                    quote_symbol(name),
                    params_str,
                    format_sort_surface(&self.ctx, &info.sort),
                    self.default_value_surface(&info.sort)
                ));
                continue;
            }

            // #quantprod-g3: a DECLARED function adopted as a definitional
            // macro (`(assert (forall X. (= (f X) body)))` recognized as a
            // pure definition) still needs a model entry — z3 prints one —
            // and its interpretation IS the definition, satisfying the
            // definitional assertion by reflexivity. Emit it before the
            // defined-symbol skip below (adoption puts it in `fun_defs`).
            if let Some((params, body)) = self.ctx.adopted_macro_interp(name) {
                let params_str = params
                    .iter()
                    .map(|(n, s)| {
                        format!(
                            "({} {})",
                            quote_symbol(n),
                            format_sort_surface(&self.ctx, s)
                        )
                    })
                    .collect::<Vec<_>>()
                    .join(" ");
                let body = *body;
                definitions.push(format!(
                    "  (define-fun {} ({}) {}\n    {})",
                    quote_symbol(name),
                    params_str,
                    format_sort_surface(&self.ctx, &info.sort),
                    self.format_term(body)
                ));
                continue;
            }

            // Skip problem-DEFINED symbols (define-fun/-rec): their
            // interpretation is fixed by the problem text. Re-emitting one is a
            // definition conflict for a model validator, and the solver has no
            // model entry keyed by the name anyway (defined applications are
            // macro-expanded at elaboration) — any table found here could only
            // be a completion default, i.e. a WRONG body (#mv-defined-fun-emit).
            if self.ctx.is_defined_fun(name) {
                continue;
            }

            // Handle functions with arguments (generate function tables).
            if !info.arg_sorts.is_empty() {
                let identity = self.ctx.symbol_identity_name(name, info);
                match model.constant_array_function_for_output(
                    self,
                    identity,
                    &info.arg_sorts,
                    &info.sort,
                ) {
                    Ok(Some(value)) => {
                        let Some(admission) = model.constant_array_read_admission(self) else {
                            return "(error \"retained array function owner unavailable\")"
                                .to_owned();
                        };
                        match self.format_retained_constant_function(
                            name,
                            &info.arg_sorts,
                            &info.sort,
                            value,
                            &admission,
                        ) {
                            Ok(definition) => {
                                if ay_core::term::reserve_counted(&mut definitions, 1, &admission)
                                    .is_err()
                                {
                                    return "(error \"retained model output refused\")".to_owned();
                                }
                                definitions.push(definition);
                            }
                            Err(_) => {
                                return "(error \"retained array function cannot be rendered\")"
                                    .to_owned()
                            }
                        }
                        continue;
                    }
                    Ok(None) => {}
                    Err(()) => {
                        return "(error \"retained array function source changed\")".to_owned()
                    }
                }
                // Did the EUF route publish an interpretation for this symbol?
                // When it does not, the ground-application fallback below is the
                // only thing standing between a UF-bearing `sat` and an
                // INCOMPLETE witness (#uf-interp-bv-lane).
                let mut euf_published = false;
                // Check if we have EUF model with function tables.
                if let Some(ref euf_model) = model.euf_model {
                    let identity = self.ctx.symbol_identity_name(name, info);
                    if let Some(table) = euf_model.function_tables.get(identity) {
                        let table = match self.sequence_table_provenance_placeholders(
                            identity,
                            &info.arg_sorts,
                            &info.sort,
                            table,
                            euf_model
                                .function_table_terms
                                .get(identity)
                                .map(Vec::as_slice),
                        ) {
                            Ok(table) => table,
                            Err(e) => {
                                unrenderable!('symbols, format!(
                                    "(error \"model value for function {} is not available: {e}\")",
                                    quote_symbol(name)
                                ));
                            }
                        };
                        // Resolve @?N placeholders in function table values (#5452).
                        // The EUF model builds tables before theory values are merged,
                        // so Int/Real/BV-returning functions have @?N placeholders
                        // instead of concrete values. Resolve them now using the
                        // full model which has all theory values available.
                        let resolved = self.resolve_function_table(model, &table);
                        // Single-source datatype branch keys/values (stage-4
                        // review F3, #mv-dt-single-source): a table over
                        // selector-bearing datatype sorts must key its branches
                        // on the SAME rendered values the constants print —
                        // abstract-element keys (`(as @N!k N)`) can never match
                        // the printed constants under a validator, sending every
                        // application to the default arm (E:bad-model, voiding).
                        // Fail-closed: an unmappable table OMITS the definition
                        // (partial, non-voiding) rather than print an
                        // unfaithful one.
                        let resolved = match self.dt_egraph_rewrite_uf_table(
                            model,
                            &info.arg_sorts,
                            &info.sort,
                            &resolved,
                        ) {
                            super::dt_egraph_values::DtUfTableRewrite::NotApplicable => resolved,
                            super::dt_egraph_values::DtUfTableRewrite::Rewritten(t) => t,
                            super::dt_egraph_values::DtUfTableRewrite::Drop => {
                                omitted.push(name.to_string());
                                continue;
                            }
                        };
                        match self.format_function_table(
                            name,
                            &info.arg_sorts,
                            &info.sort,
                            &resolved,
                            model,
                            &overloaded,
                        ) {
                            Ok(def) => {
                                definitions.push(def);
                                euf_published = true;
                            }
                            // A table value with no model value cannot be
                            // printed honestly — surface the gap as an error
                            // instead of a fabricated default
                            // (#no-fabricated-model-values).
                            Err(e) => {
                                unrenderable!('symbols, format!(
                                    "(error \"model value for function {} is not available: {e}\")",
                                    quote_symbol(name)
                                ));
                            }
                        }
                    }
                }

                // GROUND-APPLICATION FALLBACK (#uf-interp-bv-lane).
                //
                // Not every lane routes uninterpreted functions through EUF. The
                // BV lanes (QF_UFBV / QF_AUFBV / UFBV) Ackermannize instead:
                // `f(a)` is bit-blasted to a fresh BV term constrained by
                // congruence clauses (`bv_axioms_euf.rs`), and no `EufModel` is
                // ever built — `model.euf_model` is `None`. The old code then
                // fell straight through to `continue`, silently dropping the
                // symbol, so every UF-bearing `sat` in those lanes published a
                // model with NO entry for `f` while z3 printed one.
                //
                // The independent gate reads the internal `Model`, not this
                // printout, but it must certify the SAME total interpretation
                // AY publishes.  Its ground-UF fallback therefore mirrors this
                // branch and parses these rows back into canonical model values;
                // an unreadable or conflicting table remains fail-closed.
                //
                // The values are not missing, only unrouted: `(get-value ((f
                // x)))` already answers on exactly these queries, because the
                // application term carries a committed value in the bit-blasted
                // assignment. So publish the table the solver ACTUALLY decided —
                // one row per ground application of `f` occurring in the
                // assertions, keyed by the model values of its arguments and
                // valued at the model value of the application. Nothing is
                // invented: every key and every value is read back through the
                // same `term_value_string` path `(get-value)` uses, and
                // `format_function_body` reuses the last row's real value as the
                // else-branch rather than a fabricated default.
                //
                // Fail-closed throughout: a symbol whose applications cannot ALL
                // be read back is OMITTED (partial model, non-voiding) rather
                // than published with a hole, and a table that is not a function
                // is omitted too — see `uf_table_from_ground_applications`.
                //
                // SCOPE LIMIT — ground applications only determine the function
                // when nothing else constrains it. A QUANTIFIED assertion does:
                // `(forall ((y S)) (=> (bvult y #x10) (= (f y) #x00)))` pins `f`
                // at points no ground application mentions, and the printed
                // `define-fun` is TOTAL, so its else-branch would answer #x07 at
                // those points and FALSIFY the very query AY answered `sat`
                // (measured: z3 replays the published model as `unsat`). The
                // table is genuinely undetermined there, so — per the
                // fail-closed rule — omit the symbol rather than invent the
                // missing part.
                if !euf_published && self.symbol_occurs_under_quantifier(name) {
                    omitted.push(name.to_string());
                    continue;
                }
                if !euf_published {
                    let arity = info.arg_sorts.len();
                    let apps = ground_uf_apps.get_or_insert_with(|| {
                        let mut collected: DetHashMap<(String, usize), Vec<(TermId, Vec<TermId>)>> =
                            DetHashMap::default();
                        let mut visited = DetHashSet::default();
                        for &assertion in &self.ctx.assertions {
                            self.collect_uf_applications(assertion, &mut collected, &mut visited);
                        }
                        // An exact finite-domain expansion is the ground form of
                        // an assertion that is STILL asserted; the quantifier
                        // loop restores the authored vector before output, so
                        // without this the instantiated applications the model
                        // actually committed values to are invisible here and
                        // every guarded-binder UF is published as nothing.
                        for root in self.finitely_expanded_ground_roots() {
                            self.collect_uf_applications(root, &mut collected, &mut visited);
                        }
                        collected
                    });
                    if let Some(applications) = apps.get(&(name.to_string(), arity)) {
                        match self.uf_table_from_ground_applications_in_read(read, applications) {
                            Some(table) => {
                                match self.format_function_table(
                                    name,
                                    &info.arg_sorts,
                                    &info.sort,
                                    &table,
                                    model,
                                    &overloaded,
                                ) {
                                    Ok(def) => definitions.push(def),
                                    // The reconstructed table is not a function
                                    // (two applications with equal argument
                                    // values disagree on the result). That is a
                                    // congruence violation, not something to
                                    // paper over: omit the symbol and let the
                                    // stderr omission notice surface it rather
                                    // than print a falsifying interpretation.
                                    Err(_) => omitted.push(name.to_string()),
                                }
                            }
                            // At least one application has no readable model
                            // value. Publishing a partial table would commit a
                            // WRONG value at the unread point via the else
                            // branch, so omit instead
                            // (#no-fabricated-model-values).
                            None => omitted.push(name.to_string()),
                        }
                    }
                }
                continue;
            }

            // For constants (no arguments), need term_id.
            if let Some(term_id) = info.term {
                // For constants (no arguments), look up value.
                let sort_str = format_sort_surface(&self.ctx, &info.sort);
                let shared_value = match aggregate_values.resolve(self, model, term_id) {
                    Ok(AggregateConstantValue::Value(value)) => Some(value),
                    Ok(AggregateConstantValue::Absent) => None,
                    // Preserve get-model's established poisoned-class omission;
                    // get-value treats this same refusal as a batch error.
                    Ok(AggregateConstantValue::Poisoned) => continue,
                    Err(error) => unrenderable!('symbols, format!("(error \"{error}\")")),
                };

                // Handle array-sorted symbols specially. Render a `store`-chain
                // that satisfies the asserted `(select a i) = v` constraints
                // (folding in reconstructed interpretation stores and the
                // definitional `(= a <array-expr>)` value, #5450) rather than the
                // bare const-array default, which would VIOLATE the assertions —
                // an invalid witness (#model-array-witness).
                if let Sort::Array(_) = &info.sort {
                    let array_value = if let Some(value) = shared_value {
                        value
                    } else if let Some(value) =
                        self.format_array_witness_value(model, term_id, &info.sort)
                    {
                        value
                    } else {
                        unrenderable!('symbols, format!(
                            "(error \"model value for array {} is not available\")",
                            quote_symbol(name)
                        ));
                    };
                    definitions.push(format!(
                        "  (define-fun {} () {}\n    {})",
                        quote_symbol(name),
                        sort_str,
                        array_value
                    ));
                    continue;
                }

                let quoted_name = quote_symbol(name);

                // The shared resolver already applied e-graph/poison priority
                // before the gate's entailed aggregate reconstruction.
                if let Some(ctor_expr) = shared_value {
                    definitions.push(format!(
                        "  (define-fun {quoted_name} () {sort_str} {ctor_expr})"
                    ));
                    continue;
                }

                // For DT-sorted variables, resolve to constructor expression (#5412).
                if let Sort::Uninterpreted(sort_name) = &info.sort {
                    if let Some(ctor_expr) = self.resolve_dt_value(sort_name, term_id, model) {
                        definitions.push(format!(
                            "  (define-fun {quoted_name} () {sort_str} {ctor_expr})"
                        ));
                        continue;
                    }
                }

                // Try EUF model first for uninterpreted sorts. This deliberately
                // EXCLUDES Int/Real: `evaluate_var` (the value the validation gate
                // checks) resolves an arithmetic variable LIA/LRA-FIRST and only
                // falls back to the merged EUF `term_values` on a miss. Reading
                // EUF first here inverted that order, so when a combined AUFLIA
                // solve committed one value to the arithmetic model (e.g. a
                // completion default `i2 = 0`) and left a STALE value in the merged
                // EUF map (`i2 = -2`), `(get-model)` printed the EUF value while
                // the gate validated the LIA value — the emitted witness then
                // falsified the formula (seed 21453, #array-completion-order). Int/
                // Real fall through to the LIA/LRA branches and the `evaluate_term`
                // renderer below, which share `evaluate_var`'s canonical order, so
                // emit stays faithful to what the gate checked.
                // A Seq-sorted EUF entry is only an INTERNAL equality-class
                // label, not an SMT-LIB sequence value. Sequence constants are
                // rendered below through `term_value_string`, which reads the
                // concrete `EvalValue::Seq` witness installed by completion.
                // Consulting EUF first leaked bare `@ay-seq!N` identifiers and
                // made get-model disagree with get-value.
                // FloatingPoint and RoundingMode constants likewise render
                // through the chain: the FP model owns their values (a mode is
                // what the FP circuit decoded from its bits).
                // `euf_printed_constant` owns the sort rule; the independent
                // gate reads the same function, so what prints here is what
                // the gate checked.
                if let Some(elem) = self.euf_printed_constant(model, term_id, &info.sort) {
                    let elem = format_model_atom_surface(&self.ctx, &info.sort, elem);
                    definitions.push(format!("  (define-fun {quoted_name} () {sort_str} {elem})"));
                    continue;
                }

                // Try LRA model for Real sort — but an exact NRA algebraic
                // witness (e.g. x = √2 for `x*x = 2`) is authoritative and
                // prints in z3 `root-obj` syntax.
                if matches!(info.sort, Sort::Real) {
                    if let Some(alg) = self.nra_algebraic_model.get(&term_id) {
                        // A residue value can reduce to an exact rational (a
                        // triangular-assignment variable): print it as such.
                        let value_str = match alg.to_number_for_output() {
                            Some(ay_nra::RealScalar::Rational(r)) => format_real(&r),
                            Some(ay_nra::RealScalar::Algebraic(n)) => n.alpha().to_smtlib(),
                            None => alg
                                .to_smtlib()
                                .unwrap_or_else(|| "(root-obj unrepresentable)".to_string()),
                        };
                        definitions.push(format!(
                            "  (define-fun {quoted_name} () {sort_str} {value_str})"
                        ));
                        continue;
                    }
                    if let Some(ref lra_model) = model.lra_model {
                        if let Some(val) = lra_model.values.get(&term_id) {
                            // Use the actual value without minimization.
                            let value_str = format_real(val);
                            definitions.push(format!(
                                "  (define-fun {quoted_name} () {sort_str} {value_str})"
                            ));
                            continue;
                        }
                    }
                }

                // Try LIA model for Int sort.
                if matches!(info.sort, Sort::Int) {
                    let debug = debug_model();
                    if debug {
                        safe_eprintln!(
                            "[MODEL] Looking up Int symbol '{}' term_id={}, lia_model={}",
                            name,
                            term_id.0,
                            model.lia_model.is_some()
                        );
                        if let Some(ref lm) = model.lia_model {
                            safe_eprintln!(
                                "[MODEL]   LIA model keys: {:?}",
                                lm.values.keys().map(|k| k.0).collect::<Vec<_>>()
                            );
                        }
                    }
                    if let Some(ref lia_model) = model.lia_model {
                        if let Some(val) = lia_model.values.get(&term_id) {
                            if debug {
                                safe_eprintln!(
                                    "[MODEL]   Found value {} for term_id={}",
                                    val,
                                    term_id.0
                                );
                            }
                            // Only apply minimization if counterexample minimization is enabled
                            // and bounds are available. Otherwise use the actual value.
                            let value_str = format_bigint(val);
                            definitions.push(format!(
                                "  (define-fun {quoted_name} () {sort_str} {value_str})"
                            ));
                            continue;
                        } else if debug {
                            safe_eprintln!(
                                "[MODEL]   NOT found in LIA model for term_id={}",
                                term_id.0
                            );
                        }
                    }
                    // Also check LRA model for Int (when using pure LRA solver for arithmetic).
                    if let Some(ref lra_model) = model.lra_model {
                        if let Some(val) = lra_model.values.get(&term_id) {
                            // Convert rational to integer if it's a whole number.
                            if val.is_integer() {
                                // Use the actual value without minimization.
                                let value_str = format_bigint(val.numer());
                                definitions.push(format!(
                                    "  (define-fun {quoted_name} () {sort_str} {value_str})"
                                ));
                                continue;
                            }
                        }
                    }
                }

                // Try BV model for BitVec sort.
                if let Sort::BitVec(bv) = &info.sort {
                    if let Some(ref bv_model) = model.bv_model {
                        if let Some(val) = bv_model.values.get(&term_id) {
                            let hex_str = format_bitvec(val, bv.width);
                            definitions.push(format!(
                                "  (define-fun {quoted_name} () {sort_str} {hex_str})"
                            ));
                            continue;
                        }
                    }
                }

                // Try String model for String sort.
                if matches!(info.sort, Sort::String) {
                    if let Some(ref string_model) = model.string_model {
                        if let Some(val) = string_model.values.get(&term_id) {
                            let value_str = string_literal(val);
                            definitions.push(format!(
                                "  (define-fun {quoted_name} () {sort_str} {value_str})"
                            ));
                            continue;
                        }
                    }
                }

                // Try FP model for FloatingPoint sort.
                if matches!(info.sort, Sort::FloatingPoint(..)) {
                    if let Some(ref fp_model) = model.fp_model {
                        if let Some(val) = fp_model.values.get(&term_id) {
                            let value_str = val.to_smtlib();
                            definitions.push(format!(
                                "  (define-fun {quoted_name} () {sort_str} {value_str})"
                            ));
                            continue;
                        }
                    }
                }

                // Seq-sorted variables: render the witness through the SAME
                // per-term core `(get-value)` uses (`term_value_string`), so
                // `(get-model)` and `(get-value)` can never diverge
                // (#model-seq-witness). That path consults the seq theory model
                // first (via `evaluate_term`), then — on a miss — resolves the
                // var through its asserted `(= s (seq.++ ...))` equality and the
                // len/nth reconstruction, emitting a binary `seq.++` tree. The
                // previous code rendered only the direct seq-theory entry and
                // fell through to the bare `(as seq.empty ...)` default whenever
                // that entry was absent (e.g. the value lived only in an asserted
                // concat), printing an INVALID witness that contradicted the
                // assertions.
                if matches!(info.sort, Sort::Seq(..)) {
                    match self.term_value_string_in_read(read, term_id) {
                        Ok(value_str) => {
                            definitions.push(format!(
                                "  (define-fun {quoted_name} () {sort_str} {value_str})"
                            ));
                        }
                        Err(e) => {
                            unrenderable!('symbols, format!(
                                "(error \"model value for {quoted_name} is not available: {e}\")"
                            ));
                        }
                    }
                    continue;
                }

                // Check bool_overrides for Bool variables recovered from
                // preprocessor substitutions or completed at finalize time
                // (#5512, #5524, model/completion.rs). Without this, a
                // variable whose value lives only in `bool_overrides` would
                // print as the SAT-model default (false) and contradict the
                // validated model. Solver-assigned SAT values still win: the
                // overrides are only consulted when the SAT model has no
                // entry, mirroring the `eval_var` lookup chain.
                if info.sort == Sort::Bool
                    && self
                        .term_value(&model.sat_model, &model.term_to_var, term_id)
                        .is_none()
                {
                    if let Some(&b) = model.bool_overrides.get(&term_id) {
                        let value_str = if b { "true" } else { "false" };
                        definitions.push(format!(
                            "  (define-fun {quoted_name} () {sort_str} {value_str})"
                        ));
                        continue;
                    }
                    if let Some(ref bv_model) = model.bv_model {
                        if let Some(&b) = bv_model.bool_overrides.get(&term_id) {
                            let value_str = if b { "true" } else { "false" };
                            definitions.push(format!(
                                "  (define-fun {quoted_name} () {sort_str} {value_str})"
                            ));
                            continue;
                        }
                    }
                }

                // For Int/Real variables with NO committed model value, resolve
                // from committed assertion equalities (e.g. `(= v (select a i))`)
                // and inequality bounds before defaulting to 0. This keeps
                // get-model consistent with the asserted equalities in pure
                // QF_(A)LIA where preprocessing eliminated the defining
                // equality and no arithmetic model was produced (#5450).
                //
                // GATE FAITHFULNESS (#array-completion-order, scalar variant):
                // run this re-derivation ONLY when the model commits no value for
                // the variable (`evaluate_term` is Unknown). When the model DOES
                // commit a value, that is the value the validation gates checked;
                // a print-time re-derivation from the assertions can DISAGREE with
                // it (a bound / equality the solver satisfied through a different
                // read), so printing the re-derived value would emit a witness the
                // gate never validated — the class caught by seed-21453, where the
                // gate confirmed `i2 = 0` (its committed value) while this path
                // re-derived `i2 = 2`, shipping an `(= 0 i2)` the emitted model
                // falsifies. The committed value falls through to the
                // `evaluate_term` renderer below, keeping emit faithful to the gate.
                if matches!(info.sort, Sort::Int | Sort::Real)
                    && matches!(read.evaluate(term_id), EvalValue::Unknown)
                {
                    let mut resolved = self.extract_value_from_asserted_equalities(model, term_id);
                    if resolved.is_none() {
                        resolved = match info.sort {
                            Sort::Int => self
                                .extract_int_from_assertion_bounds(term_id)
                                .map(|v| EvalValue::Rational(num_rational::BigRational::from(v))),
                            Sort::Real => self
                                .extract_real_from_assertion_bounds(term_id)
                                .map(EvalValue::Rational),
                            _ => None,
                        };
                    }
                    if let Some(value) = resolved {
                        if !matches!(value, EvalValue::Unknown) {
                            let value_str = match self.try_format_eval_value_user(&value, term_id) {
                                Ok(s) => s,
                                Err(e) => {
                                    unrenderable!('symbols, format!(
                                        "(error \"model value for {quoted_name} is not available: {e}\")"
                                    ));
                                }
                            };
                            definitions.push(format!(
                                "  (define-fun {quoted_name} () {sort_str} {value_str})"
                            ));
                            continue;
                        }
                    }
                }

                // Fall back to the SAT model for Bool, then to the full
                // evaluation chain (theory models + the completion slot filled
                // before validation). Every value printed here EXISTS in the
                // model the validation gate saw; if none exists, that is an
                // internal invariant violation (the model was accepted without
                // a total assignment) and it surfaces as an explicit error —
                // never as a fabricated sort default
                // (#no-fabricated-model-values).
                if matches!(info.sort, Sort::Bool) {
                    if let Some(b) = self.term_value(&model.sat_model, &model.term_to_var, term_id)
                    {
                        let value_str = if b { "true" } else { "false" };
                        definitions.push(format!(
                            "  (define-fun {quoted_name} () {sort_str} {value_str})"
                        ));
                        continue;
                    }
                }
                let mut eval_value = read.evaluate(term_id);
                // A declared constant with no FREE occurrence in the query is
                // unconstrained: the Z3 C API binds its quantifiers over the
                // caller's own constants (`Z3_mk_forall_const`), so `q` of
                // `forall q. (3 <= q <= 6) => a = 1` is a declared symbol the
                // solver never assigns. Any value is a witness; the canonical
                // default completes it (measured: "model value for q is not
                // available (internal error: sat accepted without a total
                // model)", and the API published `sat` with an EMPTY model).
                if matches!(eval_value, EvalValue::Unknown)
                    && !self.var_occurs_free_in_current_query(term_id)
                {
                    if let Some(default) = self.unconstrained_default_value(&info.sort) {
                        eval_value = default;
                    }
                }
                let value_str = match &eval_value {
                    // Unknown keeps its specific invariant-violation message
                    // (ordered BEFORE the user-facing delegation so the
                    // "sat accepted without a total model" diagnostic text is
                    // preserved).
                    EvalValue::Unknown => {
                        unrenderable!('symbols, format!(
                            "(error \"model value for {quoted_name} is not available \
                             (internal error: sat accepted without a total model)\")"
                        ));
                    }
                    // Sort-aware user-facing formatting (#real-fmt): Real
                    // constants print as z3-exact Real literals (`0.0`,
                    // `(- 5.0)`, `(/ 7.0 2.0)`), everything else exactly as
                    // before.
                    _ => match self.try_format_eval_value_user(&eval_value, term_id) {
                        Ok(s) => s,
                        Err(e) => {
                            unrenderable!('symbols, format!(
                                "(error \"model value for {quoted_name} is not available: {e}\")"
                            ));
                        }
                    },
                };
                definitions.push(format!(
                    "  (define-fun {quoted_name} () {sort_str} {value_str})"
                ));
            }
        }

        // Uninterpreted-sort universe elements (`@Sort!n`) are emitted ONLY as
        // sort-ascribed abstract values `(as @Sort!n Sort)` at their use sites
        // — never with `(declare-fun @Sort!n () Sort)` headers. The SMT-LIB
        // get-model response grammar (and Dolmen, the SMT-COMP Model-Validation
        // validator: `SAT OPEN MODEL? definition* CLOSE`) admits nothing but
        // define-fun forms inside the response, so a declare-fun header makes
        // the whole model unparseable (E:parsing-error — the QF_UFDT
        // stream_processor ModelParsingError class). Self-containment is
        // carried by the standard instead: an `@`-prefixed symbol is an
        // abstract value (SMT-LIB 2.7), a distinguished fresh constant of the
        // ascribed sort that needs no declaration — Dolmen accepts and
        // evaluates these natively (and rejects attempts to re-define them
        // with E:id-def-conflict). This is the same declaration-free form
        // cvc5 emits for uninterpreted-sort models.
        if unvalidated_candidate {
            self.finish_candidate_definitions(&mut definitions, &mut omitted);
        }
        // Reported by the caller, once for the rendering it returns:
        // `Self::surface_response` can render the model in both spellings.
        omitted.sort();
        omitted.dedup();
        *omissions = omitted;
        self.ascribe_overloaded_constant_definitions(&mut definitions, &overloaded);
        if let Some(admission) = model.constant_array_read_admission(self) {
            let mut text = ay_core::render_admission::Buffer::new(Some(&admission));
            if !text.push("(model\n") {
                return "(error \"retained model output refused\")".to_owned();
            }
            for definition in &definitions {
                if !text.push(definition) || !text.character('\n') {
                    return "(error \"retained model output refused\")".to_owned();
                }
            }
            if !text.character(')')
                || admission.check().is_err()
                || !super::evaluation_copies::validate(self)
            {
                return "(error \"retained model output refused\")".to_owned();
            }
            text.finish()
        } else if definitions.is_empty() {
            "(model\n)".to_string()
        } else {
            format!("(model\n{}\n)", definitions.join("\n"))
        }
    }

    /// Resolve the model to evaluate query terms against, mirroring the
    /// dummy-model fallback used for trivially-SAT cases (#8743).
    ///
    /// Returns the active `Model` on success, or an SMT-LIB `(error ...)`
    /// string when no model is available. The `dummy` slot is borrowed by the
    /// caller to own a synthesized empty model for the trivially-SAT path.
    fn value_query_model<'m>(&'m self, dummy: &'m mut Option<Model>) -> Result<&'m Model, String> {
        if !self.produce_models_enabled() {
            return Err("(error \"model generation is not enabled\")".to_string());
        }
        match (&self.last_result, &self.last_model) {
            (Some(SolveResult::Sat), Some(m)) if !self.materialized_scalar_functions_current(m) => {
                Err("(error \"materialized scalar function model is stale\")".to_string())
            }
            (Some(SolveResult::Sat), Some(m)) => Ok(m),
            (Some(SolveResult::Sat), None) => {
                // Trivially-SAT: every declared constant is unconstrained, so
                // queries evaluate against the completed default model
                // (#no-fabricated-model-values).
                *dummy = Some(self.completed_default_model());
                Ok(dummy.as_ref().expect("dummy model just assigned"))
            }
            _ => Err("(error \"model is not available\")".to_string()),
        }
    }

    /// Compute the printed value of a single term against `model`.
    ///
    /// This is the fallback renderer for `(get-value ...)` and the direct
    /// renderer for `(eval ...)`. The batch value command first consults its
    /// shared aggregate-constant authority; this method handles the remaining
    /// array/datatype/uninterpreted resolution and Unknown fallbacks, returning
    /// just the value text (no `(term value)` wrapper).
    ///
    /// `Err` when the term has NO value under the model: the former behavior
    /// printed a fabricated sort default (a lie — e.g. `(get-value ((f 1)))`
    /// answered `0` while the printed `(define-fun f ...)` said `5`); callers
    /// surface the error at the command level (#no-fabricated-model-values).
    pub(in crate::executor) fn term_value_string(
        &self,
        model: &Model,
        term_id: TermId,
    ) -> Result<String, String> {
        // Internal formatting helpers run under their caller's immutable
        // model-read/gate boundary; do not create a root scan for every field.
        self.check_evaluation_read()?;
        if !self.materialized_scalar_functions_current(model) {
            return Err("materialized scalar function model is stale".to_string());
        }
        // A published finite-domain lane model is one total model of its
        // signature; every printer reads it first (#dt-fd-ground-model).
        let result = match self.dt_fd_ground_value(model, term_id) {
            Some(value) => Ok(value),
            None => self.term_value_string_unstopped(model, term_id),
        };
        self.check_evaluation_read()?;
        result
    }

    fn term_value_string_in_read(
        &self,
        read: &dyn ModelRead,
        term_id: TermId,
    ) -> Result<String, String> {
        let model = read.model();
        self.check_evaluation_read()?;
        if let Some(value) = read.check_array_functions(term_id)? {
            return self
                .format_gate_model_value(&value, self.ctx.terms.sort(term_id))
                .ok_or_else(|| "array function query value cannot be rendered exactly".to_owned());
        }
        let result = match self.dt_fd_ground_value(model, term_id) {
            Some(value) => Ok(value),
            None => self.term_value_string_unstopped_in_read(model, term_id, Some(read)),
        };
        self.check_evaluation_read()?;
        result
    }

    /// [`Self::term_value_string`] without the stop checks and without the
    /// published lane model: the per-term authorities only.
    pub(in crate::executor) fn term_value_string_unstopped(
        &self,
        model: &Model,
        term_id: TermId,
    ) -> Result<String, String> {
        self.term_value_string_unstopped_in_read(model, term_id, None)
    }

    fn term_value_string_unstopped_in_read(
        &self,
        model: &Model,
        term_id: TermId,
        read: Option<&dyn ModelRead>,
    ) -> Result<String, String> {
        match self.completed_model_value(model, term_id) {
            Ok(Some(value)) => {
                if model.has_constant_array_functions() {
                    let admission = model
                        .constant_array_read_admission(self)
                        .ok_or("retained array owner unavailable")?;
                    return self
                        .retained_array_render_value(
                            &value,
                            self.ctx.terms.sort(term_id),
                            &admission,
                        )
                        .map_err(|error| error.to_string());
                }
                return self
                    .format_gate_model_value(&value, self.ctx.terms.sort(term_id))
                    .ok_or_else(|| "completed model value cannot be rendered exactly".to_string());
            }
            Ok(None) => {}
            Err(()) => return Err("retained array model value is unavailable".to_string()),
        }
        // Route projection applications to the selected argument through this
        // same per-term formatting core. This preserves the evaluator's
        // selected argument and handles non-scalar sorts (arrays, datatypes,
        // sequences) using the selected argument's established renderer. An
        // unavailable selected value remains unavailable; no finite-table or
        // asserted-equality fallback may replace the total projection. Peeling
        // is iterative and bounded so a deeply nested native query cannot grow
        // the Rust stack through this formatting path.
        let term_id = match model
            .projection_ufs
            .peel_application_chain(&self.ctx.terms, term_id)
        {
            Ok(Some(projected_term)) => projected_term,
            Ok(None) => term_id,
            Err(error) => return Err(error.to_string()),
        };
        let sort = self.ctx.terms.sort(term_id);
        if let Some(value) = self.certified_const_array_output(model, term_id) {
            return value;
        }
        // This precedes asserted-equality/witness recovery as well as raw
        // scalar lookup: a refused owned read cannot acquire a second value.
        if let Some(value) = self.certified_const_array_read(model, term_id) {
            return self.try_format_eval_value_user(&value, term_id);
        }
        if matches!(sort, Sort::Array(_)) {
            if self.is_ordinary_array_function_application(term_id)? {
                // A per-application extraction default is not a coherent UF
                // interpretation. Rich retained packages answer before this
                // fallback; unsupported/ambiguous ordinary UFs must refuse.
                return self
                    .functional_array_render(model, term_id)
                    .map_err(|error| error.to_string())?
                    .ok_or_else(|| {
                        "array-valued function has no coherent committed interpretation".to_owned()
                    });
            }
            // Render a `store`-chain that satisfies the asserted
            // `(select term i) = v` constraints, mirroring `(get-model)`
            // (#model-array-witness).
            self.format_array_witness_value(model, term_id, sort)
                .ok_or_else(|| "array model value is incomplete".to_string())
        } else if let Some(witness) = self.array_witness_scalar_select(model, term_id) {
            // A scalar `(select b i)` read on a store-equality-dependent array
            // must agree with the `store`-chain `(get-model)` prints for `b` (the
            // raw evaluator can return a stale don't-care that the printed witness
            // overrides via the store axiom, #model-array-witness).
            Ok(witness)
        } else if let Sort::Uninterpreted(sort_name) = sort {
            // DT-sorted terms: resolve to constructor expression (#5412).
            match self.resolve_dt_value(sort_name, term_id, model) {
                Some(ctor_expr) => Ok(ctor_expr),
                None => {
                    let eval_value = read.map_or_else(
                        || self.evaluate_term(model, term_id),
                        |read| read.evaluate(term_id),
                    );
                    self.try_format_eval_value_user(&eval_value, term_id)
                }
            }
        } else {
            let eval_value = read.map_or_else(
                || self.evaluate_term(model, term_id),
                |read| read.evaluate(term_id),
            );
            self.check_evaluation_read()?;
            // For selector apps returning Unknown, scan assertions (#5432).
            let eval_value = if matches!(eval_value, EvalValue::Unknown) {
                self.extract_value_from_asserted_equalities(model, term_id)
                    .unwrap_or(eval_value)
            } else {
                eval_value
            };
            self.check_evaluation_read()?;
            // For Real/Int-sorted terms still Unknown after equality scan,
            // try bound extraction from inequality assertions (#5506).
            let eval_value = if matches!(eval_value, EvalValue::Unknown) {
                match sort {
                    Sort::Real => self
                        .extract_real_from_assertion_bounds(term_id)
                        .map(EvalValue::Rational)
                        .unwrap_or(eval_value),
                    Sort::Int => self
                        .extract_int_from_assertion_bounds(term_id)
                        .map(|v| EvalValue::Rational(num_rational::BigRational::from(v)))
                        .unwrap_or(eval_value),
                    _ => eval_value,
                }
            } else {
                eval_value
            };
            self.check_evaluation_read()?;
            // For a Seq-sorted term with no direct theory value or defining
            // `(= s ...)` equality, reconstruct the witness from its
            // `(seq.len s) = N` / `(seq.nth s i) = v` constraints (#model-seq-witness).
            // Without this, the bare `(as seq.empty ...)` default (length 0)
            // VIOLATES a `(seq.len s) = N>0` constraint and re-feeds to unsat.
            let eval_value =
                if matches!(eval_value, EvalValue::Unknown) && matches!(sort, Sort::Seq(_)) {
                    self.reconstruct_seq_from_len_nth(model, term_id)
                        .unwrap_or(eval_value)
                } else {
                    eval_value
                };
            self.check_evaluation_read()?;
            // A UF application at an argument point the function table does
            // not list reads back the printed define-fun's ELSE branch, so
            // (get-value) never contradicts (get-model).
            if matches!(eval_value, EvalValue::Unknown) {
                if let Some(else_value) = self.uf_unlisted_point_value(model, term_id) {
                    return else_value;
                }
            }
            self.try_format_eval_value_user(&eval_value, term_id)
        }
    }

    /// Model-completion read of a UF application at an argument tuple its
    /// function table does not list.
    ///
    /// The printed `(define-fun f ...)` is TOTAL: its else branch is the last
    /// resolved table entry (see `format_function_table`), or the canonical
    /// default body for an empty table. `(get-value ((f <unlisted args>)))`
    /// must therefore answer exactly that else value — the former sort-default
    /// fabrication contradicted the printed model
    /// (#no-fabricated-model-values). `None` when the term is not a UF
    /// application with a table, or when an argument itself has no model value
    /// (the read is then genuinely unavailable and the caller errors).
    fn uf_unlisted_point_value(
        &self,
        model: &Model,
        term_id: TermId,
    ) -> Option<Result<String, String>> {
        let TermData::App(sym, args) = self.ctx.terms.get(term_id) else {
            return None;
        };
        if args.is_empty() {
            return None;
        }
        let euf_model = model.euf_model.as_ref()?;
        let table = euf_model.function_tables.get(sym.name())?;
        // Every argument must itself have a concrete model value; otherwise
        // no specific point is being read and no table row can be excluded.
        for &arg in args {
            if matches!(self.evaluate_term(model, arg), EvalValue::Unknown) {
                return None;
            }
        }
        let result_sort = self.ctx.terms.sort(term_id);
        let arg_sorts: Vec<Sort> = args
            .iter()
            .map(|&arg| self.ctx.terms.sort(arg).clone())
            .collect();
        let table = match self.sequence_table_provenance_placeholders(
            sym.name(),
            &arg_sorts,
            result_sort,
            table,
            euf_model
                .function_table_terms
                .get(sym.name())
                .map(Vec::as_slice),
        ) {
            Ok(table) => table,
            Err(e) => return Some(Err(e)),
        };
        let resolved = self.resolve_function_table(model, &table);
        Some(match resolved.last() {
            // Same else value `format_function_table` prints.
            Some((_, else_value)) => self.resolve_table_value(else_value, result_sort, model),
            // Empty table: the same unconstrained-function body `(get-model)`
            // prints.
            None => Ok(self.default_value_surface(result_sort)),
        })
    }

    /// The `(get-value)` answer for one requested term.
    fn get_value_string(
        &self,
        read: &dyn ModelRead,
        aggregate_values: &AggregateConstantValues,
        term_id: TermId,
    ) -> Result<String, String> {
        if let Some(value) = read.check_array_functions(term_id)? {
            return self
                .format_gate_model_value(&value, self.ctx.terms.sort(term_id))
                .ok_or_else(|| "array function query value cannot be rendered exactly".to_owned());
        }
        if !self.materialized_scalar_functions_current(read.model()) {
            return Err("materialized scalar function model is stale".to_string());
        }
        let value = self.get_value_core(read, aggregate_values, term_id);
        if value.is_err() && matches!(self.ctx.terms.sort(term_id), Sort::Bool) {
            // A Boolean combination whose leaves all have printed values has
            // the value those printed values give it (#get-value-printed-bool).
            let mut memo = DetHashMap::default();
            if let Some(b) = self.gv_printed_bool(
                read,
                aggregate_values,
                term_id,
                &mut memo,
                PRINTED_BOOL_DEPTH,
            ) {
                return Ok(b.to_string());
            }
        }
        value
    }

    /// A Boolean term evaluated over the printed values of its parts
    /// (#get-value-printed-bool): a part with its own `(get-value)` answer
    /// reads it; connectives and `ite` combine their parts; `=` / `distinct`
    /// compare their arguments' printed values when those are ground texts
    /// that are their own identity (`canonical_datatype_value`). The
    /// per-term evaluator has no value for, e.g., `(= k29 k30)` over two
    /// eliminated single-constructor records whose fields nothing
    /// constrains, while `(get-value)` prints both records; the answer here
    /// is the one those printed records give, so the printed values stay
    /// one model (E13 round 6, `gvlane_61_0050`). `None` when some part has
    /// no printed value.
    fn gv_printed_bool(
        &self,
        read: &dyn ModelRead,
        aggregate_values: &AggregateConstantValues,
        term: TermId,
        memo: &mut DetHashMap<TermId, Option<bool>>,
        fuel: u32,
    ) -> Option<bool> {
        if let Some(&known) = memo.get(&term) {
            return known;
        }
        let value = self.gv_printed_bool_uncached(read, aggregate_values, term, memo, fuel);
        memo.insert(term, value);
        value
    }

    fn gv_printed_bool_uncached(
        &self,
        read: &dyn ModelRead,
        aggregate_values: &AggregateConstantValues,
        term: TermId,
        memo: &mut DetHashMap<TermId, Option<bool>>,
        fuel: u32,
    ) -> Option<bool> {
        if fuel == 0 {
            return None;
        }
        if let Ok(value) = self.get_value_core(read, aggregate_values, term) {
            return match value.as_str() {
                "true" => Some(true),
                "false" => Some(false),
                _ => None,
            };
        }
        let fuel = fuel - 1;
        match self.ctx.terms.get(term) {
            TermData::Not(inner) => self
                .gv_printed_bool(read, aggregate_values, *inner, memo, fuel)
                .map(|b| !b),
            TermData::Ite(c, t, e) => {
                let branch = if self.gv_printed_bool(read, aggregate_values, *c, memo, fuel)? {
                    *t
                } else {
                    *e
                };
                self.gv_printed_bool(read, aggregate_values, branch, memo, fuel)
            }
            TermData::App(sym, args) => match sym.name() {
                "not" if args.len() == 1 => self
                    .gv_printed_bool(read, aggregate_values, args[0], memo, fuel)
                    .map(|b| !b),
                "and" | "or" => {
                    let absorbing = sym.name() == "or";
                    let mut unknown = false;
                    for &a in args {
                        match self.gv_printed_bool(read, aggregate_values, a, memo, fuel) {
                            Some(b) if b == absorbing => return Some(absorbing),
                            Some(_) => {}
                            None => unknown = true,
                        }
                    }
                    (!unknown).then_some(!absorbing)
                }
                "=>" | "xor" => {
                    let mut values = Vec::with_capacity(args.len());
                    for &a in args {
                        values.push(self.gv_printed_bool(read, aggregate_values, a, memo, fuel)?);
                    }
                    if sym.name() == "xor" {
                        return Some(values.iter().fold(false, |acc, &b| acc ^ b));
                    }
                    let (last, premises) = values.split_last()?;
                    Some(!premises.iter().all(|&b| b) || *last)
                }
                "=" | "distinct" if args.len() >= 2 => {
                    let mut values = Vec::with_capacity(args.len());
                    for &a in args {
                        let value = if matches!(self.ctx.terms.sort(a), Sort::Bool) {
                            self.gv_printed_bool(read, aggregate_values, a, memo, fuel)?
                                .to_string()
                        } else {
                            self.get_value_string(read, aggregate_values, a)
                                .ok()
                                .filter(|v| self.canonical_datatype_value(v))?
                        };
                        values.push(value);
                    }
                    Some(if sym.name() == "=" {
                        values.iter().all(|v| *v == values[0])
                    } else {
                        (0..values.len())
                            .all(|i| (i + 1..values.len()).all(|j| values[i] != values[j]))
                    })
                }
                _ => None,
            },
            _ => None,
        }
    }

    /// [`Self::get_value_string`] without the printed-Boolean fallback.
    fn get_value_core(
        &self,
        read: &dyn ModelRead,
        aggregate_values: &AggregateConstantValues,
        term_id: TermId,
    ) -> Result<String, String> {
        let model = read.model();
        // A published finite-domain lane model values every term of its
        // signature as ONE total model (#dt-fd-ground-model); the
        // per-term authorities below would value a selector the query
        // does not apply independently of its argument's value.
        if let Some(value) = self.dt_fd_ground_value(model, term_id) {
            return Ok(value);
        }
        // A wrong-constructor selector application the model never valued
        // reads the printed selector table (#get-value-wrong-ctor), before
        // the aggregate reader: that reader completes a datatype-sorted term
        // interned after the check (a `(get-value)` term such as
        // `(tl13 nil15)`) with a value of its own, which the printed table
        // does not carry (E13 round 6, `incrgv_61_0017`).
        if let Some(value) = self.wrong_ctor_selector_table_value(model, term_id)? {
            return Ok(value);
        }
        match aggregate_values.resolve(self, model, term_id)? {
            AggregateConstantValue::Value(value) => Ok(value),
            AggregateConstantValue::Absent => {
                // A non-query selector on its owning constructor projects
                // the argument's printed field (#get-value-wrong-ctor).
                if let Some(value) = self.wrong_ctor_selector_case_value(model, term_id)? {
                    return Ok(value);
                }
                // A tester answers for its argument's printed value
                // (#get-value-tester-coherence).
                if let Some((arg, tested)) = self.tester_application(term_id) {
                    if let Ok(value) = self.get_value_string(read, aggregate_values, arg) {
                        if let Some(answer) = self.tester_on_printed_value(arg, tested, &value) {
                            return Ok(answer.to_string());
                        }
                    }
                }
                // So does an equality over datatype values
                // (#get-value-tester-coherence).
                if let Some(args) = self.datatype_comparison(term_id) {
                    let mut values = Vec::with_capacity(args.len());
                    for &arg in args {
                        match self.get_value_string(read, aggregate_values, arg) {
                            Ok(value) if self.canonical_datatype_value(&value) => {
                                values.push(value);
                            }
                            _ => break,
                        }
                    }
                    if values.len() == args.len() {
                        let equal = values.iter().all(|v| *v == values[0]);
                        let distinct = (0..values.len())
                            .all(|i| (i + 1..values.len()).all(|j| values[i] != values[j]));
                        let is_eq = matches!(self.ctx.terms.get(term_id), TermData::App(sym, _) if sym.name() == "=");
                        return Ok(if is_eq { equal } else { distinct }.to_string());
                    }
                }
                self.term_value_string_in_read(read, term_id)
            }
            AggregateConstantValue::Poisoned => {
                Err("datatype model class is incoherent".to_string())
            }
        }
    }

    /// Generate output for get-value command.
    pub(crate) fn values(&self, requested: &[(String, TermId)]) -> String {
        self.checked_evaluation_output(|| {
            self.surface_response(|spelling| self.values_unstopped(requested, spelling))
        })
    }

    /// [`Self::values`] in [`ValueSpelling::Sorted`], for a decoder inside
    /// this process that holds the solver.
    pub(crate) fn values_for_decoder(&self, requested: &[(String, TermId)]) -> String {
        self.checked_evaluation_output(|| self.values_unstopped(requested, ValueSpelling::Sorted))
    }

    fn values_unstopped(&self, requested: &[(String, TermId)], spelling: ValueSpelling) -> String {
        // Check if we have a model.
        //
        // For trivially-SAT cases where `last_model` is `None` (e.g., all
        // assertions simplified away during preprocessing), we still need
        // to evaluate `(select (store ...) i)` terms against the term DAG
        // via `evaluate_term`/`evaluate_select`. Mirror the dummy-model
        // pattern used by `get_objectives` so that store-chain resolution
        // and `const-array` evaluation still work (#8743).
        let mut dummy = None;
        let model = match self.value_query_model(&mut dummy) {
            Ok(m) => m,
            Err(e) => return e,
        };

        self.with_model_construction_read(model, |read| {
            self.values_from_selected(read, requested, spelling)
        })
    }

    fn values_from_selected(
        &self,
        read: &dyn ModelRead,
        requested: &[(String, TermId)],
        spelling: ValueSpelling,
    ) -> String {
        let model = read.model();
        // Memoize evaluation across ALL requested terms (#eval-memo). `get-value`
        // over N terms that share large subterms — e.g. a Kani query's ~190
        // violation flags, each a boolean expression reading the same 20M-node
        // model — otherwise re-evaluates every shared subterm once PER term (the
        // result memo is inert outside a session). One session computes each
        // unique subterm exactly once. Verdict-preserving (the model is immutable
        // for the query); dropped at function exit.
        let _eval_memo = super::EvalMemoSession::new();
        let _t_gv = std::time::Instant::now();
        let aggregate_values = match AggregateConstantValues::for_values(self, model, requested) {
            Ok(values) => values,
            Err(error) => return format!("(error \"{error}\")"),
        };

        // Echo the term's ORIGINAL SMT-LIB text as the key (per the SMT-LIB
        // spec), not a reconstruction of the elaborated term — a
        // single-constructor datatype constant `w` is eagerly eliminated to
        // `(wrap <field>)`, whose fresh field var must not leak into the key.
        let mut pairs: Vec<String> = Vec::with_capacity(requested.len());
        let overloaded = self.overloaded_ctors_for(spelling);
        for (term_str, term_id) in requested {
            match self.get_value_string(read, &aggregate_values, *term_id) {
                Ok(value_str) => {
                    // In `ValueSpelling::Surface` this may ascribe an
                    // overloaded nullary constructor (#overloaded-nil-surface).
                    let sort = self.ctx.terms.sort(*term_id);
                    let value_str = self.ascribe_overloaded_ctors(&value_str, sort, &overloaded);
                    pairs.push(format!("({term_str} {value_str})"));
                }
                // A term with no value under the model errors honestly —
                // never a fabricated default (#no-fabricated-model-values).
                Err(e) => return format!("(error \"value of {term_str} is not available: {e}\")"),
            }
        }

        if ay_core::misc_cli_flags().phase_trace {
            eprintln!(
                "c phase-trace TIMING get-value n={} {:.1}s",
                requested.len(),
                _t_gv.elapsed().as_secs_f64()
            );
        }
        format!("({})", pairs.join(" "))
    }

    /// Reconstruct a UF interpretation table from the ground applications of a
    /// symbol, for lanes that never build an `EufModel` (#uf-interp-bv-lane).
    ///
    /// Each row is `(argument values, application value)` read back through the
    /// same `term_value_string` path `(get-value ...)` uses, so every entry is a
    /// value the solver committed to — this publishes the table it HAS, it does
    /// not invent one.
    ///
    /// Returns `None` when any application or argument has no readable value
    /// under the model. That is deliberate: a partial table still prints a TOTAL
    /// `define-fun`, whose else-branch would then commit some other row's value
    /// at the unread point — a fabricated value in all but name
    /// (#no-fabricated-model-values). The caller omits the symbol instead.
    /// Whether `term` is a quantifier that the canonical finite-domain expander
    /// replaced, in THIS solve, with a ground conjunction that is still
    /// available to the model census.
    ///
    /// Two conditions make the record usable. Its ORIGINAL must still be one of
    /// the current assertions — the quantifier loop restores the authored
    /// vector after the ground run, so a record whose original is gone no
    /// longer describes anything that is asserted. And its replacement must be
    /// quantifier-free, because `collect_uf_applications` does not descend into
    /// binders and would otherwise silently miss constrained points. Together
    /// they make `expanded` an exact ground equivalent of a formula asserted
    /// right now, so the applications it mentions are EXACTLY the points at
    /// which that assertion constrains a function symbol — which is the premise
    /// the blanket quantifier guard below was conservatively assuming could
    /// never hold.
    pub(super) fn quantifier_is_finitely_expanded(&self, term: TermId) -> bool {
        self.quant_expansion_records.iter().any(|record| {
            record.original == term
                && self.ctx.assertions.contains(&record.original)
                && !crate::ematching::contains_quantifier(&self.ctx.terms, record.expanded)
        })
    }

    /// Ground replacements of the quantifiers
    /// [`Self::quantifier_is_finitely_expanded`] accepts, to be censused
    /// alongside `ctx.assertions`.
    pub(super) fn finitely_expanded_ground_roots(&self) -> Vec<TermId> {
        self.quant_expansion_records
            .iter()
            .filter(|record| self.quantifier_is_finitely_expanded(record.original))
            .map(|record| record.expanded)
            .collect()
    }

    /// True when `name` occurs anywhere beneath a quantifier in the assertions.
    ///
    /// Such a symbol is NOT determined by its ground applications: a
    /// `(forall ((y S)) ... (f y) ...)` constrains `f` at points no ground
    /// application mentions. See
    /// [`Self::uf_table_from_ground_applications`] for why that makes the
    /// ground-application table unpublishable.
    pub(super) fn symbol_occurs_under_quantifier(&self, name: &str) -> bool {
        fn walk(
            exec: &Executor,
            term: TermId,
            name: &str,
            under_quant: bool,
            seen: &mut DetHashSet<(TermId, bool)>,
        ) -> bool {
            if !seen.insert((term, under_quant)) {
                return false;
            }
            match exec.ctx.terms.get(term) {
                TermData::App(sym, args) => {
                    if under_quant && sym.name() == name {
                        return true;
                    }
                    args.iter().any(|&a| walk(exec, a, name, under_quant, seen))
                }
                TermData::Not(inner) => walk(exec, *inner, name, under_quant, seen),
                TermData::Ite(c, t, e) => {
                    walk(exec, *c, name, under_quant, seen)
                        || walk(exec, *t, name, under_quant, seen)
                        || walk(exec, *e, name, under_quant, seen)
                }
                TermData::Let(bindings, body) => {
                    bindings
                        .iter()
                        .any(|(_, b)| walk(exec, *b, name, under_quant, seen))
                        || walk(exec, *body, name, under_quant, seen)
                }
                TermData::Forall(_, body, triggers) | TermData::Exists(_, body, triggers) => {
                    // A binder the canonical finite-domain expander replaced
                    // with a quantifier-free ground conjunction constrains the
                    // symbol at exactly the points that conjunction applies it
                    // to, and the census below walks that conjunction. So this
                    // is NOT an occurrence whose points the ground table would
                    // miss, and omitting the symbol for it would discard an
                    // interpretation the solve already checked.
                    if exec.quantifier_is_finitely_expanded(term) {
                        return false;
                    }
                    walk(exec, *body, name, true, seen)
                        || triggers
                            .iter()
                            .flatten()
                            .any(|&t| walk(exec, t, name, true, seen))
                }
                _ => false,
            }
        }

        let mut seen = DetHashSet::default();
        self.ctx
            .assertions
            .iter()
            .any(|&a| walk(self, a, name, false, &mut seen))
    }

    pub(super) fn uf_table_from_ground_applications(
        &self,
        model: &Model,
        applications: &[(TermId, Vec<TermId>)],
    ) -> Option<Vec<(Vec<String>, String)>> {
        let read = ModelConstructionRead::new(self, model).ok()?;
        let result = self.uf_table_from_ground_applications_in_read(&read, applications);
        read.finish().ok()?;
        result
    }

    fn uf_table_from_ground_applications_in_read(
        &self,
        read: &dyn ModelRead,
        applications: &[(TermId, Vec<TermId>)],
    ) -> Option<Vec<(Vec<String>, String)>> {
        let mut table = Vec::with_capacity(applications.len());
        for (app, args) in applications {
            let value = self.uf_table_candidate_value_in_read(read, *app).ok()?;
            let mut key = Vec::with_capacity(args.len());
            for &arg in args {
                key.push(self.uf_table_candidate_value_in_read(read, arg).ok()?);
            }
            table.push((key, value));
        }
        Some(table)
    }

    /// Candidate rows precede the total-table interpretation they construct.
    /// Never enter public UF-table evaluation here: that would recursively
    /// ask this same builder for its unfinished table. These per-application
    /// values are only candidate DATA; duplicate argument rows and all authored
    /// assertions still pass the existing independent total-model gate.
    fn uf_table_candidate_value_in_read(
        &self,
        read: &dyn ModelRead,
        term: TermId,
    ) -> Result<String, String> {
        self.check_evaluation_read()?;
        let model = read.model();
        if !self.materialized_scalar_functions_current(model) {
            return Err("materialized scalar function model is stale".to_owned());
        }
        let result = if self.is_ordinary_array_function_application(term)? {
            match self.completed_model_value(model, term) {
                Err(()) => return Err("retained array model value is unavailable".to_owned()),
                Ok(Some(value)) => self
                    .format_gate_model_value(&value, self.ctx.terms.sort(term))
                    .ok_or_else(|| "array candidate cannot be rendered exactly".to_owned()),
                Ok(None) => {
                    if let Some(value) = self.certified_const_array_output(model, term) {
                        value
                    } else if let Some(value) = self.functional_array_render(model, term)? {
                        Ok(value)
                    } else {
                        self.format_array_witness_value(model, term, self.ctx.terms.sort(term))
                            .ok_or_else(|| "array candidate is incomplete".to_owned())
                    }
                }
            }
        } else {
            self.term_value_string_unstopped_in_read(model, term, Some(read))
        };
        self.check_evaluation_read()?;
        result
    }

    /// Generate output for the Z3 `(eval <term>)` command.
    ///
    /// Evaluates a single term in the current model and prints just its value
    /// (no `(term value)` pairing), matching Z3's `eval` surface. Shares the
    /// model resolution and per-term evaluation with `(get-value ...)`.
    pub(crate) fn eval_term(&self, term_id: TermId) -> String {
        let mut dummy = None;
        let model = match self.value_query_model(&mut dummy) {
            Ok(m) => m,
            Err(e) => return e,
        };
        self.with_model_construction_read(model, |read| {
            match self.term_value_string_in_read(read, term_id) {
                Ok(value_str) => value_str,
                Err(e) => format!("(error \"value is not available: {e}\")"),
            }
        })
    }
}

/// A `sat` from a lane that Ackermannizes uninterpreted functions (the BV
/// lanes) must still PUBLISH an interpretation for every declared UF, and the
/// interpretation it publishes must agree with `(get-value ...)` on the same
/// applications (#uf-interp-bv-lane).
///
/// Before the ground-application fallback these lanes built no `EufModel`, so
/// `(get-model)` silently dropped every function symbol: the answer was `sat`,
/// the internal gate said `confirmed-sat`, and the published witness was
/// nonetheless missing the one interpretation a checker needs.
#[cfg(test)]
mod uf_interp_bv_lane_tests {
    use super::Executor;
    use ay_frontend::parse;

    fn model_of(script: &str) -> String {
        let commands = parse(script).expect("script parses");
        let mut exec = Executor::new();
        exec.execute_all(&commands).expect("script executes");
        exec.model()
    }

    #[test]
    fn qf_ufbv_sat_publishes_a_bv_function_interpretation() {
        let out = model_of(
            "(set-logic QF_UFBV)
             (declare-fun f ((_ BitVec 8)) (_ BitVec 8))
             (declare-const x (_ BitVec 8))
             (assert (= (f x) #x07))
             (check-sat)",
        );
        assert!(
            out.contains("(define-fun f ((x0 (_ BitVec 8))) (_ BitVec 8)"),
            "QF_UFBV sat must publish an interpretation for `f`, not drop it: {out}"
        );
        assert!(
            out.contains("#x07"),
            "the published interpretation must carry the constrained value: {out}"
        );
    }

    /// The drop was never about the BV *argument* sort — a UF is dropped when
    /// BV appears anywhere in its signature, so a BV-RETURNING function over an
    /// Int domain was missing too.
    #[test]
    fn bv_returning_uf_over_int_domain_is_published() {
        let out = model_of(
            "(set-logic ALL)
             (declare-fun f (Int) (_ BitVec 8))
             (declare-const y Int)
             (assert (= (f y) #x07))
             (check-sat)",
        );
        assert!(
            out.contains("(define-fun f ((x0 Int)) (_ BitVec 8)"),
            "a BV-returning UF must be published: {out}"
        );
    }

    /// Two applications at distinct argument points must both survive into the
    /// table, so the published function is not a constant that contradicts one
    /// of them.
    #[test]
    fn distinct_application_points_both_reach_the_table() {
        let out = model_of(
            "(set-logic QF_UFBV)
             (declare-fun f ((_ BitVec 8)) (_ BitVec 8))
             (declare-const x (_ BitVec 8))
             (assert (= (f x) #x07))
             (assert (= (f #x01) #x09))
             (check-sat)",
        );
        assert!(
            out.contains("(define-fun f "),
            "interpretation is published: {out}"
        );
        assert!(
            out.contains("#x07") && out.contains("#x09"),
            "both constrained application values must appear in the table: {out}"
        );
    }

    /// A multi-argument UF keys its rows on the full argument tuple.
    #[test]
    fn multi_argument_uf_is_published_with_all_parameters() {
        let out = model_of(
            "(set-logic QF_UFBV)
             (declare-fun g ((_ BitVec 4) (_ BitVec 4)) (_ BitVec 4))
             (declare-const a (_ BitVec 4))
             (declare-const b (_ BitVec 4))
             (assert (= (g a b) #x3))
             (assert (= (g b a) #x5))
             (check-sat)",
        );
        assert!(
            out.contains("(define-fun g ((x0 (_ BitVec 4)) (x1 (_ BitVec 4))) (_ BitVec 4)"),
            "a 2-ary UF must be published with both parameters: {out}"
        );
    }

    /// SOUNDNESS GUARD. Ground applications do not determine a function that a
    /// QUANTIFIER also constrains, and the printed `define-fun` is total — so a
    /// table built only from ground rows would answer the last row's value at
    /// every quantified point and falsify the query.
    ///
    /// Here `(forall ((y ..)) (=> (bvult y #x10) (= (f y) #x00)))` forces
    /// `f(#x00) = #x00`, while the only ground application is `f(#xff) = #x07`.
    /// Publishing `f = λ. #x07` made z3 replay the model as `unsat`. The
    /// fallback must decline instead: an omission is a partial witness, a
    /// falsifying interpretation is a wrong one.
    #[test]
    fn quantified_symbol_is_omitted_not_published_from_ground_rows() {
        let out = model_of(
            "(set-logic UFBV)
             (declare-fun f ((_ BitVec 8)) (_ BitVec 8))
             (assert (forall ((y (_ BitVec 8))) (=> (bvult y #x10) (= (f y) #x00))))
             (assert (= (f #xff) #x07))
             (check-sat)",
        );
        assert!(
            !out.contains("(define-fun f ((x0 (_ BitVec 8))) (_ BitVec 8)\n    #x07)"),
            "a quantifier-constrained UF must NOT be published as the constant \
             taken from its single ground row — that model falsifies the forall: {out}"
        );
    }

    /// A DEFINED symbol keeps its problem-text interpretation: the fallback must
    /// not re-emit one (a definition conflict for any validator).
    #[test]
    fn defined_functions_are_still_not_re_emitted() {
        let out = model_of(
            "(set-logic QF_UFBV)
             (define-fun d ((v (_ BitVec 8))) (_ BitVec 8) (bvadd v #x01))
             (declare-const x (_ BitVec 8))
             (assert (= (d x) #x07))
             (check-sat)",
        );
        assert!(
            !out.contains("(define-fun d "),
            "a define-fun symbol must not be re-emitted by the fallback: {out}"
        );
    }
}

/// Render `lambda x-bar. k + sum_i c_i * x_i` as an SMT-LIB body over the
/// printer's own `x!i` parameter spellings.
///
/// The parameter names are minted here from the body's arity rather than
/// passed in, so they cannot drift from the `(define-fun f ((x!0 Int) ..) ..)`
/// signature emitted beside them — both come from the same `x!{index}` rule.
/// `None` on an empty body: a nullary head is published as a constant, never
/// through this path.
fn format_linear_int_body(linear: &LinearIntBody) -> Option<String> {
    if linear.arity() == 0 {
        return None;
    }
    let zero = num_bigint::BigInt::from(0);
    let one = num_bigint::BigInt::from(1);
    let minus_one = num_bigint::BigInt::from(-1);
    let mut summands: Vec<String> = Vec::new();
    for (index, coefficient) in linear.coefficients().iter().enumerate() {
        if *coefficient == zero {
            continue;
        }
        let parameter = quote_symbol(&format!("x!{index}"));
        summands.push(if *coefficient == one {
            parameter
        } else if *coefficient == minus_one {
            format!("(- {parameter})")
        } else {
            format!("(* {} {})", format_bigint(coefficient), parameter)
        });
    }
    if *linear.constant() != zero || summands.is_empty() {
        summands.push(format_bigint(linear.constant()));
    }
    Some(match summands.len() {
        1 => summands.remove(0),
        _ => format!("(+ {})", summands.join(" ")),
    })
}

/// The PRINTED body is the only form of a symbolic interpretation a consumer
/// ever sees, and for a head the certificate owns nothing reconciles it
/// against a second source: `printed_uf_rows` opts such a head out entirely,
/// so the independent gate re-evaluates the same in-memory [`LinearIntBody`]
/// rather than re-reading this text. Rendering and
/// [`LinearIntBody::evaluate`] are therefore two implementations of one
/// function with no cross-check between them — these tests are that
/// cross-check.
#[cfg(test)]
mod linear_int_body_printing_tests {
    use super::{format_linear_int_body, Executor, LinearIntBody};
    use ay_frontend::parse;
    use num_bigint::BigInt;

    fn body(coefficients: &[i64], constant: i64) -> LinearIntBody {
        LinearIntBody::new(
            coefficients.iter().copied().map(BigInt::from).collect(),
            BigInt::from(constant),
        )
        .expect("a non-nullary linear body")
    }

    /// Every coefficient branch, by exact spelling.
    ///
    /// The minter currently emits only `λ x̄. x_j + k` — one coefficient equal
    /// to `1` and the rest `0` — so the `-1` and `|c| > 1` arms are reachable
    /// only by widening the family. Pinning them NOW is the point: a widening
    /// that renders them wrong publishes a model that disagrees with the
    /// interpretation the certificate proved, and nothing downstream would
    /// notice (see the module note above).
    #[test]
    fn rendering_covers_every_coefficient_branch() {
        for (coefficients, constant, expected) in [
            (&[1i64][..], 3i64, "(+ x!0 3)"),
            // A negative constant must take SMT-LIB's unary-minus form; a bare
            // `-1` is not a numeral and would not re-parse.
            (&[1][..], -1, "(+ x!0 (- 1))"),
            (&[1][..], 0, "x!0"),
            (&[-1][..], 0, "(- x!0)"),
            (&[-1][..], 2, "(+ (- x!0) 2)"),
            // A zero coefficient is ELIDED, and a body that elides everything
            // must still print its constant rather than an empty `(+ )`.
            (&[0][..], 5, "5"),
            (&[0][..], 0, "0"),
            (&[0, 1][..], 2, "(+ x!1 2)"),
            (&[1, 1][..], 0, "(+ x!0 x!1)"),
            (&[3, -2][..], -7, "(+ (* 3 x!0) (* (- 2) x!1) (- 7))"),
        ] {
            assert_eq!(
                format_linear_int_body(&body(coefficients, constant)).as_deref(),
                Some(expected),
                "rendering of {coefficients:?} + {constant}"
            );
        }
        // A nullary head is published as a constant and must never reach this
        // path; `LinearIntBody::new` refuses to build one at all.
        assert!(LinearIntBody::new(Vec::new(), BigInt::from(1)).is_none());
    }

    /// AY re-reads its OWN printed body and must agree with the evaluator at
    /// the argument point.
    ///
    /// The script asserts the DISEQUALITY, so `unsat` is agreement: the
    /// printed `(define-fun ...)` body, parsed and evaluated by the ordinary
    /// front end, equals what [`LinearIntBody::evaluate`] computed. Any
    /// rendering defect — a dropped constant, a sign, a parameter index, a
    /// bare negative numeral that fails to parse — makes this `sat` or an
    /// execution error.
    #[test]
    fn printed_body_agrees_with_the_evaluator_at_every_probed_point() {
        for (coefficients, constant) in [
            (&[1i64][..], 3i64),
            (&[1][..], -1),
            (&[1][..], 0),
            (&[-1][..], 4),
            (&[0][..], 9),
            (&[5][..], -1_000_000_007),
            (&[0, 1][..], 2),
            (&[3, -2][..], -7),
        ] {
            let linear = body(coefficients, constant);
            let rendered = format_linear_int_body(&linear).expect("a renderable body");
            let signature = (0..linear.arity())
                .map(|index| format!("(x!{index} Int)"))
                .collect::<Vec<_>>()
                .join(" ");
            for point in [&[0i64, 0][..], &[7, -3][..], &[-11, 13][..]] {
                let arguments = &point[..linear.arity()];
                let expected = linear
                    .evaluate(
                        &arguments
                            .iter()
                            .copied()
                            .map(BigInt::from)
                            .collect::<Vec<_>>(),
                    )
                    .expect("the arity matches");
                let outputs = disagreement_verdict(&signature, &rendered, arguments, &expected);
                assert!(
                    outputs.iter().any(|line| line == "unsat"),
                    "printed body `{rendered}` disagrees with `evaluate` at \
                     {arguments:?}: expected {expected}, script said {outputs:?}"
                );
            }
        }
    }

    /// NEGATIVE CONTROL for the harness above, so it can never report
    /// agreement vacuously.
    ///
    /// The same script shape with a body that is ONE OFF from the certified
    /// one must come back `sat`. Without this, a harness whose script failed
    /// to parse, or that read the wrong output line, or that compared against
    /// a value it had itself derived from the rendering, would "pass" for
    /// every body including a wrong one.
    #[test]
    fn the_agreement_harness_detects_a_wrong_body() {
        let linear = body(&[1], 3);
        let expected = linear
            .evaluate(&[BigInt::from(7)])
            .expect("the arity matches");
        let outputs = disagreement_verdict("(x!0 Int)", "(+ x!0 4)", &[7], &expected);
        assert!(
            outputs.iter().any(|line| line == "sat"),
            "the harness must REFUTE `x!0 + 4` against `evaluate`'s {expected}, \
             but the script said {outputs:?}"
        );
    }

    /// Run `(assert (not (= (f args) expected)))` against the PRINTED body and
    /// return AY's own output lines. `unsat` is agreement; `sat` is a
    /// rendering that denotes a different function.
    fn disagreement_verdict(
        signature: &str,
        rendered: &str,
        arguments: &[i64],
        expected: &BigInt,
    ) -> Vec<String> {
        let call = arguments
            .iter()
            .map(|argument| numeral(&BigInt::from(*argument)))
            .collect::<Vec<_>>()
            .join(" ");
        let script = format!(
            "(set-logic ALL)\n\
             (define-fun f ({signature}) Int {rendered})\n\
             (assert (not (= (f {call}) {})))\n\
             (check-sat)\n",
            numeral(expected)
        );
        let commands = parse(&script).expect("the printed body re-parses");
        let mut exec = Executor::new();
        exec.execute_all(&commands).expect("the script executes")
    }

    /// SMT-LIB has no negative numeral literal.
    fn numeral(value: &BigInt) -> String {
        if value.sign() == num_bigint::Sign::Minus {
            format!("(- {})", value.magnitude())
        } else {
            value.to_string()
        }
    }
}

impl Executor {
    /// Whether the `Var` `var` occurs FREE in a current assertion or an
    /// assumption of the last check: an occurrence under a quantifier or
    /// `let` that binds its name is not free.
    fn var_occurs_free_in_current_query(&self, var: TermId) -> bool {
        let TermData::Var(name, _) = self.ctx.terms.get(var) else {
            return true;
        };
        // (term, binders in scope); a binder of `name` hides it below.
        let mut stack: Vec<(TermId, bool)> = self
            .ctx
            .assertions
            .iter()
            .chain(self.last_assumptions.iter().flatten())
            .map(|&root| (root, false))
            .collect();
        let mut seen: DetHashSet<(TermId, bool)> = DetHashSet::default();
        while let Some((t, shadowed)) = stack.pop() {
            if shadowed || !seen.insert((t, shadowed)) {
                continue;
            }
            if t == var {
                return true;
            }
            match self.ctx.terms.get(t) {
                TermData::App(_, args) => stack.extend(args.iter().map(|&a| (a, false))),
                TermData::Not(inner) => stack.push((*inner, false)),
                TermData::Ite(c, a, b) => stack.extend([(*c, false), (*a, false), (*b, false)]),
                TermData::Let(bindings, body) => {
                    stack.extend(bindings.iter().map(|(_, value)| (*value, false)));
                    let binds = bindings.iter().any(|(bound, _)| bound == name);
                    stack.push((*body, binds));
                }
                TermData::Forall(vars, body, triggers) | TermData::Exists(vars, body, triggers) => {
                    let binds = vars.iter().any(|(bound, _)| bound == name);
                    stack.push((*body, binds));
                    stack.extend(triggers.iter().flatten().map(|&t| (t, binds)));
                }
                _ => {}
            }
        }
        false
    }
}
