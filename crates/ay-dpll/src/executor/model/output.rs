// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Model output entry points: `get-model`, `get-value`, `get-objectives`.
//!
//! Formatting helpers (function tables, array values, eval-value rendering)
//! live in sibling `output_format.rs`.

use ay_core::kani_compat::{DetHashMap, DetHashSet};
use ay_core::term::TermData;
use ay_core::{quote_symbol, string_literal, Sort, Symbol, TermId};

use crate::executor_format::{
    format_bigint, format_bitvec, format_default_value_surface, format_model_atom_surface,
    format_real, format_sort_surface,
};
use crate::executor_types::SolveResult;

use super::Executor;
use super::{debug_model, EvalValue, Model};

impl Executor {
    /// Generate model output for get-model command.
    pub(crate) fn model(&self) -> String {
        if !self.produce_models_enabled() {
            return "(error \"model generation is not enabled\")".to_string();
        }

        // Check if we have a model.  Some SAT paths have no concrete theory
        // model because assertions were simplified away; every declared
        // constant is then unconstrained, so print the completed default
        // model (the values exist in a model, nothing is fabricated at print
        // time — #no-fabricated-model-values).
        let dummy_model;
        let model = match (&self.last_result, &self.last_model) {
            (Some(SolveResult::Sat), Some(m)) => m,
            (Some(SolveResult::Sat), None) => {
                dummy_model = self.completed_default_model();
                &dummy_model
            }
            _ => {
                return "(error \"model is not available\")".to_string();
            }
        };

        // Collect model values for user-declared symbols.
        //
        // Datatype SELECTOR totalizations come first (#mv-total-selectors):
        // without them a model validator evaluating a selector applied to a
        // wrong-constructor value rejects the whole model as partial. Each
        // definition defers to the builtin selector on the owning constructor
        // and reproduces the internal model's committed value on every
        // constrained wrong-constructor case.
        let mut definitions = self.total_selector_definitions(model);
        // Every fail-closed omission below drops a symbol from an otherwise
        // well-formed model. The result still prints `sat`, so the run scores
        // ZERO in Model-Validation while the scoreboard reads `errors: 0` — the
        // omission is invisible to every downstream consumer. Record what was
        // dropped so it can be surfaced on stderr; stdout is piped verbatim
        // into Dolmen and must stay a pure get-model response.
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
        let gate_emit = self.gate_emit_reconstructions(model);

        // Ground UF applications, collected once on first need and shared by
        // every symbol that reaches the fallback below. Lazy because the sweep
        // walks every assertion and the EUF lanes never need it.
        let mut ground_uf_apps: Option<DetHashMap<(String, usize), Vec<(TermId, Vec<TermId>)>>> =
            None;

        for (name, info) in self.ctx.symbol_iter() {
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
                definitions.push(format!(
                    "  (define-fun {} ({}) {}\n    {})",
                    quote_symbol(name),
                    params_str,
                    format_sort_surface(&self.ctx, &info.sort),
                    self.format_term(entry.value())
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
                    format_default_value_surface(&self.ctx, &info.sort)
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
                                return format!(
                                    "(error \"model value for function {} is not available: {e}\")",
                                    quote_symbol(name)
                                );
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
                                return format!(
                                    "(error \"model value for function {} is not available: {e}\")",
                                    quote_symbol(name)
                                );
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
                // Note what this is NOT: the independent gate reads the internal
                // `Model`, not this printout, and it already returned
                // `confirmed-sat` on these queries. So the gap was never a gate
                // refusal — it was the narrower and quieter failure of a
                // CONFIRMED model being published incomplete, leaving the user
                // (and any external validator) unable to check the `sat` that
                // AY had in fact justified internally.
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
                        collected
                    });
                    if let Some(applications) = apps.get(&(name.to_string(), arity)) {
                        match self.uf_table_from_ground_applications(model, applications) {
                            Some(table) => {
                                match self.format_function_table(
                                    name,
                                    &info.arg_sorts,
                                    &info.sort,
                                    &table,
                                    model,
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

                // Handle array-sorted symbols specially. Render a `store`-chain
                // that satisfies the asserted `(select a i) = v` constraints
                // (folding in reconstructed interpretation stores and the
                // definitional `(= a <array-expr>)` value, #5450) rather than the
                // bare const-array default, which would VIOLATE the assertions —
                // an invalid witness (#model-array-witness).
                if let Sort::Array(_) = &info.sort {
                    let array_value = if let Some(value) = gate_emit.get(&term_id) {
                        value.clone()
                    } else if let Some(value) =
                        self.format_array_witness_value(model, term_id, &info.sort)
                    {
                        value
                    } else {
                        return format!(
                            "(error \"model value for array {} is not available\")",
                            quote_symbol(name)
                        );
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

                // Single-source DT value (#mv-dt-single-source): when the DT
                // lane exported its e-graph model, a datatype-sorted constant
                // reads the ONE per-class assignment shared with the total
                // selector definitions and `(get-value)` — printing any other
                // engine's value here (gate reconstruction included) could
                // disagree with a totalization branch key derived from the
                // assignment and un-fire it under Dolmen. Falls through when
                // absent (combined lanes) or the class fails closed.
                if self.datatype_sort_name(&info.sort).is_some() {
                    if let Some(v) = self.dt_egraph_value(model, term_id) {
                        definitions.push(format!("  (define-fun {quoted_name} () {sort_str} {v})"));
                        continue;
                    }
                    // Fail-closed omission (stage-4 review F2): a class the
                    // assignment POISONED (self-check failure / unrepairable
                    // collision) must NOT fall back to any legacy emitter —
                    // the legacy strategies re-derive the same incoherent
                    // value the check already proved wrong
                    // (`c8-tester-distinct`: byte-identical `distinct`-violating
                    // collision → E:bad-model, division-voiding). Omitting the
                    // definition is at worst a partial model (0 points to a
                    // validator), never a wrong one.
                    if self.dt_egraph_class_poisoned(model, term_id) {
                        continue;
                    }
                }

                // Entailed gate reconstruction wins for a datatype-sorted const
                // (coherent with the confirmed model, marker-free); otherwise fall
                // through to the per-leaf DT materializer below.
                if let Some(ctor_expr) = gate_emit.get(&term_id) {
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
                if !matches!(
                    info.sort,
                    Sort::Int | Sort::Real | Sort::Seq(_) | Sort::BitVec(_)
                ) {
                    if let Some(ref euf_model) = model.euf_model {
                        if let Some(elem) = euf_model.term_values.get(&term_id) {
                            let elem = format_model_atom_surface(&self.ctx, &info.sort, elem);
                            definitions
                                .push(format!("  (define-fun {quoted_name} () {sort_str} {elem})"));
                            continue;
                        }
                    }
                }

                // Try LRA model for Real sort — but an exact NRA algebraic
                // witness (e.g. x = √2 for `x*x = 2`) is authoritative and
                // prints in z3 `root-obj` syntax.
                if matches!(info.sort, Sort::Real) {
                    if let Some(alg) = self.nra_algebraic_model.get(&term_id) {
                        // A residue value can reduce to an exact rational (a
                        // triangular-assignment variable): print it as such.
                        let value_str = match alg.to_number() {
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
                    match self.term_value_string(model, term_id) {
                        Ok(value_str) => {
                            definitions.push(format!(
                                "  (define-fun {quoted_name} () {sort_str} {value_str})"
                            ));
                        }
                        Err(e) => {
                            return format!(
                                "(error \"model value for {quoted_name} is not available: {e}\")"
                            );
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
                    && matches!(self.evaluate_term(model, term_id), EvalValue::Unknown)
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
                                    return format!(
                                        "(error \"model value for {quoted_name} is not available: {e}\")"
                                    );
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
                let eval_value = self.evaluate_term(model, term_id);
                let value_str = match &eval_value {
                    // Unknown keeps its specific invariant-violation message
                    // (ordered BEFORE the user-facing delegation so the
                    // "sat accepted without a total model" diagnostic text is
                    // preserved).
                    EvalValue::Unknown => {
                        return format!(
                            "(error \"model value for {quoted_name} is not available \
                             (internal error: sat accepted without a total model)\")"
                        );
                    }
                    // Sort-aware user-facing formatting (#real-fmt): Real
                    // constants print as z3-exact Real literals (`0.0`,
                    // `(- 5.0)`, `(/ 7.0 2.0)`), everything else exactly as
                    // before.
                    _ => match self.try_format_eval_value_user(&eval_value, term_id) {
                        Ok(s) => s,
                        Err(e) => {
                            return format!(
                                "(error \"model value for {quoted_name} is not available: {e}\")"
                            );
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
        if !omitted.is_empty() {
            // stderr ONLY — stdout is the get-model response. The harness
            // already captures `stderr_tail`, so this makes a partial model
            // greppable in the run record instead of silently scoring zero.
            omitted.sort();
            omitted.dedup();
            eprintln!(
                "c ay.model.partial omitted={} symbols=[{}]",
                omitted.len(),
                omitted.join(" ")
            );
        }
        if definitions.is_empty() {
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
    /// This is the per-term core shared by `(get-value ...)` and `(eval ...)`.
    /// It performs array/datatype/uninterpreted resolution and the Unknown
    /// fallbacks (asserted-equality and inequality-bound extraction) exactly as
    /// `get-value` does, returning just the value text (no `(term value)`
    /// wrapper).
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
        // Route projection applications to the selected argument through this
        // same per-term formatting core. This keeps `(get-value)` identical to
        // the evaluator and also handles non-scalar sorts (arrays, datatypes,
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
        if matches!(sort, Sort::Array(_)) {
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
                    let eval_value = self.evaluate_term(model, term_id);
                    self.try_format_eval_value_user(&eval_value, term_id)
                }
            }
        } else {
            let eval_value = self.evaluate_term(model, term_id);
            // For selector apps returning Unknown, scan assertions (#5432).
            let eval_value = if matches!(eval_value, EvalValue::Unknown) {
                self.extract_value_from_asserted_equalities(model, term_id)
                    .unwrap_or(eval_value)
            } else {
                eval_value
            };
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
            None => Ok(format_default_value_surface(&self.ctx, result_sort)),
        })
    }

    /// Generate output for get-value command.
    pub(crate) fn values(&self, requested: &[(String, TermId)]) -> String {
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

        // Memoize evaluation across ALL requested terms (#eval-memo). `get-value`
        // over N terms that share large subterms — e.g. a Kani query's ~190
        // violation flags, each a boolean expression reading the same 20M-node
        // model — otherwise re-evaluates every shared subterm once PER term (the
        // result memo is inert outside a session). One session computes each
        // unique subterm exactly once. Verdict-preserving (the model is immutable
        // for the query); dropped at function exit.
        let _eval_memo = super::EvalMemoSession::new();
        let _t_gv = std::time::Instant::now();

        // Echo the term's ORIGINAL SMT-LIB text as the key (per the SMT-LIB
        // spec), not a reconstruction of the elaborated term — a
        // single-constructor datatype constant `w` is eagerly eliminated to
        // `(wrap <field>)`, whose fresh field var must not leak into the key.
        let mut pairs: Vec<String> = Vec::with_capacity(requested.len());
        for (term_str, term_id) in requested {
            match self.term_value_string(model, *term_id) {
                Ok(value_str) => pairs.push(format!("({term_str} {value_str})")),
                // A term with no value under the model errors honestly —
                // never a fabricated default (#no-fabricated-model-values).
                Err(e) => return format!("(error \"value of {term_str} is not available: {e}\")"),
            }
        }

        if std::env::var_os("AY_PHASE_TRACE").is_some() {
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
    /// True when `name` occurs anywhere beneath a quantifier in the assertions.
    ///
    /// Such a symbol is NOT determined by its ground applications: a
    /// `(forall ((y S)) ... (f y) ...)` constrains `f` at points no ground
    /// application mentions. See
    /// [`Self::uf_table_from_ground_applications`] for why that makes the
    /// ground-application table unpublishable.
    fn symbol_occurs_under_quantifier(&self, name: &str) -> bool {
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

    fn uf_table_from_ground_applications(
        &self,
        model: &Model,
        applications: &[(TermId, Vec<TermId>)],
    ) -> Option<Vec<(Vec<String>, String)>> {
        let mut table = Vec::with_capacity(applications.len());
        for (app, args) in applications {
            let value = self.term_value_string(model, *app).ok()?;
            let mut key = Vec::with_capacity(args.len());
            for &arg in args {
                key.push(self.term_value_string(model, arg).ok()?);
            }
            table.push((key, value));
        }
        Some(table)
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
        match self.term_value_string(model, term_id) {
            Ok(value_str) => value_str,
            Err(e) => format!("(error \"value is not available: {e}\")"),
        }
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
