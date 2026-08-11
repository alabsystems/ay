// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

impl Model {
    /// An empty model: no SAT assignment and no theory sub-models.
    ///
    /// Used as the base for the trivially-SAT completion model (every declared
    /// constant is unconstrained after preprocessing reduced the formula to
    /// `true`) and by internal callers that synthesize partial models.
    pub(in crate::executor) fn empty() -> Self {
        Model {
            quantified_confirmation_seal: QuantifiedConfirmationModelSeal::default(),
            quantified_grant_model_seal: QuantifiedGrantModelSeal::default(),
            sat_model: Vec::new(),
            term_to_var: HashMap::default(),
            bool_overrides: HashMap::default(),
            euf_model: None,
            array_model: None,
            lra_model: None,
            lia_model: None,
            bv_model: None,
            fp_model: None,
            string_model: None,
            seq_model: None,
            projection_ufs: ProjectionUfModel::default(),
            certified_total_ufs: CertifiedTotalUfModel::default(),
            certified_const_interps: CertifiedConstInterpModel::default(),
            formula_neutral_function_defaults: FormulaNeutralFunctionDefaults::default(),
            completed_values: HashMap::default(),
            dt_ground: HashMap::default(),
            dt_pins: HashMap::default(),
        }
    }

    /// Atomically install the exact constant-function interpretation proved by
    /// a quantified certificate.
    ///
    /// Every entry must carry a live, positively checked ordinary-UF binding
    /// and a live closed value of exactly the declared result sort. Values are
    /// scalar literals or recursively nested `const-array` values, with every
    /// reachable term slot birth-stamped. The package replaces the previous
    /// package only after all entries have been checked, so rejection leaves
    /// the model unchanged. Installing it is a semantic mutation and therefore
    /// revokes every model-relative theorem.
    pub(in crate::executor) fn install_certified_const_interps(
        &mut self,
        ctx: &ay_frontend::Context,
        entries: Vec<(ay_frontend::CheckedProjectionBinding, TermId)>,
    ) -> Option<()> {
        if entries.is_empty() {
            return None;
        }

        let mut seen = HashSet::default();
        let mut checked = Vec::with_capacity(entries.len());
        for (binding, value) in entries {
            let Symbol::Named(name) = binding.symbol() else {
                return None;
            };
            let value_graph =
                StampedClosedValueGraph::capture(&ctx.terms, value, binding.result_sort())?;
            let declaration_term = if binding.parameter_sorts().is_empty() {
                let mut matching = ctx.symbol_iter().filter_map(|(surface_name, info)| {
                    (ctx.symbol_identity_name(surface_name, info) == name.as_str()
                        && info.arg_sorts.as_slice() == binding.parameter_sorts()
                        && &info.sort == binding.result_sort())
                    .then_some(info.term)
                    .flatten()
                });
                let term = matching.next()?;
                if matching.next().is_some() || !matches!(ctx.terms.get(term), TermData::Var(_, _))
                {
                    return None;
                }
                Some((term, ctx.terms.entry_stamp(term)?))
            } else {
                None
            };
            let raw_conflict = self.euf_model.as_ref().is_some_and(|euf| {
                euf.function_tables
                    .get(name)
                    .is_some_and(|table| !table.is_empty())
                    || euf.function_table_terms.contains_key(name)
                    || euf.function_table_conflicts.contains(name)
            });
            if !seen.insert(binding.symbol().clone())
                || !ctx.projection_binding_still_current(&binding)
                || self.certified_total_ufs.by_symbol.contains_key(name)
                || self.has_formula_neutral_function_default_symbol(binding.symbol())
                || raw_conflict
                || !matches!(
                    self.projection_ufs.projected_argument_for_signature(
                        binding.symbol(),
                        binding.parameter_sorts(),
                        binding.result_sort(),
                    ),
                    Ok(None)
                )
            {
                return None;
            }
            checked.push(CertifiedConstInterpEntry {
                binding,
                value,
                value_graph,
                declaration_term,
            });
        }

        self.revoke_all_quantified_model_seals();
        // Remove only lower-priority default-completion artifacts for heads now
        // owned by the certified interpretation. Non-empty/raw semantic tables
        // were rejected above, making this cleanup single-source rather than a
        // hidden priority contest between two model representations.
        for entry in &checked {
            if let Some(term) = entry.declaration_term() {
                self.completed_values.remove(&term);
            }
            if let Symbol::Named(name) = entry.symbol() {
                if let Some(euf) = self.euf_model.as_mut() {
                    euf.function_tables.remove(name);
                }
            }
        }
        self.certified_const_interps.entries = Arc::from(checked.into_boxed_slice());
        eval_memo_clear();
        Some(())
    }

    /// Return the exact constant value for a certified application.
    ///
    /// `Ok(None)` means this package does not own `symbol`. Once it does own
    /// the symbol, stale declaration/value identity or a signature mismatch is
    /// an error rather than permission to fall through to an unrelated raw EUF
    /// table.
    pub(in crate::executor) fn certified_const_interp_for_application(
        &self,
        ctx: &ay_frontend::Context,
        symbol: &Symbol,
        arguments: &[TermId],
        result_sort: &Sort,
    ) -> std::result::Result<Option<TermId>, CertifiedConstInterpReadError> {
        // Currentness belongs to the package, not only to an exact-symbol
        // hit. A declaration popped from scope can later be redeclared with
        // the same surface spelling and signature but a fresh private core
        // identity. Looking up that new identity first would miss the stale
        // entry and incorrectly fall through to ordinary model completion.
        // Once any entry is stale, this model no longer describes the current
        // declaration environment, so every application read must fail closed.
        if self
            .certified_const_interps
            .entries
            .iter()
            .any(|entry| !entry.is_current(ctx))
        {
            return Err(CertifiedConstInterpReadError::StaleIdentity);
        }
        let Some(entry) = self
            .certified_const_interps
            .entries
            .iter()
            .find(|entry| entry.symbol() == symbol)
        else {
            return Ok(None);
        };
        if entry.parameter_sorts().len() != arguments.len()
            || entry.result_sort() != result_sort
            || arguments
                .iter()
                .zip(entry.parameter_sorts())
                .any(|(&argument, expected_sort)| {
                    ctx.terms.entry_stamp(argument).is_none()
                        || ctx.terms.sort(argument) != expected_sort
                })
        {
            return Err(CertifiedConstInterpReadError::SignatureConflict);
        }
        Ok(Some(entry.value()))
    }

    /// Whether every model-owned constant interpretation still names the exact
    /// live declaration and value slot for which it was installed.
    pub(in crate::executor) fn certified_const_interps_are_current(
        &self,
        ctx: &ay_frontend::Context,
    ) -> bool {
        !self.certified_const_interps.entries.is_empty()
            && self
                .certified_const_interps
                .entries
                .iter()
                .all(|entry| entry.is_current(ctx))
    }

    pub(in crate::executor) fn certified_const_interp_entries(
        &self,
    ) -> &[CertifiedConstInterpEntry] {
        &self.certified_const_interps.entries
    }

    pub(in crate::executor) fn has_certified_const_interp_symbol(&self, symbol: &Symbol) -> bool {
        self.certified_const_interps
            .entries
            .iter()
            .any(|entry| entry.symbol() == symbol)
    }

    /// Atomically install canonical defaults for ordinary functions proved
    /// absent from an exact theorem root window.
    pub(in crate::executor) fn install_formula_neutral_function_defaults(
        &mut self,
        ctx: &ay_frontend::Context,
        entries: Vec<(ay_frontend::CheckedProjectionBinding, EvalValue)>,
    ) -> Option<()> {
        let mut seen = HashSet::default();
        let mut checked = Vec::with_capacity(entries.len());
        for (binding, value) in entries {
            let Symbol::Named(name) = binding.symbol() else {
                return None;
            };
            if binding.parameter_sorts().is_empty()
                || !seen.insert(binding.symbol().clone())
                || !ctx.projection_binding_still_current(&binding)
                || !eval_value_has_exact_sort(&value, binding.result_sort())
                || self.has_certified_const_interp_symbol(binding.symbol())
                || self.certified_total_ufs.by_symbol.contains_key(name)
                || !matches!(
                    self.projection_ufs.projected_argument_for_signature(
                        binding.symbol(),
                        binding.parameter_sorts(),
                        binding.result_sort(),
                    ),
                    Ok(None)
                )
                || self.euf_model.as_ref().is_some_and(|euf| {
                    euf.function_tables.contains_key(name)
                        || euf.function_table_terms.contains_key(name)
                        || euf.function_table_conflicts.contains(name)
                })
            {
                return None;
            }
            checked.push(FormulaNeutralFunctionDefaultEntry { binding, value });
        }

        if !checked.is_empty() || !self.formula_neutral_function_defaults.entries.is_empty() {
            self.revoke_all_quantified_model_seals();
            self.formula_neutral_function_defaults.entries = Arc::from(checked.into_boxed_slice());
            eval_memo_clear();
        }
        Some(())
    }

    pub(super) fn formula_neutral_function_default_for_application(
        &self,
        ctx: &ay_frontend::Context,
        symbol: &Symbol,
        arguments: &[TermId],
        result_sort: &Sort,
    ) -> std::result::Result<Option<EvalValue>, FormulaNeutralFunctionDefaultReadError> {
        let Some(entry) = self
            .formula_neutral_function_defaults
            .entries
            .iter()
            .find(|entry| entry.symbol() == symbol)
        else {
            return Ok(None);
        };
        if !entry.is_current(ctx) {
            return Err(FormulaNeutralFunctionDefaultReadError::StaleIdentity);
        }
        if entry.parameter_sorts().len() != arguments.len()
            || entry.result_sort() != result_sort
            || arguments
                .iter()
                .zip(entry.parameter_sorts())
                .any(|(&argument, expected_sort)| {
                    ctx.terms.entry_stamp(argument).is_none()
                        || ctx.terms.sort(argument) != expected_sort
                })
        {
            return Err(FormulaNeutralFunctionDefaultReadError::SignatureConflict);
        }
        Ok(Some(entry.value().clone()))
    }

    pub(in crate::executor) fn formula_neutral_function_defaults_are_current(
        &self,
        ctx: &ay_frontend::Context,
    ) -> bool {
        self.formula_neutral_function_defaults
            .entries
            .iter()
            .all(|entry| entry.is_current(ctx))
    }

    pub(in crate::executor) fn formula_neutral_function_default_entries(
        &self,
    ) -> &[FormulaNeutralFunctionDefaultEntry] {
        &self.formula_neutral_function_defaults.entries
    }

    pub(super) fn has_formula_neutral_function_default_symbol(&self, symbol: &Symbol) -> bool {
        self.formula_neutral_function_defaults
            .entries
            .iter()
            .any(|entry| entry.symbol() == symbol)
    }
}
