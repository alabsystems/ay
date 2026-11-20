// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

/// One package authentication retained only while its model and context are
/// immutably borrowed. This is read DATA, never SAT or theorem authority.
pub(super) struct AuthenticatedConstInterpRead<'a> {
    model: &'a Model,
    context: &'a ay_frontend::Context,
}

impl AuthenticatedConstInterpRead<'_> {
    pub(super) fn is_for(&self, context: &ay_frontend::Context, model: &Model) -> bool {
        std::ptr::eq(self.context, context) && std::ptr::eq(self.model, model)
    }

    pub(super) fn context_is(&self, context: &ay_frontend::Context) -> bool {
        std::ptr::eq(self.context, context)
    }

    pub(super) fn owns_symbol(&self, symbol: &Symbol) -> bool {
        self.model.has_certified_const_interp_symbol(symbol)
    }

    pub(super) fn entry(
        &self,
        symbol: &Symbol,
        arguments: &[TermId],
        result_sort: &Sort,
    ) -> std::result::Result<Option<&CertifiedConstInterpEntry>, CertifiedConstInterpReadError>
    {
        self.model.certified_const_interp_entry_for_signature(
            self.context,
            symbol,
            arguments,
            result_sort,
        )
    }
}

impl Model {
    /// Authenticate every entry, including entries unrelated to the requested
    /// read. The callback prepays each bounded currentness check. The returned
    /// view cannot outlive either immutable borrow, so a scope pop, declaration
    /// replacement, model mutation or term rollback requires a new check.
    pub(super) fn authenticate_const_interp_read<'a>(
        &'a self,
        context: &'a ay_frontend::Context,
        mut admit: impl FnMut(&CertifiedConstInterpEntry) -> bool,
    ) -> std::result::Result<AuthenticatedConstInterpRead<'a>, CertifiedConstInterpReadError> {
        for entry in self.certified_const_interp_entries() {
            if !admit(entry) {
                return Err(CertifiedConstInterpReadError::ResourceRefused);
            }
            if !entry.is_current(context) {
                return Err(CertifiedConstInterpReadError::StaleIdentity);
            }
        }
        Ok(AuthenticatedConstInterpRead {
            model: self,
            context,
        })
    }

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
            materialized_scalar_functions: HashMap::default(),
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
            field_assignments: Default::default(),
            dt_ground: HashMap::default(),
            dt_pins: HashMap::default(),
            dt_array_field_classes: Vec::new(),
            residual_arrays: None,
            functional_arrays: None,
            _scalar_candidate_memory: None,
            construction_owner: None,
        }
    }

    /// This model cut down to the terms of a store it shares a prefix with.
    ///
    /// A disposable probe solves in a CLONE of the caller's term store: ids
    /// below `shared_len` name the same terms in both stores, while an id at
    /// or beyond it is one of the probe's own terms and would name an
    /// unrelated term once the caller's store grows. The result keeps the SAT
    /// assignment and the entries of shared terms only, and no certified or
    /// seal state. `None` when the model holds a theory sub-model this cannot
    /// cut entry by entry; the caller then declines rather than publish a
    /// probe-local id.
    pub(in crate::executor) fn restricted_to_shared_terms(
        mut self,
        shared_len: usize,
    ) -> Option<Self> {
        if self.euf_model.is_some()
            || self.has_field_assignments()
            || !self.materialized_scalar_functions.is_empty()
            || self.array_model.is_some()
            || self.lra_model.is_some()
            || self.lia_model.is_some()
            || self.fp_model.is_some()
            || self.string_model.is_some()
            || self.seq_model.is_some()
            || self.residual_arrays.is_some()
            || self.functional_arrays.is_some()
            || !self.dt_ground.is_empty()
            || !self.dt_pins.is_empty()
            || !self.dt_array_field_classes.is_empty()
        {
            return None;
        }
        let shared = |term: &TermId| (term.0 as usize) < shared_len;
        let mut restricted = Model::empty();
        restricted.sat_model = std::mem::take(&mut self.sat_model);
        restricted.term_to_var = std::mem::take(&mut self.term_to_var);
        restricted.term_to_var.retain(|term, _| shared(term));
        restricted.bool_overrides = std::mem::take(&mut self.bool_overrides);
        restricted.bool_overrides.retain(|term, _| shared(term));
        restricted.completed_values = std::mem::take(&mut self.completed_values);
        restricted.completed_values.retain(|term, _| shared(term));
        restricted._scalar_candidate_memory = self._scalar_candidate_memory.take();
        restricted.bv_model = self.bv_model.take().map(|mut bv| {
            bv.values.retain(|term, _| shared(term));
            bv.term_to_bits.retain(|term, _| shared(term));
            bv.bool_overrides.retain(|term, _| shared(term));
            bv
        });
        Some(restricted)
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
        entries: Vec<(
            ay_frontend::CheckedProjectionBinding,
            CertifiedConstInterpWitness,
        )>,
    ) -> Option<()> {
        if entries.is_empty() {
            return None;
        }

        let mut seen = HashSet::default();
        let mut checked = Vec::with_capacity(entries.len());
        for (binding, witness) in entries {
            let Symbol::Named(name) = binding.symbol() else {
                return None;
            };
            let body = match witness {
                CertifiedConstInterpWitness::Constant(value) => {
                    let value_graph =
                        StampedClosedValueGraph::capture(&ctx.terms, value, binding.result_sort())?;
                    CertifiedConstInterpBody::Constant { value, value_graph }
                }
                // SYMBOLIC DEFAULT. Admitted only at the exact shape the
                // certificate can publish AND both readers can evaluate: an
                // `Int` result over `Int` parameters, with one coefficient per
                // declared parameter and at least one parameter. Everything
                // else fails closed here rather than at a reader.
                CertifiedConstInterpWitness::LinearInt(linear) => {
                    if linear.arity() != binding.parameter_sorts().len()
                        || binding.result_sort() != &Sort::Int
                        || !binding
                            .parameter_sorts()
                            .iter()
                            .all(|sort| sort == &Sort::Int)
                    {
                        return None;
                    }
                    CertifiedConstInterpBody::LinearInt(linear)
                }
                CertifiedConstInterpWitness::Expression(body) => {
                    if !body.is_current(ctx, binding.parameter_sorts(), binding.result_sort()) {
                        return None;
                    }
                    CertifiedConstInterpBody::Expression(body)
                }
            };
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
                    .get(name.as_str())
                    .is_some_and(|table| !table.is_empty())
                    || euf.function_table_terms.contains_key(name.as_str())
                    || euf.function_table_conflicts.contains(name.as_str())
            });
            if !seen.insert(binding.symbol().clone())
                || !ctx.projection_binding_still_current(&binding)
                || self
                    .certified_total_ufs
                    .by_symbol
                    .contains_key(name.as_str())
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
                body,
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
                self.materialized_scalar_functions.remove(name.as_str());
                if let Some(euf) = self.euf_model.as_mut() {
                    euf.function_tables.remove(name.as_str());
                }
            }
        }
        self.certified_const_interps.entries = Arc::from(checked.into_boxed_slice());
        eval_memo_clear();
        Some(())
    }

    /// Read the certified interpretation AT a specific application.
    ///
    /// `Ok(None)` means this package does not own `symbol`. Once it does own
    /// the symbol, stale declaration/value identity or a signature mismatch is
    /// an error rather than permission to fall through to an unrelated raw EUF
    /// table.
    ///
    /// A CONSTANT body answers with its published term, exactly as before. A
    /// SYMBOLIC body answers with the body and this application's argument
    /// TERMS: the value exists only once those arguments are evaluated, and
    /// which evaluator does that is the caller's business (the ordinary
    /// evaluator uses its own; the independent gate uses ITS own, which is
    /// what keeps the gate independent).
    pub(in crate::executor) fn certified_const_interp_for_application(
        &self,
        ctx: &ay_frontend::Context,
        symbol: &Symbol,
        arguments: &[TermId],
        result_sort: &Sort,
    ) -> std::result::Result<Option<CertifiedConstInterpRead>, CertifiedConstInterpReadError> {
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
        let Some(entry) =
            self.certified_const_interp_entry_for_signature(ctx, symbol, arguments, result_sort)?
        else {
            return Ok(None);
        };
        Ok(Some(match entry.body() {
            CertifiedConstInterpBody::Constant { value, .. } => {
                CertifiedConstInterpRead::Constant(*value)
            }
            CertifiedConstInterpBody::LinearInt(linear) => CertifiedConstInterpRead::LinearInt {
                body: linear.clone(),
                arguments: arguments.to_vec(),
            },
            CertifiedConstInterpBody::Expression(body) => {
                if !evaluation_copies::cells(arguments.len()) {
                    return Err(CertifiedConstInterpReadError::ResourceRefused);
                }
                CertifiedConstInterpRead::Expression {
                    body: Arc::clone(body),
                    arguments: arguments.to_vec(),
                }
            }
        }))
    }

    fn certified_const_interp_entry_for_signature(
        &self,
        ctx: &ay_frontend::Context,
        symbol: &Symbol,
        arguments: &[TermId],
        result_sort: &Sort,
    ) -> std::result::Result<Option<&CertifiedConstInterpEntry>, CertifiedConstInterpReadError>
    {
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
        Ok(Some(entry))
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
                || self
                    .certified_total_ufs
                    .by_symbol
                    .contains_key(name.as_str())
                || !matches!(
                    self.projection_ufs.projected_argument_for_signature(
                        binding.symbol(),
                        binding.parameter_sorts(),
                        binding.result_sort(),
                    ),
                    Ok(None)
                )
                || self.euf_model.as_ref().is_some_and(|euf| {
                    euf.function_tables.contains_key(name.as_str())
                        || euf.function_table_terms.contains_key(name.as_str())
                        || euf.function_table_conflicts.contains(name.as_str())
                })
            {
                return None;
            }
            checked.push(FormulaNeutralFunctionDefaultEntry { binding, value });
        }

        if !checked.is_empty() || !self.formula_neutral_function_defaults.entries.is_empty() {
            self.revoke_all_quantified_model_seals();
            for entry in &checked {
                if let Symbol::Named(name) = entry.symbol() {
                    self.materialized_scalar_functions.remove(name.as_str());
                }
            }
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
        Ok(Some(evaluation_copies::copy(entry.value())))
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
