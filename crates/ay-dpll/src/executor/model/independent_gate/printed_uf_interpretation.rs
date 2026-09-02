// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Construction of reconciled printed-UF interpretations.

use ay_core::kani_compat::DetHashSet;

use super::*;

impl IndependentModelView<'_> {
    /// Uncached body of [`Self::printed_uf_interpretation`]: the printer's own
    /// pipeline, in the printer's order, over the model's extracted table.
    pub(super) fn build_printed_uf_interpretation(
        &self,
        identity: &str,
    ) -> Option<PrintedUfInterpretation> {
        let (arg_sorts, result_sort, rows) = self.printed_uf_rows(identity)?;
        let rows = rows.ok()?;
        self.read_printed_uf_rows(&arg_sorts, &result_sort, &rows)
    }

    /// The printer's row pipeline for `identity`, stopping one step short of
    /// decoding: `None` when `(get-model)` would not print this symbol at all,
    /// otherwise the declared signature plus [`Executor::printed_uf_table_rows`]'
    /// own typed `Result`.
    ///
    /// Split out so the gate can see the ERROR that
    /// [`Self::build_printed_uf_interpretation`] discards. Coverage gaps remain
    /// distinct from the typed inconsistent-table refutation, which means two
    /// rows land on the same argument point with different results. See
    /// [`Self::non_functional_uf_interpretation`].
    pub(super) fn printed_uf_rows(
        &self,
        identity: &str,
    ) -> Option<(
        Vec<Sort>,
        Sort,
        Result<Vec<(Vec<String>, String)>, super::super::output_format::PrintedUfTableRowsError>,
    )> {
        // Locate the DECLARED signature `(get-model)` would print this table
        // under, and reproduce the printer's suppression / other-channel
        // rules (`Executor::format_model`, same order).
        let ctx = &self.exec.ctx;
        let (surface, info) = ctx
            .symbol_iter()
            .find(|(name, info)| ctx.symbol_identity_name(name, info) == identity)?;
        if self.exec.is_exact_dt_internal_symbol(identity) || ctx.is_internal_symbol(surface) {
            return None;
        }
        let symbol = Symbol::named(identity);
        if !matches!(
            self.model.projection_ufs.projected_argument_for_signature(
                &symbol,
                &info.arg_sorts,
                &info.sort,
            ),
            Ok(None)
        ) {
            return None;
        }
        if self
            .model
            .certified_total_ufs
            .by_symbol
            .contains_key(identity)
            || self
                .exec
                .const_interp_cert_witness_entries(self.model)
                .iter()
                .any(|entry| entry.name() == Some(surface.as_str()))
            || self
                .model
                .has_formula_neutral_function_default_symbol(&symbol)
            || ctx.adopted_macro_interp(surface).is_some()
            || ctx.is_defined_fun(surface)
        {
            return None;
        }
        let arg_sorts: &[Sort] = &info.arg_sorts;
        let result_sort = &info.sort;
        if arg_sorts.is_empty() {
            return None;
        }

        let table = if let Some((euf, raw)) = self
            .model
            .euf_model
            .as_ref()
            .and_then(|euf| euf.function_tables.get(identity).map(|raw| (euf, raw)))
        {
            let table = self
                .exec
                .sequence_table_provenance_placeholders(
                    identity,
                    arg_sorts,
                    result_sort,
                    raw,
                    euf.function_table_terms.get(identity).map(Vec::as_slice),
                )
                .ok()?;
            let table = self.exec.resolve_function_table(self.model, &table);
            match self
                .exec
                .dt_egraph_rewrite_uf_table(self.model, arg_sorts, result_sort, &table)
            {
                super::super::dt_egraph_values::DtUfTableRewrite::NotApplicable => table,
                super::super::dt_egraph_values::DtUfTableRewrite::Rewritten(t) => t,
                // The printer OMITS this definition, leaving the model partial here.
                super::super::dt_egraph_values::DtUfTableRewrite::Drop => return None,
            }
        } else {
            // #gate-reads-ground-uf-fallback: BV/AUFBV lanes Ackermannize
            // declared UFs and therefore publish no EufModel table.  The model
            // printer still emits a total interpretation reconstructed from
            // every ground application in the authored assertions.  Read that
            // exact fallback here as well; otherwise the independent gate sees
            // a datatype-valued application only as an opaque carrier token
            // while the public witness prints a concrete constructor value.
            //
            // Mirror the printer's quantifier guard and collection root.  A
            // quantified occurrence leaves the interpretation omitted rather
            // than inventing an else branch, and any unreadable application or
            // non-function table remains `None` through the helpers below.
            if self.exec.symbol_occurs_under_quantifier(surface) {
                return None;
            }
            let mut applications: DetHashMap<(String, usize), Vec<(TermId, Vec<TermId>)>> =
                DetHashMap::default();
            let mut visited = DetHashSet::default();
            for &assertion in &ctx.assertions {
                self.exec
                    .collect_uf_applications(assertion, &mut applications, &mut visited);
            }
            let applications = applications.get(&(surface.to_string(), arg_sorts.len()))?;
            self.exec
                .uf_table_from_ground_applications(self.model, applications)?
        };
        let rows =
            self.exec
                .printed_uf_table_rows(surface, arg_sorts, result_sort, &table, self.model);
        Some((arg_sorts.to_vec(), result_sort.clone(), rows))
    }

    /// A published model must be a FUNCTION. Report the first uninterpreted
    /// symbol whose extracted table is not one (#bv2nat-subst-recover, follow-on).
    ///
    /// `printed_uf_table_rows` already detects this — two rows resolving to the
    /// same argument point with different results — and the printer fails the
    /// `(get-model)` command on it rather than emitting a falsifying witness.
    /// The VERDICT path did not look: the gate swallowed the error with `.ok()?`
    /// and fell back to a pin-only, TermId-keyed read of the same table, which
    /// happily reads `f(v) = 1` for the pinned application while the table also
    /// carries `f(0) = 101` and the model says `v = 0`.
    ///
    /// That gap is only reachable when the conflicting row is invisible to the
    /// compositional evaluator — e.g. `f(0)` comes from a QUANTIFIER
    /// instantiation whose assertion model validation skipped, so no single
    /// conjunct is false and cross-conjunct single-valuedness never sees the
    /// pair. Measured shape:
    ///
    /// ```smt2
    /// (assert (and (<= 0 a) (< a 4)))
    /// (assert (= v (bv2nat (bvand ((_ int2bv 64) a) ((_ int2bv 64) 1)))))
    /// (assert (forall ((x Int)) (=> (and (<= 0 x) (<= x 1)) (> (f x) 100))))
    /// (assert (< (f v) 50))          ; UNSAT: v in {0,1}
    /// ```
    ///
    /// which reported `sat` with `((a 2) (v 0) ((f v) 1) ((f 0) 101))` — a model
    /// that contradicts itself, and a WRONG SAT. Before the `bv2nat` recovery
    /// fix the same query was `unknown` only because `v` had no value at all and
    /// the round-trip assertion tripped the gate first; the hole was masked, not
    /// absent.
    ///
    /// SOUNDNESS DIRECTION: this can only turn a `sat` into `unknown`. It never
    /// admits a model, never touches an UNSAT derivation, and never suppresses a
    /// report — it ADDS a refusal the printer was already making one command
    /// later.
    pub(in crate::executor) fn non_functional_uf_interpretation(&self) -> Option<String> {
        // Check both sources used by `printed_uf_rows`: extracted EUF tables
        // and the exact authored-ground fallback used when BV/AUFBV
        // Ackermannization publishes no EUF table.
        let mut identities = DetHashSet::default();
        if let Some(euf) = self.model.euf_model.as_ref() {
            identities.extend(euf.function_tables.keys().cloned());
        }
        let mut ground_applications: DetHashMap<(String, usize), Vec<(TermId, Vec<TermId>)>> =
            DetHashMap::default();
        let mut visited = DetHashSet::default();
        for &assertion in &self.exec.ctx.assertions {
            self.exec
                .collect_uf_applications(assertion, &mut ground_applications, &mut visited);
        }
        for (surface, info) in self.exec.ctx.symbol_iter() {
            if ground_applications.contains_key(&(surface.to_string(), info.arg_sorts.len())) {
                identities.insert(
                    self.exec
                        .ctx
                        .symbol_identity_name(surface, info)
                        .to_string(),
                );
            }
        }
        // Deterministic order: the first offender must not depend on hash
        // iteration, or the reason string flaps between otherwise identical runs.
        let mut identities: Vec<String> = identities.into_iter().collect();
        identities.sort();
        for identity in identities {
            if let Some((_, _, Err(error))) = self.printed_uf_rows(&identity) {
                if matches!(
                    error,
                    super::super::output_format::PrintedUfTableRowsError::InconsistentFunctionTable { .. }
                ) {
                    return Some(error.to_string());
                }
            }
        }
        None
    }

    /// Decode the printer's ordered rows into the gate's canonical value
    /// encoding, refusing the whole interpretation if any atom is unreadable.
    pub(super) fn read_printed_uf_rows(
        &self,
        arg_sorts: &[Sort],
        result_sort: &Sort,
        rows: &[(Vec<String>, String)],
    ) -> Option<PrintedUfInterpretation> {
        let ctx = &self.exec.ctx;
        // Read the printed body back into gate values ONCE. An atom this view
        // cannot parse — or parses into anything but the gate's canonical
        // encoding for its sort — leaves the whole interpretation unreadable
        // (`None`): a partially readable body could match the wrong `ite` arm.
        // MEASURED instance of the encoding case: for a QF_UFDT enum
        // `(declare-datatype Unit ((u0) (u1)))` the EUF table of `f : Unit ->
        // Unit` is keyed by the class tokens `@Unit!N`, and `(get-model)`
        // prints `(ite (= x0 (as @Unit!1 Unit)) (as @Unit!0 Unit) ..)` while
        // the gate (and the printed constant `x`) hold the value as the
        // CONSTRUCTOR `u1` (#dt-element-canon). Those tokens would never match
        // a constructor-valued argument, so every read would fall to the
        // `else` arm; the table is therefore declared unreadable and the
        // application keeps today's pin-only read
        // (`test_enum_sat_lane_gate_excludes_uf_at_variable_args` pins that).
        let read_atom = |atom: &str, sort: &Sort| -> Option<ModelValue> {
            let v = self.parse_leaf(atom, sort)?;
            self.printed_atom_in_gate_encoding(&v, sort).then_some(v)
        };
        let Some((_, else_atom)) = rows.last() else {
            // Empty table => the printer emits the canonical constant body.
            let else_value =
                read_atom(&format_default_value_surface(ctx, result_sort), result_sort)?;
            return Some(PrintedUfInterpretation {
                arity: arg_sorts.len(),
                rows: Vec::new(),
                else_value,
            });
        };
        let else_value = read_atom(else_atom, result_sort)?;
        let mut parsed_rows = Vec::with_capacity(rows.len() - 1);
        for (row_args, row_value) in rows.iter().take(rows.len() - 1) {
            if row_args.len() != arg_sorts.len() {
                return None;
            }
            let mut point = Vec::with_capacity(row_args.len());
            for (atom, sort) in row_args.iter().zip(arg_sorts) {
                point.push(read_atom(atom, sort)?);
            }
            parsed_rows.push((point, read_atom(row_value, result_sort)?));
        }
        Some(PrintedUfInterpretation {
            arity: arg_sorts.len(),
            rows: parsed_rows,
            else_value,
        })
    }
}
