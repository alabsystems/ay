// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Construction of reconciled printed-UF interpretations.

use super::*;

impl IndependentModelView<'_> {
    /// Uncached body of [`Self::printed_uf_interpretation`]: the printer's own
    /// pipeline, in the printer's order, over the model's extracted table.
    pub(super) fn build_printed_uf_interpretation(
        &self,
        identity: &str,
    ) -> Option<PrintedUfInterpretation> {
        let euf = self.model.euf_model.as_ref()?;
        let raw = euf.function_tables.get(identity)?;

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
        let table =
            match self
                .exec
                .dt_egraph_rewrite_uf_table(self.model, arg_sorts, result_sort, &table)
            {
                super::super::dt_egraph_values::DtUfTableRewrite::NotApplicable => table,
                super::super::dt_egraph_values::DtUfTableRewrite::Rewritten(t) => t,
                // The printer OMITS this definition, leaving the model partial here.
                super::super::dt_egraph_values::DtUfTableRewrite::Drop => return None,
            };
        let rows = self
            .exec
            .printed_uf_table_rows(identity, arg_sorts, result_sort, &table, self.model)
            .ok()?;
        self.read_printed_uf_rows(arg_sorts, result_sort, &rows)
    }

    /// Decode the printer's ordered rows into the gate's canonical value
    /// encoding, refusing the whole interpretation if any atom is unreadable.
    fn read_printed_uf_rows(
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
