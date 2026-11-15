// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Installation of the quantified model check's completed function tables.
//!
//! The model check (`executor/finite_model_mbqi/generic.rs`) proves each
//! quantifier against a structure in which every tabled function is the
//! `ite` chain of its table plus an else value. This installs exactly that
//! function into a staged model, so evaluation, the independent gate and the
//! printer all read the structure the checked refutations were about. Keys,
//! values and the else value are EVALUATED under the staged model itself, so
//! a key that is a pinned representative becomes that model's element.

use super::*;

impl Executor {
    /// Whether `value` is a value of `sort` a model-check table may carry.
    pub(in crate::executor) fn model_check_carrier_matches(
        &self,
        value: &EvalValue,
        sort: &Sort,
    ) -> bool {
        match (value, sort) {
            (EvalValue::Bool(_), Sort::Bool) | (EvalValue::Rational(_), Sort::Real) => true,
            (EvalValue::Rational(r), Sort::Int) => r.is_integer(),
            (EvalValue::BitVec { width, .. }, Sort::BitVec(bv)) => *width == bv.width,
            (EvalValue::Fp(fp), Sort::FloatingPoint(eb, sb)) => fp.eb() == *eb && fp.sb() == *sb,
            (EvalValue::Element(atom), Sort::Uninterpreted(_)) => {
                !atom.is_empty() && !atom.contains('?') && self.datatype_sort_name(sort).is_none()
            }
            _ => false,
        }
    }

    /// One typed, rendered value of `term` under `model`.
    fn model_check_table_value(
        &self,
        model: &Model,
        term: TermId,
        sort: &Sort,
    ) -> Option<(EvalValue, String)> {
        let value = self.evaluate_term(model, term);
        if !self.model_check_carrier_matches(&value, sort) {
            return None;
        }
        let rendered = self.try_format_eval_value_user(&value, term).ok()?;
        Some((value, rendered))
    }

    /// Install the completed table of `name` into `model`: rows keyed by the
    /// staged values of `rows`' key terms, and `default` as the explicit else
    /// value. Declines (`None`, `model` untouched) on any doubt, including a
    /// head another certificate already interprets.
    pub(in crate::executor) fn install_model_check_total_uf(
        &self,
        model: &mut Model,
        name: &str,
        arg_sorts: &[Sort],
        result_sort: &Sort,
        rows: &[(Vec<TermId>, TermId)],
        default: TermId,
    ) -> Option<()> {
        let symbol = Symbol::named(name);
        if name.is_empty()
            || arg_sorts.is_empty()
            || model.has_certified_const_interp_symbol(&symbol)
            || model.has_formula_neutral_function_default_symbol(&symbol)
            || model.has_certified_total_uf(name)
        {
            return None;
        }
        let (default_value, rendered_default) =
            self.model_check_table_value(model, default, result_sort)?;
        let mut typed: Vec<(Vec<EvalValue>, EvalValue)> = Vec::with_capacity(rows.len());
        let mut rendered: Vec<(Vec<String>, String)> = Vec::with_capacity(rows.len());
        for (keys, value) in rows {
            if keys.len() != arg_sorts.len() {
                return None;
            }
            let mut key_values = Vec::with_capacity(keys.len());
            let mut key_spellings = Vec::with_capacity(keys.len());
            for (&key, sort) in keys.iter().zip(arg_sorts) {
                let (value, spelling) = self.model_check_table_value(model, key, sort)?;
                key_values.push(value);
                key_spellings.push(spelling);
            }
            let (row_value, row_spelling) =
                self.model_check_table_value(model, *value, result_sort)?;
            // Two keys that became equal under the staged model are one point:
            // agreeing rows collapse, disagreeing ones are not a function.
            let mut duplicate = None;
            for (earlier, earlier_value) in &typed {
                let same = earlier
                    .iter()
                    .zip(&key_values)
                    .map(|(a, b)| Self::eval_values_equal_exact(a, b))
                    .try_fold(true, |all, eq| eq.map(|eq| all && eq))?;
                if same {
                    duplicate = Some(Self::eval_values_equal_exact(earlier_value, &row_value)?);
                    break;
                }
            }
            match duplicate {
                Some(true) => continue,
                Some(false) => return None,
                None => {}
            }
            typed.push((key_values, row_value));
            rendered.push((key_spellings, row_spelling));
        }
        let interpretation = CertifiedTotalUfInterpretation {
            arg_sorts: arg_sorts.to_vec(),
            result_sort: result_sort.clone(),
            rows: typed,
            default: default_value,
            rendered_rows: rendered,
            rendered_default,
            element_carriers: true,
        };
        // Commit: a changed function interpretation cannot keep any earlier
        // theorem's model identity (same order as the other installers).
        model.quantified_confirmation_seal.revoke();
        model.revoke_quantified_grant_model();
        model.certified_total_ufs.cegqi_recompletion_epoch = None;
        model.materialized_scalar_functions.remove(name);
        let euf = model.euf_model.get_or_insert_with(EufModel::default);
        euf.function_tables.remove(name);
        euf.function_table_terms.remove(name);
        euf.function_table_conflicts.remove(name);
        model
            .certified_total_ufs
            .by_symbol
            .insert(name.to_string(), interpretation);
        eval_memo_clear();
        Some(())
    }
}
