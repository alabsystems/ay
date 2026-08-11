// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

impl Model {
    /// Atomically install one certificate-constructed total interpretation in
    /// both its typed evaluation form and the EUF table used for model output.
    pub(in crate::executor) fn install_certified_total_uf(
        &mut self,
        name: String,
        arg_sorts: Vec<Sort>,
        result_sort: Sort,
        rows: Vec<(Vec<EvalValue>, EvalValue)>,
        default: EvalValue,
    ) -> Option<()> {
        if self.has_certified_const_interp_symbol(&Symbol::named(&name))
            || self.has_formula_neutral_function_default_symbol(&Symbol::named(&name))
        {
            return None;
        }
        let matches_sort = |value: &EvalValue, sort: &Sort| match (value, sort) {
            (EvalValue::Bool(_), Sort::Bool) | (EvalValue::Rational(_), Sort::Real) => true,
            (EvalValue::Rational(r), Sort::Int) => r.is_integer(),
            _ => false,
        };
        if name.is_empty()
            || arg_sorts.is_empty()
            || arg_sorts
                .iter()
                .any(|sort| !matches!(sort, Sort::Int | Sort::Real))
            || !matches_sort(&default, &result_sort)
            || rows.iter().any(|(args, value)| {
                args.len() != arg_sorts.len()
                    || args
                        .iter()
                        .zip(&arg_sorts)
                        .any(|(arg, sort)| !matches_sort(arg, sort))
                    || !matches_sort(value, &result_sort)
            })
        {
            return None;
        }
        // A finite map must be a function before it can become model data.
        // Reject duplicate keys locally even when their values happen to agree:
        // the certificate producers already canonicalize rows, and accepting a
        // duplicate here would make first-match ordering part of the TCB.
        for i in 0..rows.len() {
            if rows[..i].iter().any(|(key, _)| key == &rows[i].0) {
                return None;
            }
        }

        let render = |value: &EvalValue, sort: &Sort| -> Option<String> {
            match (value, sort) {
                (EvalValue::Bool(b), Sort::Bool) => Some(b.to_string()),
                (EvalValue::Rational(r), Sort::Int) if r.is_integer() => {
                    Some(crate::executor_format::format_bigint(r.numer()))
                }
                (EvalValue::Rational(r), Sort::Real) => {
                    Some(crate::executor_format::format_real(r))
                }
                _ => None,
            }
        };
        let mut rendered_table: ay_euf::FunctionTable = Vec::with_capacity(rows.len() + 1);
        for (args, value) in &rows {
            let rendered_args: Vec<String> = args
                .iter()
                .zip(&arg_sorts)
                .map(|(arg, sort)| render(arg, sort))
                .collect::<Option<_>>()?;
            rendered_table.push((rendered_args, render(value, &result_sort)?));
        }

        // The output layer represents a total table by treating the LAST row's
        // result as the else branch. Use an unoccupied synthetic point so its
        // otherwise-ignored key cannot collide with a real exception during
        // the printer's duplicate-key consistency check.
        let mut carrier =
            vec![EvalValue::Rational(BigRational::from_integer(BigInt::from(0))); arg_sorts.len()];
        let mut nonce = BigInt::from(0);
        while rows.iter().any(|(key, _)| key == &carrier) {
            nonce += 1;
            *carrier.last_mut()? = EvalValue::Rational(BigRational::from_integer(nonce.clone()));
        }
        let rendered_carrier: Vec<String> = carrier
            .iter()
            .zip(&arg_sorts)
            .map(|(arg, sort)| render(arg, sort))
            .collect::<Option<_>>()?;
        rendered_table.push((rendered_carrier, render(&default, &result_sort)?));

        let interpretation = CertifiedTotalUfInterpretation {
            arg_sorts,
            result_sort,
            rows,
            default,
            rendered_rows: rendered_table[..rendered_table.len().saturating_sub(1)].to_vec(),
            rendered_default: rendered_table.last()?.1.clone(),
        };
        // Any quantified theorem named the exact model before this table was
        // installed. Revoke every model-relative identity only after all
        // fallible validation/rendering has succeeded, but before the first
        // semantic mutation, so a rejected install remains atomic.
        self.quantified_confirmation_seal.revoke();
        self.revoke_quantified_grant_model();
        self.certified_total_ufs.cegqi_recompletion_epoch = None;
        let euf = self.euf_model.get_or_insert_with(EufModel::default);
        euf.function_tables.insert(name.clone(), rendered_table);
        euf.function_table_terms.remove(&name);
        euf.function_table_conflicts.remove(&name);
        self.certified_total_ufs
            .by_symbol
            .insert(name, interpretation);
        eval_memo_clear();
        Some(())
    }

    /// Install a certificate-constructed total UF whose arguments are concrete
    /// datatype values and whose result is scalar.
    ///
    /// Datatype values are represented internally by the concrete constructor
    /// spelling carried in [`EvalValue::Element`]. `rendered_arguments` must
    /// carry that exact same spelling for output; accepting two vocabularies for
    /// one row would let evaluation and model printing publish different M'.
    /// Abstract EUF elements (`@...`), unresolved/internal markers, and any
    /// typed/rendered mismatch are rejected. Unlike the legacy EUF table
    /// encoding, the certified interpretation stores its else value explicitly,
    /// so an arbitrary synthetic datatype carrier is neither needed nor
    /// admitted.
    pub(in crate::executor) fn install_certified_total_dt_uf(
        &mut self,
        name: String,
        arg_sorts: Vec<Sort>,
        result_sort: Sort,
        rows: Vec<(Vec<EvalValue>, EvalValue)>,
        rendered_arguments: Vec<Vec<String>>,
        default: EvalValue,
    ) -> Option<()> {
        if self.has_certified_const_interp_symbol(&Symbol::named(&name))
            || self.has_formula_neutral_function_default_symbol(&Symbol::named(&name))
        {
            return None;
        }
        let matches_scalar = |value: &EvalValue, sort: &Sort| match (value, sort) {
            (EvalValue::Bool(_), Sort::Bool) | (EvalValue::Rational(_), Sort::Real) => true,
            (EvalValue::Rational(r), Sort::Int) => r.is_integer(),
            _ => false,
        };
        let render_scalar = |value: &EvalValue, sort: &Sort| -> Option<String> {
            match (value, sort) {
                (EvalValue::Bool(b), Sort::Bool) => Some(b.to_string()),
                (EvalValue::Rational(r), Sort::Int) if r.is_integer() => {
                    Some(crate::executor_format::format_bigint(r.numer()))
                }
                (EvalValue::Rational(r), Sort::Real) => {
                    Some(crate::executor_format::format_real(r))
                }
                _ => None,
            }
        };
        let concrete_dt_atom = |value: &EvalValue, sort: &Sort| -> Option<()> {
            let EvalValue::Element(atom) = value else {
                return None;
            };
            if !matches!(sort, Sort::Datatype(_) | Sort::Uninterpreted(_))
                || atom.is_empty()
                || atom.starts_with('@')
                || atom.contains('?')
            {
                return None;
            }
            Some(())
        };
        if name.is_empty()
            || arg_sorts.is_empty()
            || rendered_arguments.len() != rows.len()
            || arg_sorts
                .iter()
                .any(|sort| !matches!(sort, Sort::Datatype(_) | Sort::Uninterpreted(_)))
            || !matches_scalar(&default, &result_sort)
            || rows.iter().any(|(args, value)| {
                args.len() != arg_sorts.len()
                    || args
                        .iter()
                        .zip(&arg_sorts)
                        .any(|(arg, sort)| concrete_dt_atom(arg, sort).is_none())
                    || !matches_scalar(value, &result_sort)
            })
            || rendered_arguments.iter().any(|arguments| {
                arguments.len() != arg_sorts.len()
                    || arguments.iter().any(|argument| {
                        argument.is_empty()
                            || argument.contains('@')
                            || argument.contains('?')
                            || argument.contains("ay.value-unavailable")
                    })
            })
            || rows
                .iter()
                .zip(&rendered_arguments)
                .any(|((arguments, _), rendered)| {
                    arguments.iter().zip(rendered).any(|(argument, surface)| {
                        !matches!(argument, EvalValue::Element(atom) if atom == surface)
                    })
                })
        {
            return None;
        }
        for i in 0..rows.len() {
            if rows[..i].iter().any(|(key, _)| key == &rows[i].0)
                || rendered_arguments[..i]
                    .iter()
                    .any(|key| key == &rendered_arguments[i])
            {
                return None;
            }
        }

        let rendered_rows: Vec<(Vec<String>, String)> = rows
            .iter()
            .zip(rendered_arguments)
            .map(|((_args, value), rendered_args)| {
                Some((rendered_args, render_scalar(value, &result_sort)?))
            })
            .collect::<Option<_>>()?;
        let rendered_default = render_scalar(&default, &result_sort)?;
        let interpretation = CertifiedTotalUfInterpretation {
            arg_sorts,
            result_sort,
            rows,
            default,
            rendered_rows,
            rendered_default,
        };
        // See the scalar-table installer above: a changed certified function
        // interpretation cannot retain any earlier theorem's model identity.
        self.quantified_confirmation_seal.revoke();
        self.revoke_quantified_grant_model();
        self.certified_total_ufs.cegqi_recompletion_epoch = None;
        let euf = self.euf_model.get_or_insert_with(EufModel::default);
        // The raw EUF representation encodes its default as the last row and
        // therefore cannot represent a total datatype table without inventing
        // a carrier.  The typed interpretation is the sole source for this
        // head; model output has a dedicated explicit-default path.
        euf.function_tables.remove(&name);
        euf.function_table_terms.remove(&name);
        euf.function_table_conflicts.remove(&name);
        self.certified_total_ufs
            .by_symbol
            .insert(name, interpretation);
        eval_memo_clear();
        Some(())
    }

    /// Remove only legacy/raw EUF table artifacts for one UF head.
    ///
    /// A quantified certificate may have installed an exact typed total
    /// interpretation for the same head.  That interpretation is the M' the
    /// certificate proved and must survive post-certificate cleanup; deleting
    /// it would silently restore evaluation/output to the incoming ground
    /// candidate M.  Callers that need to invalidate certified authority must
    /// discard the whole result-local [`Model`] instead.
    pub(in crate::executor) fn remove_raw_uf_table_interpretation(&mut self, name: &str) {
        if let Some(euf) = self.euf_model.as_mut() {
            euf.function_tables.remove(name);
            euf.function_table_terms.remove(name);
            euf.function_table_conflicts.remove(name);
        }
        eval_memo_clear();
    }

    /// Whether `name` is governed by an immutable, certificate-constructed
    /// total interpretation.
    ///
    /// Model-completion passes may fill genuinely unconstrained UF points, but
    /// must never add point pins or output rows after this interpretation has
    /// been certified: doing so would make the printed and evaluated models
    /// disagree about the function's else value.
    pub(in crate::executor) fn has_certified_total_uf(&self, name: &str) -> bool {
        self.certified_total_ufs.by_symbol.contains_key(name)
    }

    /// Seal the model after every CEGQI-certified table has been installed.
    /// Subsequent certified-table mutation revokes the returned identity.
    pub(in crate::executor) fn seal_cegqi_uf_recompletion(&mut self) -> CegqiUfModelEpoch {
        let epoch = CegqiUfModelEpoch::fresh();
        self.certified_total_ufs.cegqi_recompletion_epoch = Some(epoch.clone());
        epoch
    }

    /// Revoke the identity of a sealed CEGQI completion before changing any
    /// theorem-relevant part of the model. This lives on `Model` (rather than
    /// only clearing the executor-side grant) so a nested probe cannot take a
    /// grant, mutate the parked outer model, and later restore a capability
    /// whose embedded model identity still appears current.
    pub(in crate::executor) fn revoke_cegqi_uf_recompletion(&mut self) {
        self.certified_total_ufs.cegqi_recompletion_epoch = None;
    }

    /// Whether this is still the exact completed model named by `epoch`.
    pub(in crate::executor) fn carries_cegqi_uf_recompletion(
        &self,
        epoch: &CegqiUfModelEpoch,
    ) -> bool {
        self.certified_total_ufs
            .cegqi_recompletion_epoch
            .as_ref()
            .is_some_and(|installed| installed.is_same_epoch(epoch))
    }
}
