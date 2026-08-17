// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! FlatZinc variable declarations and their SMT/domain/output encodings.

use super::*;

impl Context {
    pub(crate) fn declare_variable(&mut self, var: &VarDecl) -> Result<(), TranslateError> {
        let is_output = has_output_annotation(&var.annotations);

        match &var.ty {
            FznType::Bool => {
                self.emit_scalar_var(&var.id, Sort::Bool);
                self.var_domains.insert(var.id.clone(), VarDomain::Bool);
                if is_output {
                    self.push_output(&var.id, false, true);
                }
            }
            FznType::Int => {
                self.emit_scalar_var(&var.id, Sort::Int);
                self.var_domains
                    .insert(var.id.clone(), VarDomain::IntUnbounded);
                if is_output {
                    self.push_output(&var.id, false, false);
                }
            }
            FznType::IntRange(lo, hi) => {
                self.emit_scalar_var(&var.id, Sort::Int);
                self.emit_bounds(&var.id, *lo, *hi);
                self.var_domains
                    .insert(var.id.clone(), VarDomain::IntRange(*lo, *hi));
                if is_output {
                    self.push_output(&var.id, false, false);
                }
            }
            FznType::IntSet(values) => {
                self.emit_scalar_var(&var.id, Sort::Int);
                self.emit_domain(&var.id, values);
                self.var_domains
                    .insert(var.id.clone(), VarDomain::IntSet(values.clone()));
                if is_output {
                    self.push_output(&var.id, false, false);
                }
            }
            FznType::ArrayOf { index, elem } => {
                if is_set_type(elem) {
                    self.declare_set_array_var(&var.id, index, &var.value)?;
                } else {
                    self.declare_array_var(&var.id, index, elem, is_output)?;
                }
            }
            FznType::SetOfIntRange(lo, hi) => {
                let width = materialized_range_len(*lo, *hi, "set-of-int")?;
                self.emit_set_var(&var.id, *lo, *hi, width);
                if is_output {
                    self.push_set_output(&var.id, *lo, *hi, width);
                }
            }
            ty => return Err(TranslateError::UnsupportedType(format!("{ty:?}"))),
        }

        // Handle variable assignment (alias or fixed value)
        if let Some(ref val) = var.value {
            if !matches!(&var.ty, FznType::ArrayOf { elem, .. } if is_set_type(elem)) {
                self.emit_var_assignment(&var.id, &var.ty, val)?;
            }
        }
        Ok(())
    }

    fn emit_var_assignment(
        &mut self,
        name: &str,
        ty: &FznType,
        val: &Expr,
    ) -> Result<(), TranslateError> {
        // Defer assignments to after all declarations (same as bounds).
        if let FznType::ArrayOf { index, .. } = ty {
            let (lo, hi) = index_range(index)?;
            let val_elems = self.expr_to_smt_array(val)?;
            validate_array_len(name, lo, hi, val_elems.len())?;
            for (i, smt_val) in val_elems.iter().enumerate() {
                let offset = i64::try_from(i).map_err(|_| {
                    TranslateError::UnsupportedType(format!(
                        "array {name} has too many initializer elements"
                    ))
                })?;
                let index = lo.checked_add(offset).ok_or_else(|| {
                    TranslateError::UnsupportedType(format!("array {name} index overflows i64"))
                })?;
                let smt_var = format!("{name}_{index}");
                self.deferred_bounds
                    .push(format!("(assert (= {smt_var} {smt_val}))"));
            }
        } else {
            let smt_val = self.expr_to_smt(val)?;
            self.deferred_bounds
                .push(format!("(assert (= {name} {smt_val}))"));
        }
        Ok(())
    }

    fn emit_scalar_var(&mut self, name: &str, sort: Sort) {
        self.emit_fmt(format_args!("(declare-const {} {})", name, sort.smt_name()));
        self.scalar_vars
            .insert(name.to_string(), (name.to_string(), sort));
        self.all_smt_vars.push(name.to_string());
    }

    fn emit_set_var(&mut self, name: &str, lo: i64, hi: i64, width: usize) {
        for i in 0..width {
            let bit_name = set_bit_name(name, i as u32);
            self.emit_fmt(format_args!("(declare-const {bit_name} Bool)"));
            self.all_smt_vars.push(bit_name);
        }
        self.set_vars.insert(name.to_string(), (lo, hi));
    }

    fn declare_set_array_var(
        &mut self,
        name: &str,
        index: &IndexSet,
        value: &Option<Expr>,
    ) -> Result<(), TranslateError> {
        let (lo, hi) = index_range(index)?;
        let elems = match value {
            Some(Expr::ArrayLit(elems)) => elems,
            Some(other) => {
                return Err(TranslateError::UnsupportedType(format!(
                    "array set variable {name}: expected array initializer, got {other:?}"
                )));
            }
            None => {
                validate_array_len(name, lo, hi, 0)?;
                self.array_set_vars
                    .insert(name.to_string(), (lo, hi, Vec::new()));
                return Ok(());
            }
        };
        validate_array_len(name, lo, hi, elems.len())?;

        let mut set_names = Vec::with_capacity(elems.len());
        for elem in elems {
            match elem {
                Expr::Ident(set_name) if self.set_vars.contains_key(set_name) => {
                    set_names.push(set_name.clone());
                }
                Expr::Ident(set_name) => {
                    return Err(TranslateError::UnknownIdentifier(format!(
                        "array set variable {name}: {set_name} is not a set var"
                    )));
                }
                other => {
                    return Err(TranslateError::UnsupportedType(format!(
                        "array set variable {name}: expected set variable identifier, got {other:?}"
                    )));
                }
            }
        }

        self.array_set_vars
            .insert(name.to_string(), (lo, hi, set_names));
        Ok(())
    }

    fn emit_bounds(&mut self, name: &str, lo: i64, hi: i64) {
        // Defer bounds to after all declarations to work around a ay bug
        // where interleaved declare/assert patterns cause hangs (#324).
        self.deferred_bounds
            .push(format!("(assert (>= {} {}))", name, smt_int(lo)));
        self.deferred_bounds
            .push(format!("(assert (<= {} {}))", name, smt_int(hi)));
    }

    fn emit_domain(&mut self, name: &str, values: &[i64]) {
        // Defer domain constraints to after all declarations.
        if values.is_empty() {
            self.deferred_bounds.push("(assert false)".to_string());
        } else if values.len() == 1 {
            self.deferred_bounds
                .push(format!("(assert (= {} {}))", name, smt_int(values[0])));
        } else {
            let disjuncts: Vec<String> = values
                .iter()
                .map(|v| format!("(= {} {})", name, smt_int(*v)))
                .collect();
            self.deferred_bounds
                .push(format!("(assert (or {}))", disjuncts.join(" ")));
        }
    }

    fn emit_elem_bounds(&mut self, smt_name: &str, elem: &FznType) {
        match elem {
            FznType::IntRange(lo, hi) => self.emit_bounds(smt_name, *lo, *hi),
            FznType::IntSet(values) => self.emit_domain(smt_name, values),
            _ => {}
        }
    }

    fn declare_array_var(
        &mut self,
        name: &str,
        index: &IndexSet,
        elem: &FznType,
        is_output: bool,
    ) -> Result<(), TranslateError> {
        let (lo, hi) = index_range(index)?;
        let (sort, is_bool) = elem_sort(elem)?;
        self.array_vars.insert(name.to_string(), (lo, hi, sort));
        let mut smt_names = Vec::new();
        for i in lo..=hi {
            let smt_name = format!("{name}_{i}");
            self.emit_fmt(format_args!(
                "(declare-const {} {})",
                smt_name,
                sort.smt_name()
            ));
            self.all_smt_vars.push(smt_name.clone());
            self.emit_elem_bounds(&smt_name, elem);
            let elem_domain = elem_to_domain(elem, is_bool);
            self.var_domains.insert(smt_name.clone(), elem_domain);
            smt_names.push(smt_name);
        }
        if is_output {
            self.output_vars.push(OutputVarInfo {
                fzn_name: name.to_string(),
                smt_names,
                is_array: true,
                array_range: Some((lo, hi)),
                is_bool,
                is_set: false,
                set_range: None,
            });
        }
        Ok(())
    }

    fn push_output(&mut self, name: &str, is_array: bool, is_bool: bool) {
        self.output_vars.push(OutputVarInfo {
            fzn_name: name.to_string(),
            smt_names: vec![name.to_string()],
            is_array,
            array_range: None,
            is_bool,
            is_set: false,
            set_range: None,
        });
    }

    fn push_set_output(&mut self, name: &str, lo: i64, hi: i64, width: usize) {
        let smt_names: Vec<String> = (0..width).map(|i| set_bit_name(name, i as u32)).collect();
        self.output_vars.push(OutputVarInfo {
            fzn_name: name.to_string(),
            smt_names,
            is_array: false,
            array_range: None,
            is_bool: false,
            is_set: true,
            set_range: Some((lo, hi)),
        });
    }
}
