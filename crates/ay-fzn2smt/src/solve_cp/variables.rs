// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0
//
// FlatZinc variable and parameter registration for the CP context.

use std::collections::HashSet;

use crate::error::{Fzn2smtError, Result};
use ay_cp::domain::DomainCreationError;
use ay_cp::propagator::Constraint;
use ay_cp::variable::IntVarId;
use ay_cp::Domain;
use ay_flatzinc_parser::ast::*;

use super::{materialized_range_len, CpContext, CpOutputVar};

impl CpContext {
    pub(super) fn register_parameter(&mut self, par: &ParDecl) -> Result<()> {
        match &par.ty {
            FznType::Bool => {
                let value = match &par.value {
                    Expr::Bool(value) => i64::from(*value),
                    other => {
                        return Err(Fzn2smtError::UnsupportedExpression(format!(
                            "boolean parameter {} requires a Boolean value, got {other:?}",
                            par.id
                        )))
                    }
                };
                self.par_ints.insert(par.id.clone(), value);
            }
            FznType::Int | FznType::IntRange(..) | FznType::IntSet(_) => {
                let value = self.eval_const_int(&par.value).ok_or_else(|| {
                    Fzn2smtError::UnsupportedExpression(format!(
                        "integer parameter {} requires a constant integer value, got {:?}",
                        par.id, par.value
                    ))
                })?;
                self.par_ints.insert(par.id.clone(), value);
            }
            FznType::SetOfInt | FznType::SetOfIntRange(..) | FznType::SetOfIntSet(_) => {
                self.par_sets.insert(par.id.clone(), par.value.clone());
            }
            FznType::ArrayOf { elem, .. } => {
                self.register_array_parameter(par, elem)?;
            }
            unsupported => {
                return Err(unsupported_cp_declaration(
                    &par.id,
                    "parameter",
                    unsupported,
                ));
            }
        }
        Ok(())
    }

    fn register_array_parameter(&mut self, par: &ParDecl, elem: &FznType) -> Result<()> {
        let elems = match &par.value {
            Expr::ArrayLit(e) => e,
            other => {
                return Err(Fzn2smtError::UnsupportedExpression(format!(
                    "array parameter {} requires an array literal, got {other:?}",
                    par.id
                )))
            }
        };
        let FznType::ArrayOf { index, .. } = &par.ty else {
            return Err(Fzn2smtError::UnsupportedExpression(format!(
                "parameter {} is not an array",
                par.id
            )));
        };
        let (lo, hi) = bounded_index_range(index, &par.id)?;
        validate_array_len(&par.id, lo, hi, elems.len())?;
        match elem {
            FznType::Int | FznType::IntRange(..) | FznType::IntSet(_) | FznType::Bool => {
                let vals: Vec<i64> = elems
                    .iter()
                    .map(|e| {
                        self.eval_const_int(e).ok_or_else(|| {
                            Fzn2smtError::UnsupportedExpression(format!(
                                "array parameter {} has a non-constant element {e:?}",
                                par.id
                            ))
                        })
                    })
                    .collect::<Result<_>>()?;
                self.par_int_arrays.insert(par.id.clone(), vals);
                self.par_array_ranges.insert(par.id.clone(), (lo, hi));
            }
            FznType::SetOfInt | FznType::SetOfIntRange(..) | FznType::SetOfIntSet(_) => {
                let sets: Vec<Vec<i64>> = elems
                    .iter()
                    .map(|expr| self.eval_set_elements(expr, &par.id))
                    .collect::<Result<_>>()?;
                self.par_set_arrays.insert(par.id.clone(), sets);
                self.par_array_ranges.insert(par.id.clone(), (lo, hi));
            }
            unsupported => {
                return Err(unsupported_cp_declaration(
                    &par.id,
                    "array-parameter element",
                    unsupported,
                ));
            }
        }
        Ok(())
    }

    pub(super) fn create_variable(&mut self, var: &VarDecl) -> Result<()> {
        let is_output = has_output_annotation(&var.annotations);
        let array_range = get_output_array_range(&var.id, &var.annotations)?;

        match &var.ty {
            FznType::Bool => {
                let id = self.create_scalar_var(&var.id, Domain::new(0, 1), &var.value)?;
                if is_output {
                    self.push_scalar_output(&var.id, id, true);
                }
            }
            FznType::Int => {
                return Err(unbounded_cp_domain(&var.id, "integer"));
            }
            FznType::IntRange(lo, hi) => {
                let domain = Domain::try_new(*lo, *hi)
                    .map_err(|source| invalid_cp_domain(&var.id, source))?;
                let id = self.create_scalar_var(&var.id, domain, &var.value)?;
                if is_output {
                    self.push_scalar_output(&var.id, id, false);
                }
            }
            FznType::IntSet(vals) => {
                let domain = Domain::try_from_values(vals)
                    .map_err(|source| invalid_cp_domain(&var.id, source))?;
                let id = self.create_scalar_var(&var.id, domain, &var.value)?;
                if is_output {
                    self.push_scalar_output(&var.id, id, false);
                }
            }
            FznType::SetOfIntRange(lo, hi) => {
                self.create_set_variable(&var.id, *lo, *hi)?;
                self.constrain_set_initializer(&var.id, &var.value)?;
                if is_output {
                    self.push_set_output(&var.id);
                }
            }
            FznType::SetOfInt => {
                return Err(unbounded_cp_domain(&var.id, "set-of-int"));
            }
            FznType::SetOfIntSet(vals) => {
                self.create_set_variable_from_values(&var.id, vals)?;
                self.constrain_set_initializer(&var.id, &var.value)?;
                if is_output {
                    self.push_set_output(&var.id);
                }
            }
            FznType::ArrayOf { index, elem } => {
                if is_set_type(elem) {
                    self.create_set_array_variable(var, index, elem, array_range)?;
                } else {
                    self.create_array_variable(var, index, elem, array_range)?;
                }
            }
            unsupported => {
                return Err(unsupported_cp_declaration(&var.id, "variable", unsupported));
            }
        }
        Ok(())
    }

    fn push_scalar_output(&mut self, name: &str, id: IntVarId, is_bool: bool) {
        self.output_vars.push(CpOutputVar {
            fzn_name: name.to_string(),
            var_ids: vec![id],
            is_array: false,
            array_range: None,
            is_bool,
            is_set: false,
            set_var_names: Vec::new(),
        });
    }

    fn push_set_output(&mut self, name: &str) {
        self.output_vars.push(CpOutputVar {
            fzn_name: name.to_string(),
            var_ids: Vec::new(),
            is_array: false,
            array_range: None,
            is_bool: false,
            is_set: true,
            set_var_names: vec![name.to_string()],
        });
    }

    /// Create a set variable as N boolean indicator variables.
    /// For `var set of lo..hi`, creates `hi - lo + 1` boolean vars.
    fn create_set_variable(&mut self, name: &str, lo: i64, hi: i64) -> Result<()> {
        let n = materialized_range_len(lo, hi, "set variable")?;
        let mut indicators = Vec::with_capacity(n);
        for j in 0..n {
            let elem = lo + j as i64;
            let var_name = format!("{name}_has_{elem}");
            let id = self.engine.new_bool_var(Some(&var_name));
            self.var_bounds.insert(id, (0, 1));
            indicators.push(id);
        }
        self.set_var_map.insert(name.to_string(), (lo, indicators));
        Ok(())
    }

    /// Create a set variable over an explicit, possibly non-contiguous
    /// universe. Gap indicators are fixed false so values between min/max are
    /// not silently admitted. An empty universe has no indicators and thus
    /// represents only the empty set.
    fn create_set_variable_from_values(&mut self, name: &str, values: &[i64]) -> Result<()> {
        if values.is_empty() {
            self.set_var_map.insert(name.to_string(), (0, Vec::new()));
            return Ok(());
        }

        let mut allowed = values.to_vec();
        allowed.sort_unstable();
        allowed.dedup();
        let lo = allowed[0];
        let hi = *allowed.last().expect("non-empty explicit set universe");
        let n = materialized_range_len(lo, hi, "explicit set variable")?;
        let mut indicators = Vec::with_capacity(n);
        for offset in 0..n {
            let element = lo + offset as i64;
            let var_name = format!("{name}_has_{element}");
            let allowed_element = allowed.binary_search(&element).is_ok();
            let domain = if allowed_element {
                Domain::new(0, 1)
            } else {
                Domain::singleton(0)
            };
            let id = self.engine.new_int_var(domain, Some(&var_name));
            self.var_bounds
                .insert(id, if allowed_element { (0, 1) } else { (0, 0) });
            indicators.push(id);
        }
        self.set_var_map.insert(name.to_string(), (lo, indicators));
        Ok(())
    }

    /// Apply a scalar set declaration initializer exactly. A constant fixes
    /// every membership indicator, while an alias channels membership across
    /// both universes. Values outside the declared universe make the model
    /// inconsistent instead of being silently dropped.
    fn constrain_set_initializer(&mut self, name: &str, value: &Option<Expr>) -> Result<()> {
        let Some(value) = value else {
            return Ok(());
        };

        if let Expr::Ident(source) = value {
            if self.set_var_map.contains_key(source) {
                return self.channel_set_alias(name, source);
            }
        }

        let mut seen = HashSet::new();
        let mut members = self.resolve_constant_set(value, name, &mut seen)?;
        members.sort_unstable();
        members.dedup();

        let (base, indicators) = self.set_var_map.get(name).cloned().ok_or_else(|| {
            Fzn2smtError::UnknownSetVariable {
                constraint: "set initializer".into(),
                name: name.to_string(),
            }
        })?;

        for (offset, indicator) in indicators.iter().copied().enumerate() {
            let element = i128::from(base) + offset as i128;
            let present = i64::try_from(element)
                .ok()
                .is_some_and(|element| members.binary_search(&element).is_ok());
            self.force_indicator(indicator, i64::from(present));
        }

        if members
            .iter()
            .any(|&member| set_indicator(base, &indicators, member).is_none())
        {
            self.add_set_initializer_contradiction(name);
        }
        Ok(())
    }

    fn resolve_constant_set(
        &self,
        expr: &Expr,
        declaration: &str,
        seen: &mut HashSet<String>,
    ) -> Result<Vec<i64>> {
        match expr {
            Expr::SetLit(elements) => elements
                .iter()
                .map(|element| {
                    self.eval_const_int(element).ok_or_else(|| {
                        Fzn2smtError::UnsupportedExpression(format!(
                            "set initializer for {declaration} has a non-constant element {element:?}"
                        ))
                    })
                })
                .collect(),
            Expr::IntRange(lo, hi) => {
                let len = materialized_range_len(*lo, *hi, "set initializer")?;
                Ok((0..len).map(|offset| *lo + offset as i64).collect())
            }
            Expr::EmptySet => Ok(Vec::new()),
            Expr::Ident(parameter) => {
                if !seen.insert(parameter.clone()) {
                    return Err(Fzn2smtError::UnsupportedExpression(format!(
                        "cyclic set parameter initializer involving {parameter}"
                    )));
                }
                let parameter_value = self.par_sets.get(parameter).cloned().ok_or_else(|| {
                    Fzn2smtError::UnknownSetVariable {
                        constraint: "set initializer".into(),
                        name: parameter.clone(),
                    }
                })?;
                let result = self.resolve_constant_set(&parameter_value, declaration, seen);
                seen.remove(parameter);
                result
            }
            other => Err(Fzn2smtError::UnsupportedExpression(format!(
                "set initializer for {declaration} must be a constant set or set-variable alias, got {other:?}"
            ))),
        }
    }

    fn channel_set_alias(&mut self, target: &str, source: &str) -> Result<()> {
        let (target_base, target_indicators) =
            self.set_var_map.get(target).cloned().ok_or_else(|| {
                Fzn2smtError::UnknownSetVariable {
                    constraint: "set initializer".into(),
                    name: target.to_string(),
                }
            })?;
        let (source_base, source_indicators) =
            self.set_var_map.get(source).cloned().ok_or_else(|| {
                Fzn2smtError::UnknownSetVariable {
                    constraint: "set initializer".into(),
                    name: source.to_string(),
                }
            })?;

        for (offset, target_indicator) in target_indicators.iter().copied().enumerate() {
            let element = i128::from(target_base) + offset as i128;
            let source_indicator = i64::try_from(element)
                .ok()
                .and_then(|element| set_indicator(source_base, &source_indicators, element));
            if let Some(source_indicator) = source_indicator {
                if target_indicator != source_indicator {
                    self.engine.add_constraint(Constraint::LinearEq {
                        coeffs: vec![1, -1],
                        vars: vec![target_indicator, source_indicator],
                        rhs: 0,
                    });
                }
            } else {
                self.force_indicator(target_indicator, 0);
            }
        }

        for (offset, source_indicator) in source_indicators.iter().copied().enumerate() {
            let element = i128::from(source_base) + offset as i128;
            let is_in_target = i64::try_from(element).ok().is_some_and(|element| {
                set_indicator(target_base, &target_indicators, element).is_some()
            });
            if !is_in_target {
                self.force_indicator(source_indicator, 0);
            }
        }
        Ok(())
    }

    fn force_indicator(&mut self, indicator: IntVarId, value: i64) {
        self.engine.add_constraint(Constraint::LinearEq {
            coeffs: vec![1],
            vars: vec![indicator],
            rhs: value,
        });
    }

    fn add_set_initializer_contradiction(&mut self, name: &str) {
        let witness_name = format!("{name}_invalid_initializer");
        let witness = self
            .engine
            .new_int_var(Domain::singleton(0), Some(&witness_name));
        self.var_bounds.insert(witness, (0, 0));
        self.force_indicator(witness, 1);
    }

    /// Create an array of set variables, registering each element set var.
    fn create_set_array_variable(
        &mut self,
        var: &VarDecl,
        index: &IndexSet,
        elem: &FznType,
        array_output: Option<(i64, i64)>,
    ) -> Result<()> {
        let range = bounded_index_range(index, &var.id)?;
        validate_output_array_range(&var.id, range, array_output)?;
        self.array_var_ranges.insert(var.id.clone(), range);

        let set_names = match &var.value {
            Some(Expr::ArrayLit(elems)) => {
                validate_array_len(&var.id, range.0, range.1, elems.len())?;
                let mut set_names = Vec::with_capacity(elems.len());
                for e in elems {
                    match e {
                        Expr::Ident(name) if self.set_var_map.contains_key(name) => {
                            self.constrain_set_array_element(name, elem)?;
                            set_names.push(name.clone());
                        }
                        Expr::Ident(name) => {
                            return Err(Fzn2smtError::UnknownSetVariable {
                                constraint: "array set variable".into(),
                                name: name.clone(),
                            });
                        }
                        other => {
                            return Err(Fzn2smtError::UnsupportedExpression(format!(
                                "array set variable {}: expected set variable identifier, got {other:?}",
                                var.id
                            )));
                        }
                    }
                }
                set_names
            }
            None => self.create_declared_set_array_elements(&var.id, range, elem)?,
            Some(other) => {
                return Err(Fzn2smtError::UnsupportedExpression(format!(
                    "array set variable {} requires an array initializer, got {other:?}",
                    var.id
                )))
            }
        };

        self.set_array_var_map
            .insert(var.id.clone(), set_names.clone());

        if let Some(out_range) = array_output {
            self.output_vars.push(CpOutputVar {
                fzn_name: var.id.clone(),
                var_ids: Vec::new(),
                is_array: true,
                array_range: Some(out_range),
                is_bool: false,
                is_set: true,
                set_var_names: set_names,
            });
        }
        Ok(())
    }

    fn create_declared_set_array_elements(
        &mut self,
        array_name: &str,
        range: (i64, i64),
        elem: &FznType,
    ) -> Result<Vec<String>> {
        if matches!(elem, FznType::SetOfInt) {
            return Err(unbounded_cp_domain(array_name, "set-array element"));
        }
        let len = materialized_range_len(range.0, range.1, "set array")?;
        let mut names = Vec::with_capacity(len);
        for offset in 0..len {
            let index = range.0.checked_add(offset as i64).ok_or_else(|| {
                Fzn2smtError::UnsupportedExpression(format!(
                    "array {array_name} index overflows i64"
                ))
            })?;
            let name = format!("{array_name}_{index}");
            match elem {
                FznType::SetOfIntRange(lo, hi) => self.create_set_variable(&name, *lo, *hi)?,
                FznType::SetOfIntSet(values) => {
                    self.create_set_variable_from_values(&name, values)?
                }
                _ => unreachable!("caller accepts only set element types"),
            }
            names.push(name);
        }
        Ok(names)
    }

    fn create_scalar_var(
        &mut self,
        name: &str,
        domain: Domain,
        value: &Option<Expr>,
    ) -> Result<IntVarId> {
        let lb = domain.lb();
        let ub = domain.ub();
        let id = self.engine.new_int_var(domain, Some(name));
        self.var_map.insert(name.to_string(), id);
        self.var_bounds.insert(id, (lb, ub));

        if let Some(expr) = value {
            if let Some(constant) = self.eval_const_int(expr) {
                // Keep the declared domain and channel the initializer through
                // a constraint. A constant outside the domain is a valid but
                // inconsistent model and must solve UNSAT, not escape the
                // declared bounds through a replacement singleton.
                self.engine.add_constraint(Constraint::LinearEq {
                    coeffs: vec![1],
                    vars: vec![id],
                    rhs: constant,
                });
            } else if let Expr::Ident(ref_name) = expr {
                let existing = self.var_map.get(ref_name).copied().ok_or_else(|| {
                    Fzn2smtError::UnknownVariable {
                        name: ref_name.clone(),
                    }
                })?;
                // A declaration alias is equality between two declared
                // variables, not permission to discard `name`'s own domain.
                self.engine.add_constraint(Constraint::LinearEq {
                    coeffs: vec![1, -1],
                    vars: vec![id, existing],
                    rhs: 0,
                });
            } else {
                return Err(Fzn2smtError::UnsupportedExpression(format!(
                    "variable {name} has unsupported initializer {expr:?}"
                )));
            }
        }
        Ok(id)
    }

    fn create_array_variable(
        &mut self,
        var: &VarDecl,
        index: &IndexSet,
        elem: &FznType,
        array_output: Option<(i64, i64)>,
    ) -> Result<()> {
        if !matches!(
            elem,
            FznType::Bool | FznType::Int | FznType::IntRange(..) | FznType::IntSet(_)
        ) {
            return Err(unsupported_cp_declaration(
                &var.id,
                "array-variable element",
                elem,
            ));
        }
        let is_bool = matches!(elem, FznType::Bool);
        let range = bounded_index_range(index, &var.id)?;
        validate_output_array_range(&var.id, range, array_output)?;
        self.array_var_ranges.insert(var.id.clone(), range);

        let elems = match &var.value {
            Some(Expr::ArrayLit(elems)) => elems,
            None => {
                let domain = match elem {
                    FznType::Bool => Domain::new(0, 1),
                    FznType::Int => {
                        return Err(unbounded_cp_domain(&var.id, "integer-array element"));
                    }
                    FznType::IntRange(lo, hi) => Domain::try_new(*lo, *hi)
                        .map_err(|source| invalid_cp_domain(&var.id, source))?,
                    FznType::IntSet(values) => Domain::try_from_values(values)
                        .map_err(|source| invalid_cp_domain(&var.id, source))?,
                    _ => unreachable!("unsupported array elements are rejected above"),
                };
                let len = materialized_range_len(range.0, range.1, "integer array")?;
                let mut ids = Vec::with_capacity(len);
                for offset in 0..len {
                    let index = range.0.checked_add(offset as i64).ok_or_else(|| {
                        Fzn2smtError::UnsupportedExpression(format!(
                            "array {} index overflows i64",
                            var.id
                        ))
                    })?;
                    let elem_name = format!("{}_{index}", var.id);
                    ids.push(self.create_scalar_var(&elem_name, domain.clone(), &None)?);
                }
                self.array_var_map.insert(var.id.clone(), ids.clone());
                if let Some(out_range) = array_output {
                    self.output_vars.push(CpOutputVar {
                        fzn_name: var.id.clone(),
                        var_ids: ids,
                        is_array: true,
                        array_range: Some(out_range),
                        is_bool,
                        is_set: false,
                        set_var_names: Vec::new(),
                    });
                }
                return Ok(());
            }
            Some(other) => {
                return Err(Fzn2smtError::UnsupportedExpression(format!(
                    "array variable {} requires an array initializer, got {other:?}",
                    var.id
                )))
            }
        };
        validate_array_len(&var.id, range.0, range.1, elems.len())?;

        let mut ids = Vec::with_capacity(elems.len());
        for (i, e) in elems.iter().enumerate() {
            let offset = i64::try_from(i).map_err(|_| {
                Fzn2smtError::UnsupportedExpression(format!(
                    "array {} has too many elements",
                    var.id
                ))
            })?;
            let element_index = range.0.checked_add(offset).ok_or_else(|| {
                Fzn2smtError::UnsupportedExpression(format!("array {} index overflows i64", var.id))
            })?;
            let elem_name = format!("{}_{element_index}", var.id);
            let id = self.resolve_array_element(e, &elem_name)?;
            self.constrain_array_element_domain(id, elem, &elem_name)?;
            ids.push(id);
        }

        self.array_var_map.insert(var.id.clone(), ids.clone());

        if let Some(out_range) = array_output {
            self.output_vars.push(CpOutputVar {
                fzn_name: var.id.clone(),
                var_ids: ids,
                is_array: true,
                array_range: Some(out_range),
                is_bool,
                is_set: false,
                set_var_names: Vec::new(),
            });
        }
        Ok(())
    }

    fn constrain_array_element_domain(
        &mut self,
        id: IntVarId,
        elem: &FznType,
        name: &str,
    ) -> Result<()> {
        match elem {
            // An initialized unbounded array is a view over already-declared,
            // bounded variables/constants. No synthetic fallback bounds are
            // introduced.
            FznType::Int => {
                if !self.var_bounds.contains_key(&id) {
                    return Err(unbounded_cp_domain(name, "integer-array element"));
                }
            }
            FznType::Bool => {
                self.engine.add_constraint(Constraint::LinearGe {
                    coeffs: vec![1],
                    vars: vec![id],
                    rhs: 0,
                });
                self.engine.add_constraint(Constraint::LinearLe {
                    coeffs: vec![1],
                    vars: vec![id],
                    rhs: 1,
                });
            }
            FznType::IntRange(lo, hi) => {
                Domain::try_new(*lo, *hi).map_err(|source| invalid_cp_domain(name, source))?;
                self.engine.add_constraint(Constraint::LinearGe {
                    coeffs: vec![1],
                    vars: vec![id],
                    rhs: *lo,
                });
                self.engine.add_constraint(Constraint::LinearLe {
                    coeffs: vec![1],
                    vars: vec![id],
                    rhs: *hi,
                });
            }
            FznType::IntSet(values) => {
                Domain::try_from_values(values)
                    .map_err(|source| invalid_cp_domain(name, source))?;
                let mut values = values.clone();
                values.sort_unstable();
                values.dedup();
                self.engine.add_constraint(Constraint::Table {
                    vars: vec![id],
                    tuples: values.into_iter().map(|value| vec![value]).collect(),
                });
            }
            _ => unreachable!("unsupported array elements are rejected before materialization"),
        }
        Ok(())
    }

    fn constrain_set_array_element(&mut self, name: &str, elem: &FznType) -> Result<()> {
        let Some((base, indicators)) = self.set_var_map.get(name).cloned() else {
            return Err(Fzn2smtError::UnknownSetVariable {
                constraint: "array set variable".into(),
                name: name.to_string(),
            });
        };
        for (offset, indicator) in indicators.into_iter().enumerate() {
            let element = i128::from(base) + offset as i128;
            let allowed = match elem {
                FznType::SetOfInt => true,
                FznType::SetOfIntRange(lo, hi) => {
                    element >= i128::from(*lo) && element <= i128::from(*hi)
                }
                FznType::SetOfIntSet(values) => i64::try_from(element)
                    .ok()
                    .is_some_and(|element| values.contains(&element)),
                _ => true,
            };
            if !allowed {
                self.engine.add_constraint(Constraint::LinearEq {
                    coeffs: vec![1],
                    vars: vec![indicator],
                    rhs: 0,
                });
            }
        }
        Ok(())
    }

    fn resolve_array_element(&mut self, expr: &Expr, elem_name: &str) -> Result<IntVarId> {
        match expr {
            Expr::Ident(name) => {
                if let Some(&existing) = self.var_map.get(name) {
                    self.var_map.insert(elem_name.to_string(), existing);
                    Ok(existing)
                } else if let Some(&v) = self.par_ints.get(name) {
                    let id = self
                        .engine
                        .new_int_var(Domain::singleton(v), Some(elem_name));
                    self.var_map.insert(elem_name.to_string(), id);
                    self.var_bounds.insert(id, (v, v));
                    Ok(id)
                } else {
                    Err(Fzn2smtError::UnknownVariable { name: name.clone() })
                }
            }
            Expr::Int(n) => {
                let id = self
                    .engine
                    .new_int_var(Domain::singleton(*n), Some(elem_name));
                self.var_map.insert(elem_name.to_string(), id);
                self.var_bounds.insert(id, (*n, *n));
                Ok(id)
            }
            Expr::Bool(b) => {
                let val = i64::from(*b);
                let id = self
                    .engine
                    .new_int_var(Domain::singleton(val), Some(elem_name));
                self.var_map.insert(elem_name.to_string(), id);
                self.var_bounds.insert(id, (val, val));
                Ok(id)
            }
            _ => Err(Fzn2smtError::UnsupportedExpression(format!(
                "unsupported array element expression: {expr:?}"
            ))),
        }
    }

    fn eval_set_elements(&self, expr: &Expr, parameter: &str) -> Result<Vec<i64>> {
        match expr {
            Expr::SetLit(elems) => elems
                .iter()
                .map(|element| {
                    self.eval_const_int(element).ok_or_else(|| {
                        Fzn2smtError::UnsupportedExpression(format!(
                            "set array parameter {parameter} has a non-constant element {element:?}"
                        ))
                    })
                })
                .collect(),
            Expr::IntRange(lo, hi) => {
                let len = materialized_range_len(*lo, *hi, "set parameter")?;
                let mut values = Vec::with_capacity(len);
                for offset in 0..len {
                    values.push(*lo + offset as i64);
                }
                Ok(values)
            }
            Expr::EmptySet => Ok(Vec::new()),
            other => Err(Fzn2smtError::UnsupportedExpression(format!(
                "set array parameter {parameter} requires a set literal, got {other:?}"
            ))),
        }
    }
}

fn has_output_annotation(annotations: &[Annotation]) -> bool {
    annotations
        .iter()
        .any(|a| matches!(a, Annotation::Atom(s) if s == "output_var"))
}

fn invalid_cp_domain(variable: &str, source: DomainCreationError) -> Fzn2smtError {
    Fzn2smtError::InvalidCpIntegerDomain {
        variable: variable.to_string(),
        source,
    }
}

fn unbounded_cp_domain(variable: &str, kind: &str) -> Fzn2smtError {
    Fzn2smtError::UnsupportedExpression(format!(
        "solve-cp requires a finite declared domain for {kind} variable {variable}"
    ))
}

fn unsupported_cp_declaration(name: &str, kind: &str, ty: &FznType) -> Fzn2smtError {
    Fzn2smtError::UnsupportedExpression(format!(
        "solve-cp does not support {kind} {name} with type {ty:?}"
    ))
}

fn set_indicator(base: i64, indicators: &[IntVarId], element: i64) -> Option<IntVarId> {
    let offset = i128::from(element) - i128::from(base);
    usize::try_from(offset)
        .ok()
        .and_then(|offset| indicators.get(offset).copied())
}

fn is_set_type(ty: &FznType) -> bool {
    matches!(
        ty,
        FznType::SetOfInt | FznType::SetOfIntRange(..) | FznType::SetOfIntSet(..)
    )
}

fn bounded_index_range(index: &IndexSet, name: &str) -> Result<(i64, i64)> {
    match index {
        IndexSet::Range(lo, hi) => {
            materialized_range_len(*lo, *hi, "array index")?;
            Ok((*lo, *hi))
        }
        IndexSet::Int => Err(Fzn2smtError::UnsupportedExpression(format!(
            "array {name} has an unbounded index set"
        ))),
    }
}

fn validate_array_len(name: &str, lo: i64, hi: i64, actual: usize) -> Result<()> {
    let expected = materialized_range_len(lo, hi, "array index")?;
    if actual != expected {
        return Err(Fzn2smtError::UnsupportedExpression(format!(
            "array {name} declares index range {lo}..{hi} ({expected} elements) but has {actual} initializer elements"
        )));
    }
    Ok(())
}

fn get_output_array_range(name: &str, annotations: &[Annotation]) -> Result<Option<(i64, i64)>> {
    let mut output_range = None;
    for a in annotations {
        if let Annotation::Call(annotation_name, call_args) = a {
            if annotation_name == "output_array" {
                if output_range.is_some() || call_args.len() != 1 {
                    return Err(Fzn2smtError::UnsupportedExpression(format!(
                        "array {name} has multiple or malformed output_array annotations"
                    )));
                }
                let Some(Expr::ArrayLit(ranges)) = call_args.first() else {
                    return Err(Fzn2smtError::UnsupportedExpression(format!(
                        "array {name} output_array annotation requires an index-range array"
                    )));
                };
                let [Expr::IntRange(lo, hi)] = ranges.as_slice() else {
                    return Err(Fzn2smtError::UnsupportedExpression(format!(
                        "array {name} output_array annotation must contain exactly one index range"
                    )));
                };
                output_range = Some((*lo, *hi));
            }
        }
    }
    Ok(output_range)
}

fn validate_output_array_range(
    name: &str,
    declared: (i64, i64),
    output: Option<(i64, i64)>,
) -> Result<()> {
    if let Some(output) = output {
        if output != declared {
            return Err(Fzn2smtError::UnsupportedExpression(format!(
                "array {name} declares index range {}..{} but output_array requests {}..{}",
                declared.0, declared.1, output.0, output.1
            )));
        }
    }
    Ok(())
}
