// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0
// Expression and value resolution for FlatZinc-to-SMT translation

use ay_flatzinc_parser::ast::Expr;

use crate::error::TranslateError;
use crate::translate::{materialized_range_len, smt_int, Context, ScalarValue};

/// Expression resolution methods for the translation context.
impl Context {
    /// Convert a scalar FlatZinc expression to an SMT-LIB term string.
    pub(crate) fn expr_to_smt(&self, expr: &Expr) -> Result<String, TranslateError> {
        match expr {
            Expr::Bool(true) => Ok("true".into()),
            Expr::Bool(false) => Ok("false".into()),
            Expr::Int(n) => Ok(smt_int(*n)),
            Expr::Float(f) => Ok(format!("{f}")),
            Expr::Ident(name) => self.resolve_ident(name),
            Expr::ArrayAccess(name, idx_expr) => {
                let idx = self.resolve_int(idx_expr)?;
                self.resolve_array_access(name, idx)
            }
            _ => Err(TranslateError::UnsupportedType(format!("{expr:?}"))),
        }
    }

    /// Convert an array expression to a vector of SMT term strings.
    pub(crate) fn expr_to_smt_array(&self, expr: &Expr) -> Result<Vec<String>, TranslateError> {
        self.expr_to_smt_indexed_array(expr)
            .map(|(_, _, values)| values)
    }

    /// Convert an array expression while retaining its declared index range.
    /// Array literals have the FlatZinc builtin convention `1..len`.
    pub(crate) fn expr_to_smt_indexed_array(
        &self,
        expr: &Expr,
    ) -> Result<(i64, i64, Vec<String>), TranslateError> {
        match expr {
            Expr::ArrayLit(elems) => {
                let len = i64::try_from(elems.len()).map_err(|_| {
                    TranslateError::UnsupportedType(
                        "array literal is too large to index".to_string(),
                    )
                })?;
                let values = elems
                    .iter()
                    .map(|e| self.expr_to_smt(e))
                    .collect::<Result<_, _>>()?;
                Ok((1, len, values))
            }
            Expr::Ident(name) => {
                if let Some((lo, hi, values)) = self.array_params.get(name) {
                    return Ok((*lo, *hi, values.iter().map(ScalarValue::to_smt).collect()));
                }
                if let Some((lo, hi, _)) = self.array_vars.get(name) {
                    return Ok((
                        *lo,
                        *hi,
                        (*lo..=*hi).map(|i| format!("{name}_{i}")).collect(),
                    ));
                }
                Err(TranslateError::UnknownIdentifier(name.clone()))
            }
            _ => Err(TranslateError::ExpectedArray),
        }
    }

    /// Resolve an integer array expression to concrete i64 values.
    pub(crate) fn resolve_int_array(&self, expr: &Expr) -> Result<Vec<i64>, TranslateError> {
        match expr {
            Expr::ArrayLit(elems) => elems.iter().map(|e| self.resolve_int(e)).collect(),
            Expr::Ident(name) => {
                if let Some((_, _, values)) = self.array_params.get(name) {
                    values
                        .iter()
                        .map(|v| match v {
                            ScalarValue::Int(n) => Ok(*n),
                            _ => Err(TranslateError::ExpectedIntLiteral(format!("{v:?}"))),
                        })
                        .collect()
                } else {
                    Err(TranslateError::UnknownIdentifier(name.clone()))
                }
            }
            _ => Err(TranslateError::ExpectedArray),
        }
    }

    /// Resolve a set expression to a vector of integers.
    pub(crate) fn resolve_set(&self, expr: &Expr) -> Result<Vec<i64>, TranslateError> {
        match expr {
            Expr::SetLit(elems) => elems.iter().map(|e| self.resolve_int(e)).collect(),
            Expr::IntRange(lo, hi) => materialize_range(*lo, *hi, "set literal"),
            Expr::EmptySet => Ok(vec![]),
            Expr::Ident(name) => {
                if let Some(values) = self.set_params.get(name) {
                    Ok(values.clone())
                } else {
                    Err(TranslateError::UnknownIdentifier(name.clone()))
                }
            }
            _ => Err(TranslateError::UnsupportedType(format!("{expr:?}"))),
        }
    }

    pub(crate) fn resolve_int(&self, expr: &Expr) -> Result<i64, TranslateError> {
        match expr {
            Expr::Int(n) => Ok(*n),
            Expr::Ident(name) => {
                if let Some(ScalarValue::Int(n)) = self.scalar_params.get(name) {
                    Ok(*n)
                } else {
                    Err(TranslateError::ExpectedIntLiteral(name.clone()))
                }
            }
            _ => Err(TranslateError::ExpectedIntLiteral(format!("{expr:?}"))),
        }
    }

    fn resolve_ident(&self, name: &str) -> Result<String, TranslateError> {
        if let Some(val) = self.scalar_params.get(name) {
            return Ok(val.to_smt());
        }
        if let Some((smt_name, _)) = self.scalar_vars.get(name) {
            return Ok(smt_name.clone());
        }
        // Set variables are used directly by name in SMT-LIB
        if self.set_vars.contains_key(name) {
            return Ok(name.to_string());
        }
        Err(TranslateError::UnknownIdentifier(name.into()))
    }

    fn resolve_array_access(&self, name: &str, idx: i64) -> Result<String, TranslateError> {
        if let Some((lo, hi, values)) = self.array_params.get(name) {
            if idx >= *lo && idx <= *hi {
                let offset = usize::try_from(i128::from(idx) - i128::from(*lo)).map_err(|_| {
                    TranslateError::ArrayIndexOutOfBounds {
                        name: name.into(),
                        index: idx,
                    }
                })?;
                if let Some(value) = values.get(offset) {
                    return Ok(value.to_smt());
                }
            }
            return Err(TranslateError::ArrayIndexOutOfBounds {
                name: name.into(),
                index: idx,
            });
        }
        if let Some((lo, hi, _)) = self.array_vars.get(name) {
            if idx >= *lo && idx <= *hi {
                return Ok(format!("{name}_{idx}"));
            }
            return Err(TranslateError::ArrayIndexOutOfBounds {
                name: name.into(),
                index: idx,
            });
        }
        Err(TranslateError::UnknownIdentifier(name.into()))
    }

    pub(crate) fn resolve_scalar_value(&self, expr: &Expr) -> Result<ScalarValue, TranslateError> {
        match expr {
            Expr::Bool(b) => Ok(ScalarValue::Bool(*b)),
            Expr::Int(n) => Ok(ScalarValue::Int(*n)),
            Expr::Float(f) => Ok(ScalarValue::Float(*f)),
            Expr::Ident(name) => self
                .scalar_params
                .get(name)
                .cloned()
                .ok_or_else(|| TranslateError::UnknownIdentifier(name.clone())),
            _ => Err(TranslateError::ExpectedIntLiteral(format!("{expr:?}"))),
        }
    }

    pub(crate) fn resolve_array_values(
        &self,
        expr: &Expr,
    ) -> Result<Vec<ScalarValue>, TranslateError> {
        match expr {
            Expr::ArrayLit(elems) => elems.iter().map(|e| self.resolve_scalar_value(e)).collect(),
            Expr::Ident(name) => self
                .array_params
                .get(name)
                .map(|(_, _, v)| v.clone())
                .ok_or_else(|| TranslateError::UnknownIdentifier(name.clone())),
            _ => Err(TranslateError::ExpectedArray),
        }
    }

    /// Resolve an array of set literals (for array-of-set parameters).
    pub(crate) fn resolve_array_of_sets(
        &self,
        expr: &Expr,
    ) -> Result<Vec<Vec<i64>>, TranslateError> {
        match expr {
            Expr::ArrayLit(elems) => elems.iter().map(|e| self.resolve_set_literal(e)).collect(),
            _ => Err(TranslateError::ExpectedArray),
        }
    }

    pub(crate) fn resolve_set_literal(&self, expr: &Expr) -> Result<Vec<i64>, TranslateError> {
        match expr {
            Expr::SetLit(elems) => elems.iter().map(|e| self.resolve_int(e)).collect(),
            Expr::IntRange(lo, hi) => materialize_range(*lo, *hi, "set literal"),
            Expr::EmptySet => Ok(vec![]),
            _ => Err(TranslateError::UnsupportedType(format!("{expr:?}"))),
        }
    }
}

fn materialize_range(lo: i64, hi: i64, context: &str) -> Result<Vec<i64>, TranslateError> {
    let len = materialized_range_len(lo, hi, context)?;
    let mut values = Vec::with_capacity(len);
    for offset in 0..len {
        let offset = i64::try_from(offset).map_err(|_| {
            TranslateError::UnsupportedType(format!("{context} range is too large"))
        })?;
        values.push(lo.checked_add(offset).ok_or_else(|| {
            TranslateError::UnsupportedType(format!("{context} range overflows i64"))
        })?);
    }
    Ok(values)
}
