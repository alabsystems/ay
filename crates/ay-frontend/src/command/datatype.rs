// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! SMT-LIB datatype declaration types and parsing.

use crate::sexp::{ParseError, SExpr};

use super::Sort;

/// A selector declaration in a datatype constructor: (name, sort)
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SelectorDec {
    /// The selector name (accessor function)
    pub name: String,
    /// The sort of the field
    pub sort: Sort,
}

/// A constructor declaration in a datatype: (name, selectors)
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ConstructorDec {
    /// The constructor name
    pub name: String,
    /// The selectors (fields) of this constructor
    pub selectors: Vec<SelectorDec>,
}

/// A datatype declaration: list of constructors.
///
/// For a parametric (polymorphic) datatype `(par (T1 ... Tn) (ctor+))`,
/// [`DatatypeDec::type_params`] holds the bound type-parameter names and the
/// selector sorts inside `constructors` may reference them (as bare symbols
/// `T` or applied sorts `(List T)`). For a monomorphic datatype `type_params`
/// is empty.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DatatypeDec {
    /// The constructors for this datatype
    pub constructors: Vec<ConstructorDec>,
    /// The bound type-parameter names for a parametric datatype (empty when
    /// the datatype is monomorphic).
    pub type_params: Vec<String>,
}

/// A sort declaration for declare-datatypes: (name, arity)
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SortDec {
    /// The sort name
    pub name: String,
    /// The arity (0 for non-parametric sorts)
    pub arity: u32,
}

impl SelectorDec {
    /// Parse a selector declaration: (name sort)
    pub(crate) fn from_sexp(sexp: &SExpr) -> Result<Self, ParseError> {
        let items = sexp
            .as_list()
            .ok_or_else(|| ParseError::new("selector must be a list"))?;
        if items.len() != 2 {
            return Err(ParseError::new("selector must be (name sort)"));
        }
        let name = items[0]
            .as_symbol()
            .ok_or_else(|| ParseError::new("selector name must be symbol"))?;
        let sort = Sort::from_sexp(&items[1])?;
        Ok(Self {
            name: name.to_string(),
            sort,
        })
    }
}

impl ConstructorDec {
    /// Parse a constructor declaration: `(name selector*)`, or a bare symbol
    /// `name` as shorthand for a nullary constructor `(name)`. z3 accepts the
    /// bare-symbol form in both `declare-datatype`/`declare-datatypes` (e.g.
    /// `(declare-datatype Color (red green blue))`), so AY does too.
    pub(crate) fn from_sexp(sexp: &SExpr) -> Result<Self, ParseError> {
        if let Some(name) = sexp.as_symbol() {
            return Ok(Self {
                name: name.to_string(),
                selectors: Vec::new(),
            });
        }
        let items = sexp
            .as_list()
            .ok_or_else(|| ParseError::new("constructor must be a list"))?;
        if items.is_empty() {
            return Err(ParseError::new("constructor requires name"));
        }
        let name = items[0]
            .as_symbol()
            .ok_or_else(|| ParseError::new("constructor name must be symbol"))?;
        let selectors: Result<Vec<_>, _> = items[1..].iter().map(SelectorDec::from_sexp).collect();
        Ok(Self {
            name: name.to_string(),
            selectors: selectors?,
        })
    }
}

impl DatatypeDec {
    /// Parse a datatype declaration: (constructor+) or (par (...) (constructor+))
    pub(crate) fn from_sexp(sexp: &SExpr) -> Result<Self, ParseError> {
        let items = sexp
            .as_list()
            .ok_or_else(|| ParseError::new("datatype declaration must be a list"))?;
        if items.is_empty() {
            return Err(ParseError::new(
                "datatype requires at least one constructor",
            ));
        }

        // Parametric datatype: (par (T1 ... Tn) (constructor+)).
        if items[0].is_symbol("par") {
            if items.len() != 3 {
                return Err(ParseError::new(
                    "parametric datatype must be (par (<symbol>+) (<constructor>+))",
                ));
            }
            let param_list = items[1]
                .as_list()
                .ok_or_else(|| ParseError::new("par requires a list of type parameters"))?;
            if param_list.is_empty() {
                return Err(ParseError::new("par requires at least one type parameter"));
            }
            let type_params: Result<Vec<_>, _> = param_list
                .iter()
                .map(|p| {
                    p.as_symbol()
                        .map(str::to_string)
                        .ok_or_else(|| ParseError::new("type parameter must be a symbol"))
                })
                .collect();
            let ctor_list = items[2]
                .as_list()
                .ok_or_else(|| ParseError::new("par requires a list of constructors"))?;
            if ctor_list.is_empty() {
                return Err(ParseError::new(
                    "parametric datatype requires at least one constructor",
                ));
            }
            let constructors: Result<Vec<_>, _> =
                ctor_list.iter().map(ConstructorDec::from_sexp).collect();
            return Ok(Self {
                constructors: constructors?,
                type_params: type_params?,
            });
        }

        // Non-parametric: list of constructors
        let constructors: Result<Vec<_>, _> = items.iter().map(ConstructorDec::from_sexp).collect();
        Ok(Self {
            constructors: constructors?,
            type_params: Vec::new(),
        })
    }
}

impl SortDec {
    /// Parse a sort declaration: (name arity)
    pub(crate) fn from_sexp(sexp: &SExpr) -> Result<Self, ParseError> {
        let items = sexp
            .as_list()
            .ok_or_else(|| ParseError::new("sort declaration must be a list"))?;
        if items.len() != 2 {
            return Err(ParseError::new("sort declaration must be (name arity)"));
        }
        let name = items[0]
            .as_symbol()
            .ok_or_else(|| ParseError::new("sort name must be symbol"))?;
        let arity = items[1]
            .as_numeral()
            .and_then(|n| n.parse::<u32>().ok())
            .ok_or_else(|| ParseError::new("sort arity must be numeral"))?;
        Ok(Self {
            name: name.to_string(),
            arity,
        })
    }
}
