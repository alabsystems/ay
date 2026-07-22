// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! SMT-LIB term and constant types with S-expression parsing.

use crate::sexp::{ParseError, SExpr, PARSE_STACK_RED_ZONE, PARSE_STACK_SIZE};

use super::Sort;

/// A token used as an SMT-LIB indexed-identifier index.
///
/// Token kind is semantic here: the numeral `8` and the quoted symbol `|8|`
/// are distinct indices and must not collapse to the same string.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub enum Index {
    /// A decimal numeral token.
    Numeral(String),
    /// A symbol token, including a quoted symbol.
    Symbol(String),
    /// A hexadecimal bitvector token such as `#x41`.
    Hexadecimal(String),
    /// A binary bitvector token such as `#b0100_0001`.
    Binary(String),
}

impl Index {
    pub(super) fn from_sexp(sexp: &SExpr) -> Option<Self> {
        match sexp {
            SExpr::Numeral(value) => Some(Self::Numeral(value.clone())),
            SExpr::Symbol(value) => Some(Self::Symbol(value.clone())),
            SExpr::Hexadecimal(value) => Some(Self::Hexadecimal(value.clone())),
            SExpr::Binary(value) => Some(Self::Binary(value.clone())),
            _ => None,
        }
    }

    /// Return the token text without changing its token kind.
    pub fn text(&self) -> &str {
        match self {
            Self::Numeral(value)
            | Self::Symbol(value)
            | Self::Hexadecimal(value)
            | Self::Binary(value) => value,
        }
    }

    /// Return the decimal text only when this is a numeral token.
    pub fn as_numeral(&self) -> Option<&str> {
        match self {
            Self::Numeral(value) => Some(value),
            _ => None,
        }
    }

    /// Return the identifier text only when this is a symbol token.
    pub fn as_symbol(&self) -> Option<&str> {
        match self {
            Self::Symbol(value) => Some(value),
            _ => None,
        }
    }
}

/// Identifier carried by an SMT-LIB `(as <identifier> <sort>)` qualification.
///
/// A simple symbol and an indexed identifier have distinct structure even
/// when the symbol's quoted spelling resembles the indexed form.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub enum QualifiedIdentifier {
    /// A simple or quoted symbol.
    Symbol(String),
    /// An indexed identifier `(_ name index+)`.
    Indexed(String, Vec<Index>),
}

impl QualifiedIdentifier {
    fn from_sexp(sexp: &SExpr) -> Result<Self, ParseError> {
        match sexp {
            SExpr::Symbol(name) => Ok(Self::Symbol(name.clone())),
            SExpr::List(items)
                if items.len() >= 3 && items.first().is_some_and(|head| head.is_symbol("_")) =>
            {
                let name = items[1]
                    .as_symbol()
                    .ok_or_else(|| ParseError::new("indexed identifier name must be symbol"))?;
                let indices = items[2..]
                    .iter()
                    .map(|index| {
                        Index::from_sexp(index).ok_or_else(|| {
                            ParseError::new("qualified indexed identifier has an invalid index")
                        })
                    })
                    .collect::<Result<Vec<_>, _>>()?;
                Ok(Self::Indexed(name.to_string(), indices))
            }
            _ => Err(ParseError::new(
                "qualified identifier must be a symbol or indexed identifier",
            )),
        }
    }

    /// Return the identifier only when this is a simple or quoted symbol.
    pub fn as_symbol(&self) -> Option<&str> {
        match self {
            Self::Symbol(name) => Some(name),
            Self::Indexed(_, _) => None,
        }
    }
}

/// An SMT-LIB term
#[derive(Debug, Clone, PartialEq)]
#[non_exhaustive]
pub enum Term {
    /// A constant: true, false
    Const(Constant),
    /// A variable or uninterpreted constant
    Symbol(String),
    /// Function application: (f arg1 arg2 ...)
    App(String, Vec<Self>),
    /// Indexed identifier or function application:
    /// `(_ name idx1 idx2 ...)` or `((_ name idx1 idx2 ...) arg1 arg2 ...)`.
    /// Carries the name and indices as structured data instead of
    /// stringifying `(_ extract 7 0)` into `App("(_ extract 7 0)", args)`.
    IndexedApp(String, Vec<Index>, Vec<Self>),
    /// Qualified function application: ((as \<id\> \<sort\>) arg1 arg2 ...)
    /// Carries the identifier name and sort annotation as structured data,
    /// avoiding the stringify-then-reparse anti-pattern of encoding the
    /// entire `(as ...)` expression as a string in `App`.
    QualifiedApp(QualifiedIdentifier, Sort, Vec<Self>),
    /// Let binding: (let ((x e1) (y e2)) body)
    Let(Vec<(String, Self)>, Box<Self>),
    /// Quantifier: (forall ((x Int)) body)
    Forall(Vec<(String, Sort)>, Box<Self>),
    /// Quantifier: (exists ((x Int)) body)
    Exists(Vec<(String, Sort)>, Box<Self>),
    /// Lambda array: (lambda ((x Int)) body)
    /// Creates an array where index i maps to body[x/i].
    /// Z3 extension for quantified array logics (AUFLIA, etc.).
    Lambda(Vec<(String, Sort)>, Box<Self>),
    /// Annotated term: (! term :named foo)
    Annotated(Box<Self>, Vec<(String, SExpr)>),
    /// Match expression: (match \<scrutinee\> ((\<pattern\> \<body\>)+))
    ///
    /// SMT-LIB 2.6 algebraic-datatype case analysis. Each case pairs a
    /// [`MatchPattern`] with a body term. The scrutinee and bodies are ordinary
    /// terms; the pattern is NOT — its head is a constructor (or a binder),
    /// never an applied function — so it is carried as structured data rather
    /// than a `Term`. Desugared to nested `ite` + tester + selector in the
    /// elaborator, where datatype metadata is available.
    Match(Box<Self>, Vec<(MatchPattern, Self)>),
}

/// A single `match` case pattern (SMT-LIB 2.6 Section 3.6.3).
///
/// Whether a bare [`Self::Symbol`] is a nullary constructor versus a
/// variable/wildcard binder requires the datatype's constructor metadata and is
/// therefore deferred to the elaborator; the parser records only the surface
/// shape.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub enum MatchPattern {
    /// A bare symbol: a nullary constructor, a variable binder, or the wildcard
    /// `_`. Disambiguated during elaboration against the scrutinee's datatype.
    Symbol(String),
    /// A constructor pattern `(C x1 ... xn)` binding each `x_i` to the i-th
    /// field (selector) of `C`. A field binder of `_` is an unbound wildcard.
    Constructor(String, Vec<String>),
}

/// Iterative drop to prevent stack overflow on deeply nested terms.
/// Same rationale as `SExpr::Drop` — recursive Drop on 1000+-deep
/// `App("not", vec![App("not", vec![...])])` would overflow the thread stack.
impl Drop for Term {
    fn drop(&mut self) {
        let mut stack = Vec::new();
        self.drain_children_into(&mut stack);
        while let Some(mut item) = stack.pop() {
            item.drain_children_into(&mut stack);
            // `item` now contains no nested Terms; drops trivially.
        }
    }
}

impl Term {
    /// Move all child `Term` values out of `self` into `dst`, leaving `self`
    /// in a state that can be dropped without recursion.
    fn drain_children_into(&mut self, dst: &mut Vec<Self>) {
        match self {
            Self::App(_, args) | Self::IndexedApp(_, _, args) | Self::QualifiedApp(_, _, args) => {
                dst.append(args)
            }
            Self::Let(bindings, body) => {
                for (_, term) in bindings.drain(..) {
                    dst.push(term);
                }
                // Replace Box<Term> content with a trivial variant
                let inner = std::mem::replace(body.as_mut(), Self::Const(Constant::True));
                dst.push(inner);
            }
            Self::Forall(_, body) | Self::Exists(_, body) | Self::Lambda(_, body) => {
                let inner = std::mem::replace(body.as_mut(), Self::Const(Constant::True));
                dst.push(inner);
            }
            Self::Annotated(body, _) => {
                let inner = std::mem::replace(body.as_mut(), Self::Const(Constant::True));
                dst.push(inner);
            }
            Self::Match(scrutinee, cases) => {
                let inner = std::mem::replace(scrutinee.as_mut(), Self::Const(Constant::True));
                dst.push(inner);
                for (_, body) in cases.drain(..) {
                    dst.push(body);
                }
            }
            Self::Const(_) | Self::Symbol(_) => {}
        }
    }
}

/// An SMT-LIB parsed constant token.
///
/// This is the parser-level, string-preserving representation used by
/// [`Term`]. It is intentionally separate from the native semantic
/// [`ay_core::Constant`] used by solver terms.
///
/// Prefer the [`ParsedConstant`] alias when importing both frontend and native
/// constant types in the same module.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub enum Constant {
    /// Boolean true
    True,
    /// Boolean false
    False,
    /// Numeral
    Numeral(String),
    /// Decimal
    Decimal(String),
    /// Hexadecimal bitvector
    Hexadecimal(String),
    /// Binary bitvector
    Binary(String),
    /// String literal
    String(String),
}

/// Compatibility alias for [`Constant`] that makes the parser/native
/// distinction explicit at import sites.
///
/// `ParsedConstant` and [`Constant`] are the same type. The alias avoids local
/// import collisions with native solver constants such as [`ay_core::Constant`]
/// without breaking existing `ay_frontend::Constant` users.
pub type ParsedConstant = Constant;

impl Term {
    /// Parse a term from an S-expression.
    /// Uses `stacker::maybe_grow` for stack safety on deeply nested terms (#4602).
    pub fn from_sexp(sexp: &SExpr) -> Result<Self, ParseError> {
        stacker::maybe_grow(PARSE_STACK_RED_ZONE, PARSE_STACK_SIZE, || match sexp {
            SExpr::True => Ok(Self::Const(Constant::True)),
            SExpr::False => Ok(Self::Const(Constant::False)),
            SExpr::Numeral(n) => Ok(Self::Const(Constant::Numeral(n.clone()))),
            SExpr::Decimal(d) => Ok(Self::Const(Constant::Decimal(d.clone()))),
            SExpr::Hexadecimal(h) => Ok(Self::Const(Constant::Hexadecimal(h.clone()))),
            SExpr::Binary(b) => Ok(Self::Const(Constant::Binary(b.clone()))),
            SExpr::String(s) => Ok(Self::Const(Constant::String(s.clone()))),
            SExpr::Symbol(s) => Ok(Self::Symbol(s.clone())),
            SExpr::Keyword(_) => Err(ParseError::new("Unexpected keyword in term")),
            SExpr::List(items) if items.is_empty() => {
                Err(ParseError::new("Empty list is not a valid term"))
            }
            SExpr::List(items) => {
                if let Some(head) = items[0].as_symbol() {
                    match head {
                        "let" => Self::parse_let(items),
                        "forall" => Self::parse_quantifier(items, true),
                        "exists" => Self::parse_quantifier(items, false),
                        "lambda" => Self::parse_lambda(items),
                        "match" => Self::parse_match(items),
                        "!" => Self::parse_annotated(items),
                        "_" => Self::parse_indexed_identifier(items),
                        // SMT-LIB qualified identifier: (as <id> <sort>)
                        // Carries the identifier and sort as structured data.
                        // <id> can be a symbol or an indexed identifier (_ sym idx...).
                        "as" if items.len() == 3 => {
                            let id = QualifiedIdentifier::from_sexp(&items[1])?;
                            let sort = Sort::from_sexp(&items[2])?;
                            Ok(Self::QualifiedApp(id, sort, vec![]))
                        }
                        _ => Self::parse_application(items),
                    }
                } else if let SExpr::List(_) = &items[0] {
                    Self::parse_application(items)
                } else {
                    Err(ParseError::new(format!("Invalid term head: {}", items[0])))
                }
            }
        })
    }

    fn parse_let(items: &[SExpr]) -> Result<Self, ParseError> {
        if items.len() != 3 {
            return Err(ParseError::new("let requires bindings and body"));
        }
        let bindings_sexp = items[1]
            .as_list()
            .ok_or_else(|| ParseError::new("let bindings must be a list"))?;

        let mut bindings = Vec::new();
        for binding in bindings_sexp {
            let binding_list = binding
                .as_list()
                .ok_or_else(|| ParseError::new("let binding must be a list"))?;
            if binding_list.len() != 2 {
                return Err(ParseError::new("let binding must have name and value"));
            }
            let name = binding_list[0]
                .as_symbol()
                .ok_or_else(|| ParseError::new("let binding name must be a symbol"))?;
            let value = Self::from_sexp(&binding_list[1])?;
            bindings.push((name.to_string(), value));
        }

        let body = Self::from_sexp(&items[2])?;
        Ok(Self::Let(bindings, Box::new(body)))
    }

    fn parse_quantifier(items: &[SExpr], is_forall: bool) -> Result<Self, ParseError> {
        if items.len() != 3 {
            return Err(ParseError::new("quantifier requires bindings and body"));
        }
        let bindings_sexp = items[1]
            .as_list()
            .ok_or_else(|| ParseError::new("quantifier bindings must be a list"))?;

        let mut bindings = Vec::new();
        for binding in bindings_sexp {
            let binding_list = binding
                .as_list()
                .ok_or_else(|| ParseError::new("quantifier binding must be a list"))?;
            if binding_list.len() != 2 {
                return Err(ParseError::new(
                    "quantifier binding must have name and sort",
                ));
            }
            let name = binding_list[0]
                .as_symbol()
                .ok_or_else(|| ParseError::new("quantifier binding name must be a symbol"))?;
            let sort = Sort::from_sexp(&binding_list[1])?;
            bindings.push((name.to_string(), sort));
        }

        let body = Self::from_sexp(&items[2])?;
        if is_forall {
            Ok(Self::Forall(bindings, Box::new(body)))
        } else {
            Ok(Self::Exists(bindings, Box::new(body)))
        }
    }

    /// Parse a lambda array term: (lambda ((x Int)) body)
    /// Same binding structure as quantifiers.
    fn parse_lambda(items: &[SExpr]) -> Result<Self, ParseError> {
        if items.len() != 3 {
            return Err(ParseError::new("lambda requires bindings and body"));
        }
        let bindings_sexp = items[1]
            .as_list()
            .ok_or_else(|| ParseError::new("lambda bindings must be a list"))?;

        let mut bindings = Vec::new();
        for binding in bindings_sexp {
            let binding_list = binding
                .as_list()
                .ok_or_else(|| ParseError::new("lambda binding must be a list"))?;
            if binding_list.len() != 2 {
                return Err(ParseError::new("lambda binding must have name and sort"));
            }
            let name = binding_list[0]
                .as_symbol()
                .ok_or_else(|| ParseError::new("lambda binding name must be a symbol"))?;
            let sort = Sort::from_sexp(&binding_list[1])?;
            bindings.push((name.to_string(), sort));
        }

        let body = Self::from_sexp(&items[2])?;
        Ok(Self::Lambda(bindings, Box::new(body)))
    }

    /// Parse a match term: (match \<scrutinee\> ((\<pattern\> \<body\>)+))
    ///
    /// The cases are NOT ordinary function arguments — each case is a
    /// `(pattern body)` pair whose pattern head is a constructor or binder — so
    /// `match` cannot flow through [`Self::parse_application`] and must be parsed
    /// explicitly.
    fn parse_match(items: &[SExpr]) -> Result<Self, ParseError> {
        if items.len() != 3 {
            return Err(ParseError::new(
                "match requires a scrutinee and a list of cases",
            ));
        }
        let scrutinee = Self::from_sexp(&items[1])?;
        let cases_sexp = items[2]
            .as_list()
            .ok_or_else(|| ParseError::new("match cases must be a list"))?;
        if cases_sexp.is_empty() {
            return Err(ParseError::new("match requires at least one case"));
        }

        let mut cases = Vec::with_capacity(cases_sexp.len());
        for case in cases_sexp {
            let case_list = case
                .as_list()
                .ok_or_else(|| ParseError::new("match case must be a (pattern body) list"))?;
            if case_list.len() != 2 {
                return Err(ParseError::new("match case must have a pattern and a body"));
            }
            let pattern = Self::parse_match_pattern(&case_list[0])?;
            let body = Self::from_sexp(&case_list[1])?;
            cases.push((pattern, body));
        }

        Ok(Self::Match(Box::new(scrutinee), cases))
    }

    fn parse_match_pattern(sexp: &SExpr) -> Result<MatchPattern, ParseError> {
        match sexp {
            SExpr::Symbol(symbol) => Ok(MatchPattern::Symbol(symbol.clone())),
            SExpr::List(items) if !items.is_empty() => {
                let ctor = items[0]
                    .as_symbol()
                    .ok_or_else(|| {
                        ParseError::new("match constructor pattern head must be a symbol")
                    })?
                    .to_string();
                let vars = items[1..]
                    .iter()
                    .map(|s| {
                        s.as_symbol().map(str::to_string).ok_or_else(|| {
                            ParseError::new("match pattern field binders must be symbols")
                        })
                    })
                    .collect::<Result<Vec<_>, _>>()?;
                Ok(MatchPattern::Constructor(ctor, vars))
            }
            _ => Err(ParseError::new("invalid match pattern")),
        }
    }

    fn parse_annotated(items: &[SExpr]) -> Result<Self, ParseError> {
        if items.len() < 2 {
            return Err(ParseError::new("annotation requires term"));
        }
        let term = Self::from_sexp(&items[1])?;

        let mut annotations = Vec::new();
        let mut i = 2;
        while i < items.len() {
            if let SExpr::Keyword(k) = &items[i] {
                if i + 1 < items.len() {
                    annotations.push((k.clone(), items[i + 1].clone()));
                    i += 2;
                } else {
                    return Err(ParseError::new("annotation keyword requires value"));
                }
            } else {
                return Err(ParseError::new("expected keyword in annotation"));
            }
        }

        Ok(Self::Annotated(Box::new(term), annotations))
    }

    fn parse_indexed_identifier(items: &[SExpr]) -> Result<Self, ParseError> {
        // (_ symbol index+) - indexed identifier as a term
        if items.len() < 3 {
            return Err(ParseError::new(
                "indexed identifier requires a name and at least one index",
            ));
        }
        let name = items[1]
            .as_symbol()
            .ok_or_else(|| ParseError::new("indexed identifier name must be symbol"))?;

        let indices: Vec<Index> = items[2..]
            .iter()
            .map(|sexp| {
                Index::from_sexp(sexp)
                    .ok_or_else(|| ParseError::new("indexed identifier has an invalid index"))
            })
            .collect::<Result<_, _>>()?;

        // Keep the indexed origin structural. Stringifying this as a `Symbol`
        // aliases it with a legal quoted symbol having the same spelling.
        Ok(Self::IndexedApp(name.to_string(), indices, Vec::new()))
    }

    fn parse_application(items: &[SExpr]) -> Result<Self, ParseError> {
        if items.is_empty() {
            return Err(ParseError::new("empty application"));
        }

        // Handle indexed function names like (_ extract 7 0)
        let (func_name, args_start) = if let SExpr::List(head_items) = &items[0] {
            if items.len() == 1 {
                return Err(ParseError::new(
                    "qualified or indexed application requires at least one argument",
                ));
            }
            if !head_items.is_empty() && head_items[0].is_symbol("_") {
                if head_items.len() < 3 {
                    return Err(ParseError::new(
                        "indexed application requires a name and at least one index",
                    ));
                }
                // Indexed function: produce IndexedApp directly
                let name = head_items
                    .get(1)
                    .and_then(|s| s.as_symbol())
                    .ok_or_else(|| ParseError::new("indexed identifier name must be symbol"))?
                    .to_string();
                let indices: Vec<Index> = head_items[2..]
                    .iter()
                    .map(|sexp| {
                        Index::from_sexp(sexp).ok_or_else(|| {
                            ParseError::new("indexed application has an invalid index")
                        })
                    })
                    .collect::<Result<_, _>>()?;
                let args: Result<Vec<_>, _> = items[1..].iter().map(Self::from_sexp).collect();
                return Ok(Self::IndexedApp(name, indices, args?));
            } else if !head_items.is_empty() && head_items[0].is_symbol("as") {
                // Qualified application head: ((as <id> <sort>) args...)
                // Parse as structured QualifiedApp instead of stringifying.
                if head_items.len() != 3 {
                    return Err(ParseError::new(
                        "qualified identifier requires (as <id> <sort>)",
                    ));
                }
                let id = QualifiedIdentifier::from_sexp(&head_items[1])?;
                let sort = Sort::from_sexp(&head_items[2])?;
                let args: Result<Vec<_>, _> = items[1..].iter().map(Self::from_sexp).collect();
                return Ok(Self::QualifiedApp(id, sort, args?));
            } else {
                return Err(ParseError::new("invalid function in application"));
            }
        } else {
            let name = items[0]
                .as_symbol()
                .ok_or_else(|| ParseError::new("function name must be symbol"))?
                .to_string();
            (name, 1)
        };

        let args: Result<Vec<_>, _> = items[args_start..].iter().map(Self::from_sexp).collect();

        Ok(Self::App(func_name, args?))
    }
}
