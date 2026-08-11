// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

/// The kind of a term, matching Z3's `Z3_ast_kind` classification.
///
/// Deprecated: Use [`TermKind`](super::super::introspect::TermKind) instead, which
/// provides richer metadata (operator names, argument counts).
#[deprecated(
    since = "0.2.0",
    note = "Use TermKind instead — it provides richer metadata"
)]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[non_exhaustive]
pub enum AstKind {
    /// A numeric/bitvec/boolean/string constant
    Numeral,
    /// A function application (including built-in operators)
    App,
    /// A bound variable (de Bruijn or named)
    Var,
    /// A quantifier (forall or exists)
    Quantifier,
    /// Unknown / unsupported kind
    Unknown,
}

impl Solver {
    /// Get the sort of a term.
    ///
    /// Deprecated: Use [`term_sort`](Self::term_sort) instead (has `#[must_use]`).
    #[allow(clippy::panic)]
    pub fn get_sort(&self, t: Term) -> Sort {
        let id = self
            .resolve_term("get_sort", t)
            .unwrap_or_else(|error| panic!("{error}"));
        self.terms().sort(id).clone()
    }

    /// Classify a term into its AST kind.
    ///
    /// Deprecated: Use [`term_kind`](Self::term_kind) instead — it returns
    /// [`TermKind`](super::super::introspect::TermKind) with richer metadata.
    #[allow(deprecated)]
    pub fn get_ast_kind(&self, t: Term) -> AstKind {
        let Ok(id) = self.resolve_term("get_ast_kind", t) else {
            return AstKind::Unknown;
        };
        match self.terms().get(id) {
            TermData::Const(_) => AstKind::Numeral,
            TermData::App(_, _) | TermData::Not(_) | TermData::Ite(_, _, _) => AstKind::App,
            TermData::Var(_, _) => AstKind::Var,
            TermData::Forall(..) | TermData::Exists(..) => AstKind::Quantifier,
            TermData::Let(_, _) => AstKind::Unknown,
            other => unreachable!("unhandled TermData variant in get_ast_kind(): {other:?}"),
        }
    }

    /// Return true if the term is a numeral constant (integer, real, bitvec, boolean).
    #[must_use]
    pub fn is_numeral(&self, t: Term) -> bool {
        self.resolve_term("is_numeral", t)
            .is_ok_and(|id| matches!(self.terms().get(id), TermData::Const(_)))
    }

    /// Return true if the term is an application (function, operator, Not, ITE).
    #[must_use]
    pub fn is_app(&self, t: Term) -> bool {
        self.resolve_term("is_app", t).is_ok_and(|id| {
            matches!(
                self.terms().get(id),
                TermData::App(_, _) | TermData::Not(_) | TermData::Ite(_, _, _)
            )
        })
    }

    /// Get the number of arguments of an application term.
    /// Returns 0 for non-application terms.
    #[must_use]
    pub fn app_num_args(&self, t: Term) -> usize {
        let Ok(id) = self.resolve_term("app_num_args", t) else {
            return 0;
        };
        match self.terms().get(id) {
            TermData::App(_, args) => args.len(),
            TermData::Not(_) => 1,
            TermData::Ite(_, _, _) => 3,
            _ => 0,
        }
    }

    /// Get the i-th argument of an application term.
    /// Returns None if the term is not an application or if the index is out of bounds.
    #[must_use]
    pub fn app_arg(&self, t: Term, i: usize) -> Option<Term> {
        let id = self.resolve_term("app_arg", t).ok()?;
        let child = match self.terms().get(id) {
            TermData::App(_, args) => args.get(i).copied(),
            TermData::Not(inner) if i == 0 => Some(*inner),
            TermData::Ite(c, th, el) => match i {
                0 => Some(*c),
                1 => Some(*th),
                2 => Some(*el),
                _ => None,
            },
            _ => None,
        }?;
        Some(self.wrap_term(child))
    }

    /// Get the function symbol name for an application term.
    /// Returns None for non-application terms.
    #[must_use]
    pub fn app_symbol_name(&self, t: Term) -> Option<String> {
        let id = self.resolve_term("app_symbol_name", t).ok()?;
        match self.terms().get(id) {
            TermData::App(sym, _) => Some(sym.to_string()),
            TermData::Not(_) => Some("not".to_string()),
            TermData::Ite(_, _, _) => Some("ite".to_string()),
            _ => None,
        }
    }

    /// Boolean value of a constant term.
    /// Returns None if the term is not a boolean constant.
    #[must_use]
    pub fn bool_value(&self, t: Term) -> Option<bool> {
        let id = self.resolve_term("bool_value", t).ok()?;
        match self.terms().get(id) {
            TermData::Const(ay_core::term::Constant::Bool(b)) => Some(*b),
            _ => None,
        }
    }

    /// Numeral string representation of a constant term.
    /// Returns None if the term is not a numeral constant.
    #[must_use]
    pub fn numeral_string(&self, t: Term) -> Option<String> {
        let id = self.resolve_term("numeral_string", t).ok()?;
        match self.terms().get(id) {
            TermData::Const(c) => match c {
                ay_core::term::Constant::Int(n) => Some(n.to_string()),
                ay_core::term::Constant::Rational(r) => {
                    Some(format!("{}/{}", r.0.numer(), r.0.denom()))
                }
                ay_core::term::Constant::BitVec { value, .. } => Some(value.to_string()),
                ay_core::term::Constant::Bool(b) => Some(b.to_string()),
                ay_core::term::Constant::String(s) => Some(s.clone()),
                other => {
                    unreachable!("unhandled Constant variant in numeral_string(): {other:?}")
                }
            },
            _ => None,
        }
    }

    /// Name of a declared variable term.
    /// Returns the registered name from `var_names`, or the TermData name for Var terms.
    #[must_use]
    pub fn var_name(&self, t: Term) -> Option<String> {
        let id = self.resolve_term("var_name", t).ok()?;
        if let Some(name) = self.var_names.get(&id) {
            return Some(name.clone());
        }
        match self.terms().get(id) {
            TermData::Var(name, _) => Some(name.clone()),
            _ => None,
        }
    }

    /// Sort of a declared variable (from the var_sorts registry).
    #[must_use]
    pub fn var_sort(&self, t: Term) -> Option<&Sort> {
        let id = self.resolve_term("var_sort", t).ok()?;
        self.var_sorts.get(&id)
    }

    /// Return the number of declared variables (constants) in the solver.
    #[must_use]
    pub fn num_declared_vars(&self) -> usize {
        self.var_names.len()
    }

    /// Iterate over all declared variable names and their terms, in arbitrary order.
    ///
    /// Deprecated: Use [`declared_variables`](Self::declared_variables) instead —
    /// it returns variables sorted by TermId for deterministic ordering.
    pub fn declared_vars(&self) -> impl Iterator<Item = (&str, Term)> + '_ {
        self.var_names
            .iter()
            .map(|(id, name)| (name.as_str(), self.wrap_term(*id)))
    }
}
