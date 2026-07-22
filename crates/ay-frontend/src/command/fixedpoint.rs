// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Z3 fixedpoint (relational / CHC) commands.
//!
//! Z3 exposes its fixedpoint (CHC) engine through four SMT-LIB commands:
//!
//! ```text
//! (declare-rel p (Int))              ; a Bool-valued relation p : Int -> Bool
//! (declare-var x Int)                ; a universally-quantified rule variable
//! (rule (=> (= x 0) (p x)))          ; a Horn implication body => head over rels
//! (query (p 5))                      ; check reachability of a rel application
//! ```
//!
//! These are parsed into [`Command`] variants here. `declare-var` reuses the
//! existing [`Command::DeclareVar`] variant (a SyGuS/fixedpoint universally
//! quantified variable). The full rule set is translated and discharged by the
//! existing `ay-chc` engine — see the `chc_runner` routing in the `ay` crate.
//!
//! ## sat/unsat polarity
//!
//! Per z3 fixedpoint conventions (and z3's muZ implementation), `(query R)`
//! reports:
//!
//! - `sat`   — the query relation IS reachable (the safety property does NOT
//!   hold; a derivation exists). This corresponds to the CHC system being
//!   UNSAFE.
//! - `unsat` — the query relation is unreachable (the safety property holds;
//!   no derivation exists). This corresponds to the CHC system being SAFE.
//!
//! This is the OPPOSITE polarity of the plain HORN/CHC-COMP convention, and is
//! handled by `ChcProblem::is_fixedpoint_format()` in the runner. The frontend
//! only parses; it does not decide.

use super::{Command, Sort, Term};
use crate::sexp::{ParseError, SExpr};

impl Command {
    /// Parse `(declare-rel <name> (<sort>*))`.
    ///
    /// Declares a Bool-valued relation (predicate). Unlike `declare-fun`, the
    /// return sort is implicitly `Bool` and is not written.
    pub(super) fn parse_declare_rel(items: &[SExpr]) -> Result<Self, ParseError> {
        if items.len() != 3 {
            return Err(ParseError::new(
                "declare-rel requires a name and an argument-sort list",
            ));
        }
        let name = items[1]
            .as_symbol()
            .ok_or_else(|| ParseError::new("declare-rel requires a symbol name"))?;
        let arg_list = items[2]
            .as_list()
            .ok_or_else(|| ParseError::new("declare-rel requires an argument-sort list"))?;
        let arg_sorts: Result<Vec<_>, _> = arg_list.iter().map(Sort::from_sexp).collect();
        Ok(Self::DeclareRel(name.to_string(), arg_sorts?))
    }

    /// Parse `(rule <horn-clause>)`.
    ///
    /// The body is an arbitrary SMT-LIB term, typically a Horn implication
    /// `(=> body head)` or a bare relation application `(p ...)` (an initiation
    /// fact). Variables appearing free are the previously `declare-var`-ed
    /// universally-quantified rule variables. We retain the term verbatim; the
    /// CHC engine performs the actual Horn-clause structuring.
    pub(super) fn parse_rule(items: &[SExpr]) -> Result<Self, ParseError> {
        if items.len() != 2 {
            return Err(ParseError::new("rule requires exactly one body term"));
        }
        Ok(Self::Rule(Term::from_sexp(&items[1])?))
    }

    /// Parse `(query <rel-application-or-symbol>)`.
    ///
    /// The query is a relation application `(p t1 ... tn)` or a bare relation
    /// symbol `p` (for a nullary relation). Reachability of the query relation
    /// is what the fixedpoint engine decides.
    pub(super) fn parse_query(items: &[SExpr]) -> Result<Self, ParseError> {
        if items.len() != 2 {
            return Err(ParseError::new("query requires exactly one relation term"));
        }
        Ok(Self::Query(Term::from_sexp(&items[1])?))
    }
}
