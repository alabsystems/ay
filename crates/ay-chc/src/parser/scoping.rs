// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Scoping and shape checks the parser applies while it builds clauses.
//!
//! Each closes a way a well-formed SMT-LIB HORN script used to be read as a
//! different clause set (all found by the CHC differential generator,
//! `scripts/differential/gen/chc`, z3 5.1 cross-checked):
//! - a `let` against a stripped quantifier binder of the same name;
//! - commands whose effect on the clause set is not modelled;
//! - relation applications outside the positions a Horn clause gives them.

use super::ChcParser;
use crate::{ChcError, ChcExpr, ChcResult, ClauseHead, HornClause};

/// Where the enclosing scopes stood before a `let` body: see
/// [`ChcParser::enter_let_scope`].
pub(super) struct LetScopeMark {
    renames: usize,
    let_names: usize,
}

impl ChcParser {
    /// A quantifier binder is renamed apart when its name lies in an
    /// engine-reserved family (`is_engine_reserved_var_name`) or collides
    /// with another binder of the clause, a file-scoped declare-var, a global
    /// function/relation symbol, or the name of an enclosing `let`.
    ///
    /// The first case: the engine identifies a clause variable by its name
    /// and sort, so a binder named like a variable the engine mints (the mod
    /// elimination's `_mod_q_0`, for example) would be that variable.
    ///
    /// The last case: a `let` is expanded by substituting its value for the
    /// bound name after its body is parsed, so an unrenamed binder of the same
    /// name inside the body would have its own occurrences replaced too
    /// (`(let ((y 5)) (exists ((y Int)) (= y (+ x 10))))` read as
    /// `5 = x + 10`).
    pub(super) fn binder_must_be_renamed(&self, name: &str) -> bool {
        crate::expr::is_engine_reserved_var_name(name)
            || self.clause_binder_names.contains(name)
            || self.declared_var_names.contains(name)
            || self.functions.contains_key(name)
            || self.predicates.contains_key(name)
            || self.let_scope.iter().any(|bound| bound == name)
    }

    /// The name a file-scoped or undeclared input variable `name` is renamed
    /// to when `name` lies in an engine-reserved family
    /// (`is_engine_reserved_var_name`), minted on first request with
    /// [`Self::fresh_binder_name`] and kept for the rest of the file; `None`
    /// for any other name. Quantifier binders are renamed by
    /// [`Self::binder_must_be_renamed`] instead.
    pub(super) fn reserved_variable_rename(&mut self, name: &str) -> Option<String> {
        if !crate::expr::is_engine_reserved_var_name(name) {
            return None;
        }
        if let Some(renamed) = self.reserved_var_renames.get(name) {
            return Some(renamed.clone());
        }
        let renamed = self.fresh_binder_name(name);
        self.reserved_var_renames
            .insert(name.to_string(), renamed.clone());
        Some(renamed)
    }

    /// Open the scope of a `let` body (the values were parsed in the
    /// enclosing scope, as SMT-LIB's parallel `let` requires).
    ///
    /// A let name that is the source of an active binder rename (an outer
    /// quantifier binder renamed apart, `y` -> `ay!cap!N!y`) must shadow that
    /// rename in the body, or the body's `y` resolves to the outer binder and
    /// the let is silently dropped: the identity rename `(y, y)`, innermost,
    /// makes `y` resolve to the let variable. Every let name joins `let_scope`
    /// so a quantifier binder of the same name in the body is renamed apart.
    pub(super) fn enter_let_scope(&mut self, bindings: &[(String, ChcExpr)]) -> LetScopeMark {
        let mark = LetScopeMark {
            renames: self.active_renames.len(),
            let_names: self.let_scope.len(),
        };
        for (name, _) in bindings {
            if self.active_renames.iter().any(|(from, _)| from == name) {
                self.active_renames.push((name.clone(), name.clone()));
            }
            self.let_scope.push(name.clone());
        }
        mark
    }

    pub(super) fn leave_let_scope(&mut self, mark: LetScopeMark) {
        self.active_renames.truncate(mark.renames);
        self.let_scope.truncate(mark.let_names);
    }

    /// Read a command name, refusing the commands whose effect on the clause
    /// set or the symbol table this parser does not model.
    ///
    /// Skipping them changed the problem: a `define-fun` constant became a
    /// fresh, universally quantified Int variable at every use (the
    /// unknown-symbol fallback in `parse_symbol_expr`), clauses asserted inside
    /// a popped scope or before a `reset-assertions` stayed in the problem, and
    /// an `assert` after a `check-sat` made the one verdict answer the union of
    /// both clause sets. Each published wrong verdicts. Fail closed.
    pub(super) fn parse_modelled_command(&mut self) -> ChcResult<String> {
        let cmd = self.parse_symbol()?;
        match cmd.as_str() {
            "define-fun" | "define-fun-rec" | "define-funs-rec" | "define-const" | "push"
            | "pop" | "reset" | "reset-assertions" | "check-sat-assuming" => {
                Err(ChcError::Parse(format!(
                    "unsupported command in CHC input: `{cmd}` (its effect on the \
                     clause set is not modelled)"
                )))
            }
            "assert" if self.check_sat_seen => Err(ChcError::Parse(
                "unsupported CHC input: `assert` after `check-sat` \
                 (incremental CHC scripts are not supported)"
                    .into(),
            )),
            _ => {
                self.check_sat_seen |= cmd == "check-sat";
                Ok(cmd)
            }
        }
    }

    /// Keep relation applications out of the background constraint.
    ///
    /// A relation application that is a top-level conjunct of the constraint
    /// (e.g. `P(x)` from the non-predicate head `(not (not (P x)))` negated
    /// into the body) is a positive body atom and moves into
    /// `ClauseBody::predicates`. One that is nested anywhere else (`or`, `not`,
    /// `ite`, `=`, a predicate or head argument) is not a Horn body atom this
    /// clause representation can express. Left in place, the SMT encoding reads
    /// it as a FREE Bool variable: `P(x) /\ (Q(x) \/ R(x)) => false`,
    /// `Q(x) /\ not P(x) => false` and `Q(x) => not P(x)` all became reachable
    /// queries, and AY published `unsat` on safe systems (z3 5.1: `sat`).
    /// Fail closed on those.
    pub(super) fn lift_constraint_relations(mut clause: HornClause) -> ChcResult<HornClause> {
        // Clauses without a relation in the constraint (all CHC-COMP inputs)
        // are left exactly as built.
        let lift = clause
            .body
            .constraint
            .as_ref()
            .is_some_and(crate::ChcProblem::expr_contains_predicate_app);
        if let Some(constraint) = lift.then(|| clause.body.constraint.take()).flatten() {
            let mut kept = Vec::new();
            for conjunct in constraint.collect_conjuncts() {
                if let ChcExpr::PredicateApp(_, id, args) = &conjunct {
                    let args = args.iter().map(|a| (**a).clone()).collect();
                    clause.body.predicates.push((*id, args));
                } else {
                    kept.push(conjunct);
                }
            }
            clause.body.constraint = if kept.is_empty() {
                None
            } else {
                Some(ChcExpr::and_all(kept))
            };
            if clause.body.predicates.is_empty() && clause.body.constraint.is_none() {
                clause.body.constraint = Some(ChcExpr::Bool(true));
            }
        }
        let nested = clause
            .body
            .constraint
            .iter()
            .chain(clause.body.predicates.iter().flat_map(|(_, args)| args))
            .chain(match &clause.head {
                ClauseHead::Predicate(_, args) => args.as_slice(),
                ClauseHead::False => &[][..],
            })
            .any(crate::ChcProblem::expr_contains_predicate_app);
        if nested {
            return Err(ChcError::Parse(format!(
                "unsupported CHC input: a relation application nested under a \
                 connective other than `and` (or inside a term) is not a Horn \
                 body atom: {clause}"
            )));
        }
        Ok(clause)
    }
}
