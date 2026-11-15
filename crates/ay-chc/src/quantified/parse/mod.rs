// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Strict ingress for the typed bounded array/record source boundary.
//!
//! Accepts ASCII SMT-LIB: Bool/BVs through `crate::MAX_BITVECTOR_WIDTH`, rank-two
//! arrays with BV keys, lexical lets, outer
//! universal clause binders and direct conjunctive universal premises with
//! ordered groups of one to eight BV1..64 binders. Wide literals use exact,
//! balanced concat chunks; shared admission precedes numeric/AST allocation.
//! Fixedpoint scripts use declare-var/declare-rel, rule and one final query;
//! HORN scripts use Bool-returning declare-fun, assert and final check-sat.
//! Bounded acyclic one-constructor records have authenticated declarations.
//! Scalar Bool/BV arguments and BV-returning uninterpreted functions use
//! dialect-neutral declare-fun declarations, including nullary globals.
//! Every declaration is retained; function overloading and lexical shadowing
//! of function names are refused. No declare-const, define-fun, options, annotations, incremental
//! commands or mixed dialects. Optional exit is only allowed after the query.
//! All declarations precede clauses. Comments have no semantic effect.
//! The typed safety API requires a query: HORN assertions must include a
//! false/theory consequent; fixedpoint scripts provide their explicit query.

use super::{QuantifiedChcFunction, QuantifiedChcProblem, QuantifiedHornClause};
use crate::{ChcError, ChcExpr, ChcProblem, ChcResult, ChcSort, ChcVar, PredicateId};
use ay_frontend::SExpr;
use std::collections::{BTreeMap, BTreeSet, HashMap};
use std::sync::Arc;

mod clauses;
mod functions;
mod preflight;
mod records;
mod term;
#[cfg(test)]
mod tests;
mod value;

const MAX_WORK: usize = 262_144;
const MAX_COPY_BYTES: usize = 32 * 1024 * 1024;
const MAX_TERM_DEPTH: usize = 64;

fn invalid(message: &str) -> ChcError {
    ChcError::Parse(format!("quantified source: {message}"))
}

#[derive(Default)]
struct Budget {
    work: usize,
    bytes: usize,
}

impl Budget {
    fn charge(&mut self, work: usize, bytes: usize) -> ChcResult<()> {
        self.work = self
            .work
            .checked_add(work)
            .ok_or_else(|| invalid("work limit"))?;
        self.bytes = self
            .bytes
            .checked_add(bytes)
            .ok_or_else(|| invalid("copy limit"))?;
        if self.work > MAX_WORK || self.bytes > MAX_COPY_BYTES {
            return Err(invalid("parse work/copy limit"));
        }
        Ok(())
    }

    fn enter(&mut self, depth: usize) -> ChcResult<()> {
        if depth > MAX_TERM_DEPTH {
            return Err(invalid("expanded term depth limit"));
        }
        self.charge(1, 128)
    }

    fn name(&mut self, name: &str) -> ChcResult<()> {
        if name.is_empty()
            || name.len() > 16_384
            || super::source::theory_symbol(name)
            || crate::parser::is_builtin_term_symbol(name)
            || name
                .bytes()
                .any(|b| b.is_ascii_control() || b == b'|' || b == b'\\')
        {
            return Err(invalid("invalid source symbol"));
        }
        self.charge(1, name.len().saturating_mul(4))
    }
}

enum Term {
    Value(Arc<ChcExpr>, ChcSort),
    Predicate(PredicateId, Vec<Arc<ChcExpr>>),
    And(Vec<Arc<Term>>),
    Implies(Arc<Term>, Arc<Term>),
    Forall(Vec<ChcVar>, Arc<Term>),
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum Dialect {
    Unset,
    Horn,
    Fixedpoint,
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum Phase {
    Declarations,
    Clauses,
    Queried,
    Exited,
}

struct Parser<'a> {
    declarations: ChcProblem,
    functions: functions::FunctionState,
    records: records::RecordState,
    clauses: Vec<QuantifiedHornClause>,
    bindings: BTreeMap<String, Arc<Term>>,
    reserved: BTreeSet<&'a str>,
    fresh: usize,
    // Retain keys' owners: parse-time temporary terms can disappear before a
    // command ends, and an allocation address must never be reused as authority.
    qf: HashMap<*const Term, (Arc<Term>, Arc<ChcExpr>, ChcSort)>,
    budget: Budget,
    dialect: Dialect,
    phase: Phase,
    logic_seen: bool,
}

fn list(expr: &SExpr) -> ChcResult<&[SExpr]> {
    expr.as_list().ok_or_else(|| invalid("expected list"))
}

fn symbol(expr: &SExpr) -> ChcResult<&str> {
    expr.as_symbol().ok_or_else(|| invalid("expected symbol"))
}

fn symbols<'a>(roots: &'a [SExpr]) -> BTreeSet<&'a str> {
    let mut names = BTreeSet::new();
    let mut pending = roots.iter().collect::<Vec<_>>();
    while let Some(expr) = pending.pop() {
        match expr {
            SExpr::Symbol(name) => {
                names.insert(name.as_str());
            }
            SExpr::List(items) => pending.extend(items),
            _ => {}
        }
    }
    names
}

pub(super) fn parse(input: &str) -> ChcResult<QuantifiedChcProblem> {
    preflight::check(input)?;
    let commands =
        ay_frontend::sexp::parse_sexps(input).map_err(|_| invalid("invalid SMT-LIB syntax"))?;
    let mut parser = Parser {
        declarations: ChcProblem::new(),
        functions: functions::FunctionState::default(),
        records: records::RecordState::default(),
        clauses: Vec::new(),
        bindings: BTreeMap::new(),
        reserved: symbols(&commands),
        fresh: 0,
        qf: HashMap::new(),
        budget: Budget::default(),
        dialect: Dialect::Unset,
        phase: Phase::Declarations,
        logic_seen: false,
    };
    for command in &commands {
        parser.command(command)?;
        // Release the cache's retained source/value DAGs at each command;
        // declarations and completed clauses own everything they still need.
        parser.qf.clear();
    }
    if !matches!(parser.phase, Phase::Queried | Phase::Exited) {
        return Err(invalid("expected one terminal query or check-sat"));
    }
    QuantifiedChcProblem::new_with_functions(
        parser.declarations,
        parser.functions.declarations,
        parser.clauses,
    )
}

impl Parser<'_> {
    fn dialect(&mut self, dialect: Dialect) -> ChcResult<()> {
        if self.dialect != Dialect::Unset && self.dialect != dialect {
            return Err(invalid("mixed HORN/fixedpoint script"));
        }
        self.dialect = dialect;
        if dialect == Dialect::Fixedpoint {
            self.declarations.set_fixedpoint_format();
        }
        Ok(())
    }

    fn command(&mut self, command: &SExpr) -> ChcResult<()> {
        self.budget.enter(0)?;
        let items = list(command)?;
        let Some((head, args)) = items.split_first() else {
            return Err(invalid("empty command"));
        };
        let head = symbol(head)?;
        if self.phase == Phase::Exited || (self.phase == Phase::Queried && head != "exit") {
            return Err(invalid("command after terminal query"));
        }
        match (head, args) {
            ("set-logic", [logic]) if self.phase == Phase::Declarations && !self.logic_seen => {
                if symbol(logic)? != "HORN" {
                    return Err(invalid("expected HORN logic"));
                }
                self.logic_seen = true;
            }
            ("declare-var", [name, sort]) => {
                self.dialect(Dialect::Fixedpoint)?;
                let name = self.declaration_name(name)?;
                let sort = self.source_sort(sort)?;
                self.budget.sort_copy(&sort)?;
                let var = ChcVar::new(name.clone(), sort.clone());
                self.bindings.insert(
                    name,
                    Arc::new(Term::Value(Arc::new(ChcExpr::var(var)), sort)),
                );
            }
            ("declare-rel", [name, sorts]) => {
                self.dialect(Dialect::Fixedpoint)?;
                self.predicate(name, sorts)?;
            }
            ("declare-datatype", [name, definition]) => {
                self.record_declaration(name, definition)?;
            }
            ("declare-datatypes", [names, definitions]) => {
                self.record_declarations(names, definitions)?;
            }
            ("declare-fun", [name, sorts, result]) if result.is_symbol("Bool") => {
                self.dialect(Dialect::Horn)?;
                self.predicate(name, sorts)?;
            }
            ("declare-fun", [name, sorts, result]) => {
                // Shared scalar functions do not select a Horn dialect: MC
                // also emits them before/among fixedpoint declarations.
                self.function_declaration(name, sorts, result)?;
            }
            ("rule", [formula]) => {
                self.dialect(Dialect::Fixedpoint)?;
                self.phase = Phase::Clauses;
                let term = self.term(formula, 0)?;
                self.clause(&term)?;
            }
            ("assert", [formula]) => {
                self.dialect(Dialect::Horn)?;
                self.phase = Phase::Clauses;
                let term = self.term(formula, 0)?;
                self.clause(&term)?;
            }
            ("query", [formula]) => {
                self.dialect(Dialect::Fixedpoint)?;
                let term = self.term(formula, 0)?;
                self.query(&term)?;
                self.phase = Phase::Queried;
            }
            ("check-sat", []) => {
                self.dialect(Dialect::Horn)?;
                self.phase = Phase::Queried;
            }
            ("exit", []) if self.phase == Phase::Queried => self.phase = Phase::Exited,
            _ => return Err(invalid("unsupported command or command arity")),
        }
        Ok(())
    }

    fn declaration_name(&mut self, expr: &SExpr) -> ChcResult<String> {
        if self.phase != Phase::Declarations {
            return Err(invalid("declaration after a clause"));
        }
        let name = symbol(expr)?;
        self.budget.name(name)?;
        if self.bindings.contains_key(name)
            || self.declarations.lookup_predicate(name).is_some()
            || self.records.contains(name)
            || self.functions.contains(name)
        {
            return Err(invalid("duplicate term declaration"));
        }
        Ok(name.to_owned())
    }

    fn predicate(&mut self, name: &SExpr, sorts: &SExpr) -> ChcResult<()> {
        self.check_declaration_limit()?;
        let name = self.declaration_name(name)?;
        let sorts = list(sorts)?;
        self.budget
            .charge(sorts.len(), sorts.len().saturating_mul(128))?;
        let sorts = sorts
            .iter()
            .map(|sort| self.source_sort(sort))
            .collect::<ChcResult<Vec<_>>>()?;
        self.declarations.declare_predicate(&name, sorts);
        Ok(())
    }
}
