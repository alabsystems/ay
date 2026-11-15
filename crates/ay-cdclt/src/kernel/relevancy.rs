// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Term relevancy (KC21): a kernel service, justification-based over the
//! Tseitin structure of the assertions (z3 `smt::relevancy`, simplified).
//!
//! A term is relevant when the current assignment's truth of the assertions
//! depends on it:
//! - every assertion is relevant;
//! - a relevant `not` makes its argument relevant;
//! - a relevant `and` that is true makes every conjunct relevant; one that
//!   is false makes one false conjunct relevant (the first by position,
//!   once one is false). `or` is dual; `(=> a b)` is `(or (not a) b)`;
//! - a relevant Boolean `ite` makes its condition relevant and, once the
//!   condition is assigned, the branch it selects;
//! - every other relevant term (a theory atom, an application, `xor`, a
//!   Boolean `=`, a term-level `ite`) makes all its arguments relevant.
//!
//! The marks are undone on backtrack (one scope per decision level, like the
//! hub); marks made at level 0 and terms minted during the search (whose
//! atoms the search introduced for a reason) stay relevant. A relevant term
//! with a hub node sets the node's relevancy bit.
//!
//! What it is used for now: the hub hands the search only the propagations
//! of relevant nodes (an engine option), and plug-ins read it through
//! `Ctx::is_relevant`. Both uses tolerate an imprecise answer in either
//! direction: a dropped propagation is re-found as a conflict when the
//! literal is assigned, and an extra one is T-valid. E-matching and lazy
//! internalization (KC23) are the consumers it is built for.

use ay_core::{TermData, TermId, TermStore};
use ay_sat::{SolverContext, Variable};

use crate::atoms::AtomTable;
use crate::hub::Hub;

/// The relevancy service (see the module docs).
#[derive(Debug, Default)]
pub(crate) struct Relevancy {
    /// By term index: marked in a scope still open (or at level 0).
    relevant: Vec<bool>,
    /// By term index: relevant for the rest of the check.
    always: Vec<bool>,
    /// By term index: watches are registered (once per check).
    watching: Vec<bool>,
    trail: Vec<TermId>,
    scopes: Vec<usize>,
    /// SAT variable -> its term (the encoding's variables).
    var_term: Vec<Option<TermId>>,
    /// SAT variable -> relevant connectives to re-justify when it is set.
    watches: Vec<Vec<TermId>>,
    marked: u64,
    work: Vec<TermId>,
}

fn get(bits: &[bool], term: TermId) -> bool {
    bits.get(term.0 as usize).copied().unwrap_or(false)
}

fn set(bits: &mut Vec<bool>, term: TermId, value: bool) {
    let idx = term.0 as usize;
    if bits.len() <= idx {
        bits.resize(idx + 1, false);
    }
    if let Some(slot) = bits.get_mut(idx) {
        *slot = value;
    }
}

/// How a relevant Boolean connective is justified.
enum Shape<'a> {
    /// `and` (`true` when it is a conjunction), or `or`.
    Junction(bool, &'a [TermId]),
    /// `(=> a b)`.
    Implies(TermId, TermId),
    /// A Boolean `ite`.
    Ite(TermId, TermId, TermId),
    /// Everything else: all children.
    All,
}

fn shape(terms: &TermStore, term: TermId) -> Shape<'_> {
    match terms.get(term) {
        TermData::App(sym, args) => match (sym.name(), args.as_slice()) {
            ("and", _) => Shape::Junction(true, args),
            ("or", _) => Shape::Junction(false, args),
            ("=>", &[a, b]) => Shape::Implies(a, b),
            _ => Shape::All,
        },
        TermData::Ite(c, t, e) if terms.sort(term) == &ay_core::Sort::Bool => {
            Shape::Ite(*c, *t, *e)
        }
        _ => Shape::All,
    }
}

fn children(terms: &TermStore, term: TermId) -> Vec<TermId> {
    match terms.get(term) {
        TermData::App(_, args) => args.clone(),
        TermData::Ite(c, t, e) => vec![*c, *t, *e],
        TermData::Not(inner) => vec![*inner],
        _ => Vec::new(),
    }
}

impl Relevancy {
    /// A service over the encoding's variables.
    pub(crate) fn new(atoms: &AtomTable) -> Self {
        let var_term = atoms.var_terms();
        Self {
            watches: vec![Vec::new(); var_term.len()],
            var_term,
            ..Self::default()
        }
    }

    /// Whether `term` is relevant now.
    pub(crate) fn is_relevant(&self, term: TermId) -> bool {
        get(&self.relevant, term) || get(&self.always, term)
    }

    /// Terms marked so far (undone marks included).
    pub(crate) const fn marked(&self) -> u64 {
        self.marked
    }

    /// `term` is relevant for the rest of the check (a minted atom).
    pub(crate) fn always(&mut self, term: TermId) {
        set(&mut self.always, term, true);
    }

    pub(crate) fn push_scope(&mut self) {
        self.scopes.push(self.trail.len());
    }

    pub(crate) fn pop_scopes(&mut self, n: usize) {
        let keep = self.scopes.len().saturating_sub(n);
        let Some(&mark) = self.scopes.get(keep) else {
            return;
        };
        self.scopes.truncate(keep);
        for term in self.trail.drain(mark..) {
            if let Some(slot) = self.relevant.get_mut(term.0 as usize) {
                *slot = false;
            }
        }
    }

    /// An assertion: relevant at level 0.
    pub(crate) fn mark_root(
        &mut self,
        root: TermId,
        terms: &TermStore,
        atoms: &AtomTable,
        hub: &mut Hub,
    ) {
        self.work.push(root);
        self.run(terms, atoms, hub, None);
    }

    /// SAT variable `var` was assigned: re-justify the relevant connectives
    /// that wait on it.
    pub(crate) fn assigned(
        &mut self,
        var: usize,
        terms: &TermStore,
        atoms: &AtomTable,
        hub: &mut Hub,
        sat: &dyn SolverContext,
    ) {
        if let Some(Some(term)) = self.var_term.get(var).copied() {
            if self.is_relevant(term) {
                self.justify(term, terms, atoms, sat);
            }
        }
        // `justify` only queues work; watches grow in `run`, after the loop.
        let waiting = self.watches.get(var).map_or(0, Vec::len);
        for k in 0..waiting {
            let Some(&parent) = self.watches.get(var).and_then(|w| w.get(k)) else {
                break;
            };
            if self.is_relevant(parent) {
                self.justify(parent, terms, atoms, sat);
            }
        }
        self.run(terms, atoms, hub, Some(sat));
    }

    /// Mark everything on the work list, and what it makes relevant.
    fn run(
        &mut self,
        terms: &TermStore,
        atoms: &AtomTable,
        hub: &mut Hub,
        sat: Option<&dyn SolverContext>,
    ) {
        while let Some(term) = self.work.pop() {
            if get(&self.relevant, term) {
                continue;
            }
            set(&mut self.relevant, term, true);
            if !self.scopes.is_empty() {
                self.trail.push(term);
            }
            self.marked += 1;
            if let Some(n) = hub.node_of(term) {
                hub.set_relevant(n);
            }
            match shape(terms, term) {
                Shape::All => self.work.extend(children(terms, term)),
                _ => {
                    self.watch(term, terms, atoms);
                    if let Some(sat) = sat {
                        self.justify(term, terms, atoms, sat);
                    }
                }
            }
        }
    }

    /// Register `term` (a connective) under its own variable and its
    /// children's, once.
    fn watch(&mut self, term: TermId, terms: &TermStore, atoms: &AtomTable) {
        if get(&self.watching, term) {
            return;
        }
        set(&mut self.watching, term, true);
        let mut on = vec![term];
        on.extend(children(terms, term));
        for t in on {
            let (base, _) = strip_not(terms, t);
            if let Some(var) = atoms.var_of(base) {
                let idx = var as usize;
                if self.watches.len() <= idx {
                    self.watches.resize(idx + 1, Vec::new());
                }
                if let Some(list) = self.watches.get_mut(idx) {
                    list.push(term);
                }
            }
        }
    }

    /// Queue what a relevant connective's current values make relevant.
    fn justify(
        &mut self,
        term: TermId,
        terms: &TermStore,
        atoms: &AtomTable,
        sat: &dyn SolverContext,
    ) {
        let value = |t: TermId| {
            let (base, negated) = strip_not(terms, t);
            let var = atoms.var_of(base)?;
            sat.value(Variable::new(var)).map(|v| v != negated)
        };
        match shape(terms, term) {
            Shape::All => {}
            Shape::Junction(conjunction, args) => match value(term) {
                // A true `and` / false `or`: every argument.
                Some(v) if v == conjunction => self.work.extend(args.iter().copied()),
                // A false `and` / true `or`: one argument that has the value.
                Some(v) => {
                    if let Some(&arg) = args.iter().find(|&&a| value(a) == Some(v)) {
                        self.work.push(arg);
                    }
                }
                None => {}
            },
            Shape::Implies(a, b) => match value(term) {
                Some(false) => self.work.extend([a, b]),
                Some(true) => {
                    if value(a) == Some(false) {
                        self.work.push(a);
                    } else if value(b) == Some(true) {
                        self.work.push(b);
                    }
                }
                None => {}
            },
            Shape::Ite(c, t, e) => {
                self.work.push(c);
                match value(c) {
                    Some(true) => self.work.push(t),
                    Some(false) => self.work.push(e),
                    None => {}
                }
            }
        }
    }
}

fn strip_not(terms: &TermStore, mut term: TermId) -> (TermId, bool) {
    let mut negated = false;
    while let TermData::Not(inner) = terms.get(term) {
        term = *inner;
        negated = !negated;
    }
    (term, negated)
}
