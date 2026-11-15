// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Explained ground values of string terms
//! ([`CoreSolver::known_string_with_reasons`]).
//!
//! One query memoises each equivalence class's member scan by
//! `(representative, depth)`. The value of a constant-free class at a depth
//! is a function of that pair alone, and every step goes strictly deeper
//! (class at `d`, its concat member at `d + 1`, that member's arguments at
//! `d + 2`), so the memo answers exactly what the depth-limited walk does,
//! cycles end at [`CoreSolver::MAX_RESOLVE_DEPTH`] like every other chain,
//! and a query scans each class at most `MAX_RESOLVE_DEPTH + 1` times.
//!
//! The resolver this replaces recursed from every member of a class back
//! into the members of that SAME class with `depth + 1`, so a class of `k`
//! members with no constant was walked `(k-1)^16` times before the depth
//! cap cut it. The walk polls no deadline: on cvc5 `issue8481` and the
//! #3890 `replace_re_all` membership a single
//! `check_regex_membership_violations` call ran for minutes, far past the
//! executor's 10 s budget.
//!
//! A cached class value must not outlive its depth. The cap also bounds the
//! size of a value (a doubling chain `z_i = z_{i+1}·z_{i+1}` reaches eight
//! levels, 256 copies of its constant), and a cache keyed by class alone
//! would hand a shallow visit's value to a deep one, building strings
//! exponentially past the cap.

use crate::core::CoreSolver;
use crate::state::SolverState;
use ay_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};
use ay_core::term::{TermData, TermId, TermStore};
use ay_core::TheoryLit;

/// A class value: the member `source` whose evaluation gives `value`, and
/// the literals behind `source = value`.
#[derive(Clone)]
struct ClassValue {
    source: TermId,
    value: String,
    reasons: Vec<TheoryLit>,
}

/// State of one [`CoreSolver::known_string_with_reasons`] query.
pub(in crate::core) struct KnownStringResolver<'a> {
    terms: &'a TermStore,
    state: &'a SolverState,
    /// Member-scan results by (representative, depth).
    classes: HashMap<(TermId, usize), Option<ClassValue>>,
    /// Member scans performed (the query's work).
    #[cfg(test)]
    pub(in crate::core) scans: usize,
}

impl<'a> KnownStringResolver<'a> {
    pub(in crate::core) fn new(terms: &'a TermStore, state: &'a SolverState) -> Self {
        Self {
            terms,
            state,
            classes: HashMap::default(),
            #[cfg(test)]
            scans: 0,
        }
    }

    /// The explained value of `t`, with duplicate reasons removed.
    pub(in crate::core) fn resolve(&mut self, t: TermId) -> Option<(String, Vec<TheoryLit>)> {
        let (value, reasons) = self.term(t, 0)?;
        let mut seen: HashSet<TheoryLit> = HashSet::default();
        let reasons = reasons
            .into_iter()
            .filter(|lit| seen.insert(*lit))
            .collect();
        Some((value, reasons))
    }

    fn term(&mut self, t: TermId, depth: usize) -> Option<(String, Vec<TheoryLit>)> {
        if depth > CoreSolver::MAX_RESOLVE_DEPTH {
            return None;
        }
        if let Some(s) = CoreSolver::get_string_constant(self.terms, t) {
            return Some((s.to_owned(), Vec::new()));
        }
        let rep = self.state.find(t);
        if let Some(s) = self.state.get_eqc(&rep).and_then(|e| e.constant.clone()) {
            let const_tid = self.state.find_constant_term_id(self.terms, t)?;
            if t == const_tid {
                return Some((s, Vec::new()));
            }
            let e = self.state.explain(t, const_tid);
            return (!e.is_empty()).then_some((s, e));
        }
        if Self::is_concat(self.terms, t) {
            return self.concat(t, depth);
        }
        let ClassValue {
            source,
            value,
            reasons,
        } = self.class(rep, depth)?;
        // `t` is not a concat, so it is never its class's source. The source
        // is fixed per (class, depth): when this link is unexplained the
        // query answers `None` rather than trying another member (fail
        // closed; it can cost a value, never soundness).
        let mut e = self.state.explain(t, source);
        if e.is_empty() {
            return None;
        }
        e.extend(reasons);
        Some((value, e))
    }

    /// Evaluate the `str.++` application `c` from its arguments' values.
    /// Concat evaluation is definitional: the arguments' reasons suffice.
    fn concat(&mut self, c: TermId, depth: usize) -> Option<(String, Vec<TheoryLit>)> {
        let TermData::App(_, args) = self.terms.get(c) else {
            return None;
        };
        let mut out = String::new();
        let mut reasons: Vec<TheoryLit> = Vec::new();
        for &arg in args {
            let (s, r) = self.term(arg, depth + 1)?;
            out.push_str(&s);
            reasons.extend(r);
        }
        Some((out, reasons))
    }

    /// Value of the constant-free class `rep` at `depth` through a member
    /// that evaluates; each `(rep, depth)` is scanned at most once.
    fn class(&mut self, rep: TermId, depth: usize) -> Option<ClassValue> {
        if let Some(memo) = self.classes.get(&(rep, depth)) {
            return memo.clone();
        }
        #[cfg(test)]
        {
            self.scans += 1;
        }
        let found = self.scan_members(rep, depth);
        self.classes.insert((rep, depth), found.clone());
        found
    }

    /// The first member of `rep`'s class that evaluates: a string constant
    /// or a `str.++` member (typically `x = "ab"·v·"cd"`). Any other member
    /// has no value of its own; resolving it would scan this list again.
    fn scan_members(&mut self, rep: TermId, depth: usize) -> Option<ClassValue> {
        let members: Vec<TermId> = self
            .state
            .get_eqc(&rep)
            .map(|e| e.members.clone())
            .unwrap_or_default();
        for source in members {
            if let Some(s) = CoreSolver::get_string_constant(self.terms, source) {
                return Some(ClassValue {
                    source,
                    value: s.to_owned(),
                    reasons: Vec::new(),
                });
            }
            if Self::is_concat(self.terms, source) {
                if let Some((value, reasons)) = self.concat(source, depth + 1) {
                    return Some(ClassValue {
                        source,
                        value,
                        reasons,
                    });
                }
            }
        }
        None
    }

    fn is_concat(terms: &TermStore, t: TermId) -> bool {
        matches!(terms.get(t), TermData::App(sym, _) if sym.name() == "str.++")
    }
}

impl CoreSolver {
    /// Entailed concrete string value WITH its proof-forest justification.
    ///
    /// Sources, each carrying its reasons:
    /// - a string constant term itself (no reasons needed);
    /// - an EQC constant: `explain(t, const_tid)`;
    /// - a `str.++` application whose arguments all resolve — concat
    ///   evaluation is definitional, so the arguments' reasons suffice;
    /// - a `str.++` member of `t`'s class that resolves (the concat member
    ///   of `x = str.++(...)`): `explain(t, member)` plus its reasons.
    ///
    /// The EQC-member arm is what lets a ground membership check fire
    /// under a SAT branch choice: with `v = ""` decided, `x`'s class
    /// has no constant, but its concat member `"ab"·v·"cd"` evaluates
    /// to `"abcd"`. Returns `None` when the value is unknown, when it lies
    /// deeper than [`Self::MAX_RESOLVE_DEPTH`], OR when any non-trivial
    /// link is unexplainable (same fail-closed discipline as
    /// [`Self::known_len_with_reasons`]). A query reuses each class's
    /// member scan per depth ([`KnownStringResolver`]).
    pub(in crate::core) fn known_string_with_reasons(
        terms: &TermStore,
        state: &SolverState,
        t: TermId,
    ) -> Option<(String, Vec<TheoryLit>)> {
        KnownStringResolver::new(terms, state).resolve(t)
    }
}
