// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The live term universe of the eager datatype axiom scans (#dt-live-scan).
//!
//! The eager unroll instantiates selector, tester and acyclicity axioms over
//! the TermStore by scanning it. The store is session history, and the
//! finite-domain lane (`dt_finite`) changes what that history holds: a
//! command it decides leaves the lane's model terms and value pins instead
//! of the terms the other lanes would have left, and an undecided attempt
//! whose store rollback was refused leaves its own. Instantiating over those
//! terms is sound (every axiom is a datatype tautology) but not neutral:
//! they enter the search, the extracted model gives them values, and a
//! finite enum sort then carries more distinct elements than it has
//! constructors, which the cardinality gate refuses. Measured on incremental
//! QF_DT scripts: the same third query was `sat` on a fresh session and
//! `unknown` after the lane decided the first query.
//!
//! HISTORY is therefore what follows the lane's first decision
//! (`dt_history_term_ranges`): once the lane has decided a decision command,
//! every term that command and each later decision command created, plus an
//! undecided attempt's leftovers at any time. A session the lane never
//! decided keeps every term live, exactly as a solver without the lane. The
//! authored script's own terms (built between commands) are never history.
//! Other masks lost verdicts main decides: "everything older than this
//! command" cut the authored subterms that preprocessing or the term
//! builder's normalization dropped (`(hd (cons e x))`, the arguments of an
//! `(or true ..)`), which the eager lanes have always instantiated and the
//! gates evaluate (single-check losses, E13 round-3 `lost_dead_subterm_*`,
//! `lost_boolcell_*`); "everything any earlier decision created", in a
//! session the lane never decided, cut the other lanes' axiom chains a later
//! query relied on (v2verify `incr_default_loss`); and "only the lane's own
//! terms" left the third query above `unknown`.
//!
//! A history term is still live when it can matter to THIS query: it is
//! reachable from the current assertions, the assumptions, the authored
//! roots, the pre-lift snapshot, the scan's own assertion set, or any
//! datatype axiom this command has appended so far, or it is a nullary
//! constructor (a datatype's own values). The axiom roots matter because
//! terms are hash-consed: an axiom this command generates can be handed the
//! id of a term a lane minted earlier.
//!
//! Soundness does not depend on the mask: every instantiated axiom is a
//! datatype tautology, so skipping a term can only weaken the search
//! (models are validated) and never make an UNSAT wrong.

use super::super::Executor;
use ay_core::term::TermData;
use ay_core::TermId;

impl Executor {
    /// Move the current round's appended axioms into the command's axiom
    /// roots and clear them (the round truncated them off the assertions).
    pub(in crate::executor) fn retire_dt_solver_added_axiom_terms(&mut self) {
        self.dt_command_axiom_roots
            .extend(self.dt_solver_added_axiom_terms.drain());
    }

    /// Record `[start, end)`, terms a finite-domain lane attempt minted, as
    /// session history (see the module docs).
    pub(in crate::executor) fn record_dt_history_term_range(&mut self, start: usize, end: usize) {
        if end <= start {
            return;
        }
        match self.dt_history_term_ranges.last_mut() {
            Some((_, last_end)) if *last_end >= start => *last_end = (*last_end).max(end),
            _ => self.dt_history_term_ranges.push((start, end)),
        }
    }

    /// `live[i]` for every term index below `len` (see the module docs);
    /// `extra` are further roots of the caller's query (e.g. the assertion
    /// set a scan was handed).
    pub(super) fn dt_live_term_mask(
        &self,
        len: usize,
        extra: impl IntoIterator<Item = TermId>,
    ) -> Vec<bool> {
        let mut live = vec![true; len];
        let mut any_history = false;
        for &(start, end) in &self.dt_history_term_ranges {
            for slot in live.iter_mut().take(end.min(len)).skip(start) {
                *slot = false;
                any_history = true;
            }
        }
        if !any_history {
            return live;
        }
        let mut stack: Vec<TermId> = self.ctx.assertions.clone();
        stack.extend(self.dt_pre_lift_assertions.iter().copied());
        if let Some(assumptions) = self.last_assumptions.as_ref() {
            stack.extend(assumptions.iter().copied());
        }
        if let Some(authored) = self.independent_gate_authored_assertions.as_ref() {
            stack.extend(authored.iter().copied());
        }
        stack.extend(self.dt_solver_added_axiom_terms.iter().copied());
        stack.extend(self.dt_command_axiom_roots.iter().copied());
        stack.extend(extra);
        // Reachability is traversed through EVERY term, live or not: a root
        // created in this command (a preprocessed assertion) reaches the
        // older terms it is built from.
        let mut visited = vec![false; len];
        while let Some(t) = stack.pop() {
            let i = t.index();
            if i >= len || visited[i] {
                continue;
            }
            visited[i] = true;
            live[i] = true;
            stack.extend(self.ctx.terms.children(t));
        }
        for (i, slot) in live.iter_mut().enumerate() {
            if !*slot {
                if let TermData::Var(name, _) = self.ctx.terms.get(TermId::new(i as u32)) {
                    *slot = self.ctx.is_constructor(name).is_some();
                }
            }
        }
        live
    }
}

#[cfg(test)]
mod tests {
    use ay_core::term::{Symbol, TermData};
    use ay_frontend::parse;

    use crate::Executor;

    /// Only what the lane left is history, and history is dead unless
    /// reachable; reachability runs through the query and through this
    /// command's appended axioms (hash-consing hands a regenerated term an
    /// older id) (#dt-live-scan).
    #[test]
    fn live_mask_lane_history_roots_and_axioms() {
        let mut exec = Executor::new();
        let script = "(set-logic QF_DT)\n\
            (declare-datatypes ((L 0)) (((cons (hd Bool) (tl L)) (nil))))\n\
            (declare-const x L) (assert ((_ is cons) x))\n";
        exec.execute_all(&parse(script).unwrap()).unwrap();
        let x = (0..exec.ctx.terms.len())
            .map(|i| ay_core::TermId::new(i as u32))
            .find(|&t| matches!(exec.ctx.terms.get(t), TermData::Var(n, _) if n == "x"))
            .expect("declared x");
        let sort = exec.ctx.terms.sort(x).clone();
        // A term the script built (e.g. an authored subterm preprocessing
        // dropped) is never history.
        let authored = exec
            .ctx
            .terms
            .mk_app(Symbol::named("tl"), vec![x], sort.clone());
        let len = exec.ctx.terms.len();
        assert!(
            exec.dt_live_term_mask(len, []).iter().all(|&l| l),
            "no history yet"
        );
        // A term the lane left is history.
        let start = exec.ctx.terms.len();
        let minted = exec
            .ctx
            .terms
            .mk_app(Symbol::named("tl"), vec![authored], sort);
        exec.record_dt_history_term_range(start, exec.ctx.terms.len());
        let len = exec.ctx.terms.len();
        let mask = exec.dt_live_term_mask(len, []);
        assert!(!mask[minted.index()]);
        assert!(mask[authored.index()] && mask[x.index()]);
        assert!(
            exec.dt_live_term_mask(len, [minted])[minted.index()],
            "unless reachable"
        );
        // An axiom generated in this command reuses the minted term.
        let axiom = exec.ctx.terms.mk_eq(minted, x);
        exec.dt_command_axiom_roots.push(axiom);
        let len = exec.ctx.terms.len();
        let mask = exec.dt_live_term_mask(len, []);
        assert!(mask[axiom.index()] && mask[minted.index()]);
    }
}
