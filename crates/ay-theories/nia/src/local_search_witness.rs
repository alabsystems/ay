// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Cooperative discovery, verification and publication for local-search points.

use std::collections::BTreeSet;

use super::*;

/// One invocation's existing cutoff and observed refusal. This owns no guard,
/// allowance or count. A stopped walk cannot re-enter its fallback merely
/// because an independently installed stop callback later returns false.
pub(super) struct SearchProgress {
    deadline: Option<ay_core::time::Instant>,
    stopped: bool,
}

impl SearchProgress {
    pub(super) fn new(deadline: Option<ay_core::time::Instant>) -> Self {
        Self {
            deadline,
            stopped: false,
        }
    }

    pub(super) fn poll(&mut self, solver: &NiaSolver<'_>) -> bool {
        if !self.stopped {
            self.stopped = solver.should_timeout()
                || self
                    .deadline
                    .is_some_and(|end| ay_core::time::Instant::now() >= end);
        }
        !self.stopped
    }
}

impl NiaSolver<'_> {
    /// Collect the same Int variable leaves as bounded enumeration. The
    /// iterative walk visits shared DAG nodes once and polls before every
    /// node and variable-sized edge/output loops. No recursive discovery
    /// or bulk sort sits between checkpoints.
    pub(super) fn local_search_leaves(&self, progress: &mut SearchProgress) -> Option<Vec<TermId>> {
        if !progress.poll(self) {
            return None;
        }
        let mut seen = super::super::HashSet::default();
        let mut pending = Vec::new();
        let mut leaves = BTreeSet::new();
        for &root in &self.root_assertions {
            if !progress.poll(self) {
                return None;
            }
            pending.push(root);
            while let Some(term) = pending.pop() {
                if !progress.poll(self) {
                    return None;
                }
                if !seen.insert(term) {
                    continue;
                }
                match self.terms.get(term) {
                    TermData::Var(_, _) if self.terms.sort(term) == &Sort::Int => {
                        leaves.insert(term);
                    }
                    TermData::App(_, args) => {
                        for &arg in args.iter().rev() {
                            if !progress.poll(self) {
                                return None;
                            }
                            pending.push(arg);
                        }
                    }
                    TermData::Not(inner) => pending.push(*inner),
                    TermData::Ite(c, t, e) => pending.extend([*e, *t, *c]),
                    _ => {}
                }
            }
        }
        let mut result = Vec::new();
        for term in leaves {
            if !progress.poll(self) {
                return None;
            }
            result.push(term);
        }
        Some(result)
    }

    /// Try the original all-one/all-zero points using this invocation's
    /// existing shared cutoff/slice. Every exact formula and integer visit
    /// observes the live owner. Individual BigInt operations/allocations are
    /// cooperative units, not hard-preemptible operations.
    pub(super) fn canonical_point_witness(
        &mut self,
        progress: &mut SearchProgress,
    ) -> Option<TheoryResult> {
        let leaves = self.local_search_leaves(progress)?;
        if leaves.is_empty() {
            return None;
        }
        for value in [1i64, 0] {
            let mut var_map = HashMap::default();
            let mut values = Vec::new();
            for &leaf in &leaves {
                if !progress.poll(self) {
                    return None;
                }
                var_map.insert(leaf, value);
                values.push(value);
            }
            let mut all_hold = true;
            for &root in &self.root_assertions {
                if self.eval_formula_exact_with_progress(root, true, &var_map, &mut || {
                    progress.poll(self)
                }) != Some(true)
                {
                    all_hold = false;
                    break;
                }
            }
            if !progress.poll(self) {
                return None;
            }
            if all_hold {
                if self.debug {
                    safe_eprintln!(
                        "[NIA] Split probe: every root holds with every Int leaf = {value}"
                    );
                }
                self.record_local_search_model(&leaves, &values, progress)?;
                return Some(TheoryResult::Sat);
            }
        }
        None
    }

    /// Stage the whole verified model privately; a stop during map or
    /// auxiliary construction drops the stage rather than publishing a
    /// partial point. Publication uses the same invocation, not a fresh cap.
    pub(super) fn record_local_search_model(
        &mut self,
        vars: &[TermId],
        values: &[i64],
        progress: &mut SearchProgress,
    ) -> Option<()> {
        if vars.len() != values.len() {
            return None;
        }
        let mut var_map = HashMap::default();
        let mut model = HashMap::default();
        for (&var, &value) in vars.iter().zip(values) {
            if !progress.poll(self) {
                return None;
            }
            if !matches!(self.terms.sort(var), Sort::Int) {
                return None;
            }
            var_map.insert(var, value);
            model.insert(var, BigInt::from(value));
        }
        for mon in self.monomials.values() {
            if !progress.poll(self) {
                return None;
            }
            if let Some(value) =
                self.eval_term_with_progress(mon.aux_var, &var_map, &mut || progress.poll(self))
            {
                model.insert(mon.aux_var, value);
            }
        }
        if !progress.poll(self) {
            return None;
        }
        self.bounded_enum_bool_model.clear();
        self.bounded_enum_model = Some(model);
        Some(())
    }
}
