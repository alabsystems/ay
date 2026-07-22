// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Parallel portfolio clause-sharing hooks.
//!
//! These hooks are deliberately narrow: workers may export low-quality metadata
//! on every learned clause, but imports are accepted only at decision level 0.
//! That keeps watched-clause insertion on the same safe path used by
//! inprocessing products and avoids introducing already-falsified clauses into
//! a non-root CDCL trail.

use super::*;

impl Solver {
    /// Export a learned clause to the portfolio sharing hook, if installed.
    #[inline]
    pub(super) fn export_portfolio_shared_clause(&mut self, literals: &[Literal], lbd: u32) {
        if let Some(exporter) = self.cold.portfolio_clause_exporter.as_mut() {
            exporter(literals, lbd);
        }
    }

    /// Poll and import portfolio clauses at a root-level safe point.
    ///
    /// Imported clauses are trusted learned clauses from sibling workers solving
    /// the same DIMACS formula. Proof-producing solves deliberately skip this
    /// path until cross-thread proof stitching exists.
    #[inline]
    pub(super) fn import_portfolio_shared_clauses_at_root(&mut self) {
        if self.decision_level != 0
            || self.cold.portfolio_clause_importer.is_none()
            || self.cold.lrat_enabled
            || self.proof_manager.is_some()
            || !self.cold.scope_selectors.is_empty()
            || self.watches_disconnected
        {
            return;
        }

        let clauses = {
            let Some(importer) = self.cold.portfolio_clause_importer.as_mut() else {
                return;
            };
            importer()
        };

        for clause in clauses {
            if self.has_empty_clause {
                break;
            }
            let _ = self.add_portfolio_imported_clause(clause);
        }
    }

    /// Add one trusted portfolio-imported learned clause.
    ///
    /// Returns `true` when the clause was added or was a satisfied tautology,
    /// and `false` when it was rejected by safety gates or derived UNSAT.
    pub(crate) fn add_portfolio_imported_clause(&mut self, literals: Vec<Literal>) -> bool {
        if self.decision_level != 0
            || self.cold.lrat_enabled
            || self.proof_manager.is_some()
            || !self.cold.scope_selectors.is_empty()
            || self.watches_disconnected
        {
            return false;
        }

        let Some(mut normalized) = self.normalize_portfolio_import_clause(literals) else {
            return true;
        };

        self.add_preserved_learned_watched(&mut normalized)
    }

    fn normalize_portfolio_import_clause(
        &self,
        mut literals: Vec<Literal>,
    ) -> Option<Vec<Literal>> {
        if literals.is_empty() {
            return None;
        }
        if literals.iter().any(|lit| {
            let var_idx = lit.variable().index();
            var_idx >= self.num_vars || self.var_lifecycle.is_removed(var_idx)
        }) {
            return None;
        }

        literals.sort_by_key(|lit| lit.0);
        literals.dedup();

        for pair in literals.windows(2) {
            if pair[0].variable() == pair[1].variable() {
                return None;
            }
        }

        Some(literals)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::literal::{Literal, Variable};
    use parking_lot::Mutex;
    use std::sync::Arc;

    fn pos(v: u32) -> Literal {
        Literal::positive(Variable(v))
    }

    fn neg(v: u32) -> Literal {
        Literal::negative(Variable(v))
    }

    #[test]
    fn test_portfolio_import_hook_adds_root_unit() {
        let a = pos(0);
        let imported_once = Arc::new(Mutex::new(false));
        let imported_once_for_hook = Arc::clone(&imported_once);
        let mut solver = Solver::new(1);
        solver.set_portfolio_clause_sharing(
            None,
            Some(Box::new(move || {
                let mut guard = imported_once_for_hook.lock();
                if *guard {
                    Vec::new()
                } else {
                    *guard = true;
                    vec![vec![a]]
                }
            })),
        );

        solver.import_portfolio_shared_clauses_at_root();

        assert!(*imported_once.lock(), "import hook should be polled");
        assert_eq!(
            solver.value(Variable(0)),
            Some(true),
            "imported root unit should be enqueued immediately"
        );
    }

    #[test]
    fn test_portfolio_export_hook_observes_analyzed_clause() {
        let mut solver = Solver::new(2);
        solver.add_clause(vec![pos(0), pos(1)]);
        solver.add_clause(vec![pos(0), neg(1)]);
        solver.add_clause(vec![neg(0), pos(1)]);
        solver.add_clause(vec![neg(0), neg(1)]);

        let exported = Arc::new(Mutex::new(Vec::new()));
        let exported_for_hook = Arc::clone(&exported);
        solver.set_portfolio_clause_sharing(
            Some(Box::new(move |literals, lbd| {
                exported_for_hook.lock().push((literals.to_vec(), lbd));
            })),
            None,
        );

        solver.initialize_watches();
        assert!(solver.process_initial_clauses().is_none());
        assert!(solver.propagate().is_none());

        solver.decide(pos(0));
        let conflict_ref = solver
            .propagate()
            .expect("x=true should produce a conflict");
        solver.analyze_and_backtrack(conflict_ref, "portfolio-sharing-test", |_, _| {});

        let exported = exported.lock();
        assert_eq!(exported.len(), 1);
        assert!(
            exported[0].1 <= 3,
            "test formula should export a low-LBD clause, got LBD {}",
            exported[0].1
        );
        assert!(
            !exported[0].0.is_empty(),
            "exported learned clause should be non-empty"
        );
    }
}
