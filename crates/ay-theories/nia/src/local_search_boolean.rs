// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Genuine Boolean DDfw moves, following Z3 5.3.3 ast/sls/sat_ddfw.cpp
//! pick_var/apply_flip and sls_arith_clausal.cpp's two-mode schedule.

use super::*;

#[derive(Clone, Copy, PartialEq, Eq)]
pub(super) enum SearchMode {
    Arithmetic,
    Boolean,
}

impl Search {
    /// Counts distinct SAT atoms in false clauses, classifying arithmetic
    /// atoms as external variables exactly as the upstream scheduler does.
    pub(super) fn unsat_kinds(&self, stop: &mut impl FnMut() -> bool) -> Option<(u64, u64)> {
        let mut boolean = 0;
        let mut external = 0;
        for atom in &self.atoms {
            if stop() {
                return None;
            }
            let mut present = false;
            for &(ci, _) in &atom.lit_occ {
                if stop() {
                    return None;
                }
                if self.clauses[ci as usize].num_true == 0 {
                    present = true;
                    break;
                }
            }
            if present {
                if atom.boolean.is_some() {
                    boolean += 1;
                } else {
                    external += 1;
                }
            }
        }
        Some((boolean, external))
    }

    /// Exact weighted change in false clauses for a flip. Occurrences are
    /// grouped by clause, so duplicate literals and p-or-not-p remain exact.
    fn boolean_reward(&self, ai: usize, stop: &mut impl FnMut() -> bool) -> Option<f64> {
        let atom = &self.atoms[ai];
        let mut reward = 0.0;
        let mut occurrences = atom.lit_occ.iter().peekable();
        while let Some(&(ci, _)) = occurrences.peek().copied() {
            if stop() {
                return None;
            }
            let clause = &self.clauses[ci as usize];
            let mut count = i64::from(clause.num_true);
            while occurrences.peek().is_some_and(|(next, _)| *next == ci) {
                if stop() {
                    return None;
                }
                let &(_, negated) = occurrences.next()?;
                count += if atom.truth != negated { -1 } else { 1 };
            }
            if clause.num_true == 0 && count > 0 {
                reward += clause.weight;
            }
            if clause.num_true > 0 && count == 0 {
                reward -= clause.weight;
            }
        }
        Some(reward)
    }

    pub(super) fn move_boolean(&mut self, stop: &mut impl FnMut() -> bool) -> Option<()> {
        let mut selected = None;
        let mut zero = None;
        let mut zero_count = 0;
        let mut total = 0.0;
        for ai in 0..self.atoms.len() {
            if stop() {
                return None;
            }
            if self.atoms[ai].boolean.is_none() {
                continue;
            }
            let mut in_unsat = false;
            for &(ci, _) in &self.atoms[ai].lit_occ {
                if stop() {
                    return None;
                }
                if self.clauses[ci as usize].num_true == 0 {
                    in_unsat = true;
                    break;
                }
            }
            if !in_unsat {
                continue;
            }
            let reward = self.boolean_reward(ai, stop)?;
            if reward > 0.0 {
                total += reward;
                // Weighted reservoir implements upstream score(r) == r.
                let random = self.rng.next() as f64 / (u64::MAX as f64 + 1.0);
                if random * total < reward {
                    selected = Some(ai);
                }
            } else if reward == 0.0 {
                zero_count += 1;
                if self.rng.below(zero_count) == 0 {
                    zero = Some(ai);
                }
            }
        }
        // Upstream's default permits zero-reward flips with rand(100) <= 15.
        let choice = selected.or_else(|| {
            if self.rng.below(100) <= 15 {
                zero
            } else {
                None
            }
        });
        let Some(ai) = choice else {
            if stop() {
                return None;
            }
            self.shift_weights();
            return Some(());
        };
        self.atoms[ai].truth = !self.atoms[ai].truth;
        let truth = self.atoms[ai].truth;
        let occurrences = std::mem::take(&mut self.atoms[ai].lit_occ);
        for &(ci, negated) in &occurrences {
            if stop() {
                return None;
            }
            self.bump_clause(ci, truth != negated);
        }
        self.atoms[ai].lit_occ = occurrences;
        Some(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use ay_core::resource::{ChildSpec, Guard, NodeLabel};
    use ay_core::term::TermStore;
    use ay_core::TheorySolver;

    #[test]
    fn boolean_search_publishes_typed_leaves_and_resets_the_query_point() {
        let mut terms = TermStore::new();
        let p = terms.mk_var("p", Sort::Bool);
        let x = terms.mk_var("x", Sort::Int);
        let one = terms.mk_int(BigInt::from(1));
        let square = terms.mk_mul(vec![x, x]);
        let square_one = terms.mk_eq(square, one);
        let root = terms.mk_and(vec![p, square_one]);
        let false_term = terms.mk_bool(false);
        let mut solver = NiaSolver::new(&terms);
        solver.set_root_assertions(vec![root]);
        assert!(matches!(
            solver.try_clausal_local_search(),
            Some(TheoryResult::Sat)
        ));
        assert_eq!(
            solver.boolean_witness().collect::<Vec<_>>(),
            vec![(p, true)]
        );
        let model = solver.extract_model().expect("verified point");
        assert!(model
            .values
            .keys()
            .all(|&term| terms.sort(term) == &Sort::Int));
        assert_eq!(model.values[&x].clone().pow(2), BigInt::from(1));
        solver.set_root_assertions(vec![false_term]);
        assert!(solver.boolean_witness().next().is_none());
        assert!(solver.bounded_enum_model.is_none());
    }

    #[test]
    fn contradictory_boolean_arithmetic_point_is_rejected_by_original_replay() {
        let mut terms = TermStore::new();
        let p = terms.mk_var("p", Sort::Bool);
        let x = terms.mk_var("x", Sort::Int);
        let one = terms.mk_int(BigInt::from(1));
        let equality = terms.mk_eq(x, one);
        let not_p = terms.mk_not(p);
        let roots = vec![p, not_p, equality];
        let mut builder = Builder::new(&terms);
        let clauses: Vec<_> = roots
            .iter()
            .flat_map(|&root| builder.cnf(root, true, 0).expect("mixed clauses"))
            .collect();
        let vars = builder.var_term.clone();
        let mut search = Search::new(builder, clauses, vars.len());
        search.vars[0].value = 1;
        for atom in &mut search.atoms {
            if atom.boolean.is_some() {
                atom.truth = true;
            }
        }
        search.recompute_all();
        let mut solver = NiaSolver::new(&terms);
        solver.set_root_assertions(roots);
        let mut progress = SearchProgress::new(None);
        assert!(solver
            .verify_clausal_witness(&search, &vars, &mut progress)
            .is_none());
        assert!(solver.bounded_enum_model.is_none());
        assert!(solver.boolean_witness().next().is_none());
    }

    #[test]
    fn cancelled_boolean_point_cannot_publish_and_fresh_owner_can_retry() {
        let mut terms = TermStore::new();
        let p = terms.mk_var("p", Sort::Bool);
        let mut solver = NiaSolver::new(&terms);
        solver.set_root_assertions(vec![p]);
        {
            let check = Guard::root_child(ChildSpec::new(NodeLabel::Check));
            check.cancel();
            let _scope = check.enter();
            assert!(solver.try_clausal_local_search().is_none());
            assert!(solver.boolean_witness().next().is_none());
            assert!(solver.bounded_enum_model.is_none());
        }
        assert!(matches!(
            solver.try_clausal_local_search(),
            Some(TheoryResult::Sat)
        ));
        assert_eq!(
            solver.boolean_witness().collect::<Vec<_>>(),
            vec![(p, true)]
        );
        solver.assert_literal(p, false);
        assert!(solver.boolean_witness().next().is_none());
        assert!(solver.bounded_enum_model.is_none());
    }

    #[test]
    fn boolean_flip_reward_counts_duplicate_and_opposite_occurrences_together() {
        let mut terms = TermStore::new();
        let p = terms.mk_var("p", Sort::Bool);
        let mut builder = Builder::new(&terms);
        let clauses = builder.cnf(p, true, 0).expect("Boolean unit");
        let atom = clauses[0][0].atom;
        let positive = Lit {
            atom,
            negated: false,
        };
        let negative = Lit {
            atom,
            negated: true,
        };
        let mut search = Search::new(
            builder,
            vec![vec![positive, positive], vec![positive, negative]],
            0,
        );
        search.recompute_all();
        assert_eq!(
            search.boolean_reward(atom as usize, &mut || false),
            Some(INIT_WEIGHT)
        );
        assert!(search.move_boolean(&mut || false).is_some());
        assert!(search.unsat.is_empty());
        assert!(search.atoms[atom as usize].truth);
    }
}
