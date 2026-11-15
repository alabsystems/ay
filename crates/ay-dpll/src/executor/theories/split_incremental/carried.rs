// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Replay of carried theory conflicts into a lazy split loop
//! (`crate::executor::ground_solve_carry`).

use ay_core::kani_compat::DetHashMap as HashMap;
use ay_core::{TermId, TermStore, TheoryLit};
use ay_sat::Solver as SatSolver;

use crate::executor::ground_solve_carry::CarriedLiteral;
use crate::incremental_proof_cache::IncrementalNegationCache;

/// Add the blocking clause of every carried conflict this encoding can take.
///
/// A conflict is taken when each of its atoms that came from the assertions of
/// the solve that derived it has a SAT variable here. The atoms that solve
/// minted itself (split sides, model equalities) are encoded on the way in,
/// through the route a theory lemma's atoms take
/// ([`super::apply_theory_lemma_incremental`]). A conflict over an assertion
/// atom this problem does not have is skipped: nothing here would ever assert
/// that atom to the theory.
///
/// Every carried conflict is inconsistent in the theory by itself, so each
/// clause holds in every theory model and only removes assignments the theory
/// would refuse. The clauses are scoped like every other clause of the loop
/// and go when it pops its frame. Returns the clauses added.
pub(in crate::executor) fn replay_carried_conflicts(
    terms: &TermStore,
    solver: &mut SatSolver,
    local_term_to_var: &mut HashMap<TermId, u32>,
    local_var_to_term: &mut HashMap<u32, TermId>,
    local_next_var: &mut u32,
    negations: &mut IncrementalNegationCache,
    conflicts: &[Vec<CarriedLiteral>],
) -> usize {
    let mut clause: Vec<TheoryLit> = Vec::new();
    let mut added = 0usize;
    for conflict in conflicts {
        let has_foreign_atom = conflict
            .iter()
            .any(|lit| !lit.minted && !local_term_to_var.contains_key(&lit.literal.term));
        if has_foreign_atom {
            continue;
        }
        clause.clear();
        clause.extend(
            conflict
                .iter()
                .map(|lit| TheoryLit::new(lit.literal.term, !lit.literal.value)),
        );
        let _ = super::apply_theory_lemma_incremental(
            terms,
            solver,
            local_term_to_var,
            local_var_to_term,
            local_next_var,
            negations,
            &clause,
        );
        added += 1;
    }
    added
}

#[cfg(test)]
mod tests {
    use super::*;
    use ay_core::{Sort, Symbol};
    use ay_sat::{Literal as SatLiteral, Variable as SatVariable};

    /// `a = b`, `f(a) = f(b)` and the solver-minted `a < b` over integers.
    fn atoms(terms: &mut TermStore) -> (TermId, TermId, TermId) {
        let a = terms.mk_var("a", Sort::Int);
        let b = terms.mk_var("b", Sort::Int);
        let fa = terms.mk_app(Symbol::named("f"), vec![a], Sort::Int);
        let fb = terms.mk_app(Symbol::named("f"), vec![b], Sort::Int);
        (terms.mk_eq(a, b), terms.mk_eq(fa, fb), terms.mk_lt(a, b))
    }

    fn carried(literals: &[(TermId, bool, bool)]) -> Vec<CarriedLiteral> {
        literals
            .iter()
            .map(|&(term, value, minted)| CarriedLiteral {
                literal: TheoryLit::new(term, value),
                minted,
            })
            .collect()
    }

    struct Encoding {
        solver: SatSolver,
        term_to_var: HashMap<TermId, u32>,
        var_to_term: HashMap<u32, TermId>,
        next_var: u32,
        negations: IncrementalNegationCache,
    }

    /// An encoding that has one SAT variable per term of `base`, in order.
    fn encoding(terms: &mut TermStore, base: &[TermId]) -> Encoding {
        let mut solver = SatSolver::new(base.len());
        solver.push();
        Encoding {
            solver,
            term_to_var: base
                .iter()
                .enumerate()
                .map(|(var, &term)| (term, var as u32))
                .collect(),
            var_to_term: base
                .iter()
                .enumerate()
                .map(|(var, &term)| (var as u32, term))
                .collect(),
            next_var: base.len() as u32,
            negations: IncrementalNegationCache::seed(terms, base.iter().copied(), false),
        }
    }

    fn replay(terms: &TermStore, enc: &mut Encoding, conflicts: &[Vec<CarriedLiteral>]) -> usize {
        replay_carried_conflicts(
            terms,
            &mut enc.solver,
            &mut enc.term_to_var,
            &mut enc.var_to_term,
            &mut enc.next_var,
            &mut enc.negations,
            conflicts,
        )
    }

    fn unit(enc: &mut Encoding, term: TermId, value: bool) {
        let var = SatVariable::new(enc.term_to_var[&term]);
        enc.solver.add_clause(vec![if value {
            SatLiteral::positive(var)
        } else {
            SatLiteral::negative(var)
        }]);
    }

    #[test]
    fn a_replayed_conflict_blocks_its_assignment() {
        let mut terms = TermStore::new();
        let (a_eq_b, fa_eq_fb, _) = atoms(&mut terms);
        let conflict = carried(&[(a_eq_b, true, false), (fa_eq_fb, false, false)]);
        let mut enc = encoding(&mut terms, &[a_eq_b, fa_eq_fb]);
        assert_eq!(replay(&terms, &mut enc, &[conflict]), 1);
        unit(&mut enc, a_eq_b, true);
        unit(&mut enc, fa_eq_fb, false);
        assert!(enc.solver.solve().into_inner().is_unsat());
    }

    /// The one-line twin: the clause is the negation of the conflict and no
    /// more, so `a = b` with `f(a) = f(b)` stays open.
    #[test]
    fn a_replayed_conflict_leaves_other_assignments_open() {
        let mut terms = TermStore::new();
        let (a_eq_b, fa_eq_fb, _) = atoms(&mut terms);
        let conflict = carried(&[(a_eq_b, true, false), (fa_eq_fb, false, false)]);
        let mut enc = encoding(&mut terms, &[a_eq_b, fa_eq_fb]);
        assert_eq!(replay(&terms, &mut enc, &[conflict]), 1);
        unit(&mut enc, a_eq_b, true);
        unit(&mut enc, fa_eq_fb, true);
        assert!(enc.solver.solve().into_inner().is_sat());
    }

    #[test]
    fn a_minted_atom_is_encoded_on_the_way_in() {
        let mut terms = TermStore::new();
        let (a_eq_b, _, a_lt_b) = atoms(&mut terms);
        // `a = b` came from the assertions, `a < b` from a split.
        let conflict = carried(&[(a_eq_b, true, false), (a_lt_b, true, true)]);
        let mut enc = encoding(&mut terms, &[a_eq_b]);
        assert!(!enc.term_to_var.contains_key(&a_lt_b));
        assert_eq!(replay(&terms, &mut enc, &[conflict]), 1);
        assert!(enc.term_to_var.contains_key(&a_lt_b));
        unit(&mut enc, a_eq_b, true);
        unit(&mut enc, a_lt_b, true);
        assert!(enc.solver.solve().into_inner().is_unsat());
    }

    /// The twin of the test above: the same conflict, but the atom this
    /// encoding lacks came from the assertions of another problem. A clause
    /// over the rest would assert `not (a < b)`, which no theory proved.
    #[test]
    fn a_conflict_over_a_foreign_assertion_atom_is_skipped() {
        let mut terms = TermStore::new();
        let (a_eq_b, _, a_lt_b) = atoms(&mut terms);
        let conflict = carried(&[(a_eq_b, true, false), (a_lt_b, true, true)]);
        let mut enc = encoding(&mut terms, &[a_lt_b]);
        assert_eq!(replay(&terms, &mut enc, &[conflict]), 0);
        assert!(!enc.term_to_var.contains_key(&a_eq_b));
        unit(&mut enc, a_lt_b, true);
        assert!(enc.solver.solve().into_inner().is_sat());
    }
}
