// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! In-search effects of an extension (design the development design notes,
//! §3.10, G1-G4):
//!
//! - G1: irredundant definitions ([`Solver::add_theory_definition`]).
//! - G2: final-check lemmas added at the current decision level
//!   ([`ExtCheckResult::Continue`]), with no restart.
//! - G3: every variable an extension result names beyond the solver's range is
//!   created before any literal of the result is examined, and frozen.
//! - G4: the extension sees each heuristic decision (`on_decide`) and, if it
//!   asks, each learned clause (`on_learned`).

use super::super::*;
use super::theory_callback::TheoryCallback;

/// One past the largest variable index named by `clauses`.
fn var_bound<'a>(clauses: impl IntoIterator<Item = &'a Vec<Literal>>) -> usize {
    clauses
        .into_iter()
        .flat_map(|clause| clause.iter())
        .map(|lit| lit.variable().index() + 1)
        .max()
        .unwrap_or(0)
}

impl Solver {
    /// Grow the solver to `num_vars` variables and freeze every variable the
    /// growth creates (G3): inprocessing must never eliminate a variable an
    /// extension minted, because the extension names it by index.
    pub(in crate::solver) fn grow_for_extension_vars(&mut self, num_vars: usize) {
        let old = self.num_vars;
        if num_vars <= old {
            return;
        }
        self.ensure_num_vars(num_vars);
        for idx in old..self.num_vars {
            if let Ok(raw) = u32::try_from(idx) {
                self.freeze(Variable(raw));
            }
        }
    }

    /// G3 for a propagate result: create every variable it names, frozen,
    /// before any literal of it is tested against the assignment.
    pub(in crate::solver) fn grow_for_extension_result(&mut self, result: &ExtPropagateResult) {
        let mut bound = result.num_vars;
        bound = bound.max(var_bound(&result.clauses));
        bound = bound.max(var_bound(&result.definitions));
        bound = bound.max(var_bound(result.conflict.iter()));
        bound = bound.max(var_bound(result.propagations.iter().map(|(c, _)| c)));
        for (_, lit) in &result.propagations {
            bound = bound.max(lit.variable().index() + 1);
        }
        for (lit, _) in &result.lazy_propagations {
            bound = bound.max(lit.variable().index() + 1);
        }
        self.grow_for_extension_vars(bound);
    }

    /// G3 then G1 for a propagate result: grow, then add the definitions it
    /// carries. Definitions are never dropped, whatever else the result holds.
    pub(in crate::solver) fn apply_extension_growth_and_definitions(
        &mut self,
        result: &mut ExtPropagateResult,
    ) {
        self.grow_for_extension_result(result);
        for clause in std::mem::take(&mut result.definitions) {
            self.add_theory_definition(clause);
        }
    }

    /// Add an irredundant clause during solving (design G1).
    ///
    /// Same watch, unit and falsified-clause handling as
    /// [`Solver::add_theory_lemma`], but the clause is never deleted: it goes
    /// to the irredundant tier and to the original ledger as a global clause,
    /// so neither `reduce_db`, a user `pop` nor a destructive rebuild from the
    /// ledger removes it. For a definition of a symbol the caller introduced
    /// (a Tseitin definition of a minted atom, a Skolem, an instance), which
    /// nothing would derive again.
    pub fn add_theory_definition(&mut self, mut literals: Vec<Literal>) -> Option<ClauseRef> {
        literals.sort_by_key(|l| l.0);
        literals.dedup();
        if literals
            .windows(2)
            .any(|pair| pair[0].variable() == pair[1].variable())
        {
            return None; // a tautology defines nothing
        }
        self.grow_for_extension_vars(var_bound(std::iter::once(&literals)));
        self.cold.original_ledger.push_clause_global(&literals);
        self.cold.incremental_original_boundary = self.cold.original_ledger.num_clauses();
        self.cold.uniform_formula_cache = None;
        let Some(clause_ref) = self.add_theory_lemma(literals) else {
            // Census (#l0-rebuild-epoch): the definition is in the
            // ledger but stored no arena clause (e.g. unit already
            // true at root); the next rebuild materializes it.
            self.cold.ledger_only_since_rebuild =
                self.cold.ledger_only_since_rebuild.saturating_add(1);
            return None;
        };
        let idx = clause_ref.0 as usize;
        let clause_id = self.clause_id(clause_ref);
        self.cold
            .original_ledger
            .bind_last_global_clause_id(clause_id);
        if let Some(manager) = self.proof_manager.as_mut() {
            manager.retain_ledger_original_id(clause_id);
        }
        if self.arena.is_active(idx) && self.arena.is_learned(idx) {
            self.arena.set_learned(idx, false);
            let lits: Vec<Literal> = self.arena.literals(idx).to_vec();
            self.note_clause_promoted_to_irredundant(idx, &lits);
        }
        Some(clause_ref)
    }

    /// G2: add final-check lemmas at the current decision level.
    ///
    /// A lemma that is false under the current assignment is a conflict: the
    /// first such lemma is handled exactly like a conflict from `propagate`
    /// (backjump to its asserting level, learn it). The definitions and the
    /// remaining lemmas are then added at the resulting level, where
    /// `add_theory_lemma` enqueues units and queues any lemma that is still
    /// falsified as a pending conflict. Returns `Some` when the answer is known.
    pub(in crate::solver) fn apply_final_check_continue<C: TheoryCallback>(
        &mut self,
        callback: &mut C,
        cont: ExtContinue,
    ) -> Option<SatResult> {
        let ExtContinue {
            mut lemmas,
            definitions,
            num_vars,
        } = cont;
        let bound = num_vars
            .max(var_bound(&lemmas))
            .max(var_bound(&definitions));
        self.grow_for_extension_vars(bound);
        let falsified = if self.decision_level > 0 {
            lemmas.iter().position(|clause| {
                !clause.is_empty() && clause.iter().all(|&lit| self.lit_val(lit) < 0)
            })
        } else {
            None
        };
        if let Some(pos) = falsified {
            let conflict = lemmas.swap_remove(pos);
            if let Some(result) = callback.handle_conflict_clause(self, conflict) {
                return Some(result);
            }
        }
        for clause in definitions {
            self.add_theory_definition(clause);
        }
        for clause in lemmas {
            self.add_theory_lemma(clause);
        }
        if falsified.is_some() && !self.has_empty_clause {
            self.maybe_run_restart(callback);
        }
        None
    }

    /// Materialize lazy reasons, analyze a conflict and backjump, then hand the
    /// learned clause to the callback if it asked for learned clauses (G4).
    pub(in crate::solver) fn analyze_theory_conflict<C: TheoryCallback>(
        &mut self,
        conflict_ref: ClauseRef,
        callback: &mut C,
    ) {
        // #8467: pre-materialize lazy theory reasons at the current decision
        // level so 1UIP resolution never encounters them.
        callback.materialize_lazy_reasons(self);
        let context = callback.conflict_context();
        let wants_learned = callback.wants_learned();
        let mut learned: Option<Vec<Literal>> = None;
        self.analyze_and_backtrack_with_core_hook(
            conflict_ref,
            context,
            |solver, level| callback.backtrack_after_materializing_lazy_reasons(solver, level),
            |_, clause, _| {
                if wants_learned {
                    learned = Some(clause.to_vec());
                }
            },
        );
        if let Some(clause) = learned {
            callback.on_learned(&clause);
        }
    }

    /// G4: the literal to decide once an extension has seen the heuristic's
    /// pick. An alternative over a variable beyond the range is created, frozen
    /// (G3); an alternative that is already assigned is ignored.
    pub(in crate::solver) fn extension_decision(
        &mut self,
        picked: Literal,
        alternative: Option<Literal>,
    ) -> Literal {
        let Some(alt) = alternative else {
            return picked;
        };
        self.grow_for_extension_vars(alt.variable().index() + 1);
        if self.var_is_assigned(alt.variable().index()) {
            picked
        } else {
            alt
        }
    }
}
