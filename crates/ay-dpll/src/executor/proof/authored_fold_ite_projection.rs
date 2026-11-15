// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Close an authored disequality to the ITE branch ACTUALLY selected by a
//! derived fact on this proof branch. No UF interpretation or SAT-variable
//! mapping is invented. The existing recognizer and complete-proof checker
//! independently judge the same intrinsic projection the printer exports.

use super::{same_set, Derived, Refuter};
use ay_core::{Sort, Symbol, TermData, TermId, TheoryLemmaKind};

impl Refuter<'_> {
    pub(super) fn refute_selected_ite(
        &mut self,
        equality: TermId,
        disequality: &Derived,
        side: &[TermId],
    ) -> Option<Derived> {
        let TermData::App(Symbol::Named(name), args) = self.terms.get(equality) else {
            return None;
        };
        if name != "=" || args.len() != 2 || self.terms.sort(equality) != &Sort::Bool {
            return None;
        }
        let (left, right) = (args[0], args[1]);
        for (ite, other) in [(left, right), (right, left)] {
            let TermData::Ite(condition, then_branch, else_branch) = self.terms.get(ite) else {
                continue;
            };
            let (condition, then_branch, else_branch) = (*condition, *then_branch, *else_branch);
            if self.terms.sort(condition) != &Sort::Bool
                || self.terms.sort(then_branch) != self.terms.sort(else_branch)
                || self.terms.sort(ite) != self.terms.sort(other)
                || self.terms.sort(ite) != self.terms.sort(then_branch)
            {
                continue;
            }
            for (positive, branch) in [(true, then_branch), (false, else_branch)] {
                if other != branch {
                    continue;
                }
                let not_condition = self.terms.mk_not_raw(condition);
                let required = if positive { condition } else { not_condition };
                let mut selected = None;
                for index in (0..self.facts.len()).rev() {
                    // A new search shares the ORIGINAL refutation budget,
                    // including unsuccessful fact visits.
                    self.spend()?;
                    if self.facts[index].0 == required {
                        selected = Some(index);
                        break;
                    }
                }
                let Some(index) = selected else { continue };
                self.budget = self.budget.checked_sub(self.facts[index].1.clause.len())?;
                let fact = self.facts[index].1.clone();
                let guard = if positive { not_condition } else { condition };
                let clause = vec![guard, equality];
                if !ay_proof::recognize_ite_branch_projection(self.terms, &clause) {
                    continue;
                }
                // One intrinsic lemma, then two resolutions. Preserve all
                // side literals and charge every new proof-building step.
                self.spend()?;
                let lemma = Derived {
                    id: self.proof.add_theory_lemma_with_kind(
                        "ite",
                        clause.clone(),
                        TheoryLemmaKind::IteBranchProjection,
                    ),
                    clause,
                };
                self.spend()?;
                let projected = if positive {
                    self.resolve(&lemma, &fact, condition)
                } else {
                    self.resolve(&fact, &lemma, condition)
                };
                self.spend()?;
                let closed = self.resolve(disequality, &projected, equality);
                if same_set(&closed.clause, side) {
                    return Some(closed);
                }
            }
        }
        None
    }
}

#[cfg(test)]
#[path = "authored_fold_ite_projection_tests.rs"]
mod tests;
