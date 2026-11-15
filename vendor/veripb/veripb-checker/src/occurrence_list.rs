//! [`OccurrenceList`] for mapping each literal to constraints containing this literal.

use std::rc::Rc;

use ahash::{HashSet, RandomState};
use by_address::ByAddress;
use veripb_formula::prelude::*;

/// Data structure to maintain mapping from literals to constraints containing this literal.
#[derive(Debug, Default)]
pub struct OccurrenceList {
    /// Vector indexed by the numeric representation of a literal mapping to a set of constraints.
    pub list: Vec<HashSet<ByAddress<Rc<DBConstraint>>>>,
}

impl OccurrenceList {
    /// Add a `constraint` to the [`OccurrenceList`] by adding a pointer to the constraint for each literal in the constraint to the corresponding set.
    #[inline]
    pub fn add(&mut self, constraint: &Rc<DBConstraint>) {
        match &constraint.constraint {
            PBConstraintEnum::Clause(clause) => {
                for lit in clause.get_lits() {
                    let index = lit.get_lit_data();
                    if index >= self.list.len() {
                        self.list.resize(
                            index + 1,
                            HashSet::with_hasher(RandomState::with_seeds(42, 42, 42, 42)),
                        );
                    }

                    self.list[index].insert(constraint.clone().into());
                }
            }
            PBConstraintEnum::Cardinality(cardinality) => {
                for lit in cardinality.get_lits() {
                    let index = lit.get_lit_data();
                    if index >= self.list.len() {
                        self.list.resize(
                            index + 1,
                            HashSet::with_hasher(RandomState::with_seeds(42, 42, 42, 42)),
                        );
                    }

                    self.list[index].insert(constraint.clone().into());
                }
            }
            PBConstraintEnum::GeneralPBI64(general_constraint) => {
                for lit in general_constraint.get_lits() {
                    let index = lit.get_lit_data();
                    if index >= self.list.len() {
                        self.list.resize(
                            index + 1,
                            HashSet::with_hasher(RandomState::with_seeds(42, 42, 42, 42)),
                        );
                    }

                    self.list[index].insert(constraint.clone().into());
                }
            }
            PBConstraintEnum::GeneralPBI128(general_constraint) => {
                for lit in general_constraint.get_lits() {
                    let index = lit.get_lit_data();
                    if index >= self.list.len() {
                        self.list.resize(
                            index + 1,
                            HashSet::with_hasher(RandomState::with_seeds(42, 42, 42, 42)),
                        );
                    }

                    self.list[index].insert(constraint.clone().into());
                }
            }
            PBConstraintEnum::GeneralPBBigInt(general_constraint) => {
                for lit in general_constraint.get_lits() {
                    let index = lit.get_lit_data();
                    if index >= self.list.len() {
                        self.list.resize(
                            index + 1,
                            HashSet::with_hasher(RandomState::with_seeds(42, 42, 42, 42)),
                        );
                    }

                    self.list[index].insert(constraint.clone().into());
                }
            }
        };

        constraint.header.borrow_mut().is_in_occurrences = true;
    }

    /// Remove the `constraint` from the [`OccurrenceList`] by removing it from all sets.
    #[inline]
    pub fn remove(&mut self, constraint: &Rc<DBConstraint>) {
        let constraint = ByAddress(constraint.clone());
        match &constraint.constraint {
            PBConstraintEnum::Clause(clause) => {
                for lit in clause.get_lits() {
                    self.list[lit.get_lit_data()].remove(&constraint);
                }
            }
            PBConstraintEnum::Cardinality(cardinality) => {
                for lit in cardinality.get_lits() {
                    self.list[lit.get_lit_data()].remove(&constraint);
                }
            }
            PBConstraintEnum::GeneralPBI64(general_constraint) => {
                for lit in general_constraint.get_lits() {
                    self.list[lit.get_lit_data()].remove(&constraint);
                }
            }
            PBConstraintEnum::GeneralPBI128(general_constraint) => {
                for lit in general_constraint.get_lits() {
                    self.list[lit.get_lit_data()].remove(&constraint);
                }
            }
            PBConstraintEnum::GeneralPBBigInt(general_constraint) => {
                for lit in general_constraint.get_lits() {
                    self.list[lit.get_lit_data()].remove(&constraint);
                }
            }
        }
    }

    /// Get the set of constraints that contain the literal `lit`.
    #[inline]
    pub fn get_constraints_for_lit(
        &self,
        lit: Lit,
    ) -> Option<&HashSet<ByAddress<Rc<DBConstraint>>>> {
        self.list.get(lit.get_lit_data())
    }

    /// Get a list of all literals that have at least once constraint registered in the [`OccurrenceList`].
    #[inline]
    pub fn get_used_vars(&self) -> Vec<VarIdx> {
        let mut vars = Vec::new();
        for (lit_idx, list) in self.list.iter().enumerate() {
            if !list.is_empty() {
                vars.push(lit_idx / 2);
            }
        }

        vars.dedup();
        vars
    }
}
