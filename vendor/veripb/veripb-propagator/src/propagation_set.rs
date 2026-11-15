//! Data structure for grouping specialized propagators together.
//!
//! Each specialized propagator in the group takes care of implementing the operations.

use std::rc::Rc;

use malachite_bigint::BigInt;
use veripb_formula::prelude::{DBConstraint, PBConstraintEnum};

use crate::{
    cardinality_watcher::CardinalityWatcher,
    clause_watcher::ClauseWatcher,
    error::PropagatorError,
    general_pb_watcher::GeneralPBWatcher,
    propagator::{PropagationResult, Propagator},
    trail::{Propagation, Trail},
};

/// A set of propagators that are logically grouped together.
///
/// Each set of propagators contains a propagator of each constraint type. For details on the implementation of each function refer to the implementation of [`Propagator`]. The responsibiity of [`PropagationSet`] is to forward each function call to each propagator in the set that implements this function.
#[derive(Debug, Default)]
pub struct PropagationSet {
    clause_prop: Propagator<ClauseWatcher>,
    card_prop: Propagator<CardinalityWatcher>,
    constraint_i64_prop: Propagator<GeneralPBWatcher<i64>>,
    constraint_i128_prop: Propagator<GeneralPBWatcher<i128>>,
    constraint_bigint_prop: Propagator<GeneralPBWatcher<BigInt>>,
}

impl PropagationSet {
    /// Construct a new propagation set with an initialized size.
    #[inline]
    pub fn with_size(num_variables: usize) -> Self {
        PropagationSet {
            clause_prop: Propagator::with_size(num_variables),
            card_prop: Propagator::with_size(num_variables),
            constraint_i64_prop: Propagator::with_size(num_variables),
            constraint_i128_prop: Propagator::with_size(num_variables),
            constraint_bigint_prop: Propagator::with_size(num_variables),
        }
    }

    /// Resize the propagators in the propagation set to the given size.
    #[inline]
    pub fn resize(&mut self, num_variables: usize) {
        self.clause_prop.resize(num_variables);
        self.card_prop.resize(num_variables);
        self.constraint_i64_prop.resize(num_variables);
        self.constraint_i128_prop.resize(num_variables);
        self.constraint_bigint_prop.resize(num_variables);
    }

    /// Add constraint to propagation set.
    #[inline]
    pub fn add(&mut self, constraint: &Rc<DBConstraint>) -> Result<(), PropagatorError> {
        match constraint.constraint {
            PBConstraintEnum::Clause(_) => self.clause_prop.add(constraint),
            PBConstraintEnum::Cardinality(_) => self.card_prop.add(constraint),
            PBConstraintEnum::GeneralPBI64(_) => self.constraint_i64_prop.add(constraint),
            PBConstraintEnum::GeneralPBI128(_) => self.constraint_i128_prop.add(constraint),
            PBConstraintEnum::GeneralPBBigInt(_) => self.constraint_bigint_prop.add(constraint),
        }
    }

    /// Remove constraint from propagation set.
    #[inline]
    pub fn remove(&mut self, constraint: &Rc<DBConstraint>) -> Result<(), PropagatorError> {
        match constraint.constraint {
            PBConstraintEnum::Clause(_) => self.clause_prop.remove(constraint),
            PBConstraintEnum::Cardinality(_) => self.card_prop.remove(constraint),
            PBConstraintEnum::GeneralPBI64(_) => self.constraint_i64_prop.remove(constraint),
            PBConstraintEnum::GeneralPBI128(_) => self.constraint_i128_prop.remove(constraint),
            PBConstraintEnum::GeneralPBBigInt(_) => self.constraint_bigint_prop.remove(constraint),
        }
    }

    /// Remove all constraints from this set and return the removed constraints.
    #[inline]
    pub fn remove_all(&mut self) -> Vec<Rc<DBConstraint>> {
        let mut constraints = Vec::new();
        self.clause_prop.remove_all(&mut constraints);
        self.card_prop.remove_all(&mut constraints);
        self.constraint_i64_prop.remove_all(&mut constraints);
        self.constraint_i128_prop.remove_all(&mut constraints);
        self.constraint_bigint_prop.remove_all(&mut constraints);
        constraints
    }

    /// Get the propagation at level zero from this set of constraints
    #[inline]
    pub fn get_assignment_independent_propagations(&mut self) -> Vec<Propagation> {
        let mut propagations = self
            .clause_prop
            .get_assignment_independent_propagations()
            .clone();
        propagations.extend_from_slice(
            self.card_prop
                .get_assignment_independent_propagations()
                .as_slice(),
        );
        propagations.extend_from_slice(
            self.constraint_i64_prop
                .get_assignment_independent_propagations()
                .as_slice(),
        );
        propagations.extend_from_slice(
            self.constraint_i128_prop
                .get_assignment_independent_propagations()
                .as_slice(),
        );
        propagations.extend_from_slice(
            self.constraint_bigint_prop
                .get_assignment_independent_propagations()
                .as_slice(),
        );

        propagations
    }

    /// Get the propagations at level zero from this set of constraints that have not been considered before, i.e., propagations from constraints that were added since the last proagations check.
    #[inline]
    pub fn get_new_assignment_independent_propagations(
        &mut self,
        new_propagations: &mut Vec<Propagation>,
    ) {
        self.clause_prop
            .get_new_assignment_independent_propagations(new_propagations);
        self.card_prop
            .get_new_assignment_independent_propagations(new_propagations);
        self.constraint_i64_prop
            .get_new_assignment_independent_propagations(new_propagations);
        self.constraint_i128_prop
            .get_new_assignment_independent_propagations(new_propagations);
        self.constraint_bigint_prop
            .get_new_assignment_independent_propagations(new_propagations);
    }

    /// Propagate all propagators in the propagation set until no further propagation is detected.
    #[inline]
    pub fn propagate(&mut self, trail: &mut Trail, mark_reasons: bool) -> PropagationResult {
        loop {
            let prev_len = trail.len();

            // Propagate propagators in order.
            if self
                .clause_prop
                .propagate(trail, mark_reasons, false)
                .is_conflict()
                || self
                    .card_prop
                    .propagate(trail, mark_reasons, false)
                    .is_conflict()
                || self
                    .constraint_i64_prop
                    .propagate(trail, mark_reasons, true)
                    .is_conflict()
                || self
                    .constraint_i128_prop
                    .propagate(trail, mark_reasons, true)
                    .is_conflict()
                || self
                    .constraint_bigint_prop
                    .propagate(trail, mark_reasons, true)
                    .is_conflict()
            {
                return PropagationResult::Conflict;
            }

            // Check if we had any propagation.
            if trail.len() == prev_len {
                return PropagationResult::Unknown;
            }
        }
    }

    /// Check if any constraint in the propagation set is used as a reason in the saved trail.
    #[inline]
    pub fn has_saved_reason(&self) -> bool {
        self.clause_prop.has_saved_reason()
            || self.card_prop.has_saved_reason()
            || self.constraint_i64_prop.has_saved_reason()
            || self.constraint_i128_prop.has_saved_reason()
            || self.constraint_bigint_prop.has_saved_reason()
    }

    /// Reset the propagation set. As only the general constraint propagators require a reset, the reset is only called for these propagators.
    #[inline]
    pub fn reset(&mut self, prev_trail_len: usize) {
        self.clause_prop.reset(prev_trail_len);
        self.card_prop.reset(prev_trail_len);
        self.constraint_i64_prop.reset(prev_trail_len);
        self.constraint_i128_prop.reset(prev_trail_len);
        self.constraint_bigint_prop.reset(prev_trail_len);
    }

    /// Reset the watches of all general constraints.
    #[inline]
    pub fn reset_watch(&mut self) {
        self.constraint_i64_prop.reset_watch();
        self.constraint_i128_prop.reset_watch();
        self.constraint_bigint_prop.reset_watch();
    }

    /// Clear the propagation set to delete all constraints in the propagation set.
    #[inline]
    pub fn clear(&mut self) {
        self.clause_prop.clear();
        self.card_prop.clear();
        self.constraint_i64_prop.clear();
        self.constraint_i128_prop.clear();
        self.constraint_bigint_prop.clear();
    }
}
