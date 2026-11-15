//! Main frontend data structure for interacting with the propagator crate.

use std::{collections::VecDeque, num::NonZeroUsize, rc::Rc};

use colored::Colorize;
use veripb_formula::{prelude::*, propagation::RUPHint};

use crate::{
    error::PropagatorError,
    propagation_set::PropagationSet,
    propagator::PropagationResult,
    trail::{Propagation, Reason, Trail},
};

pub const CORE_CLAUSES_CARD: usize = 0;
pub const CORE_GENERAL: usize = 1;
pub const DERIVED_CLAUSES_CARD: usize = 2;
pub const DERIVED_GENERAL: usize = 3;

/// Storage of what parts of a trail should be saved.
#[derive(Debug, Default)]
struct TrailLevel {
    /// The trail up until this position should be kept.
    level: usize,
    /// If [`true`], the conflict should be kept.
    conflict: bool,
}

/// The [`PropagationEngine`] keeps track of the known propagation sets.
///
/// This data structure maintains the propagation sets and provides helpful functions for checks involving unit propagation.
///
/// # Invariants
/// The propagation engine mainly ensures invariants about the validity of the trail by initializing the trail before propagation.
/// 1. Before propagating the trail, the trail only contains propagations from the currently enabled propagators.
///
/// 2. Ensure that the trail after propagation contains all possible propagations from the currently enabled propagators.
///    This is implied by invariant 5. of the propagator, which says that the trail contains all propagations implied by the trail up to trail_head,
///    and the fact that propagation only stops when the trail_head matches the length of the trail.
///
/// If a literal l is removed from the trail (because its reason is deleted), and l was a satisfied watch of a constraint D, then D may now have a
/// falsified watch and unassigned watches, and hence D potentially propagates. This can both happen for watches that have been set during
/// [`init_watches`](crate::watcher::Watchable::init_watches()) or [`update_watch`](crate::watcher::Watchable::update_watch()). To ensure that these
/// propagations are detected (and that invariant 5. of the propagator is preserved), the trail_head of the propagators must be reset.
#[derive(Debug, Default)]
pub struct PropagationEngine {
    /// Current propagation trail.
    trail: Trail,
    /// Storage of propagations sets.
    propagation_sets: Vec<Option<PropagationSet>>,
    /// Temporary propagation set used for temporary constraints like the negated constraint in a RUP check.
    temp_propagation_set: PropagationSet,
    /// The order in which to propagate the propagation sets of the propagator.
    /// If the constraint set is not in the order, then the propagation set is deactivated.
    propagation_order: VecDeque<usize>,
    /// If `added` is `true`, then a constraint was added to the propagator and the saved trail might be reconstructed.
    added: bool,
    /// If `true`, then the current saved trail is only with respect to core constraints.
    pub only_core_trail: bool,
    /// The previously saved level.
    saved_level: TrailLevel,
    /// If `true`, then a saved reason has been detached since last propagation.
    saved_reason_detached: bool,
    pub rup_hints: Vec<RUPHint>,
    /// If `true`, a [`KernelCertificate`] is captured for every conflicting
    /// RUP check (before the trail is unwound), so the caller can replay the
    /// propagation through the proved kernel.
    pub collect_kernel_certificate: bool,
    /// The certificate of the most recent conflicting RUP check, if
    /// collection is enabled. Callers take it; a stale value is overwritten
    /// by the next conflicting check.
    pub kernel_certificate: Option<KernelCertificate>,
}

/// A replayable record of a conflicting propagation run: every trail entry
/// with its reason, and the conflicting constraint. This is exactly the
/// shape the proved kernel's RUP replay (`veripb-core-proved`) validates.
#[derive(Debug, Clone)]
pub struct KernelCertificate {
    /// The propagations in trail order, each with its reason.
    /// [`Reason::Assumption`] entries mark literals the kernel replay cannot
    /// justify from constraints; their presence makes the certificate
    /// unverifiable (callers should count, not fail).
    pub steps: Vec<(Reason, Lit)>,
    /// The reason of the conflict.
    pub conflict: Reason,
    /// The temporarily added negated conclusion, if one was added; the
    /// kernel replay maps this constraint to its own guarded negation of the
    /// conclusion.
    pub negated: Option<Rc<DBConstraint>>,
}

impl PropagationEngine {
    /// Construct a new propagation set inside the propagation engine.
    #[inline]
    pub fn add_set(&mut self) -> usize {
        self.propagation_sets.push(Some(PropagationSet::default()));
        self.propagation_sets.len() - 1
    }

    /// Remove a propagation set from the propagation engine.
    #[inline]
    pub fn remove_set(&mut self, idx: usize) {
        self.propagation_sets[idx] = None;
    }

    /// Clears the specified propagation set.
    #[inline]
    pub fn clear_set(&mut self, idx: usize) {
        self.propagation_sets[idx].as_mut().unwrap().clear();
    }

    /// The number of propagation sets known to the propagation engine. This number does **not** include deleted propagation sets.
    #[inline]
    pub fn number_of_sets(&self) -> usize {
        self.propagation_sets
            .iter()
            .filter(|set| set.is_some())
            .count()
    }

    /// Attach a constraint to a specific propagation set.
    #[inline]
    pub fn attach_checker(
        &mut self,
        is_core: bool,
        constraint: &Rc<DBConstraint>,
    ) -> Result<(), PropagatorError> {
        if is_core {
            match constraint.constraint {
                PBConstraintEnum::Clause(_) => self.attach(CORE_CLAUSES_CARD, constraint),
                PBConstraintEnum::Cardinality(_) => self.attach(CORE_CLAUSES_CARD, constraint),
                PBConstraintEnum::GeneralPBI64(_) => self.attach(CORE_GENERAL, constraint),
                PBConstraintEnum::GeneralPBI128(_) => self.attach(CORE_GENERAL, constraint),
                PBConstraintEnum::GeneralPBBigInt(_) => self.attach(CORE_GENERAL, constraint),
            }
        } else {
            match constraint.constraint {
                PBConstraintEnum::Clause(_) => self.attach(DERIVED_CLAUSES_CARD, constraint),
                PBConstraintEnum::Cardinality(_) => self.attach(DERIVED_CLAUSES_CARD, constraint),
                PBConstraintEnum::GeneralPBI64(_) => self.attach(DERIVED_GENERAL, constraint),
                PBConstraintEnum::GeneralPBI128(_) => self.attach(DERIVED_GENERAL, constraint),
                PBConstraintEnum::GeneralPBBigInt(_) => self.attach(DERIVED_GENERAL, constraint),
            }
        }
    }

    /// Remove a constraint from a specific propagation set.
    #[inline]
    pub fn detach_checker(
        &mut self,
        is_core: bool,
        constraint: &Rc<DBConstraint>,
        poison: bool,
    ) -> Result<(), PropagatorError> {
        if is_core {
            match constraint.constraint {
                PBConstraintEnum::Clause(_) => self.detach(CORE_CLAUSES_CARD, constraint, poison),
                PBConstraintEnum::Cardinality(_) => {
                    self.detach(CORE_CLAUSES_CARD, constraint, poison)
                }
                PBConstraintEnum::GeneralPBI64(_) => self.detach(CORE_GENERAL, constraint, poison),
                PBConstraintEnum::GeneralPBI128(_) => self.detach(CORE_GENERAL, constraint, poison),
                PBConstraintEnum::GeneralPBBigInt(_) => {
                    self.detach(CORE_GENERAL, constraint, poison)
                }
            }
        } else {
            match constraint.constraint {
                PBConstraintEnum::Clause(_) => {
                    self.detach(DERIVED_CLAUSES_CARD, constraint, poison)
                }
                PBConstraintEnum::Cardinality(_) => {
                    self.detach(DERIVED_CLAUSES_CARD, constraint, poison)
                }
                PBConstraintEnum::GeneralPBI64(_) => {
                    self.detach(DERIVED_GENERAL, constraint, poison)
                }
                PBConstraintEnum::GeneralPBI128(_) => {
                    self.detach(DERIVED_GENERAL, constraint, poison)
                }
                PBConstraintEnum::GeneralPBBigInt(_) => {
                    self.detach(DERIVED_GENERAL, constraint, poison)
                }
            }
        }
    }

    /// Attach a constraint to a specific propagation set.
    #[inline]
    pub fn attach(
        &mut self,
        idx: usize,
        constraint: &Rc<DBConstraint>,
    ) -> Result<(), PropagatorError> {
        self.propagation_sets[idx]
            .as_mut()
            .unwrap()
            .add(constraint)?;
        self.added = true;
        Ok(())
    }

    /// Remove a constraint from a specific propagation set.
    #[inline]
    pub fn detach(
        &mut self,
        idx: usize,
        constraint: &Rc<DBConstraint>,
        poison: bool,
    ) -> Result<(), PropagatorError> {
        if poison && constraint.header.borrow().is_saved_reason {
            self.saved_reason_detached = true;
        }
        self.propagation_sets[idx]
            .as_mut()
            .unwrap()
            .remove(constraint)?;
        Ok(())
    }

    /// Move single constraint from one propagator to another propagator that is active.
    #[inline]
    pub fn move_constraint_checker(
        &mut self,
        is_from_core: bool,
        is_to_core: bool,
        constraint: &Rc<DBConstraint>,
    ) -> Result<(), PropagatorError> {
        self.detach_checker(is_from_core, constraint, false)?;
        self.attach_checker(is_to_core, constraint)?;
        Ok(())
    }

    /// Move single constraint from one propagator to another propagator that is active.
    #[inline]
    pub fn move_constraint(
        &mut self,
        from: usize,
        to: usize,
        constraint: &Rc<DBConstraint>,
    ) -> Result<(), PropagatorError> {
        debug_assert!(self.is_enabled(to));
        self.detach(from, constraint, false)?;
        self.attach(to, constraint)?;
        Ok(())
    }

    /// Move all constraints from one propagator to another propagator that is active.
    #[inline]
    pub fn move_all_constraints(&mut self, from: usize, to: usize) -> Result<(), PropagatorError> {
        debug_assert!(self.is_enabled(to));
        for constraint in self.propagation_sets[from]
            .as_mut()
            .unwrap()
            .remove_all()
            .iter()
        {
            self.propagation_sets[to]
                .as_mut()
                .unwrap()
                .add(constraint)?;
        }
        self.added = true;
        Ok(())
    }

    /// Check if the propagation set is enabled.
    #[inline]
    pub fn is_enabled(&self, idx: usize) -> bool {
        self.propagation_order.contains(&idx)
    }

    /// Get the position of the propagation set in the propagation order.
    ///
    /// If the propagator is not enabled, then `None` is returned.
    #[inline]
    pub fn get_position(&self, idx: usize) -> Option<usize> {
        self.propagation_order.iter().position(|&i| i == idx)
    }

    /// Enable the propagation set and add it to the start of the propagation order.
    ///
    /// If the propagation set is already enabled in the propagation order, then the propagation set is moved to the front.
    #[inline]
    pub fn enable_front(&mut self, idx: usize) {
        self.disable(idx);
        self.propagation_order.push_front(idx);
    }

    /// Enable the propagation set and add it to the back of the propagation order.
    ///
    /// If the propagation set is already enabled in the propagation order, then the propagation set is moved to the back.
    #[inline]
    pub fn enable_back(&mut self, idx: usize) {
        self.disable(idx);
        self.propagation_order.push_back(idx);
    }

    /// Remove the propagation set from the propagation order.
    ///
    /// This disables this propagation set for the engine. This does **not** delete the propagation set from the propagation engine so that it can be reenabled later on.
    #[inline]
    pub fn disable(&mut self, idx: usize) {
        // Remove from propagation order if it is enabled.
        if let Some(pos) = self.get_position(idx) {
            if let Some(propagation_set) = &mut self.propagation_sets[idx] {
                if propagation_set.has_saved_reason() {
                    self.saved_reason_detached = true;
                }
                propagation_set.reset(0);
            }
            self.propagation_order.remove(pos);
        }
    }

    /// Propagate the enabled propagation sets in order until a fix point is reached.
    ///
    /// This function propagates the enabled propagation sets in the specified propagation order.
    pub fn propagate(&mut self, using_temp: bool, mark_reasons: bool) -> PropagationResult {
        let mut prev_trail_length = self.trail.len();
        loop {
            if using_temp
                && self
                    .temp_propagation_set
                    .propagate(&mut self.trail, false)
                    .is_conflict()
            {
                return PropagationResult::Conflict;
            }
            for &idx in self.propagation_order.iter() {
                if self.propagation_sets[idx]
                    .as_mut()
                    .unwrap()
                    .propagate(&mut self.trail, mark_reasons)
                    .is_conflict()
                {
                    return PropagationResult::Conflict;
                }
            }
            if prev_trail_length == self.trail.len() {
                break;
            }
            prev_trail_length = self.trail.len();
        }

        PropagationResult::Unknown
    }

    /// Propagate the enabled propagation sets in order, always ensure the earliest propagation
    /// set is fully propagated before trying the next one.
    pub fn propagate_with_precedence(
        &mut self,
        using_temp: bool,
        mark_reasons: bool,
    ) -> PropagationResult {
        let mut prev_trail_length: usize;
        'outer: loop {
            prev_trail_length = self.trail.len();
            if using_temp
                && self
                    .temp_propagation_set
                    .propagate(&mut self.trail, false)
                    .is_conflict()
            {
                return PropagationResult::Conflict;
            }

            for &idx in self.propagation_order.iter() {
                if self.propagation_sets[idx]
                    .as_mut()
                    .unwrap()
                    .propagate(&mut self.trail, mark_reasons)
                    .is_conflict()
                {
                    return PropagationResult::Conflict;
                }

                if self.trail.len() != prev_trail_length {
                    continue 'outer;
                }
            }

            if prev_trail_length == self.trail.len() {
                break;
            }
        }

        PropagationResult::Unknown
    }

    /// Get all assignments independent of propagation for the currently enabled propagators.
    pub fn get_assignment_independent_propagations(
        &mut self,
        using_temp: bool,
    ) -> Vec<Propagation> {
        let mut propagations = Vec::new();

        if using_temp {
            propagations.append(
                &mut self
                    .temp_propagation_set
                    .get_assignment_independent_propagations(),
            );
        }

        for &idx in self.propagation_order.iter() {
            propagations.append(
                &mut self.propagation_sets[idx]
                    .as_mut()
                    .unwrap()
                    .get_assignment_independent_propagations(),
            );
        }

        propagations
    }

    /// Get assignment independent propagations for all constraints that have been added since assignment independent propagations have been requested the last time.
    pub fn get_new_assignment_independent_propagations(&mut self) -> Vec<Propagation> {
        let mut new_propagations = Vec::new();

        for &idx in self.propagation_order.iter() {
            self.propagation_sets[idx]
                .as_mut()
                .unwrap()
                .get_new_assignment_independent_propagations(&mut new_propagations);
        }

        new_propagations
    }

    /// Reset all enabled propagators. to the given `prev_trail_len`.
    pub fn reset_active_sets(&mut self, prev_trail_len: usize) {
        for &idx in self.propagation_order.iter() {
            self.propagation_sets[idx]
                .as_mut()
                .unwrap()
                .reset(prev_trail_len)
        }
    }

    /// Resize the propagation sets to the given `num_variables` so that watchlist can store watches up to given number of variables.
    pub fn resize_sets(&mut self, num_variables: usize) {
        self.temp_propagation_set.resize(num_variables);
        for set in self.propagation_sets.iter_mut().flatten() {
            set.resize(num_variables);
        }
    }

    /// Negate the `constraint` and add the negated constraint to the temporary propagation set.
    fn temporarily_add_negated_constraint(
        &mut self,
        constraint: &Rc<DBConstraint>,
        collect_hints: bool,
    ) -> Result<Rc<DBConstraint>, PropagatorError> {
        // Negate the desired constraint.
        let negated_constraint = Rc::new(DBConstraint::from(constraint.constraint.negate()));
        if collect_hints {
            // 0 is a special ID used for the negated constraint
            negated_constraint.set_out_id(0, 0);
        }
        match self.temp_propagation_set.add(&negated_constraint) {
            Ok(_) | Err(PropagatorError::AttachingAttached) => Ok(negated_constraint),
            Err(error) => Err(error),
        }
    }

    /// Record a [`KernelCertificate`] for the current (conflicting) trail,
    /// if collection is enabled. Must run before the trail is unwound.
    fn capture_kernel_certificate(&mut self, negated: Option<Rc<DBConstraint>>) {
        if !self.collect_kernel_certificate {
            return;
        }
        self.kernel_certificate = self
            .trail
            .conflict
            .clone()
            .map(|conflict| KernelCertificate {
                steps: self
                    .trail
                    .trail
                    .iter()
                    .map(|p| (p.reason.clone(), p.lit))
                    .collect(),
                conflict,
                negated,
            });
    }

    /// Initialize the trail so that it only contains propagations that are valid, where valid propagations are
    /// 1. from constraints that are not deleted; and
    /// 2. from propagators that are enabled.
    ///
    /// Afterwards all enabled propagators, except for the temporary propagator, propagate to get all non-temporary propagation that could be stored in a saved trail. So this function does the following steps:
    /// 1. Disable/Enable propagators if needed.
    /// 2. Rebuild trail if invalid.
    /// 3. Add assignment independent propagations from new constraints that were not available in the last propagation.
    /// 4. Propagate enabled propagators until completion.
    /// 5. Save current trail.
    #[inline]
    fn init_trail(
        &mut self,
        num_vars: usize,
        only_core: bool,
        collect_hints: bool,
    ) -> PropagationResult {
        self.resize_sets(num_vars);
        self.trail.resize(num_vars);

        // 1. Disable/Enable propagators if needed.
        // This might make propagations on the trail invalid.
        let mut derived_just_enabled = false;
        match (self.only_core_trail, only_core) {
            (false, true) => {
                // Change from core+derived propagation to only core propagation.
                self.only_core_trail = true;
                self.disable(DERIVED_CLAUSES_CARD);
                self.disable(DERIVED_GENERAL);
            }
            (true, false) => {
                // Change from only core propagation to core+derived propagation.
                self.only_core_trail = false;
                self.enable_back(DERIVED_CLAUSES_CARD);
                self.enable_back(DERIVED_GENERAL);
                derived_just_enabled = true;
            }
            _ => {}
        }
        let prev_trail_len = self.trail.len();

        // 2. Rebuild trail if invalid.
        let mut propagate = if self.saved_reason_detached {
            if self.unpoison(only_core) {
                // Note: unpoison (indirectly) calls reset_watch, making sure that every watcher again considers each literal for propagation.

                // Ensure that we do not miss a propagation if removed propagations did actually satisfy a constraint that propagates now.
                // IMPORTANT: This insures invariant 2. (and invariant 5. of the propagator) by reconsidering all assignments on the trail again.
                self.reset_active_sets(0);

                // Get assignment independent propagations for rebuilding trail.
                // WARNING: if rewriting this, careful with the short-circuiting semantics!
                if self.trail.is_conflicting()
                    || self
                        .get_assignment_independent_propagations(false)
                        .into_iter()
                        .any(|propagation| self.trail.push(propagation, true).is_err())
                {
                    self.analyze(collect_hints);
                    return PropagationResult::Conflict;
                }

                self.added = false;

                true
            } else {
                self.reset_active_sets(prev_trail_len);
                false
            }
        } else {
            self.reset_active_sets(prev_trail_len);
            false
        };

        // 3. Add assignment independent propagations from new constraints that were not available in the last propagation.
        if derived_just_enabled {
            // Reset watches of derived constraints since they may propagate literals that were removed from the trail.
            // This is required since there may be unreset watches if the last RUP check did not propagate on the negated conclusion.
            self.propagation_sets[DERIVED_GENERAL]
                .as_mut()
                .unwrap()
                .reset_watch();

            // Add propagations that may have been removed after core only propagation.
            if self.propagation_sets[DERIVED_CLAUSES_CARD]
                .as_mut()
                .unwrap()
                .get_assignment_independent_propagations()
                .iter()
                .any(|propagation| self.trail.push(propagation.clone(), true).is_err())
                || self.propagation_sets[DERIVED_GENERAL]
                    .as_mut()
                    .unwrap()
                    .get_assignment_independent_propagations()
                    .iter()
                    .any(|propagation| self.trail.push(propagation.clone(), true).is_err())
            {
                self.analyze(collect_hints);
                return PropagationResult::Conflict;
            }
            propagate = true;
        }
        if self.added {
            self.added = false;
            // Get level zero propagations of newly added constraints.
            if self
                .get_new_assignment_independent_propagations()
                .into_iter()
                .any(|propagation| self.trail.push(propagation, true).is_err())
            {
                self.analyze(collect_hints);
                return PropagationResult::Conflict;
            }

            propagate = true;
        };

        // 4. Propagate enabled propagators until completion.
        // WARNING: if rewriting this, careful with the short-circuiting semantics!
        let conflict = self.trail.is_conflicting()
            || (propagate && self.propagate_with_precedence(false, true).is_conflict());

        if conflict {
            self.analyze(collect_hints);
            return PropagationResult::Conflict;
        }

        // 5. Save current trail.
        self.save_level();

        PropagationResult::Unknown
    }

    /// Preform a reverse unit propagation check.
    ///
    /// The `conclusion` is what we want to show with this check. If `conclusion` is [`None`], then contradiction should be implied by unit propagation. If `conclusion` is [`Some`], then the given constraint should be implied by RUP.
    ///
    /// Further temporary premises for the propagation can be specified as `assumptions`.
    ///
    /// The options `only_core` specifies that only core constraints should be proapgated. The `proof_buf` is the optional proof buffer used for elaborating the RUP hints. The option `trace_failed` enables printing the trail if the RUP check is not successful.
    pub fn reverse_unit_propagation_check(
        &mut self,
        var_names: &VarNameManager,
        assumptions: &[Rc<DBConstraint>],
        conclusion: Option<&Rc<DBConstraint>>,
        only_core: bool,
        collect_hints: bool,
        trace_failed: bool,
    ) -> Result<PropagationResult, PropagatorError> {
        if collect_hints {
            self.rup_hints.clear();
        }
        if self.collect_kernel_certificate {
            self.kernel_certificate = None;
        }

        // Check if conclusion is trivial.
        if let Some(constraint) = conclusion
            && constraint.is_trivial()
        {
            if collect_hints {
                self.rup_hints.push(RUPHint::NegatedPremise)
            }
            return Ok(PropagationResult::Conflict);
        }

        // Reset the trail without considering the conclusion.
        if self
            .init_trail(var_names.len(), only_core, collect_hints)
            .is_conflict()
        {
            self.capture_kernel_certificate(None);
            return Ok(PropagationResult::Conflict);
        };

        assumptions.iter().try_for_each(|constraint| {
            match self.temp_propagation_set.add(constraint) {
                Ok(_) | Err(PropagatorError::AttachingAttached) => Ok(()),
                Err(err) => Err(err),
            }
        })?;

        let mut negated = None;
        if let Some(c) = conclusion {
            negated = Some(self.temporarily_add_negated_constraint(c, collect_hints)?);
            self.temp_propagation_set.reset(self.trail.len());
        }

        let conflict = {
            // WARNING: if rewriting this, careful with the short-circuiting semantics!
            let zero_conflict = self
                .temp_propagation_set
                .get_assignment_independent_propagations()
                .iter()
                .any(|propagation| self.trail.push(propagation.clone(), false).is_err());
            zero_conflict || self.propagate_with_precedence(true, false).is_conflict()
        };

        let result = if conflict {
            self.analyze(collect_hints);
            self.capture_kernel_certificate(negated);
            PropagationResult::Conflict
        } else {
            if trace_failed {
                self.trace_failed(var_names);
            }
            PropagationResult::Unknown
        };

        self.temp_propagation_set.clear();
        // Restore trail to previous level.
        self.load_level();

        Ok(result)
    }

    /// Analyze the propagation trail to generate hints for reverse unit propagation.
    ///
    /// This function expects that the `trail` is contradicting.
    #[inline]
    fn analyze(&mut self, collect_hints: bool) {
        if !collect_hints {
            return;
        }
        let mut output_ids = Vec::new();
        let mut relevant_assignment: Assignment<BooleanVar> =
            Assignment::with_size(self.trail.assignment.len());

        // Analyze the conflicting constraint.
        let conflict_constraint = self.trail.conflict.as_ref().unwrap().unwrap();
        let mut prev_constraint = conflict_constraint;
        output_ids.push(
            conflict_constraint
                .get_out_id(conflict_constraint.get_some_id())
                .unwrap(),
        );
        conflict_constraint
            .constraint
            .mark_negated_lits(&self.trail.assignment, &mut relevant_assignment);

        for propagation in self.trail.trail.iter().rev() {
            // Check if constraint did propagate something relevant.
            if unsafe { relevant_assignment.get_lit_value_unchecked(propagation.lit) }
                == BoolValue::Assigned(true)
            {
                let constraint = propagation.reason.unwrap();
                // Only add propagation if the constraint did not propagate right before.
                if !Rc::ptr_eq(constraint, prev_constraint) {
                    prev_constraint = constraint;
                    output_ids.push(constraint.get_out_id(constraint.get_some_id()).unwrap());

                    // Add literals that were relevant for the propagation of the constraint.
                    constraint
                        .constraint
                        .mark_negated_lits(&self.trail.assignment, &mut relevant_assignment);
                }
            }
        }

        // Go through the output constraint IDs in reverse order and replace ID 0 with `~`.
        for &id in output_ids.iter().rev() {
            if id == 0 {
                self.rup_hints.push(RUPHint::NegatedPremise);
            } else {
                self.rup_hints.push(RUPHint::ConstraintId(
                    NonZeroUsize::new(id).expect("should be non-zero"),
                ));
            }
        }
    }

    /// Function for pretty printing the current trail.
    fn trace_failed(&self, var_names: &VarNameManager) {
        println!("Propagation check failed! The propagation had the following trail:");
        println!("  propagations in format: <assignment> (<reason constraint>)");

        for Propagation { lit, reason } in self.trail.trail.iter() {
            println!(
                "    {} ({})",
                lit.to_pretty_string(var_names).purple(),
                match reason {
                    Reason::Assumption => "by assumption".cyan(),
                    Reason::Constraint(constraint) => constraint.to_pretty_string(var_names).cyan(),
                }
            )
        }

        if let Some(conflict) = &self.trail.conflict {
            println!(
                "    {} ({})",
                "*conflict*".red(),
                match conflict {
                    Reason::Assumption => "by assumption".cyan(),
                    Reason::Constraint(constraint) => constraint.to_pretty_string(var_names).cyan(),
                }
            )
        } else if self.trail.trail.is_empty() {
            // An empty trail is itself the diagnosis, but printing only a header and a
            // legend reads as if the trace failed to render. Say what actually happened.
            println!(
                "    {}",
                "(no propagations: asserting the negation of this constraint left every \
                 constraint with slack >= 1, so unit propagation had nothing to derive and \
                 stopped immediately)"
                    .yellow()
            );
            println!(
                "    {}",
                "hint: a single 'rup' step cannot justify this constraint; derive it \
                 explicitly with 'pol' instead"
                    .yellow()
            );
        }
    }

    /// Propagate a (partial) assignment to possibly get more variables assigned.
    ///
    /// This function takes a `Vec<Lit>` as input for the assignment to start building the propagation trail in order of the solution given by the user.
    #[inline]
    pub fn propagate_solution(
        &mut self,
        literals: &Vec<Lit>,
        var_names: &VarNameManager,
        trace_failed: bool,
    ) -> Result<Assignment<BooleanVar>, PropagatorError> {
        // Reset the trail without considering the assignment.
        if self.init_trail(var_names.len(), false, false).is_conflict() {
            return Err(PropagatorError::SolutionConflictingWithConstraint(
                self.trail.conflict.as_ref().unwrap().unwrap().get_some_id(),
            ));
        };

        // Initialize the trail to the assignment.
        if self.trail.add_assumptions(literals).is_err() {
            if trace_failed {
                self.trace_failed(var_names);
            }
            return Err(PropagatorError::SolutionConflictingWithSavedTrail);
        }

        // Run the actual propagation, i.e., going through the trail and looking at watch list to see which constraints to consider.
        if self.propagate_with_precedence(false, false).is_conflict() {
            if trace_failed {
                self.trace_failed(var_names);
            }
            return Err(PropagatorError::SolutionConflictingWithConstraint(
                self.trail.conflict.as_ref().unwrap().unwrap().get_some_id(),
            ));
        }

        let full_assignment = self.trail.assignment.clone();
        self.load_level();

        Ok(full_assignment)
    }

    /// The the assignment of the saved trail.
    ///
    /// The option `only_core` specifies if we want the saved trail with propagations from derived constraints or only core constraints. The number of variables `num_vars` is required for setting up the propagation to get all propagations from the selected propagation sets.
    #[inline]
    pub fn get_propagated_assignment(
        &mut self,
        num_vars: usize,
        only_core: bool,
    ) -> &Assignment<BooleanVar> {
        self.init_trail(num_vars, only_core, false);
        &self.trail.assignment
    }

    /// This function should only be called after [`Self::get_propagated_assignment()`] has been called and is used similar to analyze to get the unit propagations.
    #[inline]
    pub fn collect_propagated_assignment_hints(&mut self) {
        self.rup_hints.clear();
        let mut output_ids = Vec::new();

        // Set up previous constraint.
        let mut prev_constraint = None;

        for propagation in self.trail.trail.iter().rev() {
            // Check if constraint did propagate something relevant.
            let constraint = propagation.reason.unwrap();
            // Only add propagation if the constraint did not propagate right before.
            if prev_constraint.is_none_or(|prev| !Rc::ptr_eq(constraint, prev)) {
                prev_constraint = Some(constraint);
                output_ids.push(constraint.get_out_id(constraint.get_some_id()).unwrap());
            }
        }

        for &id in output_ids.iter().rev() {
            self.rup_hints.push(RUPHint::ConstraintId(
                NonZeroUsize::new(id).expect("should be non-zero"),
            ))
        }
    }

    /// Get a reference to the current [`Trail`].
    #[inline]
    pub fn get_trail(&self) -> &Trail {
        &self.trail
    }

    /// Remove propagations on the trail until only valid prpagations remain on the trail.
    ///
    /// Return [`true`] iff there were actually propagations removed from the trail.
    #[inline]
    fn unpoison(&mut self, only_core: bool) -> bool {
        debug_assert!(self.saved_reason_detached);
        self.saved_reason_detached = false;
        self.reset_to_valid(only_core)
    }

    /// Reset the watchers of **every** propagation set, enabled or not.
    ///
    /// This runs from [`Self::load_level()`] and [`Self::reset_to_level()`], i.e. exactly where the
    /// trail is unwound, and it is what re-establishes invariants 1. and 2. of
    /// [`GeneralPBWatcher`](crate::general_pb_watcher::GeneralPBWatcher) after literals were
    /// unassigned: `next_pos` and `next_pos_prop` are resume positions that are only valid for the
    /// trail they were reached on, and `is_reset_not_contributing` records that
    /// `watched_but_not_contributing` was last checked against that trail.
    ///
    /// Skipping the disabled sets here is *not* safe. A set is disabled exactly while an
    /// `only_core` phase runs (see step 1. of [`Self::init_trail()`]), and the same `init_trail`
    /// truncates the trail in [`Self::unpoison()`]. A disabled set that kept its resume state would
    /// then describe a longer trail than the one it is re-enabled on: literals that were falsified
    /// when the state was recorded but are unassigned now are skipped by the resume scan and stay
    /// in `watched_but_not_contributing`, so `watches_slack` sits *below* the true slack — the
    /// unsafe direction, in which the watcher reports conflicts and propagations that do not exist.
    /// An invented conflict at trail level zero makes every following RUP check succeed.
    ///
    /// Resetting a disabled set is cheap (it only walks that set's `touched_watchers`) and always
    /// sound: the reset state simply forces the next
    /// [`update_watch`](crate::watcher::Watchable::update_watch()) to rescan from the start.
    #[inline]
    fn reset_watch(&mut self) {
        for set in self.propagation_sets.iter_mut().flatten() {
            set.reset_watch();
        }
    }

    /// Save the current trail internally.
    #[inline]
    fn save_level(&mut self) {
        self.saved_level.level = self.trail.trail.len();
        self.saved_level.conflict = self.trail.conflict.is_some();
    }

    /// Load the trail from the internally stored trail positions.
    #[inline]
    fn load_level(&mut self) {
        if !self.saved_level.conflict {
            self.trail.conflict = None;
        }

        while self.trail.len() > self.saved_level.level {
            self.trail.pop();
        }

        self.reset_watch();
    }

    /// Reset a trail to a specified level.
    #[inline]
    fn reset_to_level(&mut self, level: usize) {
        if self.trail.len() > level {
            self.trail.conflict = None;
        }

        while self.trail.len() > level {
            self.trail.pop();
        }

        self.reset_watch();
    }

    /// Reset the trail so that it only contains constraints that have not been deleted.
    ///
    /// Return [`true`] iff the resetting changed the trail.
    #[inline]
    fn reset_to_valid(&mut self, only_core: bool) -> bool {
        let mut modified_trail = false;
        let mut level = 0;
        for Propagation { reason, .. } in self.trail.trail.iter() {
            if let Reason::Constraint(constraint) = reason {
                if constraint.all_constraint_ids_empty(only_core) {
                    break;
                }
            } else {
                break;
            }
            level += 1;
        }
        if level < self.trail.len() {
            modified_trail = true;
        }

        if let Some(Reason::Constraint(conflict)) = &self.trail.conflict
            && conflict.all_constraint_ids_empty(only_core)
        {
            self.trail.conflict = None;
            modified_trail = true;
        }

        self.reset_to_level(level);

        modified_trail
    }
}
