//! Standard propagator for constraints using watchlists.

use std::rc::Rc;

use ahash::HashMap;
use by_address::ByAddress;
use veripb_formula::prelude::*;

use crate::{
    error::PropagatorError,
    trail::{Propagation, Reason, Trail},
    watcher::{Watch, WatchInit, WatchUpdate, Watchable},
};

/// The result of a propagation.
#[derive(Debug, PartialEq, Eq)]
pub enum PropagationResult {
    /// It is not known if the propagation results in a conflict or not.
    Unknown,
    /// Propagation resulted in a conflict.
    Conflict,
}

impl PropagationResult {
    /// Check if [`PropagationResult`] is a conflict or not.
    #[inline]
    pub fn is_conflict(&self) -> bool {
        matches!(*self, PropagationResult::Conflict)
    }
}

/// Propagator for one type of watchers.
///
/// The propagator maintains its own watchlist of its registered constraints. For each constraint a subset of literals for this constraint are watched. If a watched literal for this constraint becomes falsified, then we need to find new watches, so that all propagations can be detected.
///
/// # Invariants
/// There are some invariants that the propagator needs to preserve for its internal data structures.
/// 1. Any deleted watch has to be communicated to the corresponding constraint watchers through [`Watchable::update_watch()`].
/// 2. Any new watch returned by [`Watchable::init_watches()`] or [`Watchable::update_watch()`] has to be added into a watchlist.
/// 3. If [`Watchable::init_watches()`] results in a conflict, then no watches are added to the watchlist for this watcher, the propagator returns the conflict, and this watcher is not registered.
/// 4. If [`Watchable::update_watch()`] results in a conflict, then no watches are added to the watchlist and the removed watch is added back to the watchlist.
/// 5. If a constraint contains no falsified watches whose position in the trail is beyond the trail_head, then this constraint is fully propagated.
#[derive(Debug)]
pub struct Propagator<W>
where
    W: Watchable,
{
    size: usize,
    /// List indexed by literals containing a list of constraints that are watched for this literal.
    ///
    /// Each entry carries the watcher index plus an inline blocker literal, see [`Watch`].
    watchlist: Vec<Vec<Watch>>,
    /// Scratch buffer holding the entries of the watchlist currently being processed by
    /// [`Propagator::propagate()`]. Kept on the struct so its allocation is reused across calls;
    /// it is empty outside of `propagate()`.
    propagate_scratch: Vec<Watch>,
    /// All watchers attached to this propagator.
    watchers: Vec<Option<Box<W>>>,
    /// First empty position in the `watchers` vector.
    empty_watcher_pos: usize,
    /// List of indices of watchers where no watches have been registered.
    unregistered_watchers: Vec<usize>,
    /// Position for the next propagation in the trail that has to be considered by this propagator.
    trail_head: usize,
    /// A list of propagation that will always happen. E.g., this are unit clauses or cardinality constraints with a degree equal to the number of literals in the constraint.
    assignment_independent_propagations: Vec<Propagation>,
    /// List of indices to watchers where no assignment independent propagations have been registered.
    unhandled_assignment_independent_watchers: Vec<usize>,
    /// List of indices to watchers that have been modified during the propagations and that need to be reset before the next top-level propagation check (RUP or solution propagation).
    touched_watchers: Vec<usize>,
    /// Mapping of constraints to their watch indices in this propagator
    constraint_to_index: HashMap<ByAddress<Rc<DBConstraint>>, usize>,
}

impl<W> Propagator<W>
where
    W: Watchable,
{
    /// Return the number of attached watchers.
    pub fn len(&self) -> usize {
        self.watchers.len()
    }

    /// Whether there are any watchers attached.
    pub fn is_empty(&self) -> bool {
        self.watchers.is_empty()
    }

    /// Construct a new propagator with capacity for specified variables.
    #[inline]
    pub fn with_size(num_variables: usize) -> Self {
        Propagator {
            size: num_variables,
            ..Default::default()
        }
    }

    /// Resize the propagator to fit a size of `num_variable` many variables. Since the watchlist is indexed by the literal, we need to allocate twice the number of variables.
    #[inline]
    pub fn resize(&mut self, num_variables: usize) {
        self.size = num_variables;
        if self.is_empty() {
            return;
        }
        self.watchlist.resize(num_variables * 2, Vec::new());
    }

    /// Add `constraint` to the propagator.
    ///
    /// The propagator should create a watcher to watch the constraint and add the watcher to the watchers handled by the propagator. This operation should not add watches to the watchlist of the propagator.
    #[inline]
    pub fn add(&mut self, constraint: &Rc<DBConstraint>) -> Result<(), PropagatorError> {
        if self.is_empty() {
            self.watchlist.resize(self.size * 2, Vec::default());
        }
        let watcher = W::from_db_constraint(constraint);
        for watcher in self.watchers[self.empty_watcher_pos..].iter() {
            if watcher.is_none() {
                break;
            }
            self.empty_watcher_pos += 1;
        }
        constraint.header.borrow_mut().attached_propagator_count += 1;
        debug_assert!(constraint.header.borrow().attached_propagator_count == 1);
        self.constraint_to_index
            .insert(ByAddress(constraint.clone()), self.empty_watcher_pos);
        if self.empty_watcher_pos == self.watchers.len() {
            self.watchers.push(Some(Box::new(watcher)));
        } else {
            // We checked that the index is inside the size of the vector.
            *unsafe { self.watchers.get_unchecked_mut(self.empty_watcher_pos) } =
                Some(Box::new(watcher));
        }
        self.unregistered_watchers.push(self.empty_watcher_pos);
        self.unhandled_assignment_independent_watchers
            .push(self.empty_watcher_pos);
        self.empty_watcher_pos += 1;
        Ok(())
    }

    /// Remove `constraint` from the propagator.
    ///
    /// Remove the constraint from the propagator and delete the constraint from the watchlist, as there is no easy way to remove the constraint lazily. This is because the constraint could immediately be added to a different propagator.
    #[inline]
    pub fn remove(&mut self, constraint: &Rc<DBConstraint>) -> Result<(), PropagatorError> {
        let Some(watch_index) = self
            .constraint_to_index
            .remove(&ByAddress(constraint.clone()))
        else {
            return Ok(());
        };

        let mut header = constraint.header.borrow_mut();
        if header.attached_propagator_count > 0 {
            if let Some(mut watcher) = self.watchers[watch_index].take() {
                // Track first free space.
                if watch_index < self.empty_watcher_pos {
                    self.empty_watcher_pos = watch_index;
                }
                header.attached_propagator_count -= 1;
                debug_assert!(header.attached_propagator_count == 0);
                if watcher.is_propagating_independent_of_assignment() {
                    self.assignment_independent_propagations
                        .retain(|p| !Rc::ptr_eq(p.reason.unwrap(), constraint));
                    if watcher.no_watches_required() {
                        return Ok(());
                    }
                }
                // Watches are removed eagerly.
                watcher.remove_watches(&mut self.watchlist, watch_index);

                // for lit in watcher.get_watches() {
                //     if lit.is_undef() {
                //         continue;
                //     }
                //     let list = self.watchlist.get_mut(lit.get_lit_data()).unwrap();
                //     let index = list.iter().position(|c| Rc::ptr_eq(c, constraint)).unwrap();
                //     list.swap_remove(index);
                // }

                Ok(())
            } else {
                Err(PropagatorError::AttachedToOtherPropagator)
            }
        } else {
            Ok(())
        }
    }

    /// Check if propagator has a constraint that is a reason in the saved trail.
    pub fn has_saved_reason(&self) -> bool {
        for watcher in self.watchers.iter().flatten() {
            if watcher.get_constraint().header.borrow().is_saved_reason {
                return true;
            }
        }
        false
    }

    /// Remove all constraints from this propagator and return the removed constraints.
    pub fn remove_all(&mut self, removed_constraints: &mut Vec<Rc<DBConstraint>>) {
        // If there are no watchers, then there are no constraints in this propagator, so we can avoid the work.
        if !self.watchers.is_empty() {
            for watcher in self.watchers.iter().flatten() {
                let constraint = watcher.get_constraint();
                constraint.header.borrow_mut().attached_propagator_count -= 1;
                debug_assert!(constraint.header.borrow_mut().attached_propagator_count == 0);
                removed_constraints.push(constraint.clone());
            }

            self.watchlist.clear();
            self.watchers.clear();
            self.assignment_independent_propagations.clear();
            self.empty_watcher_pos = 0;
            self.unregistered_watchers.clear();
            self.unhandled_assignment_independent_watchers.clear();
            self.trail_head = 0;
            self.touched_watchers.clear();
            // See `clear()`: the map keys are strong references and have to go
            // together with the watchers, otherwise the removed constraints stay
            // allocated for the rest of the process.
            self.constraint_to_index.clear();
        }
    }

    /// Reset [`Propagator`] to the `prev_trail_len` by setting the consider head of the propagator on the trail.
    #[inline]
    pub fn reset(&mut self, prev_trail_len: usize) {
        self.trail_head = self.trail_head.min(prev_trail_len);
    }

    /// Register unregistered constraints to the watchlist.
    ///
    /// This initializes watches for the constraint and adds the constraint for the watches to the watchlist. The watches are determined with respect to the current `trail`. If the option `mark_reason` is used, then the constraint remembers that has a propagation on the trail if it propagates.
    #[inline]
    fn register_unregistered_to_watchlist(
        &mut self,
        trail: &mut Trail,
        mark_reasons: bool,
        remember_watcher: bool,
    ) -> PropagationResult {
        while let Some(watcher_pos) = self.unregistered_watchers.pop() {
            if let Some(watcher) = self.watchers.get_mut(watcher_pos).unwrap() {
                // Do not add watches for constraints that are already fully propagated.
                if watcher.no_watches_required() {
                    // Check if the constraint is also conflicting.
                    if watcher.get_constraint().is_contradicting() {
                        // Directly terminate with conflict, if constraint is conflicting.
                        trail.conflict = Some(Reason::Constraint(watcher.get_constraint().clone()));
                        if mark_reasons {
                            watcher.get_constraint().header.borrow_mut().is_saved_reason = true;
                        }
                        self.unregistered_watchers.push(watcher_pos);
                        return PropagationResult::Conflict;
                    }
                    continue;
                }

                if remember_watcher {
                    self.touched_watchers.push(watcher_pos);
                }
                match watcher.init_watches(&trail.assignment) {
                    WatchInit::Conflict => {
                        trail.conflict = Some(Reason::Constraint(watcher.get_constraint().clone()));
                        if mark_reasons {
                            watcher.get_constraint().header.borrow_mut().is_saved_reason = true;
                        }
                        self.unregistered_watchers.push(watcher_pos);
                        return PropagationResult::Conflict;
                    }
                    WatchInit::Watching {
                        propagated,
                        watches,
                    } => {
                        // Initialize watches for unregistered constraint.
                        let constraint = watcher.get_constraint().clone();
                        for &watch in watches.iter() {
                            let entry = Watch {
                                index: watcher_pos,
                                blocker: watcher.blocker_for(watch),
                            };
                            self.watchlist[watch.get_lit_data()].push(entry);
                        }
                        for &lit in propagated.iter() {
                            if trail
                                .push(
                                    Propagation::new(lit, Reason::Constraint(constraint.clone())),
                                    mark_reasons,
                                )
                                .is_err()
                            {
                                return PropagationResult::Conflict;
                            }
                        }
                    }
                }
            }
        }
        PropagationResult::Unknown
    }

    /// Propagate with respect to the given `trail`.
    ///
    /// Propagation happens literal by literal on the `trail` by advancing the `trail_head` of the [`Propagator`]. For each literal, the constraints for which this literal is watched are updated. If the option `mark_reason` is used, then the constraint remembers that has a propagation on the trail if it propagates.
    #[inline]
    pub fn propagate(
        &mut self,
        trail: &mut Trail,
        mark_reasons: bool,
        remember_watcher: bool,
    ) -> PropagationResult {
        if self.watchers.is_empty() {
            return PropagationResult::Unknown;
        }
        if self
            .register_unregistered_to_watchlist(trail, mark_reasons, remember_watcher)
            .is_conflict()
        {
            return PropagationResult::Conflict;
        }

        // Update watches for the negated literals on the trail.
        while self.trail_head < trail.len() {
            let Propagation { mut lit, reason: _ } = trail.trail[self.trail_head];
            lit.negate();
            let list = unsafe { self.watchlist.get_unchecked_mut(lit.get_lit_data()) };
            if list.is_empty() {
                self.trail_head += 1;
                continue;
            }
            // Move the entries into the persistent scratch buffer. Unlike the previous
            // `mem::take`, `append` leaves the watchlist `Vec` its allocation, so the
            // re-registrations below do not regrow it from capacity zero on every pass.
            // The visit order (pop from the back) is identical.
            debug_assert!(self.propagate_scratch.is_empty());
            self.propagate_scratch.append(list);
            while let Some(entry) = self.propagate_scratch.pop() {
                // Blocker fast path: if the cached blocker literal is currently satisfied,
                // the whole constraint is satisfied, so it can neither conflict nor
                // propagate, and its watch does not need to move (the contract of
                // `Watchable::blocker_for()`). Keep the entry as is, without touching the
                // watcher box, the constraint, or the trail.
                if !entry.blocker.is_undef()
                    && unsafe { trail.assignment.get_lit_value_unchecked(entry.blocker) }
                        == BoolValue::Assigned(true)
                {
                    unsafe { self.watchlist.get_unchecked_mut(lit.get_lit_data()) }.push(entry);
                    continue;
                }
                let watcher_index = entry.index;
                let watcher = unsafe {
                    self.watchers
                        .get_unchecked_mut(watcher_index)
                        .as_mut()
                        .unwrap_unchecked()
                };
                if remember_watcher {
                    self.touched_watchers.push(watcher_index);
                }
                match watcher.update_watch(lit, &trail.assignment) {
                    WatchUpdate::None => {}
                    WatchUpdate::Conflict => {
                        trail.conflict = Some(Reason::Constraint(watcher.get_constraint().clone()));
                        if mark_reasons {
                            watcher.get_constraint().header.borrow_mut().is_saved_reason = true;
                        }
                        self.watchlist[lit.get_lit_data()].push(entry);
                        self.watchlist[lit.get_lit_data()].append(&mut self.propagate_scratch);
                        return PropagationResult::Conflict;
                    }
                    WatchUpdate::Unknown {
                        propagated,
                        new_watches,
                    } if propagated.is_empty() => {
                        for &watch in new_watches.iter() {
                            let entry = Watch {
                                index: watcher_index,
                                blocker: watcher.blocker_for(watch),
                            };
                            self.watchlist[watch.get_lit_data()].push(entry);
                        }
                    }
                    WatchUpdate::Unknown {
                        propagated,
                        new_watches,
                    } => {
                        let constraint = watcher.get_constraint().clone();
                        for &watch in new_watches.iter() {
                            let entry = Watch {
                                index: watcher_index,
                                blocker: watcher.blocker_for(watch),
                            };
                            self.watchlist[watch.get_lit_data()].push(entry);
                        }
                        for &propagated_lit in propagated.iter() {
                            if trail
                                .push(
                                    Propagation {
                                        lit: propagated_lit,
                                        reason: Reason::Constraint(constraint.clone()),
                                    },
                                    mark_reasons,
                                )
                                .is_err()
                            {
                                self.watchlist[lit.get_lit_data()]
                                    .append(&mut self.propagate_scratch);
                                return PropagationResult::Conflict;
                            }
                        }
                    }
                    WatchUpdate::UnknownSingle {
                        propagated: None,
                        new_watches,
                    } => {
                        let entry = Watch {
                            index: watcher_index,
                            blocker: watcher.blocker_for(new_watches),
                        };
                        self.watchlist[new_watches.get_lit_data()].push(entry);
                    }
                    WatchUpdate::UnknownSingle {
                        propagated,
                        new_watches,
                    } => {
                        let constraint = watcher.get_constraint().clone();
                        let entry = Watch {
                            index: watcher_index,
                            blocker: watcher.blocker_for(new_watches),
                        };
                        self.watchlist[new_watches.get_lit_data()].push(entry);
                        if let Some(propagated_lit) = propagated
                            && trail
                                .push(
                                    Propagation {
                                        lit: propagated_lit,
                                        reason: Reason::Constraint(constraint.clone()),
                                    },
                                    mark_reasons,
                                )
                                .is_err()
                        {
                            self.watchlist[lit.get_lit_data()].append(&mut self.propagate_scratch);
                            return PropagationResult::Conflict;
                        }
                    }
                }
            }

            self.trail_head += 1;
        }

        PropagationResult::Unknown
    }

    /// Get all assignment independent propagations of this [`Propagator`]. This function also adds all assignment independent propagations from the unhandled watchers with respect to assignment independent propagations.
    #[inline]
    pub fn get_assignment_independent_propagations(&mut self) -> &Vec<Propagation> {
        // Check for propagation at level zero of new watchers.
        while let Some(watcher_pos) = self.unhandled_assignment_independent_watchers.pop() {
            if let Some(watcher) = &self.watchers[watcher_pos]
                && let Some(propagations) = &mut watcher.get_assignment_independent_propagations()
            {
                self.assignment_independent_propagations
                    .append(propagations);
            }
        }

        &self.assignment_independent_propagations
    }

    /// Get the assignment independent propagations for all watchers where assignment independent propagations have not been handled. The new assignment independent propagations are added to the `new_propagations` vector.
    #[inline]
    pub fn get_new_assignment_independent_propagations(
        &mut self,
        new_propagations: &mut Vec<Propagation>,
    ) {
        // Check for propagation at level zero of new watchers.
        while let Some(watcher_pos) = self.unhandled_assignment_independent_watchers.pop() {
            if let Some(watcher) = &self.watchers[watcher_pos]
                && let Some(propagations) = &mut watcher.get_assignment_independent_propagations()
            {
                new_propagations.extend(propagations.iter().cloned());
                self.assignment_independent_propagations
                    .append(propagations);
            }
        }
    }

    /// Remove all watchers from this [`Propagator`] and reset all data structures.
    #[inline]
    pub fn clear(&mut self) {
        self.watchers.drain(..).for_each(|watcher| {
            let Some(watcher) = watcher else {
                return;
            };
            watcher.get_watches().for_each(|lit| {
                let opt_watchlist = self.watchlist.get_mut(lit.get_lit_data());
                if let Some(watchlist) = opt_watchlist {
                    watchlist.clear()
                }
            });
            watcher
                .get_constraint()
                .header
                .borrow_mut()
                .attached_propagator_count -= 1;
            debug_assert!(
                watcher
                    .get_constraint()
                    .header
                    .borrow_mut()
                    .attached_propagator_count
                    == 0
            );
        });
        self.watchers.clear();
        self.empty_watcher_pos = 0;
        self.unregistered_watchers.clear();
        self.trail_head = 0;
        self.assignment_independent_propagations.clear();
        self.unhandled_assignment_independent_watchers.clear();
        self.touched_watchers.clear();
        // The keys of `constraint_to_index` are strong references, so failing to
        // drop them here keeps every constraint ever added to this propagator
        // alive for the rest of the process. This matters most for the temporary
        // propagation set used by every RUP check, which is cleared after each
        // check and would otherwise retain each negated goal constraint forever.
        self.constraint_to_index.clear();
    }

    /// Reset watchers for watchers registered in `touched_watchers`.
    #[inline]
    pub fn reset_watch(&mut self) {
        if self.watchers.len() < self.touched_watchers.len() {
            self.watchers
                .iter_mut()
                .flatten()
                .for_each(|w| w.reset_watch());
        } else {
            self.touched_watchers.iter().for_each(|&pos| {
                if let Some(watcher) = unsafe { self.watchers.get_unchecked_mut(pos) } {
                    watcher.reset_watch();
                }
            })
        }
        self.touched_watchers.clear();
    }
}

impl<W: Watchable> Default for Propagator<W> {
    fn default() -> Self {
        Propagator {
            size: 0,
            watchlist: Vec::new(),
            propagate_scratch: Vec::new(),
            watchers: Vec::new(),
            empty_watcher_pos: 0,
            unregistered_watchers: Vec::new(),
            trail_head: 0,
            assignment_independent_propagations: Vec::new(),
            unhandled_assignment_independent_watchers: Vec::new(),
            touched_watchers: Vec::new(),
            constraint_to_index: HashMap::default(),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::clause_watcher::ClauseWatcher;
    use veripb_formula::clause::Clause;

    /// A two-literal clause over `x1` and `x2` wrapped in a fresh [`Rc`].
    fn clause() -> Rc<DBConstraint> {
        Rc::new(DBConstraint::from(Clause::from_lits(vec![
            Lit::from_var(1, false),
            Lit::from_var(2, false),
        ])))
    }

    /// `clear()` used to leave the `constraint_to_index` entry (a strong
    /// reference) behind, so every constraint ever added to a propagator stayed
    /// alive. The temporary propagation set of the RUP check is cleared after
    /// every single RUP step, which turned this into unbounded growth.
    #[test]
    fn clear_releases_all_constraint_references() {
        let constraint = clause();
        let mut propagator: Propagator<ClauseWatcher> = Propagator::with_size(4);
        propagator.add(&constraint).unwrap();
        assert!(
            Rc::strong_count(&constraint) > 1,
            "the propagator should hold a reference while the constraint is attached"
        );

        propagator.clear();

        assert_eq!(
            Rc::strong_count(&constraint),
            1,
            "clear() must drop every reference the propagator holds"
        );
    }

    /// Same for the bulk removal path used when constraints are moved to core.
    #[test]
    fn remove_all_releases_all_constraint_references() {
        let constraint = clause();
        let mut propagator: Propagator<ClauseWatcher> = Propagator::with_size(4);
        propagator.add(&constraint).unwrap();

        let mut removed = Vec::new();
        propagator.remove_all(&mut removed);
        assert_eq!(removed.len(), 1);
        drop(removed);

        assert_eq!(
            Rc::strong_count(&constraint),
            1,
            "remove_all() must drop every reference the propagator holds"
        );
    }
}
