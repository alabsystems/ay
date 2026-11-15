//! Defines the [`Watchable`] trait for a constraint watcher.
//!
//! Each watcher should keep track of the watcher know to the propagator where the watcher is attached.

use std::{fmt::Debug, rc::Rc};

use veripb_formula::{
    lit::Lit,
    prelude::{Assignment, BooleanVar, DBConstraint},
};

use crate::trail::Propagation;

/// A single watchlist entry of a [`Propagator`](crate::propagator::Propagator).
///
/// Besides the index of the watcher in the propagator's watcher table, the entry caches an
/// inline *blocker* literal (see [`Watchable::blocker_for()`]). Storing the blocker inline lets
/// the hot propagation loop skip a satisfied constraint with a single assignment lookup,
/// without dereferencing the watcher box, the constraint [`Rc`], or the literal slice.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Watch {
    /// Index of the watcher in the propagator's watcher table.
    pub index: usize,
    /// Blocker literal hint; [`Lit::new_undef()`] when the constraint type provides none.
    pub blocker: Lit,
}

/// Return type for [`Watchable::init_watches()`].
#[derive(Debug, PartialEq, Eq)]
pub enum WatchInit {
    /// Initializing watches led to a conflict, i.e., the constraint is falsified by the current assignment.
    Conflict,
    /// There are enough non-falsified literals to watch such that the constraint is not falsified.
    Watching {
        /// The literals propagated by the constraint under the current assignment.
        propagated: Vec<Lit>,
        /// The watches for the constraint.
        watches: Vec<Lit>,
    },
}

/// Return type for [`Watchable::update_watch()`].
#[derive(Debug, PartialEq, Eq)]
pub enum WatchUpdate {
    /// Current assignment falsifies constraint.
    Conflict,
    /// New watches and propagations.
    Unknown {
        propagated: Vec<Lit>,
        new_watches: Vec<Lit>,
    },
    /// One new watch and maybe one propagation. This variant is mainly used for clauses.
    UnknownSingle {
        propagated: Option<Lit>,
        new_watches: Lit,
    },
    /// No new propagations and watches, which means that the invalid watch can just be deleted.
    None,
}

impl WatchUpdate {
    /// Check if [`WatchUpdate`] is a conflict or not.
    #[inline]
    pub fn is_conflict(&self) -> bool {
        matches!(*self, WatchUpdate::Conflict)
    }
}

/// It should be assumed that we only watch a constraint, i.e., add watches to the propagator for this constraint, if the constraint does not completely propagate or is conflicting in itself.
///
/// # Invariants
/// The following invariants should be maintained by any struct implementing [`Watchable`].
/// 1. After the [`Watchable`] has been initialized, the sum of the coefficients of the watched literals is at least the right-hand side plus the largest coefficient to detect any propagation.
/// 2. The watches maintained by each [`Watchable`] are in sync with the watches known to the owner of the [`Watchable`]. This is achieved through the return of [`Watchable::init_watches()`] and [`Watchable::update_watch()`] and a literal is deleted if it is given as a parameter for [`Watchable::update_watch()`].
pub trait Watchable: Debug {
    /// Construct watcher from `DBConstraint`.
    fn from_db_constraint(constraint: &Rc<DBConstraint>) -> Self;

    /// Check for propagation at decision level 0.
    ///
    /// E.g., if the constraint is a unit clause then the literal is propagated to true and the function reports that the constraint has fully propagated.
    fn get_assignment_independent_propagations(&self) -> Option<Vec<Propagation>>;

    /// Check if constraint can even propagate and thus requires watches.
    ///
    /// If all coefficients are larger than the slack with respect to the empty assignment, then this constraint is either conflicting or propagating all its literals independent of the assignment.
    /// Also if the right-hand side is non-positive, then the constraint is always satisfied. In both cases computing the propagations with respect to a partial assignment does not change the propagation.
    fn no_watches_required(&mut self) -> bool;

    /// Check if a constraint is propagating at level 0.
    ///
    /// If a constraint is propagating partially or fully at level 0, then return true, else if no propagation happens, then return false.
    fn is_propagating_independent_of_assignment(&self) -> bool;

    /// Initialize the watches of a constraint to be in sync with the current assignment.
    ///
    /// If the constraint is satisfied by `assign`, then the [`Watchable`] should still return enough watches, so that the sum of the coefficients of the watches is at least the right-hand side of the constraint.
    fn init_watches(&mut self, assign: &Assignment<BooleanVar>) -> WatchInit;

    /// Update the watched literal after the literal `old_watch` has been propagated.
    ///
    /// The literal `old_watch` is no longer watched in the watchlist of the owner of [`Watchable`]. If `old_watch` should still be a valid watch, then `old_watch` should be returned inside [`WatchUpdate`] as a new watch.
    fn update_watch(&mut self, old_watch: Lit, assign: &Assignment<BooleanVar>) -> WatchUpdate;

    /// Get the currently watched literals.
    fn get_watches(&self) -> impl Iterator<Item = &Lit>;

    /// Return the *blocker* literal to cache inline in the watchlist entry for `watch`.
    ///
    /// # Contract
    /// The returned literal is either [`Lit::new_undef()`] or a literal of the watched
    /// constraint whose assignment to true implies that the whole constraint is satisfied.
    /// A satisfied constraint can neither conflict nor propagate, and keeping a falsified
    /// watch on it is an accepted propagator state ([`Watchable::update_watch()`] itself keeps
    /// `old_watch` when the constraint is satisfied and no replacement watch is found), so the
    /// propagator may skip [`Watchable::update_watch()`] entirely while the blocker is true.
    ///
    /// Only clauses have such a literal (any single true literal satisfies a clause); every
    /// other constraint type uses this default, which disables the skip.
    #[inline]
    fn blocker_for(&self, _watch: Lit) -> Lit {
        Lit::new_undef()
    }

    /// Remove the watches from the given watchlist.
    fn remove_watches(&self, watchlist: &mut Vec<Vec<Watch>>, watch_index: usize);

    /// Get the constraint that the watcher is watching.
    fn get_constraint(&self) -> &Rc<DBConstraint>;

    /// Reset the last position to look for watches and propagations, and whether the constraint might have non-contributing watches that are actually contributing.
    ///
    /// Only implemented for general watchers. Should not be called for watchers of clauses and cardinalities.
    fn reset_watch(&mut self) {
        unreachable!();
    }

    /// Check whether watches listed as not contributing are actually contributing, and if so, move them to watches.
    ///
    /// Only implemented for general watchers. Should not be called for watchers of clauses and cardinalities.
    fn reset_not_contributing(&mut self, _assign: &Assignment<BooleanVar>) {
        unreachable!();
    }
}
