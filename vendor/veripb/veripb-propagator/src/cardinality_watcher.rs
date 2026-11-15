//! Watcher structure for [`Cardinality`] constraints.

use std::{cell::RefCell, rc::Rc};

use ahash::HashSet;
use veripb_formula::prelude::*;

use crate::{
    trail::{Propagation, Reason},
    watcher::{Watch, WatchInit, WatchUpdate, Watchable},
};

/// [`Watchable`] for cardinality constraints.
///
/// The lookup of new watches is implemented as a cyclic check, where we start looking for a new watch from literal after the last literal that was added as a watch.
#[derive(Debug)]
pub struct CardinalityWatcher {
    /// Reference to the constraint that is watched.
    pub constraint: Rc<DBConstraint>,
    /// Current watches maintained by the watcher.
    pub watches: HashSet<Lit>,
    /// The position in the vector of literals of the cardinality after the last found watch.
    pub next_pos: usize,
}

impl CardinalityWatcher {
    /// Get a watcher for the cardinality constraint `card`.
    pub fn from_card(card: Cardinality) -> Self {
        CardinalityWatcher {
            constraint: Rc::new(DBConstraint {
                header: RefCell::new(DBHeader::default()),
                constraint: card.into(),
            }),
            watches: HashSet::with_hasher(crate::general_pb_watcher::deterministic_state()),
            next_pos: 0,
        }
    }
}

impl Watchable for CardinalityWatcher {
    #[inline]
    fn from_db_constraint(constraint: &Rc<DBConstraint>) -> Self {
        CardinalityWatcher {
            constraint: constraint.clone(),
            watches: HashSet::with_hasher(crate::general_pb_watcher::deterministic_state()),
            next_pos: 0,
        }
    }

    #[inline]
    fn get_assignment_independent_propagations(&self) -> Option<Vec<Propagation>> {
        let card = self.constraint.constraint.as_card();
        if card.len() as i64 == *card.get_degree() {
            let mut propagations = Vec::with_capacity(card.len());
            for lit in card.get_lits() {
                propagations.push(Propagation::new(
                    *lit,
                    Reason::Constraint(self.constraint.clone()),
                ));
            }
            Some(propagations)
        } else {
            None
        }
    }

    #[inline]
    fn no_watches_required(&mut self) -> bool {
        self.is_propagating_independent_of_assignment() || self.constraint.is_trivial()
    }

    #[inline]
    fn is_propagating_independent_of_assignment(&self) -> bool {
        let card = self.constraint.constraint.as_card();
        card.len() as i64 <= *card.get_degree()
    }

    #[inline]
    fn init_watches(&mut self, assign: &Assignment<BooleanVar>) -> WatchInit {
        if !self.watches.is_empty() {
            // Watches already defined.
            return WatchInit::Watching {
                propagated: vec![],
                watches: vec![],
            };
        }
        let card = self.constraint.constraint.as_card();
        if card.is_trivial() {
            return WatchInit::Watching {
                propagated: vec![],
                watches: vec![],
            };
        }

        let mut num_watches_found = 0;
        let num_watches_target = card.len().min(*card.get_degree() as usize + 1);
        for (pos, &lit) in card.get_lits().enumerate() {
            let value = unsafe { assign.get_lit_value_unchecked(lit) };
            match value {
                BoolValue::Unassigned | BoolValue::Assigned(true) => {
                    self.watches.insert(lit);
                    num_watches_found += 1;
                    if num_watches_found == num_watches_target {
                        self.next_pos = pos + 1;
                        return WatchInit::Watching {
                            propagated: vec![],
                            watches: self.watches.clone().into_iter().collect(),
                        };
                    }
                }
                BoolValue::Assigned(false) => {}
            }
        }

        // If we managed to get watches for all but one of the required watch, we propagated the watches.
        if num_watches_found == num_watches_target - 1 {
            // Save propagations.
            let propagated = self.watches.clone().into_iter().collect();
            // Assign last remaining watch to an unwatched literal.
            for &lit in card.get_lits() {
                if !self.watches.contains(&lit) {
                    self.watches.insert(lit);
                    break;
                }
            }
            WatchInit::Watching {
                propagated,
                watches: self.watches.clone().into_iter().collect(),
            }
        } else {
            self.watches.clear();
            WatchInit::Conflict
        }
    }

    fn update_watch(&mut self, old_watch: Lit, assign: &Assignment<BooleanVar>) -> WatchUpdate {
        let card = self.constraint.constraint.as_card();

        debug_assert_eq!(0.max(*card.get_degree()), self.watches.len() as i64 - 1);

        // Remove old watch from watches.
        self.watches.remove(&old_watch);

        let (llits, rlits) = unsafe { card.as_slice().split_at_unchecked(self.next_pos) };
        for (n, &lit) in (rlits.iter()).chain(llits.iter()).enumerate() {
            let value = unsafe { assign.get_lit_value_unchecked(lit) };
            match value {
                BoolValue::Unassigned | BoolValue::Assigned(true) => {
                    // Check if this literal is not already watched.
                    if !self.watches.contains(&lit) {
                        self.next_pos = ((self.next_pos + n) % card.len()) + 1;
                        self.watches.insert(lit);
                        return WatchUpdate::UnknownSingle {
                            propagated: None,
                            new_watches: lit,
                        };
                    }
                }
                BoolValue::Assigned(false) => {}
            }
        }

        // Unable to find a new literal to watch, hence we add the old watch back again. Maybe other watched literals are already satisfied.
        for &lit in self.watches.iter() {
            let value = unsafe { assign.get_lit_value_unchecked(lit) };
            if value == BoolValue::Assigned(false) {
                self.watches.insert(old_watch);
                return WatchUpdate::Conflict;
            }
        }

        // Cardinality constraint is propagating and will not propagate again. Hence, we can directly reset it by continuing to watch the `old_watch`.
        let propagated = self.watches.clone().into_iter().collect();
        self.watches.insert(old_watch);
        WatchUpdate::Unknown {
            propagated,
            new_watches: vec![old_watch],
        }
    }

    #[inline]
    fn get_watches(&self) -> impl Iterator<Item = &Lit> {
        self.watches.iter()
    }

    #[inline]
    fn get_constraint(&self) -> &Rc<DBConstraint> {
        &self.constraint
    }

    fn remove_watches(&self, watchlist: &mut Vec<Vec<Watch>>, watch_index: usize) {
        for lit in self.watches.iter() {
            let list = watchlist.get_mut(lit.get_lit_data()).unwrap();
            let index = list.iter().position(|w| w.index == watch_index).unwrap();
            list.swap_remove(index);
        }
    }
}
