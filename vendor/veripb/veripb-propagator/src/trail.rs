//! Propagation trail storing the assignment and propagation reasons in order.

use core::panic;
use std::rc::Rc;

use veripb_formula::prelude::*;

use crate::error::PropagatorError;

/// Propagation reason.
#[derive(Debug, Default, Clone, PartialEq)]
pub enum Reason {
    /// Propagation by a given assignment meaning that the propagation of this literal is motivated externally.
    #[default]
    Assumption,
    /// The propagation is due to the given constraint.
    Constraint(Rc<DBConstraint>),
}

impl Reason {
    /// Get the reason constraint from the `Reason`.
    ///
    /// This function panics if the `Reason` was an `Assumption`.
    #[inline]
    pub fn unwrap(&self) -> &Rc<DBConstraint> {
        match self {
            Reason::Assumption => panic!("The reason is not a constraint."),
            Reason::Constraint(constraint) => constraint,
        }
    }
}

/// Propagation of one literal. A propagation consists of a [`Lit`] that is propagated to true and a [`Reason`] for the propagation.
#[derive(Debug, Clone, PartialEq)]
pub struct Propagation {
    /// Literal that has been propagated.
    pub lit: Lit,
    /// Reason for the propagation of the literal.
    pub reason: Reason,
}

impl Propagation {
    /// Construct a new propagation with the given `lit` and `reason`.
    pub fn new(lit: Lit, reason: Reason) -> Self {
        Propagation { lit, reason }
    }
}

/// Trail of propagation.
///
/// Propagations are stored in a [`Vec<Propagation>`]. To easily access the assignment of a variable, an [`Assignment`] is kept in sync with the propagations.
///
/// # Invariants
/// 1. The [`Self::assignment`] and [`Self::trail`] are in sync. This means that any literal propagation in [`Self::trail`] is satisfied by the [`Self::assignment`] and for any assigned variable in [`Self::assignment`], there is a propagation on the [`Self::trail`] that is satisfied by this variable assignment.
#[derive(Debug, Default, Clone)]
pub struct Trail {
    /// Current assignment of variables to values for this trail.
    pub assignment: Assignment<BooleanVar>,
    /// Propagations of literals in order of propagation.
    pub trail: Vec<Propagation>,
    /// If [`None`], then propagation is not conflicting. If [`Some`], then this field contains the reason for the conflict.
    pub conflict: Option<Reason>,
}

impl Trail {
    /// Initialize a [`Trail`] with a given size for the stored [`Self::assignment`].
    #[inline]
    pub fn with_size(size: usize) -> Self {
        Trail {
            assignment: Assignment::with_size(size),
            ..Default::default()
        }
    }

    /// Add a new [`Propagation`] to the trail.
    ///
    /// The option `mark_reason` specifies if the reason should remember that it is a reason on the trail. Currently, this is only used for constraints, so that constraints know when they are used as reasons on the trail.
    #[inline]
    pub fn push(
        &mut self,
        propagation: Propagation,
        mark_reason: bool,
    ) -> Result<(), PropagatorError> {
        match unsafe { self.assignment.get_lit_value_unchecked(propagation.lit) } {
            BoolValue::Unassigned => {
                unsafe {
                    self.assignment
                        .set_lit_value_unchecked(propagation.lit, BoolValue::Assigned(true))
                };
                if mark_reason && let Reason::Constraint(constraint) = &propagation.reason {
                    constraint.header.borrow_mut().is_saved_reason = true;
                }
                self.trail.push(propagation);
            }
            BoolValue::Assigned(false) => {
                if mark_reason && let Reason::Constraint(constraint) = &propagation.reason {
                    constraint.header.borrow_mut().is_saved_reason = true;
                }
                self.conflict = Some(propagation.reason);
                return Err(PropagatorError::TrailContainsNegatedLit);
            }
            BoolValue::Assigned(true) => {}
        }

        Ok(())
    }

    /// Remove the last propagation from the [`Self::trail`].
    #[inline]
    pub fn pop(&mut self) -> Option<Propagation> {
        match self.trail.pop() {
            Some(propagation) => {
                unsafe {
                    self.assignment
                        .set_lit_value_unchecked(propagation.lit, BoolValue::Unassigned)
                };
                Some(propagation)
            }
            None => None,
        }
    }

    /// Number of variables the assignment in the trail can keep track of.
    #[inline]
    pub fn size(&self) -> usize {
        self.assignment.len()
    }

    /// Resize the assignment of the trail to have enough capacity for all variables that could be propagated on the [`Trail`].
    #[inline]
    pub fn resize(&mut self, new_len: usize) {
        if new_len != self.size() {
            self.assignment.resize(new_len);
        }
    }

    /// Check if [`Trail`] is conflicting.
    #[inline]
    pub fn is_conflicting(&self) -> bool {
        self.conflict.is_some()
    }

    /// The length of [`Self::trail`], which is equivalent to the number of assigned variables by the trail.
    #[inline]
    pub fn len(&self) -> usize {
        self.trail.len()
    }

    /// Check if [`Self::trail`] is empty.
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Add a propagation by assumption to the [`Trail`].
    #[inline]
    pub fn add_assumptions(&mut self, assumptions: &Vec<Lit>) -> Result<(), PropagatorError> {
        for lit in assumptions {
            self.push(Propagation::new(*lit, Reason::Assumption), false)?
        }
        Ok(())
    }
}

impl From<(&Vec<Lit>, Assignment<BooleanVar>)> for Trail {
    fn from(value: (&Vec<Lit>, Assignment<BooleanVar>)) -> Self {
        let (lierals, assignment) = value;
        let mut trail = Trail {
            assignment,
            ..Default::default()
        };
        for lit in lierals {
            trail.trail.push(Propagation::new(*lit, Reason::Assumption));
        }

        trail
    }
}
