//! Collection of [`PBConstraint`](crate::pb_constraint::PBConstraint) with [`PBObjective`] to form a problem.

use crate::{pb_constraint::PBConstraintEnum, pb_objective::PBObjective};

/// Data structure to store a collection of constraints and an optional objective function.
#[derive(Debug, Default)]
pub struct Formula {
    /// The constraints in the problem.
    pub constraints: Vec<PBConstraintEnum>,
    /// The objective to be minimized.
    pub objective: Option<PBObjective>,
}

impl Formula {
    /// Construct a new [`Formula`] with an initial allocated capacity.
    #[inline]
    pub fn with_capacity(capacity: usize) -> Self {
        Formula {
            constraints: Vec::with_capacity(capacity),
            objective: None,
        }
    }

    /// Returns the number of constraints in the [`Formula`].
    #[inline]
    pub fn len(&self) -> usize {
        self.constraints.len()
    }

    /// Test if the [`Formula`] does contain any constraint.
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.constraints.is_empty()
    }

    /// The allocated capacity for the [`Formula`].
    #[inline]
    pub fn capacity(&self) -> usize {
        self.constraints.capacity()
    }

    /// Reserve capacity for exactly `additional` many more constraints in the constraint set.
    ///
    /// This function can be used to avoid reallocation of the memory inside the constraint set when the number of `additional` constraints is known.
    ///
    /// # Panics
    /// Aborts the process if the allocation fails. Use
    /// [`try_reserve_exact`](Formula::try_reserve_exact) when `additional` comes from an input
    /// file rather than from a count the caller measured itself.
    #[inline]
    pub fn reserve_exact(&mut self, additional: usize) {
        self.constraints.reserve_exact(additional);
    }

    /// Best-effort version of [`reserve_exact`](Formula::reserve_exact): a reservation the
    /// allocator cannot satisfy is silently skipped instead of aborting the process.
    ///
    /// A reservation is an optimisation, never a requirement — the vector grows on demand
    /// either way — so this is what a parser should use for a count it read out of a file
    /// header. A DIMACS `p cnf 1 999999999999999` line otherwise takes the process down with
    /// `memory allocation of ... bytes failed` before a single clause has been parsed, which is
    /// a crash rather than a verdict or a diagnosis.
    #[inline]
    pub fn try_reserve_exact(&mut self, additional: usize) {
        let _ = self.constraints.try_reserve_exact(additional);
    }
}
