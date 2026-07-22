// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// Andrew Yates <andrewyates.name@gmail.com>
//! Guard bits for compiled clause deletion tracking.
//!
//! Each compiled clause has a `u8` guard value: 1 = active (propagate normally),
//! 0 = deleted (skip propagation). The guard array is indexed by clause arena
//! offset (the same ID used as the reason in propagation), allowing O(1)
//! deletion marking without recompilation.
//!
//! JIT-compiled propagation functions receive the guard array base pointer via
//! `PropagationContext::guards` and check `guards[clause_id]` before executing
//! clause logic. Since deletions are rare, the branch is well-predicted.

/// Guard bits for compiled clauses. Each clause has a u8 guard:
/// - 1 = clause is active (propagate normally)
/// - 0 = clause is deleted (skip propagation)
///
/// The guard array is indexed by clause arena offset (same ID used as
/// reason in propagation). This allows O(1) deletion marking.
pub struct ClauseGuards {
    /// Guard bits indexed by clause arena offset.
    /// Using u8 instead of bool for direct memory-mapped access from JIT code.
    guards: Vec<u8>,
}

impl ClauseGuards {
    /// Create a guard array with the given capacity, all guards active (1).
    #[must_use]
    pub fn new(capacity: usize) -> Self {
        Self {
            guards: vec![1u8; capacity],
        }
    }

    /// Mark a clause as deleted (guard = 0). The compiled propagation function
    /// will skip this clause on the next invocation.
    pub fn mark_deleted(&mut self, clause_id: u32) {
        if let Some(g) = self.guards.get_mut(clause_id as usize) {
            *g = 0;
        }
    }

    /// Mark a clause as active (guard = 1). Used when a clause is re-added
    /// or when restoring after a failed inprocessing attempt.
    pub fn mark_active(&mut self, clause_id: u32) {
        if let Some(g) = self.guards.get_mut(clause_id as usize) {
            *g = 1;
        }
    }

    /// Check if a clause guard is active.
    #[must_use]
    pub fn is_active(&self, clause_id: u32) -> bool {
        self.guards.get(clause_id as usize).copied().unwrap_or(0) != 0
    }

    /// Raw pointer to the guard array for JIT code access.
    ///
    /// The pointer is valid as long as `self` is alive and no reallocation
    /// occurs (i.e., no calls to `ensure_capacity` that trigger growth).
    ///
    /// # Safety contract for callers
    ///
    /// JIT-compiled propagation functions dereference this pointer at
    /// `guards[clause_id]` offsets. The caller must ensure:
    /// - `clause_id < self.len()` for all clause IDs in the compiled formula
    /// - No `ensure_capacity` call occurs between obtaining this pointer and
    ///   the last JIT function call (reallocation would invalidate the pointer)
    /// - No concurrent mutation of the guard array while JIT code is executing
    #[must_use]
    pub fn as_ptr(&self) -> *const u8 {
        self.guards.as_ptr()
    }

    /// Grow the guard array if needed so that `max_id` is a valid index.
    /// New entries default to active (1).
    pub fn ensure_capacity(&mut self, max_id: u32) {
        let needed = max_id as usize + 1;
        if needed > self.guards.len() {
            self.guards.resize(needed, 1u8);
        }
    }

    /// Set all guards back to active (1). Called after a full recompilation
    /// that rebuilds all propagation functions from the current clause set.
    pub fn reset_all_active(&mut self) {
        self.guards.fill(1u8);
    }

    /// Count the number of active guards (for diagnostics).
    #[must_use]
    pub fn count_active(&self) -> usize {
        self.guards.iter().filter(|&&g| g != 0).count()
    }

    /// Total number of guard slots.
    #[must_use]
    pub fn len(&self) -> usize {
        self.guards.len()
    }

    /// Whether the guard array is empty.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.guards.is_empty()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_guards_default_active() {
        let guards = ClauseGuards::new(10);
        for i in 0..10 {
            assert!(guards.is_active(i), "guard {i} should be active by default");
        }
        assert_eq!(guards.count_active(), 10);
        assert_eq!(guards.len(), 10);
    }

    #[test]
    fn test_guards_mark_deleted() {
        let mut guards = ClauseGuards::new(5);
        guards.mark_deleted(2);
        assert!(guards.is_active(0));
        assert!(guards.is_active(1));
        assert!(!guards.is_active(2), "guard 2 should be deleted");
        assert!(guards.is_active(3));
        assert!(guards.is_active(4));
        assert_eq!(guards.count_active(), 4);

        // Re-activate
        guards.mark_active(2);
        assert!(guards.is_active(2));
        assert_eq!(guards.count_active(), 5);
    }

    #[test]
    fn test_guards_ensure_capacity() {
        let mut guards = ClauseGuards::new(3);
        assert_eq!(guards.len(), 3);

        // Mark one deleted before growing
        guards.mark_deleted(1);

        // Grow to accommodate clause_id 9
        guards.ensure_capacity(9);
        assert_eq!(guards.len(), 10);

        // Original entries preserved
        assert!(guards.is_active(0));
        assert!(
            !guards.is_active(1),
            "deleted guard should stay deleted after grow"
        );
        assert!(guards.is_active(2));

        // New entries are active
        for i in 3..10 {
            assert!(guards.is_active(i), "new guard {i} should be active");
        }

        // Ensure capacity with smaller value is a no-op
        guards.ensure_capacity(5);
        assert_eq!(guards.len(), 10);
    }

    #[test]
    fn test_guards_reset_all() {
        let mut guards = ClauseGuards::new(5);
        guards.mark_deleted(0);
        guards.mark_deleted(2);
        guards.mark_deleted(4);
        assert_eq!(guards.count_active(), 2);

        guards.reset_all_active();
        assert_eq!(guards.count_active(), 5);
        for i in 0..5 {
            assert!(
                guards.is_active(i),
                "guard {i} should be active after reset"
            );
        }
    }

    #[test]
    fn test_guards_out_of_bounds() {
        let guards = ClauseGuards::new(3);
        // Out-of-bounds reads return false (inactive)
        assert!(!guards.is_active(100));

        let mut guards = ClauseGuards::new(3);
        // Out-of-bounds writes are silent no-ops
        guards.mark_deleted(100);
        guards.mark_active(100);
        assert_eq!(guards.len(), 3);
    }

    #[test]
    fn test_guards_as_ptr() {
        let guards = ClauseGuards::new(4);
        let ptr = guards.as_ptr();
        assert!(!ptr.is_null());
        // SAFETY: ptr is valid for guards.len() bytes, all initialized to 1.
        unsafe {
            for i in 0..4 {
                assert_eq!(*ptr.add(i), 1u8);
            }
        }
    }

    #[test]
    fn test_guards_empty() {
        let guards = ClauseGuards::new(0);
        assert!(guards.is_empty());
        assert_eq!(guards.count_active(), 0);
    }
}
