// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// Andrew Yates <andrewyates.name@gmail.com>
//! Propagation context: the C-ABI struct passed to JIT-compiled propagation
//! functions. Layout must be `#[repr(C)]` so generated machine code can
//! access fields at fixed offsets.

/// The runtime context passed (by pointer) to every compiled propagation
/// function. Fields are accessed by generated machine code at known byte offsets.
///
/// # Encoding
///
/// Literals use the standard DIMACS-like encoding used throughout ay-sat:
///   `encoded = var * 2 + polarity`  where polarity 0 = positive, 1 = negative.
///
/// Variable assignments in `vals`:
///   0 = unassigned, 1 = true, -1 (0xFF as u8 / -1 as i8) = false.
#[repr(C)]
pub struct PropagationContext {
    /// Literal assignment values indexed by encoded literal (`var * 2 + polarity`).
    /// `vals[lit]`: 0 = unassigned, 1 = satisfied, -1 (as i8) = falsified.
    /// Mutable because JIT-compiled propagation functions update vals[] inline
    /// when enqueuing propagated literals, so subsequent clauses see the assignment.
    pub vals: *mut i8,
    /// Trail array for enqueuing new propagations (encoded literals).
    pub trail: *mut u32,
    /// Pointer to current trail length (write position).
    pub trail_len: *mut u32,
    /// Pointer to conflict clause id. 0 = no conflict.
    pub conflict: *mut u32,
    /// Decision levels per variable, indexed by variable number.
    pub levels: *const u32,
    /// Reason clause ids per variable, indexed by variable number.
    pub reasons: *mut u32,
    /// Current decision level (value, not pointer).
    pub decision_level: u32,
    /// Padding to align `guards` pointer to 8 bytes after the u32 field.
    pub pad0: u32,
    /// Guard bits for compiled clauses. Each byte is 1 (active) or 0 (deleted).
    /// Compiled propagation functions check `guards[clause_id]` before
    /// propagating. Null if guard checking is disabled.
    pub guards: *const u8,
}

// Byte offsets for each field, verified by the test below.
//
// With the register-based calling convention (#8260), these offsets are no
// longer used by machine code generation (args are passed in registers, not
// via a struct pointer). They remain as test-only constants to verify the
// `#[repr(C)]` layout is stable — if someone adds/removes fields, the test
// catches layout drift even though it no longer affects codegen.

// Byte offsets for `PropagationContext` fields. Kept for tests that verify the
// C layout remains stable for native helpers.
#[cfg(test)]
pub(crate) const OFFSET_VALS: i32 = 0;
#[cfg(test)]
pub(crate) const OFFSET_TRAIL: i32 = 8;
#[cfg(test)]
pub(crate) const OFFSET_TRAIL_LEN: i32 = 16;
#[cfg(test)]
pub(crate) const OFFSET_CONFLICT: i32 = 24;
#[cfg(test)]
pub(crate) const OFFSET_LEVELS: i32 = 32;
#[cfg(test)]
pub(crate) const OFFSET_REASONS: i32 = 40;
#[cfg(test)]
pub(crate) const OFFSET_DECISION_LEVEL: i32 = 48;
// pad0 is at offset 52, 4 bytes
#[cfg(test)]
pub(crate) const OFFSET_GUARDS: i32 = 56;

#[cfg(test)]
mod tests {
    use std::mem::offset_of;

    use super::*;

    #[test]
    fn test_context_offsets_match_repr_c() {
        assert_eq!(
            size_of::<PropagationContext>(),
            64,
            "PropagationContext should be 64 bytes on 64-bit"
        );
        assert_eq!(offset_of!(PropagationContext, vals) as i32, OFFSET_VALS);
        assert_eq!(offset_of!(PropagationContext, trail) as i32, OFFSET_TRAIL);
        assert_eq!(
            offset_of!(PropagationContext, trail_len) as i32,
            OFFSET_TRAIL_LEN
        );
        assert_eq!(
            offset_of!(PropagationContext, conflict) as i32,
            OFFSET_CONFLICT
        );
        assert_eq!(offset_of!(PropagationContext, levels) as i32, OFFSET_LEVELS);
        assert_eq!(
            offset_of!(PropagationContext, reasons) as i32,
            OFFSET_REASONS
        );
        assert_eq!(
            offset_of!(PropagationContext, decision_level) as i32,
            OFFSET_DECISION_LEVEL
        );
        assert_eq!(offset_of!(PropagationContext, guards) as i32, OFFSET_GUARDS);
    }
}
