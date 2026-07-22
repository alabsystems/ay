// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Per-variable data structure for the CDCL solver.
//!
//! Extracted from solver/mod.rs for maintainability (#5142).

use std::mem::size_of;

/// Sentinel value for VarData.reason indicating a decision variable (no reason clause).
/// Arena offsets cannot reach u32::MAX (4GB of clause data would exhaust memory first).
pub(crate) const NO_REASON: u32 = u32::MAX;

/// Tag bit for binary literal reasons in VarData.reason (#8034).
///
/// When set (bit 31), the remaining 31 bits encode a `Literal.0` value
/// (the OTHER literal from the binary clause). Arena clause offsets are
/// always < 2^31 (the arena is u32-indexed with max capacity ~2GB), so
/// bit 31 being clear unambiguously identifies a clause reference.
///
/// Encoding:
/// - `NO_REASON` (0xFFFF_FFFF): decision / unassigned
/// - Bit 31 clear: arena clause offset (`ClauseRef`)
/// - Bit 31 set, != `NO_REASON`: binary literal reason (remaining bits = `Literal.0`)
const BINARY_REASON_FLAG: u32 = 0x8000_0000;

/// Check if a reason value encodes a binary literal reason (#8034).
#[inline(always)]
pub(crate) fn is_binary_literal_reason(reason: u32) -> bool {
    reason != NO_REASON && reason & BINARY_REASON_FLAG != 0
}

/// Extract the raw literal value from a binary literal reason (#8034).
///
/// REQUIRES: `is_binary_literal_reason(reason)` is true.
#[inline(always)]
pub(crate) fn binary_reason_lit(reason: u32) -> u32 {
    reason & !BINARY_REASON_FLAG
}

/// Construct a binary literal reason from a raw literal value (#8034).
///
/// REQUIRES: `lit_raw` < 2^31 (all valid literal values satisfy this).
#[inline(always)]
pub(crate) fn make_binary_reason(lit_raw: u32) -> u32 {
    debug_assert!(
        lit_raw & BINARY_REASON_FLAG == 0,
        "BUG: make_binary_reason called with lit_raw {lit_raw:#x} that has bit 31 set"
    );
    let result = lit_raw | BINARY_REASON_FLAG;
    debug_assert!(
        result != NO_REASON,
        "BUG: make_binary_reason({lit_raw:#x}) produces NO_REASON — would corrupt reason tracking"
    );
    result
}

/// Check if a reason value encodes an arena clause reference (#8034).
#[inline(always)]
pub(crate) fn is_clause_reason(reason: u32) -> bool {
    reason != NO_REASON && reason & BINARY_REASON_FLAG == 0
}

/// Per-variable data packed for cache locality during conflict analysis.
/// CaDiCaL reference: `var.hpp` Var struct (16 bytes).
/// 16 bytes total: 4 variables per 64-byte cache line.
///
/// The `flags` field colocates conflict-analysis marks (seen, poison, keep,
/// removable) with level/reason so they share the same cache line (#6994).
/// CaDiCaL stores these in `Flags` alongside per-variable data.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[repr(C)]
pub(crate) struct VarData {
    /// Decision level at which variable was assigned (0 = root).
    pub level: u32,
    /// Trail position (index into trail Vec) when variable was assigned.
    /// CaDiCaL: `Var::trail` (int). u32 is sufficient (max 2^31 variables).
    pub trail_pos: u32,
    /// Reason clause reference. `NO_REASON` (u32::MAX) = no reason (decision variable).
    /// CaDiCaL: `Var::reason` (Clause*), nullptr = decision.
    /// Stored as raw u32 to avoid Option overhead (8 bytes -> 4 bytes).
    ///
    /// With jump reasons (#8034), bit 31 may be set to encode a binary literal
    /// reason instead of a clause reference. Use `is_clause_reason()` /
    /// `is_binary_literal_reason()` to distinguish.
    pub reason: u32,
    /// Conflict analysis flags, colocated for cache locality (#6994).
    /// Bit 0: seen (conflict analysis mark).
    /// Bits 1-7: reserved for poison/keep/removable/minimize marks.
    pub flags: u8,
    /// Padding to maintain 16-byte alignment (4 vars per cache line).
    pub _pad: [u8; 3],
}

// Compile-time enforcement of VarData field offsets (#8565).
//
// JIT-emitted machine code (ay-jit minimize_jit.rs, conflict_jit.rs) hardcodes
// these byte offsets for direct memory access into VarData arrays. If the struct
// layout changes (fields reordered, new field inserted, padding altered), JIT
// code will silently read wrong data. These assertions make layout changes a
// compile error instead of a runtime memory corruption bug.
const _: () = {
    assert!(
        size_of::<VarData>() == 16,
        "VarData must be 16 bytes (4 per cache line)"
    );
    assert!(
        std::mem::offset_of!(VarData, level) == 0,
        "VarData.level must be at offset 0"
    );
    assert!(
        std::mem::offset_of!(VarData, trail_pos) == 4,
        "VarData.trail_pos must be at offset 4"
    );
    assert!(
        std::mem::offset_of!(VarData, reason) == 8,
        "VarData.reason must be at offset 8"
    );
    assert!(
        std::mem::offset_of!(VarData, flags) == 12,
        "VarData.flags must be at offset 12"
    );
};

impl Default for VarData {
    fn default() -> Self {
        Self::UNASSIGNED
    }
}

impl VarData {
    /// Bit 0 of `flags`: conflict analysis seen mark.
    const FLAG_SEEN: u8 = 1 << 0;

    /// Public accessor for FLAG_SEEN, used by enqueue paths to preserve the
    /// seen flag across struct-write VarData updates (#8042).
    pub(crate) const FLAG_SEEN_PUB: u8 = Self::FLAG_SEEN;
    /// Bit 1 of `flags`: reason clause is binary.
    /// Set on assignment when the reason is a binary clause, cleared on
    /// unassignment. Used by jump reasons (Kissat fastassign.h:12-19, #8034)
    /// to detect binary reason chains without arena access.
    const FLAG_BINARY_REASON: u8 = 1 << 1;

    /// Public accessor for FLAG_BINARY_REASON, used by `enqueue_bcp_binary`
    /// to construct VarData structs with the flag pre-set (#8042).
    pub(crate) const FLAG_BINARY_REASON_PUB: u8 = Self::FLAG_BINARY_REASON;

    /// Bit 2 of `flags`: lazy theory reason (#8467).
    ///
    /// When set, the `reason` field does NOT contain an arena clause offset.
    /// Instead, the reason must be materialized on demand by calling
    /// `Extension::explain_lazy_reason()` during conflict analysis. The
    /// `reason` field stores the index into the solver's `lazy_theory_reasons`
    /// table which holds the theory-opaque `reason_data: u64`.
    ///
    /// This defers the O(reason_len) clause allocation from propagation time
    /// to conflict analysis time. ~90% of propagated variables are never
    /// resolved during conflict analysis, so their reasons never need to be
    /// materialized. Reference: Z3's `u_dependency` in `lp/lp_bound_propagator.h`.
    const FLAG_LAZY_THEORY_REASON: u8 = 1 << 2;

    /// Public accessor for FLAG_LAZY_THEORY_REASON (#8467).
    pub(crate) const FLAG_LAZY_THEORY_REASON_PUB: u8 = Self::FLAG_LAZY_THEORY_REASON;

    /// Default unassigned state.
    pub(crate) const UNASSIGNED: Self = Self {
        level: 0,
        trail_pos: u32::MAX,
        reason: NO_REASON,
        flags: 0,
        _pad: [0; 3],
    };

    /// Check if the seen flag is set (conflict analysis).
    #[inline(always)]
    pub(crate) fn is_seen(self) -> bool {
        self.flags & Self::FLAG_SEEN != 0
    }

    /// Set or clear the seen flag.
    #[inline(always)]
    pub(crate) fn set_seen(&mut self, val: bool) {
        if val {
            self.flags |= Self::FLAG_SEEN;
        } else {
            self.flags &= !Self::FLAG_SEEN;
        }
    }

    /// Check if the reason clause is binary (jump reasons, #8034).
    #[inline(always)]
    pub(crate) fn is_binary_reason(self) -> bool {
        self.flags & Self::FLAG_BINARY_REASON != 0
    }

    /// Set or clear the binary reason flag.
    #[inline(always)]
    pub(crate) fn set_binary_reason(&mut self, val: bool) {
        if val {
            self.flags |= Self::FLAG_BINARY_REASON;
        } else {
            self.flags &= !Self::FLAG_BINARY_REASON;
        }
    }

    /// Check if this variable has a lazy theory reason (#8467).
    #[inline(always)]
    pub(crate) fn is_lazy_theory_reason(self) -> bool {
        self.flags & Self::FLAG_LAZY_THEORY_REASON != 0
    }

    /// Set or clear the lazy theory reason flag (#8467).
    #[inline(always)]
    pub(crate) fn set_lazy_theory_reason(&mut self, val: bool) {
        if val {
            self.flags |= Self::FLAG_LAZY_THEORY_REASON;
        } else {
            self.flags &= !Self::FLAG_LAZY_THEORY_REASON;
        }
    }
}

// Compile-time assertion: VarData must be exactly 16 bytes.
const _: () = assert!(size_of::<VarData>() == 16);

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_no_reason_is_not_binary() {
        assert!(!is_binary_literal_reason(NO_REASON));
        assert!(!is_clause_reason(NO_REASON));
    }

    #[test]
    fn test_clause_reason_encoding() {
        // Low arena offsets are clause reasons (bit 31 clear).
        for offset in [0u32, 1, 100, 1000, 0x7FFF_FFFE] {
            assert!(
                is_clause_reason(offset),
                "offset {offset} should be clause reason"
            );
            assert!(
                !is_binary_literal_reason(offset),
                "offset {offset} should not be binary reason"
            );
        }
    }

    #[test]
    fn test_binary_reason_encoding() {
        // Literal raw values are < 2^31; encoding sets bit 31.
        for lit_raw in [0u32, 1, 2, 3, 100, 1000, 0x7FFF_FFFE] {
            let encoded = make_binary_reason(lit_raw);
            assert!(
                is_binary_literal_reason(encoded),
                "encoded {encoded:#x} should be binary reason"
            );
            assert!(
                !is_clause_reason(encoded),
                "encoded {encoded:#x} should not be clause reason"
            );
            assert_eq!(
                binary_reason_lit(encoded),
                lit_raw,
                "round-trip failed for {lit_raw}"
            );
        }
    }

    #[test]
    fn test_binary_reason_flag_bit31() {
        let encoded = make_binary_reason(0);
        assert_eq!(encoded, BINARY_REASON_FLAG);
        assert_eq!(binary_reason_lit(encoded), 0);
    }

    #[test]
    fn test_vardata_binary_reason_flag() {
        let mut vd = VarData::UNASSIGNED;
        assert!(!vd.is_binary_reason());
        vd.set_binary_reason(true);
        assert!(vd.is_binary_reason());
        vd.set_binary_reason(false);
        assert!(!vd.is_binary_reason());
    }

    #[test]
    fn test_seen_and_binary_reason_orthogonal() {
        let mut vd = VarData::UNASSIGNED;
        // Setting seen does not affect binary_reason and vice versa.
        vd.set_seen(true);
        assert!(vd.is_seen());
        assert!(!vd.is_binary_reason());

        vd.set_binary_reason(true);
        assert!(vd.is_seen());
        assert!(vd.is_binary_reason());

        vd.set_seen(false);
        assert!(!vd.is_seen());
        assert!(vd.is_binary_reason());

        vd.set_binary_reason(false);
        assert!(!vd.is_seen());
        assert!(!vd.is_binary_reason());
    }

    #[test]
    fn test_binary_reason_no_overlap_with_no_reason() {
        // NO_REASON has all bits set (0xFFFF_FFFF). make_binary_reason cannot
        // produce NO_REASON because bit 31 is set but bits 0-30 can't all be set
        // (that would require lit_raw = 0x7FFF_FFFF which is a valid literal raw).
        // However, NO_REASON is explicitly excluded by is_binary_literal_reason.
        assert!(!is_binary_literal_reason(NO_REASON));
    }

    #[test]
    fn test_max_literal_raw_binary_reason() {
        // Maximum valid literal raw: 0x7FFF_FFFE (bit 31 clear).
        let max_lit = 0x7FFF_FFFEu32;
        let encoded = make_binary_reason(max_lit);
        assert_eq!(encoded, 0xFFFF_FFFE);
        assert!(is_binary_literal_reason(encoded));
        assert_eq!(binary_reason_lit(encoded), max_lit);
    }
}
