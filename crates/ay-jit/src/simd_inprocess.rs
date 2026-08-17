// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! SIMD batch literal scanning for SAT inprocessing passes.
//!
//! While SIMD for the BCP inner loop was found non-viable because 2WL filtering
//! avoids most clause visits, inprocessing passes like subsumption, BCE, and
//! vivification iterate over ENTIRE clause databases checking
//! properties like "does clause C contain literal L?" or "is clause D a
//! subset of clause C?". This is a pure scan workload where SIMD shines.
//!
//! ## Design
//!
//! `SimdClauseScanner` packs a clause database into a cache-friendly arena
//! of `i32` literals. Each clause is stored as:
//! ```text
//! [lit0, lit1, ..., litN, SENTINEL, ..., SENTINEL]
//! ```
//! Padded to a multiple of 4 elements (128 bits) so SIMD loads never cross
//! clause boundaries unexpectedly. The sentinel value `i32::MAX` is used
//! for padding; it cannot match any valid literal since literals are encoded
//! as `var * 2 + polarity` with `var < i32::MAX / 2`.
//!
//! ## Operations
//!
//! - `contains_literal(lit)` -- find all clause indices containing a literal.
//!   NEON/SSE2 parallel comparison of 4 i32 lanes per cycle.
//! - `subsumes_scalar(a, b)` -- check if every literal in `a` appears in `b`.
//! - `batch_subsumption_check(pairs)` -- check many (a, b) subsumption pairs.
//! - `find_clauses_containing(lit)` -- batch occurrence lookup.
//!
//! ## Platform support
//!
//! - `aarch64`: NEON intrinsics via `std::arch::aarch64`
//! - `x86_64`: SSE2 intrinsics via `std::arch::x86_64`
//! - Scalar fallback for all other architectures

/// Sentinel value used for SIMD padding. Cannot collide with valid literals
/// since literal encoding `var * 2 + polarity` requires `var < i32::MAX / 2`.
const SENTINEL: i32 = i32::MAX;

/// SIMD-friendly clause database scanner for inprocessing.
///
/// Stores clauses in a flat, cache-aligned arena of `i32` literals with
/// 4-element padding for SIMD alignment. Supports batch literal containment
/// checks and subsumption queries.
pub struct SimdClauseScanner {
    /// Flat arena of clause literals. Each clause occupies a contiguous
    /// range padded to a multiple of 4 elements with `SENTINEL` values.
    arena: Vec<i32>,
    /// Start offset of each clause in `arena` (element index, not byte).
    offsets: Vec<u32>,
    /// Number of real (non-padding) literals in each clause.
    lengths: Vec<u16>,
    /// Padded length (multiple of 4) for each clause, in elements.
    padded_lengths: Vec<u16>,
}

impl Default for SimdClauseScanner {
    fn default() -> Self {
        Self::new()
    }
}

impl SimdClauseScanner {
    /// Create a new empty scanner.
    pub fn new() -> Self {
        Self {
            arena: Vec::new(),
            offsets: Vec::new(),
            lengths: Vec::new(),
            padded_lengths: Vec::new(),
        }
    }

    /// Create a scanner with pre-allocated capacity.
    pub fn with_capacity(num_clauses: usize, total_lits: usize) -> Self {
        // Over-estimate arena by ~25% for padding.
        let arena_cap = total_lits + total_lits / 4 + num_clauses * 4;
        Self {
            arena: Vec::with_capacity(arena_cap),
            offsets: Vec::with_capacity(num_clauses),
            lengths: Vec::with_capacity(num_clauses),
            padded_lengths: Vec::with_capacity(num_clauses),
        }
    }

    /// Add a clause to the scanner. Literals are stored as raw i32 values
    /// (the `.0` field of `Literal(u32)` cast to `i32`).
    pub fn push(&mut self, lits: &[i32]) {
        let offset = self.arena.len() as u32;
        let len = lits.len() as u16;
        // Pad to multiple of 4.
        let padded = lits.len().div_ceil(4) * 4;
        let padded_len = padded as u16;

        self.offsets.push(offset);
        self.lengths.push(len);
        self.padded_lengths.push(padded_len);

        self.arena.extend_from_slice(lits);
        // Fill remaining slots with sentinel.
        for _ in lits.len()..padded {
            self.arena.push(SENTINEL);
        }
    }

    /// Number of clauses in the scanner.
    pub fn len(&self) -> usize {
        self.offsets.len()
    }

    /// Whether the scanner contains no clauses.
    pub fn is_empty(&self) -> bool {
        self.offsets.is_empty()
    }

    /// Get the literals of clause `idx` (without padding).
    pub fn clause_lits(&self, idx: usize) -> &[i32] {
        let off = self.offsets[idx] as usize;
        let len = self.lengths[idx] as usize;
        &self.arena[off..off + len]
    }

    // ------------------------------------------------------------------
    // Scalar implementations (portable baseline)
    // ------------------------------------------------------------------

    /// Check if a clause contains a specific literal (scalar).
    fn clause_contains_scalar(&self, clause_idx: usize, lit: i32) -> bool {
        self.clause_lits(clause_idx).contains(&lit)
    }

    /// Find all clause indices containing `lit` (scalar).
    pub fn find_clauses_containing_scalar(&self, lit: i32) -> Vec<u32> {
        let mut result = Vec::new();
        for i in 0..self.len() {
            if self.clause_contains_scalar(i, lit) {
                result.push(i as u32);
            }
        }
        result
    }

    /// Check if every literal in `a_lits` appears in `b_lits` (scalar).
    /// This means clause A subsumes clause B (A is a subset of B).
    pub fn subsumes_scalar(a_lits: &[i32], b_lits: &[i32]) -> bool {
        // For subsumption, |A| <= |B| is required.
        if a_lits.len() > b_lits.len() {
            return false;
        }
        a_lits.iter().all(|a| b_lits.contains(a))
    }

    /// Batch subsumption check: for each (a_idx, b_idx) pair, check if
    /// clause A subsumes clause B (scalar).
    pub fn batch_subsumption_check_scalar(
        &self,
        pairs: &[(usize, usize)],
    ) -> Vec<(usize, usize, bool)> {
        pairs
            .iter()
            .map(|&(a, b)| {
                let a_lits = self.clause_lits(a);
                let b_lits = self.clause_lits(b);
                (a, b, Self::subsumes_scalar(a_lits, b_lits))
            })
            .collect()
    }

    // ------------------------------------------------------------------
    // SIMD-accelerated implementations
    // ------------------------------------------------------------------

    /// Find all clause indices containing `lit` using SIMD.
    ///
    /// Dispatches to the best available SIMD path.
    pub fn find_clauses_containing(&self, lit: i32) -> Vec<u32> {
        #[cfg(target_arch = "aarch64")]
        {
            // SAFETY: arena is a valid, contiguous i32 slice. All loads
            // are bounded by offset + padded_length which is within arena.
            unsafe { self.find_clauses_containing_neon(lit) }
        }
        #[cfg(target_arch = "x86_64")]
        {
            // SAFETY: same invariants as NEON path.
            unsafe { self.find_clauses_containing_sse2(lit) }
        }
        #[cfg(not(any(target_arch = "aarch64", target_arch = "x86_64")))]
        {
            self.find_clauses_containing_scalar(lit)
        }
    }

    /// Batch subsumption check using SIMD-accelerated literal lookup.
    pub fn batch_subsumption_check(&self, pairs: &[(usize, usize)]) -> Vec<(usize, usize, bool)> {
        #[cfg(target_arch = "aarch64")]
        {
            pairs
                .iter()
                .map(|&(a, b)| {
                    let a_lits = self.clause_lits(a);
                    let b_off = self.offsets[b] as usize;
                    let b_len = self.lengths[b] as usize;
                    let b_padded = self.padded_lengths[b] as usize;
                    if a_lits.len() > b_len {
                        return (a, b, false);
                    }
                    // SAFETY: b_off + b_padded is within arena bounds (guaranteed by push).
                    let result = unsafe {
                        Self::subsumes_neon(a_lits, &self.arena[b_off..b_off + b_padded], b_len)
                    };
                    (a, b, result)
                })
                .collect()
        }
        #[cfg(target_arch = "x86_64")]
        {
            pairs
                .iter()
                .map(|&(a, b)| {
                    let a_lits = self.clause_lits(a);
                    let b_off = self.offsets[b] as usize;
                    let b_len = self.lengths[b] as usize;
                    let b_padded = self.padded_lengths[b] as usize;
                    if a_lits.len() > b_len {
                        return (a, b, false);
                    }
                    // SAFETY: b_off + b_padded is within arena bounds.
                    let result = unsafe {
                        Self::subsumes_sse2(a_lits, &self.arena[b_off..b_off + b_padded], b_len)
                    };
                    (a, b, result)
                })
                .collect()
        }
        #[cfg(not(any(target_arch = "aarch64", target_arch = "x86_64")))]
        {
            self.batch_subsumption_check_scalar(pairs)
        }
    }

    // ------------------------------------------------------------------
    // NEON (aarch64) implementation
    // ------------------------------------------------------------------

    /// Find clauses containing `lit` using NEON 4-lane loads.
    ///
    /// # Safety
    ///
    /// This relies on the scanner construction invariant: every clause slice in
    /// `arena` is padded to a multiple of 4 `i32` elements, so each vector load
    /// reads four initialized elements within the clause extent. NEON loads used
    /// here do not require 16-byte alignment; pointer validity and 4-lane
    /// padding are the relevant external code generation native dispatch contract.
    #[cfg(target_arch = "aarch64")]
    unsafe fn find_clauses_containing_neon(&self, lit: i32) -> Vec<u32> {
        use std::arch::aarch64::*;

        let mut result = Vec::new();
        // SAFETY: vdupq_n_s32 broadcasts a scalar to all 4 lanes of a
        // 128-bit NEON register. No memory access, always safe.
        let target = unsafe { vdupq_n_s32(lit) };
        let arena_ptr = self.arena.as_ptr();

        for i in 0..self.len() {
            let off = self.offsets[i] as usize;
            let real_len = self.lengths[i] as usize;
            let padded = self.padded_lengths[i] as usize;
            let mut found = false;

            // Scan clause in 4-element chunks using NEON.
            let mut j = 0;
            while j < padded {
                // SAFETY: off + j + 3 < arena.len() because padded is a
                // multiple of 4 and push() ensures arena has exactly
                // off + padded elements for this clause. arena_ptr is valid
                // for the lifetime of &self.
                let chunk = unsafe { vld1q_s32(arena_ptr.add(off + j)) };
                // SAFETY: vceqq_s32 compares corresponding lanes, producing
                // 0xFFFFFFFF for equal, 0 for not equal. vmaxvq_u32 reduces
                // across all 4 lanes. Both are pure register operations.
                let cmp = unsafe { vceqq_s32(chunk, target) };
                // SAFETY: `cmp` is an initialized NEON register; the two
                // reinterpretations and horizontal maximum access no memory.
                let reduced =
                    unsafe { vmaxvq_u32(vreinterpretq_u32_s32(vreinterpretq_s32_u32(cmp))) };
                if reduced != 0 {
                    // Verify the match is in a real literal, not padding.
                    // This check is only needed for the last chunk which may
                    // contain sentinel padding. For interior chunks, all
                    // 4 elements are real literals.
                    if j + 4 <= real_len {
                        // Entire chunk is real literals.
                        found = true;
                    } else {
                        // Last chunk: check each matching lane is within bounds.
                        // SAFETY: vst1q_u32 stores a uint32x4_t vector to a
                        // [u32; 4] array. cmp is already uint32x4_t (returned
                        // by vceqq_s32). The destination array is stack-local
                        // with correct size and alignment.
                        let mut cmp_arr = [0u32; 4];
                        // SAFETY: `cmp_arr` provides four writable `u32` lanes,
                        // exactly the extent written by `vst1q_u32`.
                        unsafe { vst1q_u32(cmp_arr.as_mut_ptr(), cmp) };
                        for (lane, &cmp_val) in cmp_arr.iter().enumerate() {
                            if cmp_val != 0 && j + lane < real_len {
                                found = true;
                                break;
                            }
                        }
                    }
                    if found {
                        break;
                    }
                }
                j += 4;
            }

            if found {
                result.push(i as u32);
            }
        }

        result
    }

    /// Check if every literal in `a_lits` appears in `b_padded` (NEON).
    ///
    /// `b_padded` is the arena slice for clause B, padded to a multiple of 4.
    /// `b_real_len` is the number of real literals in B.
    ///
    /// # Safety
    ///
    /// `b_padded` must contain initialized `i32` elements and have length
    /// divisible by 4. The NEON load contract is unaligned-load tolerant, so
    /// this function depends on in-bounds 4-lane chunks rather than 16-byte
    /// arena alignment.
    #[cfg(target_arch = "aarch64")]
    unsafe fn subsumes_neon(a_lits: &[i32], b_padded: &[i32], b_real_len: usize) -> bool {
        use std::arch::aarch64::*;

        if a_lits.len() > b_real_len {
            return false;
        }

        let b_ptr = b_padded.as_ptr();
        let b_padded_len = b_padded.len();

        for &a_lit in a_lits {
            // SAFETY: vdupq_n_s32 is a pure register broadcast.
            let target = unsafe { vdupq_n_s32(a_lit) };
            let mut found = false;

            let mut j = 0;
            while j < b_padded_len {
                // SAFETY: j + 3 < b_padded.len() because b_padded is a
                // multiple of 4 elements. b_ptr is valid for the lifetime
                // of the b_padded slice reference.
                let chunk = unsafe { vld1q_s32(b_ptr.add(j)) };
                // SAFETY: `chunk` and `target` are initialized NEON registers;
                // the comparison performs no memory access.
                let cmp = unsafe { vceqq_s32(chunk, target) };
                // SAFETY: `cmp` is initialized; these reinterpretations and
                // the horizontal maximum are register-only operations.
                let reduced =
                    unsafe { vmaxvq_u32(vreinterpretq_u32_s32(vreinterpretq_s32_u32(cmp))) };
                if reduced != 0 {
                    found = true;
                    break;
                }
                j += 4;
            }

            if !found {
                return false;
            }
        }

        true
    }

    // ------------------------------------------------------------------
    // SSE2 (x86_64) implementation
    // ------------------------------------------------------------------

    /// Find clauses containing `lit` using SSE2 4-lane loads.
    ///
    /// # Safety
    ///
    /// This relies on the scanner construction invariant: every clause slice in
    /// `arena` is padded to a multiple of 4 `i32` elements, so each vector load
    /// reads four initialized elements within the clause extent. This path uses
    /// `_mm_loadu_si128`, so 16-byte alignment is not required.
    #[cfg(target_arch = "x86_64")]
    #[allow(clippy::cast_ptr_alignment)]
    unsafe fn find_clauses_containing_sse2(&self, lit: i32) -> Vec<u32> {
        use std::arch::x86_64::*;

        let mut result = Vec::new();
        // SAFETY: x86_64 guarantees SSE2 support, and this only broadcasts a
        // scalar into a vector register.
        let target = unsafe { _mm_set1_epi32(lit) };
        let arena_ptr = self.arena.as_ptr();

        for i in 0..self.len() {
            let off = self.offsets[i] as usize;
            let real_len = self.lengths[i] as usize;
            let padded = self.padded_lengths[i] as usize;
            let mut found = false;

            let mut j = 0;
            while j < padded {
                // SAFETY: off + j points to four initialized padded elements in
                // arena. _mm_loadu_si128 accepts unaligned valid pointers, and
                // x86_64 guarantees SSE2 support.
                let chunk_ptr = unsafe { arena_ptr.add(off + j) }.cast::<__m128i>();
                // SAFETY: `chunk_ptr` addresses four initialized `i32` values
                // in the padded clause, and the unaligned load needs no
                // stronger alignment than the source slice provides.
                let chunk = unsafe { _mm_loadu_si128(chunk_ptr) };
                // SAFETY: x86_64 guarantees SSE2 support, and both arguments
                // are initialized vector registers.
                let cmp = unsafe { _mm_cmpeq_epi32(chunk, target) };
                // SAFETY: x86_64 guarantees SSE2 support, and this only
                // extracts bits from an initialized vector register.
                let mask = unsafe { _mm_movemask_epi8(cmp) };
                if mask != 0 {
                    // Verify match is in real literal, not padding.
                    if j + 4 <= real_len {
                        found = true;
                    } else {
                        // Check each lane: mask has 4 bytes per i32 lane.
                        for lane in 0..4 {
                            let lane_mask = mask & (0xF << (lane * 4));
                            if lane_mask != 0 && j + lane < real_len {
                                found = true;
                                break;
                            }
                        }
                    }
                    if found {
                        break;
                    }
                }
                j += 4;
            }

            if found {
                result.push(i as u32);
            }
        }

        result
    }

    /// Check if every literal in `a_lits` appears in `b_padded` (SSE2).
    ///
    /// # Safety
    ///
    /// `b_padded` must contain initialized `i32` elements and have length
    /// divisible by 4. The SSE2 path uses `_mm_loadu_si128`, so pointer validity
    /// and 4-lane padding are sufficient; 16-byte alignment is not required.
    #[cfg(target_arch = "x86_64")]
    #[allow(clippy::cast_ptr_alignment)]
    unsafe fn subsumes_sse2(a_lits: &[i32], b_padded: &[i32], b_real_len: usize) -> bool {
        use std::arch::x86_64::*;

        if a_lits.len() > b_real_len {
            return false;
        }

        let b_ptr = b_padded.as_ptr();
        let b_padded_len = b_padded.len();

        for &a_lit in a_lits {
            // SAFETY: x86_64 guarantees SSE2 support, and this only broadcasts
            // a scalar into a vector register.
            let target = unsafe { _mm_set1_epi32(a_lit) };
            let mut found = false;

            let mut j = 0;
            while j < b_padded_len {
                // SAFETY: j + 3 < b_padded.len() because b_padded is a
                // multiple of 4. b_ptr is valid for the slice lifetime,
                // _mm_loadu_si128 accepts unaligned valid pointers, and x86_64
                // guarantees SSE2 support.
                let chunk_ptr = unsafe { b_ptr.add(j) }.cast::<__m128i>();
                // SAFETY: `chunk_ptr` addresses four initialized `i32` values
                // within `b_padded`; `_mm_loadu_si128` permits this alignment.
                let chunk = unsafe { _mm_loadu_si128(chunk_ptr) };
                // SAFETY: x86_64 guarantees SSE2 support, and both arguments
                // are initialized vector registers.
                let cmp = unsafe { _mm_cmpeq_epi32(chunk, target) };
                // SAFETY: x86_64 guarantees SSE2 support, and this only
                // extracts bits from an initialized vector register.
                let mask = unsafe { _mm_movemask_epi8(cmp) };
                if mask != 0 {
                    found = true;
                    break;
                }
                j += 4;
            }

            if !found {
                return false;
            }
        }

        true
    }
}

// ------------------------------------------------------------------
// Tests
// ------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    fn encode_lit(var: u32, polarity: u32) -> i32 {
        (var * 2 + polarity) as i32
    }

    #[test]
    fn test_scanner_push_and_retrieve() {
        let mut scanner = SimdClauseScanner::new();
        let lits = vec![encode_lit(0, 0), encode_lit(1, 1), encode_lit(2, 0)];
        scanner.push(&lits);
        assert_eq!(scanner.len(), 1);
        assert_eq!(scanner.clause_lits(0), &lits);
    }

    #[test]
    fn test_scanner_padding() {
        let mut scanner = SimdClauseScanner::new();
        // 5-literal clause should be padded to 8.
        let lits: Vec<i32> = (0..5).map(|v| encode_lit(v, 0)).collect();
        scanner.push(&lits);
        assert_eq!(scanner.padded_lengths[0], 8);
        assert_eq!(scanner.lengths[0], 5);
        // Check padding is sentinel.
        let off = scanner.offsets[0] as usize;
        assert_eq!(scanner.arena[off + 5], SENTINEL);
        assert_eq!(scanner.arena[off + 6], SENTINEL);
        assert_eq!(scanner.arena[off + 7], SENTINEL);
    }

    #[test]
    fn test_simd_load_padding_contract() {
        let mut scanner = SimdClauseScanner::new();
        for len in 1..16usize {
            let lits: Vec<i32> = (0..len).map(|v| encode_lit(v as u32, 0)).collect();
            scanner.push(&lits);
        }

        for idx in 0..scanner.len() {
            let off = scanner.offsets[idx] as usize;
            let real_len = scanner.lengths[idx] as usize;
            let padded_len = scanner.padded_lengths[idx] as usize;
            assert_eq!(padded_len % 4, 0, "clause {idx} must be 4-lane padded");
            assert!(
                off + padded_len <= scanner.arena.len(),
                "clause {idx} padded extent must stay in arena bounds"
            );
            assert!(
                scanner.arena[off + real_len..off + padded_len]
                    .iter()
                    .all(|&lit| lit == SENTINEL),
                "clause {idx} padding lanes must be initialized sentinels"
            );
        }
    }

    #[test]
    fn test_contains_literal_scalar() {
        let mut scanner = SimdClauseScanner::new();
        scanner.push(&[encode_lit(0, 0), encode_lit(1, 0), encode_lit(2, 0)]);
        scanner.push(&[encode_lit(3, 0), encode_lit(4, 0), encode_lit(5, 0)]);
        scanner.push(&[encode_lit(0, 0), encode_lit(6, 0), encode_lit(7, 0)]);

        let target = encode_lit(0, 0);
        let result = scanner.find_clauses_containing_scalar(target);
        assert_eq!(result, vec![0, 2]);

        let result = scanner.find_clauses_containing_scalar(encode_lit(5, 0));
        assert_eq!(result, vec![1]);

        let result = scanner.find_clauses_containing_scalar(encode_lit(99, 0));
        assert!(result.is_empty());
    }

    #[test]
    fn test_contains_literal_simd_matches_scalar() {
        let mut scanner = SimdClauseScanner::new();
        // Add clauses of varying lengths.
        for i in 0..100u32 {
            let len = (i % 7) as usize + 2; // 2..8 literals
            let lits: Vec<i32> = (0..len)
                .map(|j| encode_lit(i * 10 + j as u32, (j & 1) as u32))
                .collect();
            scanner.push(&lits);
        }

        // Also add some with a known literal.
        let target_lit = encode_lit(999, 0);
        scanner.push(&[target_lit, encode_lit(1000, 0)]);
        scanner.push(&[encode_lit(2000, 0), target_lit, encode_lit(2001, 0)]);

        let scalar = scanner.find_clauses_containing_scalar(target_lit);
        let simd = scanner.find_clauses_containing(target_lit);
        assert_eq!(scalar, simd, "SIMD must match scalar for contains_literal");
    }

    #[test]
    fn test_subsumes_scalar_basic() {
        // {A, B} subsumes {A, B, C}
        let a = vec![encode_lit(0, 0), encode_lit(1, 0)];
        let b = vec![encode_lit(0, 0), encode_lit(1, 0), encode_lit(2, 0)];
        assert!(SimdClauseScanner::subsumes_scalar(&a, &b));

        // {A, B, C} does NOT subsume {A, B}
        assert!(!SimdClauseScanner::subsumes_scalar(&b, &a));

        // {A, D} does NOT subsume {A, B, C}
        let c = vec![encode_lit(0, 0), encode_lit(3, 0)];
        assert!(!SimdClauseScanner::subsumes_scalar(&c, &b));

        // Identical clauses subsume each other.
        assert!(SimdClauseScanner::subsumes_scalar(&a, &a));
    }

    #[test]
    fn test_batch_subsumption_simd_matches_scalar() {
        let mut scanner = SimdClauseScanner::new();
        // Clause 0: {0, 1}
        scanner.push(&[encode_lit(0, 0), encode_lit(1, 0)]);
        // Clause 1: {0, 1, 2}
        scanner.push(&[encode_lit(0, 0), encode_lit(1, 0), encode_lit(2, 0)]);
        // Clause 2: {3, 4, 5}
        scanner.push(&[encode_lit(3, 0), encode_lit(4, 0), encode_lit(5, 0)]);
        // Clause 3: {0, 2}
        scanner.push(&[encode_lit(0, 0), encode_lit(2, 0)]);

        let pairs = vec![
            (0, 1), // {0,1} subsumes {0,1,2} -> true
            (1, 0), // {0,1,2} subsumes {0,1} -> false (bigger)
            (2, 1), // {3,4,5} subsumes {0,1,2} -> false
            (3, 1), // {0,2} subsumes {0,1,2} -> true
            (0, 2), // {0,1} subsumes {3,4,5} -> false
        ];

        let scalar = scanner.batch_subsumption_check_scalar(&pairs);
        let simd = scanner.batch_subsumption_check(&pairs);
        assert_eq!(scalar, simd, "SIMD batch subsumption must match scalar");

        // Verify expected results.
        assert!(scalar[0].2, "(0,1) should subsume (0,1,2)");
        assert!(!scalar[1].2, "(0,1,2) should not subsume (0,1)");
        assert!(!scalar[2].2, "(3,4,5) should not subsume (0,1,2)");
        assert!(scalar[3].2, "(0,2) should subsume (0,1,2)");
        assert!(!scalar[4].2, "(0,1) should not subsume (3,4,5)");
    }

    #[test]
    fn test_large_clause_contains() {
        let mut scanner = SimdClauseScanner::new();
        // Clause with 20 literals.
        let lits: Vec<i32> = (0..20).map(|v| encode_lit(v, 0)).collect();
        scanner.push(&lits);

        // Search for first, middle, last, and missing.
        assert_eq!(scanner.find_clauses_containing(encode_lit(0, 0)), vec![0]);
        assert_eq!(scanner.find_clauses_containing(encode_lit(10, 0)), vec![0]);
        assert_eq!(scanner.find_clauses_containing(encode_lit(19, 0)), vec![0]);
        assert!(scanner
            .find_clauses_containing(encode_lit(20, 0))
            .is_empty());
    }

    #[test]
    fn test_sentinel_not_matched() {
        let mut scanner = SimdClauseScanner::new();
        // 3-literal clause padded to 4 with SENTINEL.
        scanner.push(&[encode_lit(0, 0), encode_lit(1, 0), encode_lit(2, 0)]);

        // Searching for SENTINEL should not find the clause.
        assert!(scanner.find_clauses_containing(SENTINEL).is_empty());
    }

    // ------------------------------------------------------------------
    // Throughput benchmarks (run with --release --nocapture)
    // ------------------------------------------------------------------

    #[test]
    fn test_throughput_contains_literal() {
        let num_clauses = 50_000usize;
        let num_vars = 5_000usize;

        let mut scanner = SimdClauseScanner::with_capacity(num_clauses, num_clauses * 4);
        for i in 0..num_clauses {
            let len = (i % 5) + 3; // 3..7 literals
            let lits: Vec<i32> = (0..len)
                .map(|j| encode_lit(((i * 7 + j * 13) % num_vars) as u32, (j & 1) as u32))
                .collect();
            scanner.push(&lits);
        }

        let target = encode_lit(42, 0);

        // Warm up.
        for _ in 0..10 {
            let _ = scanner.find_clauses_containing(target);
        }

        // Measure SIMD path.
        let iterations = 500;
        let start = ay_core::time::Instant::now();
        let mut total_found = 0usize;
        for _ in 0..iterations {
            let found = scanner.find_clauses_containing(target);
            total_found += found.len();
        }
        let elapsed = start.elapsed();
        let total_scanned = num_clauses as u64 * iterations as u64;
        let clauses_per_us = total_scanned as f64 / elapsed.as_micros() as f64;

        // Measure scalar path.
        let start_scalar = ay_core::time::Instant::now();
        let mut total_found_scalar = 0usize;
        for _ in 0..iterations {
            let found = scanner.find_clauses_containing_scalar(target);
            total_found_scalar += found.len();
        }
        let elapsed_scalar = start_scalar.elapsed();
        let clauses_per_us_scalar = total_scanned as f64 / elapsed_scalar.as_micros() as f64;

        eprintln!("--- Contains-literal throughput ({num_clauses} clauses) ---");
        eprintln!("  SIMD:   {clauses_per_us:.1} clauses/us ({elapsed:?})");
        eprintln!("  Scalar: {clauses_per_us_scalar:.1} clauses/us ({elapsed_scalar:?})");
        eprintln!(
            "  Speedup: {:.2}x",
            clauses_per_us / clauses_per_us_scalar.max(0.001)
        );
        eprintln!(
            "  Found: {}/iter (SIMD), {}/iter (scalar)",
            total_found / iterations,
            total_found_scalar / iterations
        );
        assert_eq!(
            total_found, total_found_scalar,
            "SIMD and scalar must find same count"
        );
    }

    #[test]
    fn test_throughput_batch_subsumption() {
        let num_clauses = 5_000usize;
        let num_vars = 2_000usize;

        let mut scanner = SimdClauseScanner::with_capacity(num_clauses, num_clauses * 4);
        for i in 0..num_clauses {
            let len = (i % 5) + 2; // 2..6 literals
            let lits: Vec<i32> = (0..len)
                .map(|j| encode_lit(((i * 7 + j * 13) % num_vars) as u32, (j & 1) as u32))
                .collect();
            scanner.push(&lits);
        }

        // Generate 10K subsumption pairs.
        let num_pairs = 10_000usize;
        let pairs: Vec<(usize, usize)> = (0..num_pairs)
            .map(|i| {
                let a = (i * 3 + 1) % num_clauses;
                let b = (i * 7 + 5) % num_clauses;
                (a, b)
            })
            .collect();

        // Warm up.
        for _ in 0..5 {
            let _ = scanner.batch_subsumption_check(&pairs);
        }

        // Measure SIMD path.
        let iterations = 100;
        let start = ay_core::time::Instant::now();
        let mut total_subsumed = 0usize;
        for _ in 0..iterations {
            let results = scanner.batch_subsumption_check(&pairs);
            total_subsumed += results.iter().filter(|r| r.2).count();
        }
        let elapsed = start.elapsed();
        let total_pairs = num_pairs as u64 * iterations as u64;
        let pairs_per_us = total_pairs as f64 / elapsed.as_micros() as f64;

        // Measure scalar path.
        let start_scalar = ay_core::time::Instant::now();
        let mut total_subsumed_scalar = 0usize;
        for _ in 0..iterations {
            let results = scanner.batch_subsumption_check_scalar(&pairs);
            total_subsumed_scalar += results.iter().filter(|r| r.2).count();
        }
        let elapsed_scalar = start_scalar.elapsed();
        let pairs_per_us_scalar = total_pairs as f64 / elapsed_scalar.as_micros() as f64;

        eprintln!("--- Batch subsumption throughput ({num_pairs} pairs x {iterations} iters) ---");
        eprintln!("  SIMD:   {pairs_per_us:.1} pairs/us ({elapsed:?})");
        eprintln!("  Scalar: {pairs_per_us_scalar:.1} pairs/us ({elapsed_scalar:?})");
        eprintln!(
            "  Speedup: {:.2}x",
            pairs_per_us / pairs_per_us_scalar.max(0.001)
        );
        eprintln!(
            "  Subsumed: {}/iter (SIMD), {}/iter (scalar)",
            total_subsumed / iterations,
            total_subsumed_scalar / iterations
        );
        assert_eq!(
            total_subsumed, total_subsumed_scalar,
            "SIMD and scalar must agree on subsumption count"
        );
    }
}
