// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Platform-specific software prefetch hints.
//!
//! Provides a single function [`prefetch_read_l2`] that issues a non-blocking
//! L2 cache prefetch hint for a memory address. Used by ay-sat's BCP loop
//! to hide main-memory latency (~60-80 cycles) when scanning watch lists.
//!
//! This crate exists to isolate the `unsafe` inline assembly required for
//! prefetch hints, allowing ay-sat to maintain `#![forbid(unsafe_code)]`.
//!
//! # Platform support
//!
//! - **aarch64**: `prfm pldl2keep, [addr]` (prefetch for read, L2, keep)
//! - **x86_64**: `prefetcht1 [addr]` (prefetch to L2 cache)
//! - **Other**: no-op (hardware prefetchers handle it)
//!
//! # Safety
//!
//! Software prefetch is always safe: the CPU treats it as a performance hint.
//! Invalid addresses are silently ignored (no fault, no UB). The `unsafe`
//! block is required only because inline assembly is syntactically `unsafe`
//! in Rust, not because the operation has any safety preconditions.
//!
//! Reference: CaDiCaL propagate.cpp:160-166 (`__builtin_prefetch`).

/// Issue a non-blocking L2 cache prefetch hint for the given address.
///
/// This is a performance hint only — it has no semantic effect. The CPU
/// will attempt to bring the cache line containing `ptr` into L2 cache.
/// If `ptr` is null or invalid, the hint is silently ignored.
#[inline(always)]
pub fn prefetch_read_l2<T>(ptr: *const T) {
    #[cfg(target_arch = "aarch64")]
    {
        // SAFETY: PRFM is a hint instruction that never faults.
        // Invalid addresses are silently ignored by the CPU.
        // Reference: ARM Architecture Reference Manual, PRFM instruction.
        unsafe {
            core::arch::asm!(
                "prfm pldl2keep, [{addr}]",
                addr = in(reg) ptr,
                options(nostack, preserves_flags, readonly),
            );
        }
    }

    #[cfg(target_arch = "x86_64")]
    {
        // SAFETY: PREFETCHT1 is a hint instruction that never faults.
        // Invalid addresses are silently ignored by the CPU.
        // Reference: Intel SDM, PREFETCH instruction.
        unsafe {
            core::arch::asm!(
                "prefetcht1 [{addr}]",
                addr = in(reg) ptr,
                options(nostack, preserves_flags, readonly),
            );
        }
    }

    // On unsupported platforms, let hardware prefetchers handle it.
    #[cfg(not(any(target_arch = "aarch64", target_arch = "x86_64")))]
    {
        let _ = ptr;
    }
}

/// Slice index for `i8` arrays (val lookup in the BCP hot path).
///
/// Panics when `index` is out of bounds. Keeping this public function checked
/// is required for a sound safe API; callers that have proved a raw-pointer
/// access valid can use the explicitly unsafe helpers below.
#[inline(always)]
pub fn val_at(vals: &[i8], index: usize) -> i8 {
    vals[index]
}

/// Checked slice index for `u32` arrays (arena word lookup in BCP hot path).
///
/// Like [`val_at`], this panics on an out-of-bounds index. Used for arena
/// literal access during the BCP replacement scan where the clause offset +
/// literal index is known to be within the arena's allocated words.
#[inline(always)]
pub fn word_at(words: &[u32], index: usize) -> u32 {
    words[index]
}

/// Checked slice read for `u32` arrays (SoA blocker/clause_ref in BCP hot path).
///
/// Like [`val_at`], this panics on an out-of-bounds index. Used in the SoA
/// blocker fast path to read blocker values (#8243).
/// With SoA layout, 32 blockers fit per cache line (vs 16 packed u64 entries),
/// doubling the blocker scan throughput.
#[inline(always)]
pub fn blocker_at(blockers: &[u32], index: usize) -> u32 {
    blockers[index]
}

/// Checked mutable slice write for `u32` arrays (SoA blocker store in BCP).
///
/// Like [`blocker_at`], this panics on an out-of-bounds index. Used in the BCP
/// compaction loop for the speculative copy `blockers[j] = blockers[i]` (#8243).
#[inline(always)]
pub fn blocker_set(blockers: &mut [u32], index: usize, value: u32) {
    blockers[index] = value;
}

/// Checked slice read for `u64` arrays (SoA clause_ref in BCP slow path).
///
/// Like [`blocker_at`], this panics on an out-of-bounds index. It is only
/// accessed on blocker miss, avoiding cache pollution on the fast path (#8243).
/// Each clause_ref word is a `u64` carrying the binary flag at bit 32 plus the
/// full 32-bit clause word offset in the low bits (#9670).
#[inline(always)]
pub fn clause_ref_at(clause_refs: &[u64], index: usize) -> u64 {
    clause_refs[index]
}

/// Checked mutable slice write for `u64` arrays (SoA clause_ref store).
///
/// Like [`blocker_at`], this panics on an out-of-bounds index.
#[inline(always)]
pub fn clause_ref_set(clause_refs: &mut [u64], index: usize, value: u64) {
    clause_refs[index] = value;
}

/// Checked slice read for `u64` arrays (watch entry load in BCP hot path).
///
/// Like [`val_at`], this panics on an out-of-bounds index. Used in the BCP
/// blocker fast path to read packed watch entries.
#[inline(always)]
pub fn entry_at(entries: &[u64], index: usize) -> u64 {
    entries[index]
}

/// Checked mutable slice write for `u64` arrays (watch entry store in BCP).
///
/// Like [`entry_at`], this panics on an out-of-bounds index. Used in the BCP
/// blocker fast path for the speculative copy `entries[j] = entries[i]`.
/// The compaction invariant `j <= i < entries.len()` guarantees safety.
#[inline(always)]
pub fn entry_set(entries: &mut [u64], index: usize, value: u64) {
    entries[index] = value;
}

/// Checked mutable slice write for `i8` arrays (val store in enqueue).
///
/// Like [`val_at`], this panics on an out-of-bounds index. Used in `enqueue()`
/// to set `vals[lit] = 1` and `vals[¬lit] = -1`.
#[inline(always)]
pub fn val_set(vals: &mut [i8], index: usize, value: i8) {
    vals[index] = value;
}

/// Issue a non-blocking L2 cache prefetch hint for a specific offset
/// within a `u32` slice (clause arena data prefetch).
///
/// Prefetches the cache line containing `slice[offset]`. The CPU will
/// bring in ~16 u32 words (64-byte cache line), covering a typical clause
/// header (5 words) + first 11 literal words.
///
/// Used by the BCP loop to prefetch the next clause's arena data while
/// processing the current clause, hiding main-memory latency (~60-80 cycles).
///
/// If `offset >= slice.len()`, the prefetch hint targets a valid but
/// potentially unmapped address — the CPU silently ignores it (no fault).
///
/// Reference: CaDiCaL propagate.cpp clause data prefetch pattern (#8000).
#[inline(always)]
pub fn prefetch_arena_at(words: &[u32], offset: usize) {
    // Prefetch never faults — the CPU silently ignores invalid addresses.
    // Use unchecked pointer arithmetic to avoid a conditional branch in the
    // BCP hot path. The bounds check that `words.get(offset)` previously
    // added is unnecessary overhead for a hint instruction.
    //
    // SAFETY: prefetch instructions (PRFM on aarch64, PREFETCHT1 on x86_64)
    // are defined to be no-ops for unmapped/invalid addresses. Even if
    // offset >= words.len(), the computed address simply produces a silent
    // no-op prefetch hint with no fault or UB.
    let ptr = words.as_ptr();
    // SAFETY: ptr.wrapping_add never causes UB — it performs wrapping
    // pointer arithmetic without creating a reference. The result is only
    // passed to prefetch_read_l2 which issues a non-faulting hint.
    prefetch_read_l2(ptr.wrapping_add(offset));
}

/// Issue a non-blocking L1 cache prefetch hint for a specific offset
/// within a `u32` slice (clause arena second cache-line prefetch).
///
/// Same as [`prefetch_arena_at`] but targets L1 cache instead of L2.
/// Used for the second cache line of long clauses: the data is needed
/// within ~10-20 cycles (during the replacement scan) rather than ~60-80
/// cycles (next clause lookahead).
///
/// Reference: #8000 — BCP cache miss reduction.
#[inline(always)]
pub fn prefetch_arena_at_l1(words: &[u32], offset: usize) {
    // Same as prefetch_arena_at but targets L1 cache. See that function
    // for the safety rationale on wrapping_add + non-faulting hint.
    let ptr = words.as_ptr();
    prefetch_read_l1(ptr.wrapping_add(offset));
}

/// Issue a non-blocking L1 cache prefetch hint for a val lookup (#8465).
///
/// Prefetches the cache line containing `vals[index]`. Used by the safe BCP
/// blocker scan to prefetch the NEXT blocker's val while processing the current
/// one. On large instances (50K+ vars), vals[] spans ~100KB+ and each blocker
/// indexes randomly into it. Prefetching hides L2/L3 access latency.
///
/// If `index >= vals.len()`, the prefetch targets an address past the allocation
/// -- the CPU silently ignores it (prefetch never faults).
#[inline(always)]
pub fn prefetch_val_l1(vals: &[i8], index: usize) {
    let ptr = vals.as_ptr();
    prefetch_read_l1(ptr.wrapping_add(index));
}

// --- Raw pointer helpers for unsafe BCP (#7989) ---

/// L1 cache prefetch hint. Closer than L2, used when data will be
/// accessed within ~10 cycles (e.g., watch list entries during active scan).
///
/// Reference: CaDiCaL propagate.cpp:160-166.
#[inline(always)]
pub fn prefetch_read_l1<T>(ptr: *const T) {
    #[cfg(target_arch = "aarch64")]
    {
        // SAFETY: PRFM is a hint instruction that never faults.
        unsafe {
            core::arch::asm!(
                "prfm pldl1keep, [{addr}]",
                addr = in(reg) ptr,
                options(nostack, preserves_flags, readonly),
            );
        }
    }

    #[cfg(target_arch = "x86_64")]
    {
        // SAFETY: PREFETCHT0 is a hint instruction that never faults.
        unsafe {
            core::arch::asm!(
                "prefetcht0 [{addr}]",
                addr = in(reg) ptr,
                options(nostack, preserves_flags, readonly),
            );
        }
    }

    #[cfg(not(any(target_arch = "aarch64", target_arch = "x86_64")))]
    {
        let _ = ptr;
    }
}

/// Get raw mutable pointer range for in-place watch list iteration.
/// Returns (begin, end) pointers.
/// CaDiCaL pattern: `watch_iterator j = ws.begin(); const_watch_iterator i = j;`
///
/// The returned pointers are valid for the lifetime of the mutable borrow.
#[inline(always)]
pub fn watch_iter_raw(entries: &mut [u64]) -> (*mut u64, *const u64) {
    let len = entries.len();
    let ptr = entries.as_mut_ptr();
    // SAFETY: ptr.add(len) computes the one-past-end pointer for the slice.
    // This is always valid per Rust's pointer arithmetic rules: for a slice
    // of `len` elements, `ptr.add(len)` is within or one-past the allocation.
    // The result is used only for pointer comparison (i < end), never dereferenced.
    let end = unsafe { ptr.add(len).cast_const() };
    (ptr, end)
}

/// Read a literal u32 from the clause arena using raw pointer arithmetic.
/// Equivalent to CaDiCaL's `lits[k]` where `lits = clause->begin()`.
///
/// # Safety
///
/// Caller must ensure:
/// - `words_ptr` was obtained from a valid `&[u32]` slice (the clause arena)
/// - `clause_offset + header_words + lit_index < arena_len` (within bounds)
/// - The `words_ptr` slice has not been reallocated since the pointer was taken
///   (no arena growth during BCP)
///
/// `arena_len` is the length of the slice that produced `words_ptr`. It is used
/// only for `debug_assert!` bounds checking and has no effect in release builds.
///
/// In ay-sat, these invariants are maintained because:
/// - `clause_offset` is a valid arena offset stored in watch entries
/// - `header_words` is a compile-time constant (HEADER_WORDS = 3)
/// - `lit_index < clause_len` which was read from the clause header
/// - The arena is not resized during BCP (no clause additions mid-propagation)
#[inline(always)]
pub unsafe fn arena_literal_raw(
    words_ptr: *const u32,
    clause_offset: usize,
    header_words: usize,
    lit_index: usize,
    arena_len: usize,
) -> u32 {
    debug_assert!(
        clause_offset
            .checked_add(header_words)
            .and_then(|v| v.checked_add(lit_index))
            .map_or(false, |total| total < arena_len),
        "arena_literal_raw: offset {clause_offset} + header {header_words} + lit {lit_index} \
         out of bounds for arena of length {arena_len}",
    );
    // SAFETY: caller guarantees clause_offset + header_words + lit_index
    // is within the arena allocation. Debug builds verify via the assert above.
    unsafe { *words_ptr.add(clause_offset + header_words + lit_index) }
}

/// Read a clause header word via raw pointer.
///
/// # Safety
///
/// Caller must ensure:
/// - `words_ptr` was obtained from a valid `&[u32]` slice (the clause arena)
/// - `clause_offset + word_index < arena_len` (within bounds)
/// - The `words_ptr` slice has not been reallocated since the pointer was taken
///
/// `arena_len` is the length of the slice that produced `words_ptr`. It is used
/// only for `debug_assert!` bounds checking and has no effect in release builds.
#[inline(always)]
pub unsafe fn arena_header_word_raw(
    words_ptr: *const u32,
    clause_offset: usize,
    word_index: usize,
    arena_len: usize,
) -> u32 {
    debug_assert!(
        clause_offset
            .checked_add(word_index)
            .map_or(false, |total| total < arena_len),
        "arena_header_word_raw: offset {clause_offset} + word {word_index} \
         out of bounds for arena of length {arena_len}",
    );
    // SAFETY: caller guarantees clause_offset + word_index is within the arena.
    // Debug builds verify via the assert above.
    unsafe { *words_ptr.add(clause_offset + word_index) }
}

/// Get raw const pointer to vals array for pointer-based val lookup.
/// CaDiCaL pattern: uses `signed char *vals` directly.
#[inline(always)]
pub fn vals_ptr(vals: &[i8]) -> *const i8 {
    vals.as_ptr()
}

/// Read val at index using raw pointer. No bounds check in release builds.
///
/// # Safety
///
/// - `index` must be `< vals_len` (the length of the slice that produced `ptr`)
/// - `ptr` must still be valid (the backing `Vec<i8>` has not been reallocated)
///
/// `vals_len` is the length of the slice that produced `ptr`. It is used only
/// for `debug_assert!` bounds checking and has no effect in release builds.
///
/// In ay-sat, `index` is always a `Literal::index()` value which is bounded
/// by `2 * num_vars == vals.len()` by the literal encoding invariant.
#[inline(always)]
pub unsafe fn val_raw(ptr: *const i8, index: usize, vals_len: usize) -> i8 {
    debug_assert!(
        index < vals_len,
        "val_raw: index {index} out of bounds for vals of length {vals_len}",
    );
    // SAFETY: caller guarantees index < vals_len. Debug builds verify via
    // the assert above.
    unsafe { *ptr.add(index) }
}

/// Set the length of a `Vec<u64>` after in-place compaction.
/// CaDiCaL pattern: `ws.resize(j - ws.begin())`
///
/// # Safety
///
/// - `new_len` must be `<= vec.capacity()`
/// - All elements in `[0..new_len)` must be initialized (written by the BCP
///   compaction loop before this call)
/// - The Vec must not have been reallocated since the raw pointer iteration
///   began (no push/extend during the compaction)
#[inline(always)]
pub unsafe fn vec_set_len(vec: &mut Vec<u64>, new_len: usize) {
    debug_assert!(new_len <= vec.capacity());
    // SAFETY: caller guarantees new_len <= capacity and [0..new_len) initialized.
    unsafe { vec.set_len(new_len) };
}

#[cfg(test)]
#[path = "lib_tests.rs"]
mod tests;
