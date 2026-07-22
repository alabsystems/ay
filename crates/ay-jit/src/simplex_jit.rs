// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! JIT-compiled simplex pivot row updates for LRA.
//!
//! When a pivot row is stable (reused for many consecutive pivots), the
//! coefficient pattern can be compiled into native code that performs the
//! multiply-add update with hardcoded coefficients as immediates.
//!
//! The hot inner loop in `pivot()` does:
//!   for each (var, coeff) in pivot_row: target\[var\] += scale * coeff
//!
//! For the common all-integer case (all denominators == 1), this compiles to
//! a sequence of LDR + MADD + STR instructions with coefficients baked in.
//!
//! ## When JIT is used
//!
//! The LRA simplex solver uses integer (i64) coefficients as a fast path
//! when all row coefficients have denominator 1. When a pivot row is reused
//! as the entering variable's row for `COMPILE_THRESHOLD` (8) consecutive
//! pivots, the [`PivotRowCache`] compiles the coefficient pattern into
//! native code. The compiled function is then used for subsequent pivots
//! until the row changes (detected via [`CompiledPivotRow::matches`]).
//!
//! Two compilation modes exist:
//! - **Single-row** ([`CompiledPivotRow`]): `target\[j\] += scale * coeff\[j\]`
//! - **Batch** ([`CompiledBatchPivotUpdate`]): applies the same coefficient
//!   pattern to multiple target rows in one call, amortizing I-cache fills.
//!
//! A pure-Rust fallback ([`batch_pivot_update_i64`]) handles non-aarch64
//! platforms and provides overflow detection via `checked_mul`/`checked_add`.
//!
//! ## Calling convention
//!
//! **Single-row function** (`PivotRowFn`):
//!   `extern "C" fn(target: *mut i64, scale: i64)`
//!
//! - `target` (x0): pointer to dense i64 array indexed by variable ID
//! - `scale` (x1): the integer scale factor
//!
//! **Batch function** (`BatchPivotFn`):
//!   `extern "C" fn(targets: *const *mut i64, scales: *const i64, num_rows: u64) -> i64`
//!
//! - `targets` (x0): array of pointers to dense i64 arrays
//! - `scales` (x1): array of scale factors (one per target row)
//! - `num_rows` (x2): number of target rows to update
//! - Returns 0 on success, or 1-based row index on i64 overflow
//!
//! ## Register allocation (aarch64)
//!
//! **Single-row:**
//! - x0 = target pointer, x1 = scale, x2 = scratch (loaded value),
//!   x3 = scratch (coefficient immediate)
//!
//! **Batch:**
//! - x3 = targets base, x8 = scales base, x9 = num_rows, x10 = loop counter,
//!   x4 = current target, x5 = current scale, x6/x7 = scratch,
//!   x11 = overflow scratch (SMULH high bits)
//! - Only caller-saved registers used (no STP/LDP save/restore needed)
//!
//! ## Coefficient optimizations
//!
//! Special cases avoid multiplication:
//! - coeff == +1:  ADD (single instruction)
//! - coeff == -1:  SUB (single instruction)
//! - coeff == +2:  ADD + ADD (cheaper than MUL on Apple M-series)
//! - coeff == -2:  SUB + SUB
//! - general:      MOV imm64 + MADD (3-5 instructions depending on immediate size)
//!
//! ## Tiered compilation
//!
//! Public builds keep sparse substitution on the interpreted, overflow-checked
//! fallback path.
//!
//! ## Overflow semantics
//!
//! **Batch path**: The JIT batch function detects i64 overflow using
//! SMULH (signed multiply high) for multiplication and ADDS/SUBS (flag-setting
//! add/subtract) for addition. On overflow, it returns the 1-based index of the
//! first overflowing row, matching the pure-Rust [`batch_pivot_update_i64`]
//! fallback behavior.
//!
//! **Single-row path**: Uses wrapping i64 arithmetic (no overflow detection).
//! The caller is responsible for falling back to Rational arithmetic when
//! overflow is possible.
//!
//! ## Limitations
//!
//! - aarch64 only (returns `None` on other architectures)
//! - Maximum 128 non-zero coefficients per compiled row (`MAX_COEFFICIENTS`)
//! - No staleness detection in [`PivotRowCache`] after initial compilation;
//!   callers must use [`CompiledPivotRow::matches`] and [`PivotRowCache::invalidate`]

use std::collections::BTreeMap;

use crate::executable::ExecutableMemory;
use crate::JitError;

/// Backend-neutral owner for compiled machine code.
///
/// All current JIT tiers end up with the same owned runtime artifact:
/// executable memory containing a single callable function. Keeping the owner
/// backend-neutral lets the cache/install path evolve without re-encoding the
/// producing backend in every compiled artifact wrapper. The function pointers
/// stored in `CompiledPivotRow` / `CompiledBatchPivotUpdate` point into this
/// memory, so the owner must outlive those wrappers.
struct ArtifactBacking(
    #[allow(dead_code)] // Holds executable memory alive for the function pointer lifetime.
    ExecutableMemory,
);

// SAFETY: ExecutableMemory is Send+Sync (immutable after construction) and is
// process-global mmap'd executable memory, safe to share across threads.
unsafe impl Send for ArtifactBacking {}
unsafe impl Sync for ArtifactBacking {}

/// Maximum number of non-zero coefficients in a compilable pivot row.
/// Beyond this, the code size exceeds L1 I-cache benefit.
const MAX_COEFFICIENTS: usize = 128;

/// Minimum number of pivot reuses before compilation is triggered.
/// This amortizes the ~2us compilation cost over enough applications.
pub const COMPILE_THRESHOLD: u32 = 8;

/// Type alias for the compiled row update function.
///
/// Parameters:
///   target: *mut i64 -- dense coefficient array indexed by variable
///   scale:  i64      -- multiplicative factor from the entering variable's
///                        coefficient in the target row
///
/// The function computes: target\[j\] += scale * coeff_j for each non-zero
/// position j in the pivot row.
type PivotRowFn = unsafe extern "C" fn(*mut i64, i64);

/// Type alias for the compiled batch update function (#8353).
///
/// Parameters:
///   targets:  *const *mut i64 -- array of pointers to dense i64 arrays
///   scales:   *const i64      -- array of scale factors (one per target row)
///   num_rows: u64             -- number of target rows to update
///
/// For each target row i, computes:
///   targets\[i\]\[j\] += scales\[i\] * coeff_j for each non-zero position j
///
/// Returns 0 on success, or the 1-based overflowing row index (caller should
/// fall back to Rational arithmetic for that row and the remainder).
type BatchPivotFn = unsafe extern "C" fn(*const *mut i64, *const i64, u64) -> i64;

/// A JIT-compiled pivot row for fast multiply-add updates.
///
/// Holds the compiled native function and the backing executable memory.
/// The row's non-zero positions and integer coefficients are hardcoded
/// as immediates in the generated machine code.
pub struct CompiledPivotRow {
    /// The compiled update function.
    func: PivotRowFn,
    /// Number of non-zero coefficients compiled into this function.
    num_coeffs: usize,
    /// Variable positions for which coefficients are compiled (sorted).
    /// Used for cache invalidation: if the pivot row changes, the compiled
    /// version must be discarded.
    positions: Vec<u32>,
    /// The integer coefficients at each position (parallel to `positions`).
    /// Used for staleness checks.
    coefficients: Vec<i64>,
    /// Number of times this compiled row has been applied.
    apply_count: u64,
    /// Backing store for the compiled code (must outlive func).
    _backing: ArtifactBacking,
}

// SAFETY: The compiled function pointer points into immutable executable memory.
// The function is pure: it reads from and writes to the target array, with no
// other side effects. The backing store is process-global executable memory.
unsafe impl Send for CompiledPivotRow {}
unsafe impl Sync for CompiledPivotRow {}

impl CompiledPivotRow {
    /// Apply the compiled row update: target\[j\] += scale * coeff\[j\] for all j.
    ///
    /// # Safety
    ///
    /// The caller must ensure:
    /// - `target` points to a valid i64 array large enough to hold all compiled
    ///   variable positions (i.e., target.len() > max(positions))
    /// - No concurrent modification of the target array elements at compiled positions
    #[inline]
    pub unsafe fn apply(&mut self, target: *mut i64, scale: i64) {
        // SAFETY: Caller guarantees target validity. func is a valid function
        // pointer in executable memory that remains alive via _backing.
        unsafe { (self.func)(target, scale) };
        self.apply_count += 1;
    }

    /// Number of non-zero coefficients in this compiled row.
    pub fn num_coeffs(&self) -> usize {
        self.num_coeffs
    }

    /// Number of times this compiled row has been applied.
    pub fn apply_count(&self) -> u64 {
        self.apply_count
    }

    /// Check if the compiled row matches the given coefficients.
    /// Returns false if the pivot row has changed since compilation.
    pub fn matches(&self, coeffs: &[(u32, i64)]) -> bool {
        if coeffs.len() != self.positions.len() {
            return false;
        }
        coeffs
            .iter()
            .zip(self.positions.iter().zip(self.coefficients.iter()))
            .all(|((var, coeff), (pos, compiled_coeff))| *var == *pos && *coeff == *compiled_coeff)
    }
}

/// A JIT-compiled batch pivot update for updating multiple rows at once (#8353).
///
/// When pivoting, the same pivot row coefficients are applied to every affected
/// row. Instead of calling `CompiledPivotRow::apply()` N times (each call
/// re-loading the hardcoded coefficients from I-cache), a batch function
/// iterates over all target rows in a single call, amortizing I-cache fills.
///
/// The batch function also includes i64 overflow detection: if any
/// multiply-add overflows i64, the function returns early with overflow status
/// so the caller can fall back to Rational arithmetic for the remaining rows.
pub struct CompiledBatchPivotUpdate {
    /// The compiled batch update function.
    func: BatchPivotFn,
    /// Number of non-zero coefficients compiled into this function.
    num_coeffs: usize,
    /// Variable positions (parallel to coefficients, sorted).
    positions: Vec<u32>,
    /// Integer coefficients at each position.
    coefficients: Vec<i64>,
    /// Number of times this batch function has been applied.
    apply_count: u64,
    /// Backing store for the compiled code (must outlive func).
    _backing: ArtifactBacking,
}

// SAFETY: Same reasoning as CompiledPivotRow — immutable executable memory,
// pure function with no side effects beyond writing to target arrays.
unsafe impl Send for CompiledBatchPivotUpdate {}
unsafe impl Sync for CompiledBatchPivotUpdate {}

impl CompiledBatchPivotUpdate {
    /// Apply the batch update to multiple target rows.
    ///
    /// For each row i in 0..num_rows:
    ///   targets\[i\]\[j\] += scales\[i\] * coeff\[j\] for all j
    ///
    /// Returns the number of rows successfully updated. If overflow is detected
    /// on row k, returns k (rows 0..k were updated, rows k..num_rows were not).
    ///
    /// # Safety
    ///
    /// The caller must ensure:
    /// - `targets` points to an array of at least `num_rows` valid `*mut i64` pointers
    /// - Each `targets[i]` points to a valid i64 array large enough for all compiled positions
    /// - `scales` points to an array of at least `num_rows` i64 values
    /// - No concurrent modification of target arrays at compiled positions
    #[inline]
    pub unsafe fn apply(&mut self, targets: &[*mut i64], scales: &[i64]) -> usize {
        let num_rows = targets.len().min(scales.len());
        if num_rows == 0 {
            return 0;
        }
        // SAFETY: Caller guarantees pointer validity. func is valid in executable
        // memory that remains alive via _backing.
        let result = unsafe { (self.func)(targets.as_ptr(), scales.as_ptr(), num_rows as u64) };
        self.apply_count += 1;
        if result == 0 {
            num_rows // all rows updated successfully
        } else {
            // Overflow detected — result encodes which row overflowed.
            // The batch function processes rows sequentially, so the return
            // value (1-based) indicates the first row that overflowed.
            // Rows before it were updated successfully.
            (result as usize).saturating_sub(1).min(num_rows)
        }
    }

    /// Number of non-zero coefficients in this compiled function.
    pub fn num_coeffs(&self) -> usize {
        self.num_coeffs
    }

    /// Number of times this batch function has been applied.
    pub fn apply_count(&self) -> u64 {
        self.apply_count
    }

    /// Check if the compiled function matches the given coefficients.
    pub fn matches(&self, coeffs: &[(u32, i64)]) -> bool {
        if coeffs.len() != self.positions.len() {
            return false;
        }
        coeffs
            .iter()
            .zip(self.positions.iter().zip(self.coefficients.iter()))
            .all(|((var, coeff), (pos, compiled_coeff))| *var == *pos && *coeff == *compiled_coeff)
    }
}

/// Pure-Rust i64 batch pivot update with overflow detection (#8353).
///
/// When the JIT compiler is not available (non-aarch64 platform) or when the
/// coefficient count is too small to justify compilation, this function provides
/// the same i64 fast-path semantics using safe Rust with `checked_mul`/`checked_add`.
///
/// Returns the number of rows successfully updated. If overflow occurs on row k,
/// returns k (rows 0..k were fully updated).
pub fn batch_pivot_update_i64(
    coefficients: &[(u32, i64)],
    targets: &mut [&mut [i64]],
    scales: &[i64],
) -> usize {
    let num_rows = targets.len().min(scales.len());
    for row_idx in 0..num_rows {
        let scale = scales[row_idx];
        let target = &mut targets[row_idx];
        for &(var_idx, coeff) in coefficients {
            let vi = var_idx as usize;
            if vi >= target.len() {
                continue;
            }
            // Fast paths for common coefficients
            let product = match coeff {
                0 => continue,
                1 => scale,
                -1 => match scale.checked_neg() {
                    Some(v) => v,
                    None => return row_idx,
                },
                _ => match scale.checked_mul(coeff) {
                    Some(v) => v,
                    None => return row_idx,
                },
            };
            match target[vi].checked_add(product) {
                Some(v) => target[vi] = v,
                None => return row_idx,
            }
        }
    }
    num_rows
}

/// Cache for JIT-compiled pivot rows, tracking reuse counts and compiled functions.
///
/// Keyed by row index. When a row is used as a pivot row repeatedly (the
/// "entering variable" row that gets substituted into all affected rows),
/// the cache tracks its reuse count. Sparse substitution remains on the
/// interpreted fallback in public builds.
///
/// The cache is invalidated per-entry when the row's coefficients change
/// (detected via the `matches()` check on `CompiledPivotRow`).
pub struct PivotRowCache {
    /// Maps row_idx -> (use_count, optional compiled row).
    entries: BTreeMap<usize, PivotRowCacheEntry>,
    /// Total single-row compilation count (for stats).
    compilations: u64,
    /// Total batch compilation count (for stats, #8353).
    batch_compilations: u64,
    /// Total JIT-applied pivot updates (for stats).
    jit_applies: u64,
    /// Total batch JIT-applied pivot updates (for stats, #8353).
    batch_jit_applies: u64,
    /// Total rows updated via batch JIT (for stats, #8353).
    batch_rows_updated: u64,
    /// Total i64 fast-path rows updated (for stats, #8353).
    i64_fast_path_rows: u64,
    /// Total i64 overflow fallbacks (for stats, #8353).
    i64_overflow_fallbacks: u64,
    /// Total sparse substitute compilation attempts.
    substitute_compile_attempts: u64,
    /// Total sparse substitute compilations that produced executable code.
    substitute_compilations: u64,
    /// Total sparse substitute compilations produced by the EXTERNAL_CODEGEN backend.
    substitute_external_codegen_compilations: u64,
    /// Total sparse substitute compile failures / unsupported cases.
    substitute_compile_failures: u64,
    /// Total sparse substitute retries skipped due to per-row backoff.
    substitute_compile_backoff_skips: u64,
    /// Total sparse substitute compile skips due to runtime disable policy.
    substitute_compile_disabled_skips: u64,
    /// Total successful compiled sparse substitute wrapper applications.
    substitute_compiled_applies: u64,
    /// Total sparse substitute applications that used the interpreted fallback path.
    substitute_fallback_applies: u64,
    /// Total compiled sparse substitute applications served by the runtime wrapper.
    substitute_compiled_runtime_applies: u64,
    /// Total successful sparse substitute applications served by the external code generation function.
    substitute_external_codegen_applies: u64,
    /// Total successful empty-target sparse substitute applications served by external code generation.
    substitute_external_codegen_empty_target_applies: u64,
    /// Total successful non-empty sparse substitute applications served by external code generation.
    substitute_external_codegen_non_empty_target_applies: u64,
    /// Total sparse substitute overflows that fell back to the interpreted path.
    substitute_overflow_fallbacks: u64,
    /// Backend-neutral runtime disable for sparse substitute compilation.
    /// Controlled through `SatDisableFlags` / CLI policy and overridable via
    /// `set_substitute_disabled()`.
    substitute_disabled: bool,
}

/// A single cache entry tracking a pivot row's reuse and compilation state.
struct PivotRowCacheEntry {
    /// Number of times this row has been the pivot row.
    use_count: u32,
    /// JIT-compiled single-row update, if available and still valid.
    compiled: Option<CompiledPivotRow>,
    /// JIT-compiled batch update for multiple target rows (#8353).
    batch_compiled: Option<CompiledBatchPivotUpdate>,
}

impl PivotRowCache {
    /// Create an empty cache.
    pub fn new() -> Self {
        Self {
            entries: BTreeMap::new(),
            compilations: 0,
            batch_compilations: 0,
            jit_applies: 0,
            batch_jit_applies: 0,
            batch_rows_updated: 0,
            i64_fast_path_rows: 0,
            i64_overflow_fallbacks: 0,
            substitute_compile_attempts: 0,
            substitute_compilations: 0,
            substitute_external_codegen_compilations: 0,
            substitute_compile_failures: 0,
            substitute_compile_backoff_skips: 0,
            substitute_compile_disabled_skips: 0,
            substitute_compiled_applies: 0,
            substitute_fallback_applies: 0,
            substitute_compiled_runtime_applies: 0,
            substitute_external_codegen_applies: 0,
            substitute_external_codegen_empty_target_applies: 0,
            substitute_external_codegen_non_empty_target_applies: 0,
            substitute_overflow_fallbacks: 0,
            substitute_disabled: crate::no_external_codegen_backend_cached(),
        }
    }

    /// Record that `row_idx` was used as a pivot row. If the row's integer
    /// coefficients are provided and the use count exceeds `COMPILE_THRESHOLD`,
    /// this tracks reuse for sparse-substitute compilation.
    ///
    /// `int_coeffs` should be `Some(coefficients)` when all coefficients in
    /// the pivot row have denominator 1 (the all-integer fast path).
    /// Pass `None` when coefficients are non-integer rationals.
    pub fn record_pivot(&mut self, row_idx: usize, int_coeffs: Option<&[(u32, i64)]>) {
        let entry = self.entries.entry(row_idx).or_insert(PivotRowCacheEntry {
            use_count: 0,
            compiled: None,
            batch_compiled: None,
        });
        entry.use_count += 1;

        // Check if we should attempt compilation
        if entry.use_count < COMPILE_THRESHOLD {
            return;
        }

        // Only compile on the exact threshold hit (avoid re-compiling every time)
        if entry.use_count > COMPILE_THRESHOLD && entry.compiled.is_some() {
            // Already compiled and still valid -- check staleness below
            return;
        }

        if let Some(_coeffs) = int_coeffs {
            // If already compiled, check if still valid
            if let Some(ref compiled) = entry.compiled {
                if compiled.matches(_coeffs) { // Still valid
                }
                // Stale -- recompile
            }
        }
    }

    /// Get a mutable reference to the compiled row for `row_idx`, if available.
    pub fn get_compiled(&mut self, row_idx: usize) -> Option<&mut CompiledPivotRow> {
        self.entries
            .get_mut(&row_idx)
            .and_then(|e| e.compiled.as_mut())
    }

    /// Get a mutable reference to the batch-compiled update for `row_idx` (#8353).
    pub fn get_batch_compiled(&mut self, row_idx: usize) -> Option<&mut CompiledBatchPivotUpdate> {
        self.entries
            .get_mut(&row_idx)
            .and_then(|e| e.batch_compiled.as_mut())
    }

    /// Submit one basis-region request to the background compiler.
    ///
    /// This is a fail-closed skeleton: the request carries typed rows through
    /// the compiler service, but no basis-region native dispatch is enabled.
    pub fn submit_lra_basis_region_request(
        &mut self,
        request: crate::lra_region::LraBasisRegionRequest,
    ) -> bool {
        self.submit_lra_basis_region_request_impl(request)
    }

    fn submit_lra_basis_region_request_impl(
        &mut self,
        _request: crate::lra_region::LraBasisRegionRequest,
    ) -> bool {
        false
    }

    /// Record a JIT application for stats tracking.
    pub fn record_jit_apply(&mut self) {
        self.jit_applies += 1;
    }

    /// Record a successful compiled sparse substitute wrapper application.
    pub fn record_substitute_compiled_wrapper_apply(&mut self) {
        self.substitute_compiled_applies += 1;
    }

    /// Record successful sparse substitute work served by the runtime wrapper.
    pub fn record_substitute_compiled_runtime_apply_delta(&mut self, delta: u64) {
        self.substitute_compiled_runtime_applies = self
            .substitute_compiled_runtime_applies
            .saturating_add(delta);
    }

    /// Record successful sparse substitute work served by the external code generation function.
    pub fn record_substitute_external_codegen_native_function_apply(
        &mut self,
        empty_target_applies: u64,
        non_empty_target_applies: u64,
    ) {
        self.substitute_external_codegen_empty_target_applies = self
            .substitute_external_codegen_empty_target_applies
            .saturating_add(empty_target_applies);
        self.substitute_external_codegen_non_empty_target_applies = self
            .substitute_external_codegen_non_empty_target_applies
            .saturating_add(non_empty_target_applies);
        self.substitute_external_codegen_applies = self
            .substitute_external_codegen_applies
            .saturating_add(empty_target_applies.saturating_add(non_empty_target_applies));
    }

    /// Record a sparse substitute application that used the interpreted fallback path.
    pub fn record_substitute_fallback_apply(&mut self) {
        self.substitute_fallback_applies += 1;
    }

    /// Remove a cache entry (e.g., when a row is destroyed or significantly modified).
    pub fn invalidate(&mut self, row_idx: usize) {
        self.entries.remove(&row_idx);
    }

    /// Clear all entries (e.g., on solver reset).
    pub fn clear(&mut self) {
        self.entries.clear();
    }

    /// Drop only LRA basis-region artifacts while preserving unrelated sparse-substitute cache state.
    pub fn clear_lra_basis_region_artifacts(&mut self) {}

    /// Record a batch JIT application for stats tracking (#8353).
    pub fn record_batch_jit_apply(&mut self, rows_updated: usize) {
        self.batch_jit_applies += 1;
        self.batch_rows_updated += rows_updated as u64;
    }

    /// Record an i64 fast-path batch update for stats (#8353).
    pub fn record_i64_fast_path(&mut self, rows_updated: usize) {
        self.i64_fast_path_rows += rows_updated as u64;
    }

    /// Record an i64 overflow fallback for stats (#8353).
    pub fn record_i64_overflow(&mut self) {
        self.i64_overflow_fallbacks += 1;
    }

    /// Record a compiled sparse substitute overflow fallback.
    pub fn record_substitute_overflow_fallback(&mut self) {
        self.substitute_overflow_fallbacks += 1;
    }

    /// Total number of single-row compilations performed.
    pub fn compilations(&self) -> u64 {
        self.compilations
    }

    /// Total number of batch compilations performed (#8353).
    pub fn batch_compilations(&self) -> u64 {
        self.batch_compilations
    }

    /// Total number of JIT-applied single-row pivot updates.
    pub fn jit_applies(&self) -> u64 {
        self.jit_applies
    }

    /// Total number of batch JIT applications (#8353).
    pub fn batch_jit_applies(&self) -> u64 {
        self.batch_jit_applies
    }

    /// Total rows updated via batch JIT (#8353).
    pub fn batch_rows_updated(&self) -> u64 {
        self.batch_rows_updated
    }

    /// Total i64 fast-path rows updated (#8353).
    pub fn i64_fast_path_rows(&self) -> u64 {
        self.i64_fast_path_rows
    }

    /// Total i64 overflow fallbacks (#8353).
    pub fn i64_overflow_fallbacks(&self) -> u64 {
        self.i64_overflow_fallbacks
    }

    /// Total sparse substitute compile attempts.
    pub fn substitute_compile_attempts(&self) -> u64 {
        self.substitute_compile_attempts
    }

    /// Total sparse substitute compilations that produced executable code.
    pub fn substitute_compilations(&self) -> u64 {
        self.substitute_compilations
    }

    /// Total sparse substitute compilations produced by EXTERNAL_CODEGEN.
    pub fn substitute_external_codegen_compilations(&self) -> u64 {
        self.substitute_external_codegen_compilations
    }

    /// Total sparse substitute compile failures / unsupported cases.
    pub fn substitute_compile_failures(&self) -> u64 {
        self.substitute_compile_failures
    }

    /// Total sparse substitute retries skipped due to backoff.
    pub fn substitute_compile_backoff_skips(&self) -> u64 {
        self.substitute_compile_backoff_skips
    }

    /// Total sparse substitute compile skips due to runtime disable policy.
    pub fn substitute_compile_disabled_skips(&self) -> u64 {
        self.substitute_compile_disabled_skips
    }

    /// Total successful compiled sparse substitute wrapper applications.
    pub fn substitute_compiled_applies(&self) -> u64 {
        self.substitute_compiled_applies
    }

    /// Total sparse substitute applications that used the interpreted fallback path.
    pub fn substitute_fallback_applies(&self) -> u64 {
        self.substitute_fallback_applies
    }

    /// Total compiled sparse substitute applications served by the runtime wrapper.
    pub fn substitute_compiled_runtime_applies(&self) -> u64 {
        self.substitute_compiled_runtime_applies
    }

    /// Total successful sparse substitute applications served by the external code generation function.
    pub fn substitute_external_codegen_applies(&self) -> u64 {
        self.substitute_external_codegen_applies
    }

    /// Total successful empty-target sparse substitute applications served by external code generation.
    pub fn substitute_external_codegen_empty_target_applies(&self) -> u64 {
        self.substitute_external_codegen_empty_target_applies
    }

    /// Total successful non-empty sparse substitute applications served by external code generation.
    pub fn substitute_external_codegen_non_empty_target_applies(&self) -> u64 {
        self.substitute_external_codegen_non_empty_target_applies
    }

    /// Total sparse substitute overflows that fell back to the interpreted path.
    pub fn substitute_overflow_fallbacks(&self) -> u64 {
        self.substitute_overflow_fallbacks
    }

    /// Total sparse substitute queue submissions.
    pub fn substitute_queue_submissions(&self) -> u64 {
        {
            0
        }
    }

    /// Total sparse substitute installs from the background queue.
    pub fn substitute_queue_installs(&self) -> u64 {
        {
            0
        }
    }

    /// Total sparse substitute queue submissions rejected for exhausted budget.
    pub fn substitute_queue_budget_rejects(&self) -> u64 {
        {
            0
        }
    }

    /// Total sparse substitute queue results dropped as stale or invalidated.
    pub fn substitute_queue_dropped_stale(&self) -> u64 {
        {
            0
        }
    }

    /// Total sparse substitute background compile time.
    pub fn substitute_queue_compile_us_total(&self) -> u64 {
        {
            0
        }
    }

    /// Maximum sparse substitute background compile time.
    pub fn substitute_queue_compile_us_max(&self) -> u64 {
        {
            0
        }
    }

    /// Total sparse substitute submit-to-install latency.
    pub fn substitute_queue_submit_to_install_us_total(&self) -> u64 {
        {
            0
        }
    }

    /// Maximum sparse substitute submit-to-install latency.
    pub fn substitute_queue_submit_to_install_us_max(&self) -> u64 {
        {
            0
        }
    }

    /// Remaining sparse substitute background compilation budget in microseconds.
    pub fn substitute_queue_budget_remaining_us(&self) -> u64 {
        {
            0
        }
    }

    /// Total basis-region queue submissions.
    pub fn lra_basis_region_queue_submissions(&self) -> u64 {
        {
            0
        }
    }

    /// Total basis-region installs from the background queue.
    pub fn lra_basis_region_queue_installs(&self) -> u64 {
        {
            0
        }
    }

    /// Total basis-region queue submissions rejected for exhausted budget.
    pub fn lra_basis_region_queue_budget_rejects(&self) -> u64 {
        {
            0
        }
    }

    /// Total basis-region queue results dropped as stale or invalidated.
    pub fn lra_basis_region_queue_dropped_stale(&self) -> u64 {
        {
            0
        }
    }

    /// Total unsupported basis-region results that fell back.
    pub fn lra_basis_region_unsupported_fallbacks(&self) -> u64 {
        {
            0
        }
    }

    /// Total basis-region compile failures or timeouts.
    pub fn lra_basis_region_compile_failures(&self) -> u64 {
        {
            0
        }
    }

    /// Total guarded basis-region native applications.
    pub fn lra_basis_region_native_applies(&self) -> u64 {
        {
            0
        }
    }

    /// Total batch sparse-substitute native applications attributed to basis-region leaves.
    pub fn lra_basis_region_batch_native_applies(&self) -> u64 {
        {
            0
        }
    }

    /// Total basis-region background compile time.
    pub fn lra_basis_region_queue_compile_us_total(&self) -> u64 {
        {
            0
        }
    }

    /// Maximum basis-region background compile time.
    pub fn lra_basis_region_queue_compile_us_max(&self) -> u64 {
        {
            0
        }
    }

    /// Number of basis-region compiler requests waiting for safe-boundary polling.
    pub fn lra_basis_region_pending_requests(&self) -> usize {
        {
            0
        }
    }

    /// Number of installed basis-region guarded-apply bundles.
    pub fn lra_basis_region_installed_count(&self) -> usize {
        {
            0
        }
    }

    /// Whether there is background JIT work that may be ready to install.
    pub fn has_pending_background_work(&self) -> bool {
        false
    }

    /// Backend-neutral restart-boundary install hook.
    ///
    /// Today this forwards EXTERNAL_CODEGEN sparse-substitute compiler results. It remains
    /// unconditional so solver code can call one install hook without knowing
    /// whether compiled artifacts are enabled.
    pub fn install_ready_results(&mut self) -> usize {
        let installed = 0;

        installed
    }

    /// Set the backend-neutral sparse substitute disabled flag at runtime.
    pub fn set_substitute_disabled(&mut self, disabled: bool) {
        self.substitute_disabled = disabled;
    }

    /// Whether sparse substitute compilation is currently disabled.
    pub fn is_substitute_disabled(&self) -> bool {
        self.substitute_disabled
    }

    /// Number of cached entries.
    pub fn len(&self) -> usize {
        self.entries.len()
    }

    /// Whether the cache is empty.
    pub fn is_empty(&self) -> bool {
        self.entries.is_empty()
    }
}

impl Default for PivotRowCache {
    fn default() -> Self {
        Self::new()
    }
}

/// Compile a pivot row's integer coefficients into a native update function.
///
/// Returns `None` if:
/// - The coefficient list is empty
/// - There are too many coefficients (> MAX_COEFFICIENTS)
/// - The platform is not aarch64
///
/// The `coefficients` slice must be sorted by variable index and contain
/// only non-zero entries as `(variable_index, integer_coefficient)`.
///
/// # Errors
///
/// Returns `JitError::MmapFailed` if executable memory allocation fails.
pub fn compile_pivot_row(
    coefficients: &[(u32, i64)],
) -> Result<Option<CompiledPivotRow>, JitError> {
    if coefficients.is_empty() || coefficients.len() > MAX_COEFFICIENTS {
        return Ok(None);
    }

    #[cfg(not(target_arch = "aarch64"))]
    {
        let _ = coefficients;
        Ok(None)
    }

    #[cfg(target_arch = "aarch64")]
    {
        let code = emit_pivot_row_function(coefficients);
        let executable = ExecutableMemory::new(&code)?;
        let fn_ptr = executable.as_ptr();

        // SAFETY: fn_ptr points to the start of our compiled function in
        // executable memory. The function has extern "C" ABI with signature
        // fn(*mut i64, i64). The ExecutableMemory is owned by CompiledPivotRow
        // and remains alive for the lifetime of the struct.
        let func: PivotRowFn = unsafe { std::mem::transmute::<*const u8, PivotRowFn>(fn_ptr) };

        let positions: Vec<u32> = coefficients.iter().map(|(v, _)| *v).collect();
        let coeff_vals: Vec<i64> = coefficients.iter().map(|(_, c)| *c).collect();

        Ok(Some(CompiledPivotRow {
            func,
            num_coeffs: coefficients.len(),
            positions,
            coefficients: coeff_vals,
            apply_count: 0,
            _backing: ArtifactBacking(executable),
        }))
    }
}

/// Compile a batch pivot update function for the given integer coefficients (#8353, #8517).
///
/// The compiled function takes an array of target row pointers, an array of
/// scale factors, and a count. For each row i, it applies:
///   targets\[i\]\[j\] += scales\[i\] * coeff_j for each non-zero position j
///
/// Includes i64 overflow detection (#8517):
/// - Multiply: SMULH gets high 64 bits; if they differ from ASR(low, 63)
///   (sign extension), the multiply overflowed.
/// - Add/Sub: ADDS/SUBS sets the V flag; B.VS branches on signed overflow.
///
/// On overflow, returns early with the 1-based index of the overflowing row.
///
/// Returns `None` if:
/// - The coefficient list is empty or too large
/// - The platform is not aarch64
///
/// # Errors
///
/// Returns `JitError::MmapFailed` if executable memory allocation fails.
pub fn compile_batch_pivot_update(
    coefficients: &[(u32, i64)],
) -> Result<Option<CompiledBatchPivotUpdate>, JitError> {
    if coefficients.is_empty() || coefficients.len() > MAX_COEFFICIENTS {
        return Ok(None);
    }

    #[cfg(not(target_arch = "aarch64"))]
    {
        let _ = coefficients;
        Ok(None)
    }

    #[cfg(target_arch = "aarch64")]
    {
        let code = emit_batch_pivot_function(coefficients);
        let executable = ExecutableMemory::new(&code)?;
        let fn_ptr = executable.as_ptr();

        // SAFETY: fn_ptr points to the start of our compiled batch function in
        // executable memory. The function has extern "C" ABI with signature
        // fn(*const *mut i64, *const i64, u64) -> i64. The ExecutableMemory is
        // owned by CompiledBatchPivotUpdate and remains alive for the struct's lifetime.
        let func: BatchPivotFn = unsafe { std::mem::transmute::<*const u8, BatchPivotFn>(fn_ptr) };

        let positions: Vec<u32> = coefficients.iter().map(|(v, _)| *v).collect();
        let coeff_vals: Vec<i64> = coefficients.iter().map(|(_, c)| *c).collect();

        Ok(Some(CompiledBatchPivotUpdate {
            func,
            num_coeffs: coefficients.len(),
            positions,
            coefficients: coeff_vals,
            apply_count: 0,
            _backing: ArtifactBacking(executable),
        }))
    }
}

// ---------------------------------------------------------------------------
// aarch64 code generation
// ---------------------------------------------------------------------------

/// Minimal 64-bit aarch64 assembler for pivot row functions.
///
/// Separate from the BCP assembler in `aarch64.rs` because the instruction
/// set is different (64-bit arithmetic, MADD, no branches/guards).
#[cfg(target_arch = "aarch64")]
struct SimplexAsm {
    code: Vec<u32>,
}

#[cfg(target_arch = "aarch64")]
impl SimplexAsm {
    fn new() -> Self {
        Self {
            code: Vec::with_capacity(64),
        }
    }

    fn emit(&mut self, instr: u32) {
        self.code.push(instr);
    }

    /// STP x29, x30, [sp, #-16]! ; MOV x29, sp
    fn prologue(&mut self) {
        self.emit(0xa9bf7bfd);
        self.emit(0x910003fd);
    }

    /// LDP x29, x30, [sp], #16 ; RET
    fn epilogue(&mut self) {
        self.emit(0xa8c17bfd);
        self.emit(0xd65f03c0);
    }

    /// LDR Xt, [Xn, #imm] -- 64-bit load, imm must be 8-byte aligned.
    fn ldr_x_uimm(&mut self, rt: u8, rn: u8, byte_offset: u32) {
        debug_assert!(byte_offset.is_multiple_of(8) && byte_offset / 8 < 4096);
        let imm12 = byte_offset / 8;
        self.emit(0xf9400000 | (imm12 << 10) | (u32::from(rn) << 5) | u32::from(rt));
    }

    /// STR Xt, [Xn, #imm] -- 64-bit store, imm must be 8-byte aligned.
    fn str_x_uimm(&mut self, rt: u8, rn: u8, byte_offset: u32) {
        debug_assert!(byte_offset.is_multiple_of(8) && byte_offset / 8 < 4096);
        let imm12 = byte_offset / 8;
        self.emit(0xf9000000 | (imm12 << 10) | (u32::from(rn) << 5) | u32::from(rt));
    }

    /// ADD Xd, Xn, Xm -- 64-bit register add.
    fn add_x(&mut self, rd: u8, rn: u8, rm: u8) {
        self.emit(0x8b000000 | (u32::from(rm) << 16) | (u32::from(rn) << 5) | u32::from(rd));
    }

    /// SUB Xd, Xn, Xm -- 64-bit register subtract.
    fn sub_x(&mut self, rd: u8, rn: u8, rm: u8) {
        self.emit(0xcb000000 | (u32::from(rm) << 16) | (u32::from(rn) << 5) | u32::from(rd));
    }

    /// MADD Xd, Xn, Xm, Xa -- Xd = Xa + Xn * Xm
    fn madd_x(&mut self, rd: u8, rn: u8, rm: u8, ra: u8) {
        self.emit(
            0x9b000000
                | (u32::from(rm) << 16)
                | (u32::from(ra) << 10)
                | (u32::from(rn) << 5)
                | u32::from(rd),
        );
    }

    /// MOV Xd, Xm -- alias for ORR Xd, XZR, Xm
    fn mov_x(&mut self, rd: u8, rm: u8) {
        self.emit(0xaa0003e0 | (u32::from(rm) << 16) | u32::from(rd));
    }

    /// MOVZ Xd, #imm16 (shift=0)
    fn movz_x(&mut self, rd: u8, imm16: u16) {
        self.emit(0xd2800000 | (u32::from(imm16) << 5) | u32::from(rd));
    }

    /// MOVZ Xd, #imm16, LSL #16
    fn movz_x_lsl16(&mut self, rd: u8, imm16: u16) {
        self.emit(0xd2a00000 | (u32::from(imm16) << 5) | u32::from(rd));
    }

    /// MOVZ Xd, #imm16, LSL #32
    fn movz_x_lsl32(&mut self, rd: u8, imm16: u16) {
        self.emit(0xd2c00000 | (u32::from(imm16) << 5) | u32::from(rd));
    }

    /// MOVZ Xd, #imm16, LSL #48
    fn movz_x_lsl48(&mut self, rd: u8, imm16: u16) {
        self.emit(0xd2e00000 | (u32::from(imm16) << 5) | u32::from(rd));
    }

    /// MOVK Xd, #imm16, LSL #16
    fn movk_x_lsl16(&mut self, rd: u8, imm16: u16) {
        self.emit(0xf2a00000 | (u32::from(imm16) << 5) | u32::from(rd));
    }

    /// MOVK Xd, #imm16, LSL #32
    fn movk_x_lsl32(&mut self, rd: u8, imm16: u16) {
        self.emit(0xf2c00000 | (u32::from(imm16) << 5) | u32::from(rd));
    }

    /// MOVK Xd, #imm16, LSL #48
    fn movk_x_lsl48(&mut self, rd: u8, imm16: u16) {
        self.emit(0xf2e00000 | (u32::from(imm16) << 5) | u32::from(rd));
    }

    /// MOVN Xd, #imm16 (shift=0) -- move NOT of imm16
    fn movn_x(&mut self, rd: u8, imm16: u16) {
        self.emit(0x92800000 | (u32::from(imm16) << 5) | u32::from(rd));
    }

    /// MUL Xd, Xn, Xm -- 64-bit multiply (low 64 bits of result).
    /// MUL is an alias for MADD with Ra=XZR.
    fn mul_x(&mut self, rd: u8, rn: u8, rm: u8) {
        self.emit(0x9b007c00 | (u32::from(rm) << 16) | (u32::from(rn) << 5) | u32::from(rd));
    }

    /// SMULH Xd, Xn, Xm -- signed multiply high (high 64 bits of 128-bit result).
    /// Used for overflow detection: if SMULH(a,b) != ASR(MUL(a,b), 63), overflow occurred.
    fn smulh_x(&mut self, rd: u8, rn: u8, rm: u8) {
        self.emit(0x9b407c00 | (u32::from(rm) << 16) | (u32::from(rn) << 5) | u32::from(rd));
    }

    /// ADDS Xd, Xn, Xm -- 64-bit add, setting NZCV flags.
    /// The V (overflow) flag is set when signed overflow occurs.
    fn adds_x(&mut self, rd: u8, rn: u8, rm: u8) {
        self.emit(0xab000000 | (u32::from(rm) << 16) | (u32::from(rn) << 5) | u32::from(rd));
    }

    /// SUBS Xd, Xn, Xm -- 64-bit subtract, setting NZCV flags.
    /// The V (overflow) flag is set when signed overflow occurs.
    fn subs_x(&mut self, rd: u8, rn: u8, rm: u8) {
        self.emit(0xeb000000 | (u32::from(rm) << 16) | (u32::from(rn) << 5) | u32::from(rd));
    }

    /// CMP Xn, Xm, ASR #63 -- compare Xn with arithmetic-right-shifted Xm.
    /// Alias for SUBS XZR, Xn, Xm, ASR #63.
    /// Used to check if SMULH result matches sign extension of MUL result
    /// (i.e., whether a signed 64-bit multiply overflowed).
    fn cmp_x_asr63(&mut self, rn: u8, rm: u8) {
        // SUBS XZR, Xn, Xm, ASR #63
        // sf=1 op=1 S=1 shift=10(ASR) 0 Rm imm6(63) Rn Rd(31)
        // = 0xEB800000 | (Rm << 16) | (63 << 10) | (Rn << 5) | 31
        self.emit(0xeb80fc00 | (u32::from(rm) << 16) | (u32::from(rn) << 5) | 31);
    }

    /// Load a 64-bit immediate into Xd.
    fn mov_imm64(&mut self, rd: u8, value: i64) {
        let v = value as u64;

        // Optimize common small constants
        if (0..=0xFFFF).contains(&value) {
            self.movz_x(rd, v as u16);
            return;
        }

        // Small negative values: use MOVN
        if (-0x10000..0).contains(&value) {
            self.movn_x(rd, (!v) as u16);
            return;
        }

        // General case: MOVZ + MOVK sequence
        let h0 = v as u16;
        let h1 = (v >> 16) as u16;
        let h2 = (v >> 32) as u16;
        let h3 = (v >> 48) as u16;

        if h0 != 0 || (h1 == 0 && h2 == 0 && h3 == 0) {
            self.movz_x(rd, h0);
        } else if h1 != 0 {
            self.movz_x_lsl16(rd, h1);
        } else if h2 != 0 {
            self.movz_x_lsl32(rd, h2);
        } else {
            self.movz_x_lsl48(rd, h3);
        }

        // Fill remaining halfwords
        if h0 != 0 || (h1 == 0 && h2 == 0 && h3 == 0) {
            if h1 != 0 {
                self.movk_x_lsl16(rd, h1);
            }
            if h2 != 0 {
                self.movk_x_lsl32(rd, h2);
            }
            if h3 != 0 {
                self.movk_x_lsl48(rd, h3);
            }
        } else if h1 != 0 {
            if h2 != 0 {
                self.movk_x_lsl32(rd, h2);
            }
            if h3 != 0 {
                self.movk_x_lsl48(rd, h3);
            }
        } else if h2 != 0 {
            if h3 != 0 {
                self.movk_x_lsl48(rd, h3);
            }
        }
    }

    /// Finalize into a byte vector.
    fn finalize(self) -> Vec<u8> {
        let mut bytes = Vec::with_capacity(self.code.len() * 4);
        for &instr in &self.code {
            bytes.extend_from_slice(&instr.to_le_bytes());
        }
        bytes
    }
}

// Register assignments for the compiled pivot row function:
// x0 = target (pointer to dense i64 array)
// x1 = scale (integer multiplier)
// x2 = scratch (loaded target value / computation result)
// x3 = scratch (coefficient immediate, when needed for MADD)
#[cfg(target_arch = "aarch64")]
const TARGET: u8 = 0;
#[cfg(target_arch = "aarch64")]
const SCALE: u8 = 1;
#[cfg(target_arch = "aarch64")]
const TMP: u8 = 2;
#[cfg(target_arch = "aarch64")]
const COEFF: u8 = 3;

/// Emit machine code for a pivot row update function.
///
/// For each (var_index, coefficient) in the pivot row:
///   target[var_index] += scale * coefficient
///
/// Optimizations:
/// - coeff == 1:  target\[j\] += scale  (ADD)
/// - coeff == -1: target\[j\] -= scale  (SUB)
/// - coeff == 2:  target\[j\] += scale + scale (ADD + ADD, avoids MUL)
/// - otherwise:   load coeff as immediate, MADD target\[j\], scale, coeff, target\[j\]
#[cfg(target_arch = "aarch64")]
fn emit_pivot_row_function(coefficients: &[(u32, i64)]) -> Vec<u8> {
    let mut asm = SimplexAsm::new();

    asm.prologue();

    for &(var_idx, coeff) in coefficients {
        let byte_offset = var_idx * 8;

        // Load current target[var_idx] into TMP
        if byte_offset / 8 < 4096 {
            asm.ldr_x_uimm(TMP, TARGET, byte_offset);
        } else {
            // Large offset: compute address in scratch register
            asm.mov_imm64(COEFF, i64::from(byte_offset));
            asm.add_x(COEFF, TARGET, COEFF);
            asm.ldr_x_uimm(TMP, COEFF, 0);
        }

        // Compute target[var_idx] += scale * coeff
        match coeff {
            1 => {
                // target\[j\] += scale
                asm.add_x(TMP, TMP, SCALE);
            }
            -1 => {
                // target\[j\] -= scale
                asm.sub_x(TMP, TMP, SCALE);
            }
            2 => {
                // target\[j\] += 2 * scale (two ADDs cheaper than MUL on Apple M-series)
                asm.add_x(TMP, TMP, SCALE);
                asm.add_x(TMP, TMP, SCALE);
            }
            -2 => {
                // target\[j\] -= 2 * scale
                asm.sub_x(TMP, TMP, SCALE);
                asm.sub_x(TMP, TMP, SCALE);
            }
            _ => {
                // General case: load coefficient, then MADD
                asm.mov_imm64(COEFF, coeff);
                // TMP = TMP + SCALE * COEFF  (MADD Xd, Xn, Xm, Xa = Xa + Xn*Xm)
                asm.madd_x(TMP, SCALE, COEFF, TMP);
            }
        }

        // Store result back
        if byte_offset / 8 < 4096 {
            asm.str_x_uimm(TMP, TARGET, byte_offset);
        } else {
            // Large offset: recompute address
            asm.mov_imm64(COEFF, i64::from(byte_offset));
            asm.add_x(COEFF, TARGET, COEFF);
            asm.str_x_uimm(TMP, COEFF, 0);
        }
    }

    // Return void (x0 is clobbered by target pointer, which is fine for void return)
    asm.epilogue();

    asm.finalize()
}

/// Emit machine code for a batch pivot update function (#8353, #8517).
///
/// Calling convention:
///   x0 = targets (*const *mut i64) -- array of row pointers
///   x1 = scales  (*const i64)      -- array of scale factors
///   x2 = num_rows (u64)            -- number of rows to update
///
/// Returns (in x0):
///   0 -- all rows updated successfully
///   N -- 1-based index of the first row that overflowed (rows 0..N-1 updated)
///
/// Overflow detection (#8517):
/// - Multiply: SMULH gets high 64 bits; compare with ASR(low, 63).
///   If they differ, the signed 64-bit multiply overflowed.
/// - Add/Sub: ADDS/SUBS sets the V (overflow) flag; B.VS branches on overflow.
/// - Special cases (coeff +-1, +-2): use ADDS/SUBS directly.
///
/// Register allocation uses only caller-saved registers (x3-x11) to avoid
/// the complexity and potential bugs of STP/LDP save/restore of callee-saved
/// registers.
#[cfg(target_arch = "aarch64")]
fn emit_batch_pivot_function(coefficients: &[(u32, i64)]) -> Vec<u8> {
    let mut asm = SimplexAsm::new();

    // Caller-saved registers -- no STP/LDP needed.
    const TARGETS_BASE: u8 = 3; // x3 = targets base pointer
    const SCALES_BASE: u8 = 8; // x8 = scales base pointer
    const NUM_ROWS: u8 = 9; // x9 = num_rows
    const ROW_IDX: u8 = 10; // x10 = loop counter
    const CUR_TARGET: u8 = 4; // x4 = current target row pointer
    const CUR_SCALE: u8 = 5; // x5 = current scale
    const TMP_VAL: u8 = 6; // x6 = scratch (loaded target value)
    const TMP_COEFF: u8 = 7; // x7 = scratch (coefficient immediate / product low)
    const OVERFLOW_TMP: u8 = 11; // x11 = overflow scratch (SMULH high bits)

    // Collect positions of overflow branch placeholders for patching.
    let mut overflow_branch_positions: Vec<usize> = Vec::new();

    asm.prologue();

    // Move parameters out of x0-x2 to caller-saved registers.
    // x0/x1/x2 are caller-saved too, but x0 is used for return value.
    asm.mov_x(TARGETS_BASE, 0); // x3 = targets (x0)
    asm.mov_x(SCALES_BASE, 1); // x8 = scales (x1)
    asm.mov_x(NUM_ROWS, 2); // x9 = num_rows (x2)
    asm.movz_x(ROW_IDX, 0); // x10 = row_idx = 0

    let loop_start = asm.code.len();

    // CMP ROW_IDX, NUM_ROWS ; B.HS exit
    // SUBS XZR, x10, x9
    asm.emit(
        0xeb000000
            | (u32::from(NUM_ROWS) << 16)   // Rm = x9
            | (u32::from(ROW_IDX) << 5)     // Rn = x10
            | 0x1f, // Rd = XZR (31)
    );
    let branch_exit_pos = asm.code.len();
    asm.emit(0x54000002); // B.HS placeholder

    // LDR x4, [x3, x10, LSL #3] -- load targets[row_idx]
    asm.emit(
        0xf8607800
            | (u32::from(ROW_IDX) << 16)      // Rm = x10
            | (u32::from(TARGETS_BASE) << 5)  // Rn = x3
            | u32::from(CUR_TARGET),
    );

    // LDR x5, [x8, x10, LSL #3] -- load scales[row_idx]
    asm.emit(
        0xf8607800
            | (u32::from(ROW_IDX) << 16)     // Rm = x10
            | (u32::from(SCALES_BASE) << 5)  // Rn = x8
            | u32::from(CUR_SCALE),
    );

    // Apply each coefficient to the current target row, with overflow detection.
    for &(var_idx, coeff) in coefficients {
        let byte_offset = var_idx * 8;

        // Load target[var_idx] into TMP_VAL
        if byte_offset / 8 < 4096 {
            asm.ldr_x_uimm(TMP_VAL, CUR_TARGET, byte_offset);
        } else {
            asm.mov_imm64(TMP_COEFF, i64::from(byte_offset));
            asm.add_x(TMP_COEFF, CUR_TARGET, TMP_COEFF);
            asm.ldr_x_uimm(TMP_VAL, TMP_COEFF, 0);
        }

        match coeff {
            1 => {
                // target\[j\] += scale; ADDS sets V flag on signed overflow.
                asm.adds_x(TMP_VAL, TMP_VAL, CUR_SCALE);
                overflow_branch_positions.push(asm.code.len());
                asm.emit(0x54000006); // B.VS placeholder
            }
            -1 => {
                // target\[j\] -= scale; SUBS sets V flag on signed overflow.
                asm.subs_x(TMP_VAL, TMP_VAL, CUR_SCALE);
                overflow_branch_positions.push(asm.code.len());
                asm.emit(0x54000006); // B.VS placeholder
            }
            2 => {
                // target\[j\] += 2 * scale (two ADDS, each checked).
                asm.adds_x(TMP_VAL, TMP_VAL, CUR_SCALE);
                overflow_branch_positions.push(asm.code.len());
                asm.emit(0x54000006); // B.VS placeholder
                asm.adds_x(TMP_VAL, TMP_VAL, CUR_SCALE);
                overflow_branch_positions.push(asm.code.len());
                asm.emit(0x54000006); // B.VS placeholder
            }
            -2 => {
                // target\[j\] -= 2 * scale (two SUBS, each checked).
                asm.subs_x(TMP_VAL, TMP_VAL, CUR_SCALE);
                overflow_branch_positions.push(asm.code.len());
                asm.emit(0x54000006); // B.VS placeholder
                asm.subs_x(TMP_VAL, TMP_VAL, CUR_SCALE);
                overflow_branch_positions.push(asm.code.len());
                asm.emit(0x54000006); // B.VS placeholder
            }
            _ => {
                // General case: product = scale * coeff, then target += product.
                // 1. Load coefficient immediate
                asm.mov_imm64(TMP_COEFF, coeff);
                // 2. SMULH x11, scale, coeff -> high 64 bits of signed 128-bit product
                asm.smulh_x(OVERFLOW_TMP, CUR_SCALE, TMP_COEFF);
                // 3. MUL x7, scale, coeff -> low 64 bits (reuse TMP_COEFF)
                asm.mul_x(TMP_COEFF, CUR_SCALE, TMP_COEFF);
                // 4. CMP x11, x7, ASR #63 -> check if high bits match sign extension
                //    If they differ, the multiply overflowed.
                asm.cmp_x_asr63(OVERFLOW_TMP, TMP_COEFF);
                overflow_branch_positions.push(asm.code.len());
                asm.emit(0x54000001); // B.NE placeholder (condition 0001 = NE)
                                      // 5. ADDS target, target, product -> add with overflow check
                asm.adds_x(TMP_VAL, TMP_VAL, TMP_COEFF);
                overflow_branch_positions.push(asm.code.len());
                asm.emit(0x54000006); // B.VS placeholder
            }
        }

        // Store result back
        if byte_offset / 8 < 4096 {
            asm.str_x_uimm(TMP_VAL, CUR_TARGET, byte_offset);
        } else {
            asm.mov_imm64(TMP_COEFF, i64::from(byte_offset));
            asm.add_x(TMP_COEFF, CUR_TARGET, TMP_COEFF);
            asm.str_x_uimm(TMP_VAL, TMP_COEFF, 0);
        }
    }

    // row_idx++ : ADD ROW_IDX, ROW_IDX, #1
    asm.emit(0x91000400 | (u32::from(ROW_IDX) << 5) | u32::from(ROW_IDX));

    // B loop_start
    let branch_back_pos = asm.code.len();
    let backward_offset = (loop_start as i32) - (branch_back_pos as i32);
    let imm26 = (backward_offset as u32) & 0x03ffffff;
    asm.emit(0x14000000 | imm26);

    // Exit: return 0 (success, all rows updated)
    let exit_pos = asm.code.len();
    asm.movz_x(0, 0);
    asm.epilogue();

    // Overflow exit: return (row_idx + 1) as 1-based overflow indicator.
    // ADD x0, ROW_IDX, #1
    let overflow_exit_pos = asm.code.len();
    asm.emit(0x91000400 | (u32::from(ROW_IDX) << 5) | u32::from(0u8));
    asm.epilogue();

    // Patch B.HS to normal exit
    {
        let offset = (exit_pos as i32) - (branch_exit_pos as i32);
        let imm19 = ((offset as u32) & 0x7ffff) << 5;
        asm.code[branch_exit_pos] = 0x54000002 | imm19;
    }

    // Patch all overflow branches to overflow_exit.
    // B.VS has condition code 0110, B.NE has condition code 0001.
    // We preserve the condition code from the placeholder and patch the offset.
    for &pos in &overflow_branch_positions {
        let offset = (overflow_exit_pos as i32) - (pos as i32);
        let imm19 = ((offset as u32) & 0x7ffff) << 5;
        let cond = asm.code[pos] & 0xf; // preserve condition code
        asm.code[pos] = 0x54000000 | imm19 | cond;
    }

    asm.finalize()
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
#[cfg(target_arch = "aarch64")]
mod tests {
    use super::*;
    use proptest::collection::{btree_set, vec as prop_vec};
    use proptest::prelude::*;

    fn assert_cached_row_use_count(cache: &PivotRowCache, row_idx: usize, expected_use_count: u32) {
        let entry = cache
            .entries
            .get(&row_idx)
            .expect("row should remain tracked in the cache");
        assert_eq!(entry.use_count, expected_use_count);
    }

    /// Helper: apply compiled pivot row to a dense array and return the result.
    fn apply_and_check(coefficients: &[(u32, i64)], initial: &mut [i64], scale: i64) {
        let compiled = compile_pivot_row(coefficients)
            .expect("compile_pivot_row failed")
            .expect("compile_pivot_row returned None");

        assert_eq!(compiled.num_coeffs(), coefficients.len());
        assert!(compiled.matches(coefficients));

        // SAFETY: initial is a valid mutable slice, and all variable indices
        // in coefficients are within bounds (verified by test setup).
        unsafe {
            let mut compiled = compiled;
            compiled.apply(initial.as_mut_ptr(), scale);
        }
    }

    #[test]
    fn test_compile_pivot_row_single_coeff() {
        // target[5] += scale * 3
        let coeffs = vec![(5, 3i64)];
        let mut target = vec![0i64; 10];
        target[5] = 100;

        apply_and_check(&coeffs, &mut target, 7);

        // Expected: target[5] = 100 + 7 * 3 = 121
        assert_eq!(target[5], 121);
        assert_eq!(target[0], 0);
        assert_eq!(target[9], 0);
    }

    #[test]
    fn test_compile_pivot_row_identity_coeff() {
        // target[3] += scale * 1 (should use ADD, not MUL)
        let coeffs = vec![(3, 1i64)];
        let mut target = vec![0i64; 10];
        target[3] = 50;

        apply_and_check(&coeffs, &mut target, 10);

        assert_eq!(target[3], 60); // 50 + 10 * 1
    }

    #[test]
    fn test_compile_pivot_row_negative_coeff() {
        // target[2] += scale * (-5)
        let coeffs = vec![(2, -5i64)];
        let mut target = vec![0i64; 10];
        target[2] = 100;

        apply_and_check(&coeffs, &mut target, 4);

        assert_eq!(target[2], 80); // 100 + 4 * (-5) = 80
    }

    #[test]
    fn test_compile_pivot_row_neg_one() {
        // target[0] += scale * (-1) (should use SUB)
        let coeffs = vec![(0, -1i64)];
        let mut target = vec![0i64; 10];
        target[0] = 30;

        apply_and_check(&coeffs, &mut target, 12);

        assert_eq!(target[0], 18); // 30 + 12 * (-1) = 18
    }

    #[test]
    fn test_compile_pivot_row_multiple_coeffs() {
        // target[1] += scale * 2
        // target[3] += scale * (-3)
        // target[7] += scale * 1
        let coeffs = vec![(1, 2i64), (3, -3i64), (7, 1i64)];
        let mut target = vec![0i64; 10];
        target[1] = 10;
        target[3] = 20;
        target[7] = 30;

        apply_and_check(&coeffs, &mut target, 5);

        assert_eq!(target[1], 20); // 10 + 5 * 2 = 20
        assert_eq!(target[3], 5); // 20 + 5 * (-3) = 5
        assert_eq!(target[7], 35); // 30 + 5 * 1 = 35
        assert_eq!(target[0], 0);
        assert_eq!(target[2], 0);
    }

    #[test]
    fn test_compile_pivot_row_coeff_two() {
        // target[4] += scale * 2 (should use ADD+ADD, not MUL)
        let coeffs = vec![(4, 2i64)];
        let mut target = vec![0i64; 10];
        target[4] = 100;

        apply_and_check(&coeffs, &mut target, 7);

        assert_eq!(target[4], 114); // 100 + 7 * 2 = 114
    }

    #[test]
    fn test_compile_pivot_row_coeff_neg_two() {
        // target[6] += scale * (-2) (should use SUB+SUB)
        let coeffs = vec![(6, -2i64)];
        let mut target = vec![0i64; 10];
        target[6] = 100;

        apply_and_check(&coeffs, &mut target, 3);

        assert_eq!(target[6], 94); // 100 + 3 * (-2) = 94
    }

    #[test]
    fn test_compile_pivot_row_large_coeff() {
        // Test with a large coefficient that requires multi-instruction immediate load
        let coeffs = vec![(0, 100_000i64)];
        let mut target = vec![0i64; 10];
        target[0] = 0;

        apply_and_check(&coeffs, &mut target, 3);

        assert_eq!(target[0], 300_000); // 0 + 3 * 100_000
    }

    #[test]
    fn test_compile_pivot_row_negative_scale() {
        // scale can be negative too
        let coeffs = vec![(1, 3i64), (2, -1i64)];
        let mut target = vec![0i64; 10];
        target[1] = 100;
        target[2] = 50;

        apply_and_check(&coeffs, &mut target, -4);

        assert_eq!(target[1], 88); // 100 + (-4) * 3 = 88
        assert_eq!(target[2], 54); // 50 + (-4) * (-1) = 54
    }

    #[test]
    fn test_compile_pivot_row_zero_scale() {
        // scale = 0 should be a no-op
        let coeffs = vec![(0, 5i64), (1, -3i64)];
        let mut target = vec![42i64; 10];

        apply_and_check(&coeffs, &mut target, 0);

        for &v in &target {
            assert_eq!(v, 42);
        }
    }

    #[test]
    fn test_compile_pivot_row_empty_returns_none() {
        let result = compile_pivot_row(&[]).expect("should not error");
        assert!(result.is_none());
    }

    #[test]
    fn test_compile_pivot_row_matches_check() {
        let coeffs = vec![(1, 2i64), (3, -5i64)];
        let compiled = compile_pivot_row(&coeffs)
            .expect("compile failed")
            .expect("returned None");

        assert!(compiled.matches(&[(1, 2), (3, -5)]));
        assert!(!compiled.matches(&[(1, 2), (3, -4)])); // different coeff
        assert!(!compiled.matches(&[(1, 2)])); // different length
        assert!(!compiled.matches(&[(2, 2), (3, -5)])); // different position
    }

    #[test]
    fn test_compile_pivot_row_apply_count() {
        let coeffs = vec![(0, 1i64)];
        let mut compiled = compile_pivot_row(&coeffs)
            .expect("compile failed")
            .expect("returned None");

        assert_eq!(compiled.apply_count(), 0);

        let mut target = vec![0i64; 4];
        unsafe {
            compiled.apply(target.as_mut_ptr(), 1);
        }
        assert_eq!(compiled.apply_count(), 1);

        unsafe {
            compiled.apply(target.as_mut_ptr(), 1);
        }
        assert_eq!(compiled.apply_count(), 2);

        assert_eq!(target[0], 2); // applied twice with scale=1, coeff=1
    }

    #[test]
    fn test_compile_pivot_row_negative_large_coeff() {
        // Test negative coefficient requiring MOVN optimization
        let coeffs = vec![(0, -1_000i64)];
        let mut target = vec![0i64; 4];

        apply_and_check(&coeffs, &mut target, 5);

        assert_eq!(target[0], -5_000); // 0 + 5 * (-1000)
    }

    #[test]
    fn test_pivot_row_cache_basic() {
        let mut cache = PivotRowCache::new();
        assert!(cache.is_empty());
        assert_eq!(cache.len(), 0);

        // Record uses below threshold -- should not compile
        let coeffs = vec![(0u32, 1i64), (1, -2)];
        for _ in 0..COMPILE_THRESHOLD - 1 {
            cache.record_pivot(0, Some(&coeffs));
        }
        assert!(cache.get_compiled(0).is_none());
        assert_eq!(cache.compilations(), 0);
        assert_cached_row_use_count(&cache, 0, COMPILE_THRESHOLD - 1);

        // Hit threshold. Reuse tracking is active, but pivot-row cache
        // compilation is retired; sparse substitute is the EXTERNAL_CODEGEN-backed path.
        cache.record_pivot(0, Some(&coeffs));
        assert_cached_row_use_count(&cache, 0, COMPILE_THRESHOLD);
        assert!(cache.get_compiled(0).is_none());
        assert_eq!(cache.compilations(), 0);

        // Invalidation
        cache.invalidate(0);
        assert!(cache.get_compiled(0).is_none());
        assert!(!cache.entries.contains_key(&0));
    }

    #[test]
    fn test_pivot_row_cache_clear() {
        let mut cache = PivotRowCache::new();
        let coeffs = vec![(0u32, 5i64)];

        for _ in 0..=COMPILE_THRESHOLD {
            cache.record_pivot(0, Some(&coeffs));
        }
        assert!(!cache.is_empty());

        cache.clear();
        assert!(cache.is_empty());
        assert!(cache.get_compiled(0).is_none());
    }

    #[test]
    fn test_pivot_row_cache_non_integer_skip() {
        let mut cache = PivotRowCache::new();

        // Passing None for non-integer coefficients should never compile
        for _ in 0..COMPILE_THRESHOLD * 2 {
            cache.record_pivot(0, None);
        }
        assert!(cache.get_compiled(0).is_none());
        assert_eq!(cache.compilations(), 0);
    }

    // --- Batch pivot update tests (#8353) ---

    #[test]
    fn test_batch_pivot_compile_single_row() {
        let coeffs = vec![(1, 3i64), (3, -2i64)];
        let mut batch = compile_batch_pivot_update(&coeffs)
            .expect("compile failed")
            .expect("returned None");

        assert_eq!(batch.num_coeffs(), 2);
        assert!(batch.matches(&coeffs));

        let mut row0 = vec![0i64; 10];
        row0[1] = 10;
        row0[3] = 20;

        let targets = vec![row0.as_mut_ptr()];
        let scales = vec![5i64];

        let updated = unsafe { batch.apply(&targets, &scales) };
        assert_eq!(updated, 1);

        assert_eq!(row0[1], 25); // 10 + 5 * 3 = 25
        assert_eq!(row0[3], 10); // 20 + 5 * (-2) = 10
    }

    #[test]
    fn test_batch_pivot_compile_multiple_rows() {
        let coeffs = vec![(0, 1i64), (2, -1i64), (4, 5i64)];
        let mut batch = compile_batch_pivot_update(&coeffs)
            .expect("compile failed")
            .expect("returned None");

        let mut row0 = vec![100i64; 10];
        let mut row1 = vec![200i64; 10];
        let mut row2 = vec![300i64; 10];

        let targets = vec![row0.as_mut_ptr(), row1.as_mut_ptr(), row2.as_mut_ptr()];
        let scales = vec![2i64, -3i64, 1i64];

        let updated = unsafe { batch.apply(&targets, &scales) };
        assert_eq!(updated, 3);

        // Row 0: scale=2
        assert_eq!(row0[0], 102); // 100 + 2 * 1
        assert_eq!(row0[2], 98); // 100 + 2 * (-1)
        assert_eq!(row0[4], 110); // 100 + 2 * 5

        // Row 1: scale=-3
        assert_eq!(row1[0], 197); // 200 + (-3) * 1
        assert_eq!(row1[2], 203); // 200 + (-3) * (-1)
        assert_eq!(row1[4], 185); // 200 + (-3) * 5

        // Row 2: scale=1
        assert_eq!(row2[0], 301); // 300 + 1 * 1
        assert_eq!(row2[2], 299); // 300 + 1 * (-1)
        assert_eq!(row2[4], 305); // 300 + 1 * 5
    }

    #[test]
    fn test_batch_pivot_compile_zero_rows() {
        let coeffs = vec![(0, 1i64)];
        let mut batch = compile_batch_pivot_update(&coeffs)
            .expect("compile failed")
            .expect("returned None");

        let targets: Vec<*mut i64> = vec![];
        let scales: Vec<i64> = vec![];

        let updated = unsafe { batch.apply(&targets, &scales) };
        assert_eq!(updated, 0);
    }

    #[test]
    fn test_batch_pivot_compile_coeff_two() {
        // Test the ADD+ADD optimization for coeff=2
        let coeffs = vec![(0, 2i64)];
        let mut batch = compile_batch_pivot_update(&coeffs)
            .expect("compile failed")
            .expect("returned None");

        let mut row0 = vec![10i64; 4];
        let targets = vec![row0.as_mut_ptr()];
        let scales = vec![7i64];

        let updated = unsafe { batch.apply(&targets, &scales) };
        assert_eq!(updated, 1);
        assert_eq!(row0[0], 24); // 10 + 7 * 2 = 24
    }

    #[test]
    fn test_batch_pivot_compile_empty_returns_none() {
        let result = compile_batch_pivot_update(&[]).expect("should not error");
        assert!(result.is_none());
    }

    #[test]
    fn test_batch_pivot_matches_single_row_update() {
        // Verify batch update with 1 row produces same result as single-row update
        let coeffs = vec![(1, 3i64), (2, -5i64), (5, 1i64), (8, -2i64)];

        let mut single_target = vec![50i64; 10];
        let mut batch_target = vec![50i64; 10];
        let scale = 7i64;

        // Apply single-row
        let mut single = compile_pivot_row(&coeffs)
            .expect("compile failed")
            .expect("returned None");
        unsafe {
            single.apply(single_target.as_mut_ptr(), scale);
        }

        // Apply batch
        let mut batch = compile_batch_pivot_update(&coeffs)
            .expect("compile failed")
            .expect("returned None");
        let targets = vec![batch_target.as_mut_ptr()];
        let scales = vec![scale];
        unsafe {
            batch.apply(&targets, &scales);
        }

        // Results must match
        assert_eq!(single_target, batch_target);
    }

    #[test]
    fn test_batch_pivot_cache_integration() {
        let mut cache = PivotRowCache::new();
        let coeffs = vec![(0u32, 1i64), (1, -2)];

        // Hit threshold to trigger reuse tracking; pivot-row cache compilation
        // remains retired.
        for _ in 0..=COMPILE_THRESHOLD {
            cache.record_pivot(0, Some(&coeffs));
        }
        assert_cached_row_use_count(&cache, 0, COMPILE_THRESHOLD + 1);

        assert!(cache.get_compiled(0).is_none());
        assert!(cache.get_batch_compiled(0).is_none());
        assert_eq!(cache.compilations(), 0);
        assert_eq!(cache.batch_compilations(), 0);
    }

    // --- Pure-Rust i64 batch update tests (#8353) ---

    #[test]
    fn test_batch_pivot_update_i64_basic() {
        let coeffs = vec![(1, 3i64), (3, -2i64)];
        let mut row0 = vec![0i64; 10];
        let mut row1 = vec![100i64; 10];
        row0[1] = 10;
        row0[3] = 20;

        let scales = vec![5i64, -1i64];
        let updated = batch_pivot_update_i64(&coeffs, &mut [&mut row0, &mut row1], &scales);
        assert_eq!(updated, 2);

        assert_eq!(row0[1], 25); // 10 + 5 * 3
        assert_eq!(row0[3], 10); // 20 + 5 * (-2)
        assert_eq!(row1[1], 97); // 100 + (-1) * 3
        assert_eq!(row1[3], 102); // 100 + (-1) * (-2)
    }

    #[test]
    fn test_batch_pivot_update_i64_overflow() {
        let coeffs = vec![(0, i64::MAX)];
        let mut row0 = vec![0i64; 4];
        let mut row1 = vec![0i64; 4];

        let scales = vec![1i64, 2i64];
        let updated = batch_pivot_update_i64(&coeffs, &mut [&mut row0, &mut row1], &scales);
        // Row 0 succeeds (0 + 1 * MAX = MAX), row 1 overflows (0 + 2 * MAX)
        assert_eq!(updated, 1);
        assert_eq!(row0[0], i64::MAX);
        assert_eq!(row1[0], 0); // not modified
    }

    #[test]
    fn test_batch_pivot_update_i64_empty_coeffs() {
        let mut row0 = vec![42i64; 4];
        let scales = vec![5i64];
        let updated = batch_pivot_update_i64(&[], &mut [&mut row0], &scales);
        assert_eq!(updated, 1); // no-op, all rows "succeed"
        assert_eq!(row0[0], 42);
    }

    #[test]
    fn test_batch_pivot_update_i64_zero_coeff_skipped() {
        let coeffs = vec![(0, 0i64), (1, 3i64)];
        let mut row0 = vec![10i64; 4];
        let scales = vec![2i64];
        let updated = batch_pivot_update_i64(&coeffs, &mut [&mut row0], &scales);
        assert_eq!(updated, 1);
        assert_eq!(row0[0], 10); // unchanged (coeff=0)
        assert_eq!(row0[1], 16); // 10 + 2 * 3
    }

    #[test]
    fn test_compile_pivot_row_single_element_row() {
        let coeffs = vec![(0, 42i64)];
        let mut target = vec![0i64; 4];

        apply_and_check(&coeffs, &mut target, 3);

        assert_eq!(target[0], 126); // 0 + 3 * 42
    }

    #[test]
    fn test_compile_pivot_row_mixed_coefficient_patterns() {
        let coeffs = vec![(0, 1i64), (1, -1), (2, 2), (3, -2), (4, 7), (5, -13)];
        let mut target = vec![100i64; 6];

        apply_and_check(&coeffs, &mut target, 3);

        assert_eq!(target[0], 103); // 100 + 3 * 1
        assert_eq!(target[1], 97); // 100 + 3 * (-1)
        assert_eq!(target[2], 106); // 100 + 3 * 2
        assert_eq!(target[3], 94); // 100 + 3 * (-2)
        assert_eq!(target[4], 121); // 100 + 3 * 7
        assert_eq!(target[5], 61); // 100 + 3 * (-13)
    }

    #[test]
    fn test_compile_pivot_row_large_var_index() {
        let coeffs = vec![(4096, 5i64)];
        let mut target = vec![0i64; 4097];
        target[4096] = 10;

        apply_and_check(&coeffs, &mut target, 3);

        assert_eq!(target[4096], 25); // 10 + 3 * 5
    }

    #[test]
    fn test_compile_pivot_row_overflow_wraps_silently() {
        let coeffs = vec![(0, i64::MAX)];
        let mut target = vec![0i64; 1];

        apply_and_check(&coeffs, &mut target, 2);

        let expected = 0i64.wrapping_add(2i64.wrapping_mul(i64::MAX));
        assert_eq!(target[0], expected);
    }

    #[test]
    fn test_compile_pivot_row_max_coefficients_boundary() {
        let coeffs: Vec<_> = (0..MAX_COEFFICIENTS)
            .map(|var| (var as u32, 1i64))
            .collect();
        let mut target = vec![0i64; MAX_COEFFICIENTS];

        apply_and_check(&coeffs, &mut target, 1);

        assert!(target.iter().all(|&value| value == 1));
    }

    #[test]
    fn test_compile_pivot_row_over_max_returns_none() {
        let coeffs: Vec<_> = (0..=MAX_COEFFICIENTS)
            .map(|var| (var as u32, 1i64))
            .collect();
        assert_eq!(coeffs.len(), MAX_COEFFICIENTS + 1);

        let result = compile_pivot_row(&coeffs).expect("compile should not error");
        assert!(result.is_none());
    }

    #[test]
    fn test_compile_pivot_row_negative_initial_values() {
        let coeffs = vec![(0, 3i64), (1, -2)];
        let mut target = vec![-50i64, -100];

        apply_and_check(&coeffs, &mut target, 4);

        assert_eq!(target[0], -38); // -50 + 4 * 3
        assert_eq!(target[1], -108); // -100 + 4 * (-2)
    }

    #[test]
    fn test_compile_pivot_row_large_immediate_multi_halfword() {
        let coeff = 0x0001_0001_0001_0001i64;
        let coeffs = vec![(0, coeff)];
        let mut target = vec![0i64; 1];

        apply_and_check(&coeffs, &mut target, 1);

        assert_eq!(target[0], coeff);
    }

    #[test]
    fn test_compile_pivot_row_negative_large_immediate() {
        let coeff = -0x1_0000_0001i64;
        let coeffs = vec![(0, coeff)];
        let mut target = vec![0i64; 1];

        apply_and_check(&coeffs, &mut target, 1);

        assert_eq!(target[0], coeff);
    }

    #[test]
    fn test_batch_pivot_neg_two_coeff() {
        let coeffs = vec![(0, -2i64)];
        let mut batch = compile_batch_pivot_update(&coeffs)
            .expect("compile failed")
            .expect("returned None");

        let mut row0 = vec![0i64; 1];
        row0[0] = 100;

        let targets = vec![row0.as_mut_ptr()];
        let scales = vec![3i64];

        let updated = unsafe { batch.apply(&targets, &scales) };
        assert_eq!(updated, 1);
        assert_eq!(row0[0], 94); // 100 + 3 * (-2)
    }

    #[test]
    fn test_batch_pivot_many_rows() {
        let coeffs = vec![(0, 1i64), (1, -1i64)];
        let mut batch = compile_batch_pivot_update(&coeffs)
            .expect("compile failed")
            .expect("returned None");

        let mut rows: Vec<Vec<i64>> = (0..10).map(|_| vec![50i64; 4]).collect();
        let targets: Vec<*mut i64> = rows.iter_mut().map(Vec::as_mut_ptr).collect();
        let scales: Vec<i64> = (1..=10).map(i64::from).collect();

        let updated = unsafe { batch.apply(&targets, &scales) };
        assert_eq!(updated, rows.len());

        for (idx, row) in rows.iter().enumerate() {
            let scale = (idx + 1) as i64;
            assert_eq!(row[0], 50 + scale);
            assert_eq!(row[1], 50 - scale);
            assert_eq!(row[2], 50);
            assert_eq!(row[3], 50);
        }
    }

    #[test]
    fn test_batch_pivot_matches_check() {
        let coeffs = vec![(1, 2i64), (3, -5i64)];
        let compiled = compile_batch_pivot_update(&coeffs)
            .expect("compile failed")
            .expect("returned None");

        assert!(compiled.matches(&[(1, 2), (3, -5)]));
        assert!(!compiled.matches(&[(1, 2), (3, -4)])); // different coeff
        assert!(!compiled.matches(&[(2, 2), (3, -5)])); // different position
        assert!(!compiled.matches(&[(1, 2)])); // different length
    }

    #[test]
    fn test_pivot_row_cache_staleness_after_invalidation() {
        // After invalidation, recording the same row with different coefficients
        // should start a fresh threshold window without installing retired
        // pivot-row cache artifacts.
        let mut cache = PivotRowCache::new();
        let coeffs1 = vec![(0u32, 1i64)];

        // Hit threshold with coeffs1.
        for _ in 0..COMPILE_THRESHOLD {
            cache.record_pivot(0, Some(&coeffs1));
        }
        assert_cached_row_use_count(&cache, 0, COMPILE_THRESHOLD);
        assert!(cache.get_compiled(0).is_none());
        assert_eq!(cache.compilations(), 0);

        // Invalidate and re-record with different coefficients
        cache.invalidate(0);
        assert!(cache.get_compiled(0).is_none());
        assert!(!cache.entries.contains_key(&0));

        let coeffs2 = vec![(0u32, 2i64)];
        for _ in 0..COMPILE_THRESHOLD {
            cache.record_pivot(0, Some(&coeffs2));
        }
        assert_cached_row_use_count(&cache, 0, COMPILE_THRESHOLD);
        assert!(cache.get_compiled(0).is_none());
        assert_eq!(cache.compilations(), 0);
    }

    #[test]
    fn test_pivot_row_cache_no_staleness_detection_after_compile() {
        // NOTE: The cache only has coefficient staleness semantics once it
        // actually contains a compiled artifact. The retired pivot-row cache
        // path no longer installs one, so repeated records keep tracking reuse.
        let mut cache = PivotRowCache::new();
        let coeffs1 = vec![(0u32, 1i64)];

        for _ in 0..COMPILE_THRESHOLD {
            cache.record_pivot(0, Some(&coeffs1));
        }
        assert_cached_row_use_count(&cache, 0, COMPILE_THRESHOLD);

        // Record with different coefficients -- cache only advances reuse.
        let coeffs2 = vec![(0u32, 2i64)];
        cache.record_pivot(0, Some(&coeffs2));
        assert_cached_row_use_count(&cache, 0, COMPILE_THRESHOLD + 1);
        assert!(cache.get_compiled(0).is_none());
        assert_eq!(
            cache.compilations(),
            0,
            "no pivot-row cache compilation occurs"
        );
    }

    #[test]
    fn test_batch_pivot_single_coeff_all_patterns() {
        for coeff in [1i64, -1, 2, -2, 7, -13] {
            let coeffs = vec![(0, coeff)];
            let mut batch = compile_batch_pivot_update(&coeffs)
                .expect("compile failed")
                .expect("returned None");

            let mut row0 = vec![100i64; 1];
            let targets = vec![row0.as_mut_ptr()];
            let scales = vec![5i64];

            let updated = unsafe { batch.apply(&targets, &scales) };
            assert_eq!(updated, 1);
            assert_eq!(row0[0], 100 + 5 * coeff);
        }
    }

    // --- Batch pivot JIT overflow detection tests (#8517) ---

    #[test]
    fn test_batch_pivot_jit_overflow_mul_detected() {
        // (i64::MAX / 2 + 1) * 2 overflows i64
        let coeffs = vec![(0, 2i64)];
        let mut batch = compile_batch_pivot_update(&coeffs)
            .expect("compile failed")
            .expect("returned None");

        let mut row0 = vec![0i64; 1];
        let targets = vec![row0.as_mut_ptr()];
        let scales = vec![i64::MAX / 2 + 1];

        let updated = unsafe { batch.apply(&targets, &scales) };
        assert_eq!(updated, 0, "should detect mul overflow on row 0");
    }

    #[test]
    fn test_batch_pivot_jit_no_overflow_near_boundary() {
        // (i64::MAX / 2) * 2 = i64::MAX - 1, does NOT overflow
        let coeffs = vec![(0, 2i64)];
        let mut batch = compile_batch_pivot_update(&coeffs)
            .expect("compile failed")
            .expect("returned None");

        let mut row0 = vec![0i64; 1];
        let targets = vec![row0.as_mut_ptr()];
        let scales = vec![i64::MAX / 2];

        let updated = unsafe { batch.apply(&targets, &scales) };
        assert_eq!(updated, 1, "should NOT overflow");
        assert_eq!(row0[0], (i64::MAX / 2) * 2);
    }

    #[test]
    fn test_batch_pivot_jit_overflow_add_detected() {
        // Start at i64::MAX, adding scale=1 * coeff=1 overflows the add
        let coeffs = vec![(0, 1i64)];
        let mut batch = compile_batch_pivot_update(&coeffs)
            .expect("compile failed")
            .expect("returned None");

        let mut row0 = vec![i64::MAX; 1];
        let targets = vec![row0.as_mut_ptr()];
        let scales = vec![1i64];

        let updated = unsafe { batch.apply(&targets, &scales) };
        assert_eq!(updated, 0, "should detect add overflow on row 0");
    }

    #[test]
    fn test_batch_pivot_jit_overflow_partial_rows() {
        // 3 rows; row 1 overflows. Row 0 should be updated, row 2 untouched.
        let coeffs = vec![(0, 1i64)];
        let mut batch = compile_batch_pivot_update(&coeffs)
            .expect("compile failed")
            .expect("returned None");

        let mut row0 = vec![0i64; 1];
        let mut row1 = vec![i64::MAX; 1];
        let mut row2 = vec![42i64; 1];

        let targets = vec![row0.as_mut_ptr(), row1.as_mut_ptr(), row2.as_mut_ptr()];
        let scales = vec![5i64, 1i64, 10i64];

        let updated = unsafe { batch.apply(&targets, &scales) };
        assert_eq!(updated, 1, "row 1 should overflow, so 1 row updated");
        assert_eq!(row0[0], 5); // row 0 was updated
        assert_eq!(row2[0], 42); // row 2 was NOT touched
    }

    #[test]
    fn test_batch_pivot_jit_overflow_neg_one_min() {
        // For coeff=-1, the code does SUBS(target, target, scale).
        // target[0] = 0 - i64::MIN = i64::MIN's negation overflows because
        // 0 - (-2^63) = 2^63 > i64::MAX = 2^63-1.
        let coeffs = vec![(0, -1i64)];
        let mut batch = compile_batch_pivot_update(&coeffs)
            .expect("compile failed")
            .expect("returned None");

        let mut row0 = vec![0i64; 1];
        let targets = vec![row0.as_mut_ptr()];
        let scales = vec![i64::MIN];

        let updated = unsafe { batch.apply(&targets, &scales) };
        assert_eq!(updated, 0, "negating i64::MIN via SUB should overflow");
    }

    #[test]
    fn test_batch_pivot_jit_overflow_general_coeff() {
        // General coefficient path: scale * coeff overflows
        let coeffs = vec![(0, i64::MAX)];
        let mut batch = compile_batch_pivot_update(&coeffs)
            .expect("compile failed")
            .expect("returned None");

        let mut row0 = vec![0i64; 1];
        let mut row1 = vec![0i64; 1];

        let targets = vec![row0.as_mut_ptr(), row1.as_mut_ptr()];
        let scales = vec![1i64, 2i64];

        let updated = unsafe { batch.apply(&targets, &scales) };
        // Row 0: 0 + 1 * MAX = MAX (no overflow)
        // Row 1: 0 + 2 * MAX = overflow in multiply
        assert_eq!(updated, 1);
        assert_eq!(row0[0], i64::MAX);
    }

    #[test]
    fn test_batch_pivot_jit_overflow_sub_underflow() {
        // SUBS overflow: i64::MIN - 1 underflows
        let coeffs = vec![(0, 1i64)];
        let mut batch = compile_batch_pivot_update(&coeffs)
            .expect("compile failed")
            .expect("returned None");

        let mut row0 = vec![i64::MIN; 1];
        let targets = vec![row0.as_mut_ptr()];
        let scales = vec![-1i64]; // -1 * 1 = -1, then MIN + (-1) underflows

        let updated = unsafe { batch.apply(&targets, &scales) };
        assert_eq!(updated, 0, "i64::MIN + (-1) should underflow");
    }

    #[test]
    fn test_batch_pivot_jit_matches_rust_overflow_boundary() {
        // Verify JIT overflow detection matches Rust checked arithmetic
        // across several boundary cases.
        let boundary_cases: Vec<(i64, i64, i64)> = vec![
            // (initial, scale, coeff)
            (0, i64::MAX / 2, 2),     // product = MAX - 1, no overflow
            (0, i64::MAX / 2 + 1, 2), // product overflows
            (i64::MAX, 1, 1),         // add overflows
            (0, 1, i64::MAX),         // product = MAX, no overflow
            (0, 2, i64::MAX),         // product overflows
            (i64::MAX, -1, -1),       // SUB: MAX - (-1) = MAX + 1 overflows
            (i64::MIN, 1, -1),        // SUB: MIN - 1 underflows
            (0, 100, 100),            // 10000, no overflow
            (i64::MAX - 100, 100, 1), // MAX-100 + 100 = MAX, no overflow
            (i64::MAX - 99, 100, 1),  // MAX-99 + 100 overflows
        ];

        for (initial, scale, coeff) in boundary_cases {
            let coeffs = vec![(0, coeff)];

            // Rust fallback
            let mut rust_row = vec![initial];
            let rust_result = batch_pivot_update_i64(&coeffs, &mut [&mut rust_row], &[scale]);

            // JIT
            let mut batch = compile_batch_pivot_update(&coeffs)
                .expect("compile failed")
                .expect("returned None");
            let mut jit_row = vec![initial];
            let targets = vec![jit_row.as_mut_ptr()];
            let scales = vec![scale];
            let jit_result = unsafe { batch.apply(&targets, &scales) };

            assert_eq!(
                jit_result, rust_result,
                "JIT vs Rust mismatch: initial={initial}, scale={scale}, coeff={coeff}: jit={jit_result}, rust={rust_result}"
            );

            if rust_result == 1 {
                // Both succeeded -- values should match
                assert_eq!(
                    jit_row[0], rust_row[0],
                    "Value mismatch: initial={initial}, scale={scale}, coeff={coeff}"
                );
            }
        }
    }

    fn non_zero_coeff() -> impl Strategy<Value = i64> {
        (-1000i64..=1000).prop_filter("coefficients must be non-zero", |coeff| *coeff != 0)
    }

    fn sparse_coefficients(max_len: usize) -> impl Strategy<Value = Vec<(u32, i64)>> {
        btree_set(0u32..101, 1..=max_len).prop_flat_map(|vars| {
            let vars: Vec<u32> = vars.into_iter().collect();
            let len = vars.len();
            prop_vec(non_zero_coeff(), len..=len)
                .prop_map(move |coeffs| vars.iter().copied().zip(coeffs).collect::<Vec<_>>())
        })
    }

    fn apply_reference_wrapping(coefficients: &[(u32, i64)], target: &mut [i64], scale: i64) {
        for &(var_idx, coeff) in coefficients {
            let vi = var_idx as usize;
            target[vi] = target[vi].wrapping_add(scale.wrapping_mul(coeff));
        }
    }

    fn batch_case() -> impl Strategy<Value = (Vec<(u32, i64)>, Vec<Vec<i64>>, Vec<i64>)> {
        sparse_coefficients(20).prop_flat_map(|coefficients| {
            (1usize..=5).prop_flat_map(move |num_rows| {
                (
                    Just(coefficients.clone()),
                    prop_vec(prop_vec(-1000i64..=1000, 101), num_rows..=num_rows),
                    prop_vec(-1000i64..=1000, num_rows..=num_rows),
                )
            })
        })
    }

    proptest! {
        #[test]
        fn proptest_compile_pivot_row_matches_reference(
            coefficients in sparse_coefficients(20),
            scale in -1000i64..=1000,
            initial_target in prop_vec(any::<i64>(), 101),
        ) {
            let mut jit_target = initial_target.clone();
            let mut reference_target = initial_target;

            let mut compiled = compile_pivot_row(&coefficients)
                .expect("compile_pivot_row failed")
                .expect("compile_pivot_row returned None");

            unsafe {
                compiled.apply(jit_target.as_mut_ptr(), scale);
            }
            apply_reference_wrapping(&coefficients, &mut reference_target, scale);

            prop_assert_eq!(
                jit_target,
                reference_target,
                "JIT vs reference mismatch: coeffs={:?}, scale={}",
                coefficients,
                scale,
            );
        }

        #[test]
        fn proptest_batch_pivot_matches_reference(case in batch_case()) {
            let (coefficients, mut jit_rows, scales) = case;
            let mut reference_rows = jit_rows.clone();

            let mut batch = compile_batch_pivot_update(&coefficients)
                .expect("compile_batch_pivot_update failed")
                .expect("compile_batch_pivot_update returned None");

            let targets: Vec<*mut i64> = jit_rows.iter_mut().map(Vec::as_mut_ptr).collect();
            let jit_updated = unsafe { batch.apply(&targets, &scales) };

            let mut reference_slices: Vec<&mut [i64]> = reference_rows
                .iter_mut()
                .map(Vec::as_mut_slice)
                .collect();
            let reference_updated =
                batch_pivot_update_i64(&coefficients, &mut reference_slices, &scales);

            prop_assert_eq!(
                jit_updated,
                reference_updated,
                "updated row count mismatch: coeffs={:?}, scales={:?}",
                coefficients,
                scales,
            );
            prop_assert_eq!(
                jit_rows,
                reference_rows,
                "JIT vs reference batch mismatch: coeffs={:?}, scales={:?}",
                coefficients,
                scales,
            );
        }
    }
}

// --- Sparse substitute backend integration tests (#8380) ---
