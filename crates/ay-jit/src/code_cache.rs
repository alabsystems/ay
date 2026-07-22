// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Code cache management and eviction for JIT-compiled solvers (#8394).
//!
//! Tracks total executable memory allocated across all active JIT compilations
//! (conflict processors and solver-program artifacts) and enforces a global
//! memory budget. When the budget is exceeded, the cache manager invalidates
//! the least-recently-used slots in its bookkeeping and returns those
//! invalidations to the solver so the owning compiled values can be dropped.
//!
//! ## Design
//!
//! The manager tracks a set of named slots for active native-code surfaces.
//! Each slot has a size (mmap'd bytes) and a last-used counter. When a new
//! compilation would push total usage over the budget, the manager invalidates
//! the least-recently-used slots until the new allocation fits.
//!
//! The manager does NOT own the compiled objects -- it tracks their sizes and
//! returns explicit reclamation records. The solver owns the objects and must
//! drop the matching compiled values after `admit_allocation`, `invalidate`, or
//! `set_budget` reports a reclaimed slot. This stays backend-agnostic and works
//! for external code generation-backed objects because the only contract is allocated
//! executable bytes plus a stable slot key.

/// Default code cache budget: 32 MB.
///
/// This covers active JIT allocations:
/// - Conflict processor: small (~16 KB)
/// - Solver-program native artifacts: can be large for big formulas
///
/// The budget prevents unbounded accumulation during long incremental solving.
pub const DEFAULT_CODE_CACHE_BUDGET: usize = 32 * 1024 * 1024;

/// Configures size-limit accounting for the code cache.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct CodeCacheConfig {
    /// Maximum executable bytes that may remain active after admission.
    pub max_active_bytes: usize,
}

impl CodeCacheConfig {
    /// Create a config with an explicit active-byte limit.
    pub const fn new(max_active_bytes: usize) -> Self {
        Self { max_active_bytes }
    }
}

impl Default for CodeCacheConfig {
    fn default() -> Self {
        Self::new(DEFAULT_CODE_CACHE_BUDGET)
    }
}

/// Identifies a JIT memory allocation slot.
///
/// Each slot corresponds to an `Option<CompiledX>` field on the solver.
/// The order defines LRU eviction priority (lower = evicted first when
/// tied on access count).
#[repr(u8)]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum CacheSlot {
    /// JIT-compiled conflict analysis processor.
    ConflictProcessor,
    /// Larger solver-program artifact.
    SolverProgram,
}

impl CacheSlot {
    const COUNT: usize = 2;

    /// All slot variants in a fixed order.
    const ALL: [Self; Self::COUNT] = [Self::ConflictProcessor, Self::SolverProgram];

    const fn index(self) -> usize {
        self as usize
    }

    /// Stable tie-breaker when two slots have the same LRU counter.
    fn lru_tie_breaker(self) -> u8 {
        match self {
            Self::ConflictProcessor => 0, // small and cheap to recompile
            Self::SolverProgram => 1,     // larger guarded artifact
        }
    }
}

/// Per-slot tracking state.
#[derive(Debug, Clone, Copy, Default)]
struct SlotState {
    /// Current allocation size in bytes (0 if slot is empty).
    size_bytes: usize,
    /// Monotonic counter value at last access. Used for LRU eviction.
    last_used: u64,
}

/// Tracks JIT code memory usage and provides bounded admission.
///
/// The manager is a pure bookkeeping struct. It does not own any compiled
/// objects. The solver calls `register_allocation` when a new JIT object
/// is created and `invalidate` when one is dropped. The manager maintains
/// totals, lookup stats, and the LRU order used for budget-driven eviction.
pub struct CodeCacheManager {
    /// Per-slot allocation state.
    slots: [SlotState; CacheSlot::COUNT],
    /// Maximum total code cache size in bytes.
    budget: usize,
    /// Monotonic counter incremented on every access/registration.
    counter: u64,
    /// Cumulative statistics.
    stats: CodeCacheStats,
}

/// Reason a slot was invalidated and its bytes can be reclaimed by the owner.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CodeCacheInvalidationReason {
    /// Explicit caller-driven invalidation.
    Explicit,
    /// Automatic LRU eviction to satisfy the active-byte budget.
    Evicted,
    /// The slot was replaced by a newly admitted allocation for the same slot.
    Replaced,
}

/// Reclamation record returned to the solver after a slot is invalidated.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct CodeCacheInvalidation {
    /// Slot whose compiled object should be dropped by the owner.
    pub slot: CacheSlot,
    /// Executable bytes reclaimed from the cache accounting.
    pub bytes: usize,
    /// Why the slot was invalidated.
    pub reason: CodeCacheInvalidationReason,
}

/// Successful bounded admission result.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CodeCacheAdmission {
    /// Slots invalidated before the new allocation was admitted.
    pub invalidated: Vec<CodeCacheInvalidation>,
    /// Active bytes after admission.
    pub active_bytes: usize,
    /// Peak active bytes observed after admission.
    pub peak_bytes: usize,
}

/// Admission failure for an allocation that cannot fit even in an empty cache.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct CodeCacheAdmissionError {
    /// Slot requested for the allocation.
    pub slot: CacheSlot,
    /// Requested executable bytes.
    pub requested_bytes: usize,
    /// Configured active-byte budget.
    pub budget: usize,
    /// Active bytes left unchanged after the rejection.
    pub active_bytes: usize,
}

/// Cumulative statistics snapshot for the code cache.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct CodeCacheStats {
    /// Bytes currently allocated across all active slots.
    pub active_bytes: usize,
    /// Peak active bytes observed.
    pub peak_bytes: usize,
    /// Number of evictions performed.
    pub evictions: u64,
    /// Total bytes evicted.
    pub bytes_evicted: u64,
    /// Cache lookup hits.
    pub hits: u64,
    /// Cache lookup misses.
    pub misses: u64,
    /// Number of allocation registrations.
    pub registrations: u64,
    /// Number of same-slot replacements.
    pub replacements: u64,
    /// Number of explicit invalidations.
    pub invalidations: u64,
    /// Number of rejected allocations that exceeded the full budget.
    pub rejections: u64,
}

impl CodeCacheManager {
    /// Create a new code cache manager with the given budget.
    pub fn new(budget: usize) -> Self {
        Self::with_config(CodeCacheConfig::new(budget))
    }

    /// Create a new code cache manager with explicit configuration.
    pub fn with_config(config: CodeCacheConfig) -> Self {
        Self {
            slots: [SlotState::default(); CacheSlot::COUNT],
            budget: config.max_active_bytes,
            counter: 0,
            stats: CodeCacheStats::default(),
        }
    }

    /// Create a manager with the default 32 MB budget.
    pub fn with_default_budget() -> Self {
        Self::with_config(CodeCacheConfig::default())
    }

    /// Register a new allocation in a slot without enforcing the budget.
    ///
    /// Updates the slot's size and last-used counter, and recalculates totals.
    /// Prefer `admit_allocation` for bounded cache operation; this method exists
    /// for legacy call sites that already performed their own reclamation.
    pub fn register_allocation(&mut self, slot: CacheSlot, size_bytes: usize) {
        self.register_allocation_unbounded(slot, size_bytes);
    }

    /// Admit a new allocation while keeping active bytes within the budget.
    ///
    /// The returned invalidations identify compiled objects that the owner must
    /// drop to make the bookkeeping match actual executable-memory ownership.
    /// An allocation larger than the full budget is rejected and leaves the
    /// cache unchanged.
    pub fn admit_allocation(
        &mut self,
        slot: CacheSlot,
        size_bytes: usize,
    ) -> Result<CodeCacheAdmission, CodeCacheAdmissionError> {
        if size_bytes > self.budget {
            self.stats.rejections += 1;
            return Err(CodeCacheAdmissionError {
                slot,
                requested_bytes: size_bytes,
                budget: self.budget,
                active_bytes: self.stats.active_bytes,
            });
        }

        let mut invalidated = Vec::new();
        if let Some(replaced) =
            self.invalidate_with_reason(slot, CodeCacheInvalidationReason::Replaced)
        {
            invalidated.push(replaced);
        }

        let excess = self.excess_bytes(size_bytes);
        if excess > 0 {
            invalidated.extend(self.evict_bytes(excess, Some(slot)));
        }

        self.register_allocation_unbounded(slot, size_bytes);
        debug_assert!(self.stats.active_bytes <= self.budget);

        Ok(CodeCacheAdmission {
            invalidated,
            active_bytes: self.stats.active_bytes,
            peak_bytes: self.stats.peak_bytes,
        })
    }

    /// Deregister an allocation (slot is now empty).
    ///
    /// Called when a compiled object is dropped/invalidated.
    pub fn deregister_allocation(&mut self, slot: CacheSlot) {
        let _ = self.invalidate(slot);
    }

    /// Explicitly invalidate a slot and return the reclaimed bytes.
    pub fn invalidate(&mut self, slot: CacheSlot) -> Option<CodeCacheInvalidation> {
        self.invalidate_with_reason(slot, CodeCacheInvalidationReason::Explicit)
    }

    /// Change the active-byte budget and evict LRU slots until it is satisfied.
    ///
    /// The returned invalidations must be reflected by dropping the matching
    /// compiled objects owned by the solver.
    pub fn set_budget(&mut self, budget: usize) -> Vec<CodeCacheInvalidation> {
        self.budget = budget;
        let excess = self.stats.active_bytes.saturating_sub(self.budget);
        if excess == 0 {
            return Vec::new();
        }
        self.evict_bytes(excess, None)
    }

    /// Record a touch (access) on a slot without changing its size.
    ///
    /// Called when a compiled function is used for propagation to update
    /// its LRU position.
    pub fn touch(&mut self, slot: CacheSlot) {
        let idx = slot.index();
        if self.slots[idx].size_bytes > 0 {
            self.bump_counter();
            self.slots[idx].last_used = self.counter;
        }
    }

    /// Record a cache lookup and update LRU state on hit.
    pub fn record_lookup(&mut self, slot: CacheSlot) -> bool {
        if self.contains(slot) {
            self.stats.hits += 1;
            self.touch(slot);
            true
        } else {
            self.stats.misses += 1;
            false
        }
    }

    /// Return whether a slot currently has active executable bytes.
    pub fn contains(&self, slot: CacheSlot) -> bool {
        self.slot_size(slot) > 0
    }

    /// Check if adding `new_size` bytes would exceed the budget.
    ///
    /// Returns the amount of excess bytes if over budget, or 0 if within.
    pub fn excess_bytes(&self, new_size: usize) -> usize {
        let projected = self.stats.active_bytes.saturating_add(new_size);
        projected.saturating_sub(self.budget)
    }

    /// Check if replacing `slot` with `new_size` bytes would exceed the budget.
    pub fn excess_bytes_for(&self, slot: CacheSlot, new_size: usize) -> usize {
        self.projected_active_bytes(slot, new_size)
            .saturating_sub(self.budget)
    }

    /// Project active bytes after replacing `slot` with `new_size`.
    pub fn projected_active_bytes(&self, slot: CacheSlot, new_size: usize) -> usize {
        let old_size = self.slot_size(slot);
        self.stats
            .active_bytes
            .saturating_sub(old_size)
            .saturating_add(new_size)
    }

    /// Get eviction candidates to free at least `needed_bytes` of space.
    ///
    /// Returns slots sorted by LRU order (oldest `last_used` counter first).
    ///
    /// Only returns non-empty slots. This is a planning helper; use
    /// `admit_allocation` or `set_budget` when the manager should update its
    /// own bookkeeping and return explicit invalidation records.
    pub fn eviction_candidates(&self, needed_bytes: usize) -> Vec<CacheSlot> {
        self.eviction_candidates_excluding(needed_bytes, None)
    }

    /// Get LRU eviction candidates needed to fit a replacement allocation.
    pub fn eviction_candidates_for(&self, slot: CacheSlot, new_size: usize) -> Vec<CacheSlot> {
        let needed_bytes = self.excess_bytes_for(slot, new_size);
        self.eviction_candidates_excluding(needed_bytes, Some(slot))
    }

    fn eviction_candidates_excluding(
        &self,
        needed_bytes: usize,
        exclude: Option<CacheSlot>,
    ) -> Vec<CacheSlot> {
        let mut candidates: Vec<(CacheSlot, u64, u8, usize)> = Vec::new();

        for &slot in &CacheSlot::ALL {
            if Some(slot) == exclude {
                continue;
            }

            let idx = slot.index();
            let state = &self.slots[idx];
            if state.size_bytes > 0 {
                candidates.push((
                    slot,
                    state.last_used,
                    slot.lru_tie_breaker(),
                    state.size_bytes,
                ));
            }
        }

        // Sort: least recently used first, then deterministic slot tie-breaker,
        // then largest allocation to satisfy the byte target quickly.
        candidates.sort_unstable_by(|a, b| {
            a.1.cmp(&b.1)
                .then_with(|| a.2.cmp(&b.2))
                .then_with(|| b.3.cmp(&a.3))
        });

        // Collect candidates until we have enough bytes to free.
        let mut freed = 0usize;
        let mut result = Vec::new();
        for (slot, _, _, size) in &candidates {
            if freed >= needed_bytes {
                break;
            }
            result.push(*slot);
            freed += size;
        }

        result
    }

    /// Record that an eviction was performed for a slot.
    ///
    /// This updates eviction statistics. The caller should have already
    /// called `deregister_allocation` for the slot.
    pub fn record_eviction(&mut self, slot: CacheSlot, freed_bytes: usize) {
        let _ = slot;
        self.stats.evictions += 1;
        self.stats.bytes_evicted += freed_bytes as u64;
    }

    /// Total bytes currently allocated across all slots.
    pub fn total_allocated_bytes(&self) -> usize {
        self.stats.active_bytes
    }

    /// Bytes currently allocated across all active slots.
    pub fn active_bytes(&self) -> usize {
        self.stats.active_bytes
    }

    /// Peak total allocation observed since creation.
    pub fn peak_allocated_bytes(&self) -> usize {
        self.stats.peak_bytes
    }

    /// Peak active bytes observed since creation.
    pub fn peak_bytes(&self) -> usize {
        self.stats.peak_bytes
    }

    /// Current code cache budget.
    pub fn budget(&self) -> usize {
        self.budget
    }

    /// Cumulative statistics snapshot.
    pub fn stats(&self) -> CodeCacheStats {
        self.stats
    }

    /// Size of a specific slot in bytes (0 if empty).
    pub fn slot_size(&self, slot: CacheSlot) -> usize {
        self.slots[slot.index()].size_bytes
    }

    fn register_allocation_unbounded(&mut self, slot: CacheSlot, size_bytes: usize) {
        let _ = self.invalidate_with_reason(slot, CodeCacheInvalidationReason::Replaced);

        self.bump_counter();
        self.slots[slot.index()] = SlotState {
            size_bytes,
            last_used: self.counter,
        };

        self.stats.active_bytes = self.stats.active_bytes.saturating_add(size_bytes);
        self.stats.registrations += 1;
        self.stats.peak_bytes = self.stats.peak_bytes.max(self.stats.active_bytes);
    }

    fn invalidate_with_reason(
        &mut self,
        slot: CacheSlot,
        reason: CodeCacheInvalidationReason,
    ) -> Option<CodeCacheInvalidation> {
        let idx = slot.index();
        let size = self.slots[idx].size_bytes;
        if size == 0 {
            self.slots[idx] = SlotState::default();
            return None;
        }

        self.slots[idx] = SlotState::default();
        self.stats.active_bytes = self.stats.active_bytes.saturating_sub(size);

        match reason {
            CodeCacheInvalidationReason::Explicit => {
                self.stats.invalidations += 1;
            }
            CodeCacheInvalidationReason::Evicted => {
                self.stats.evictions += 1;
                self.stats.bytes_evicted += size as u64;
            }
            CodeCacheInvalidationReason::Replaced => {
                self.stats.replacements += 1;
            }
        }

        Some(CodeCacheInvalidation {
            slot,
            bytes: size,
            reason,
        })
    }

    fn evict_bytes(
        &mut self,
        needed_bytes: usize,
        exclude: Option<CacheSlot>,
    ) -> Vec<CodeCacheInvalidation> {
        self.eviction_candidates_excluding(needed_bytes, exclude)
            .into_iter()
            .filter_map(|slot| {
                self.invalidate_with_reason(slot, CodeCacheInvalidationReason::Evicted)
            })
            .collect()
    }

    fn bump_counter(&mut self) {
        self.counter = self.counter.saturating_add(1);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    const CONFLICT: CacheSlot = CacheSlot::ConflictProcessor;
    const PROGRAM: CacheSlot = CacheSlot::SolverProgram;

    #[test]
    fn register_and_total_tracks_replacement() {
        let mut mgr = CodeCacheManager::new(4 * 1024 * 1024);
        assert_eq!(mgr.active_bytes(), 0);

        mgr.register_allocation(PROGRAM, 1_000_000);
        assert_eq!(mgr.active_bytes(), 1_000_000);

        mgr.register_allocation(CONFLICT, 500_000);
        assert_eq!(mgr.active_bytes(), 1_500_000);

        mgr.register_allocation(PROGRAM, 800_000);
        assert_eq!(mgr.active_bytes(), 1_300_000);
        assert_eq!(mgr.stats().replacements, 1);
    }

    #[test]
    fn explicit_invalidate_reclaims_bytes() {
        let mut mgr = CodeCacheManager::new(4 * 1024 * 1024);
        mgr.register_allocation(PROGRAM, 1_000_000);
        mgr.register_allocation(CONFLICT, 500_000);
        assert_eq!(mgr.active_bytes(), 1_500_000);

        let reclaimed = mgr.invalidate(PROGRAM).unwrap();
        assert_eq!(
            reclaimed,
            CodeCacheInvalidation {
                slot: PROGRAM,
                bytes: 1_000_000,
                reason: CodeCacheInvalidationReason::Explicit,
            }
        );
        assert_eq!(mgr.active_bytes(), 500_000);
        assert!(!mgr.contains(PROGRAM));

        assert_eq!(mgr.invalidate(PROGRAM), None);
        assert_eq!(mgr.active_bytes(), 500_000);
        assert_eq!(mgr.stats().invalidations, 1);
    }

    #[test]
    fn excess_bytes_accounts_for_replacement() {
        let mut mgr = CodeCacheManager::new(2_000_000);
        mgr.register_allocation(PROGRAM, 1_500_000);

        assert_eq!(mgr.excess_bytes(400_000), 0);
        assert_eq!(mgr.excess_bytes(600_000), 100_000);
        assert_eq!(mgr.projected_active_bytes(PROGRAM, 1_800_000), 1_800_000);
        assert_eq!(mgr.excess_bytes_for(PROGRAM, 1_800_000), 0);
    }

    #[test]
    fn eviction_candidates_are_lru_not_slot_priority() {
        let mut mgr = CodeCacheManager::new(2_000_000);
        mgr.register_allocation(PROGRAM, 800_000);
        mgr.register_allocation(CONFLICT, 600_000);

        mgr.touch(PROGRAM);

        let candidates = mgr.eviction_candidates(200_000);
        assert_eq!(candidates.len(), 1);
        assert_eq!(candidates[0], CONFLICT);
    }

    #[test]
    fn eviction_candidates_need_multiple_lru_slots() {
        let mut mgr = CodeCacheManager::new(2_000_000);
        mgr.register_allocation(PROGRAM, 800_000);
        mgr.register_allocation(CONFLICT, 300_000);

        mgr.touch(PROGRAM);

        let candidates = mgr.eviction_candidates(1_000_000);
        assert_eq!(candidates[0], CONFLICT);
        assert_eq!(candidates[1], PROGRAM);
        assert_eq!(candidates.len(), 2);
    }

    #[test]
    fn lookup_updates_hit_miss_stats_and_lru() {
        let mut mgr = CodeCacheManager::new(2_000_000);
        mgr.register_allocation(CONFLICT, 500_000);

        assert!(mgr.record_lookup(CONFLICT));
        assert!(!mgr.record_lookup(PROGRAM));

        let stats = mgr.stats();
        assert_eq!(stats.hits, 1);
        assert_eq!(stats.misses, 1);

        let candidates = mgr.eviction_candidates(500_000);
        assert_eq!(candidates[0], CONFLICT);
    }

    #[test]
    fn peak_tracking_survives_reclamation() {
        let mut mgr = CodeCacheManager::new(4 * 1024 * 1024);
        mgr.register_allocation(PROGRAM, 1_000_000);
        mgr.register_allocation(CONFLICT, 500_000);
        assert_eq!(mgr.peak_bytes(), 1_500_000);

        mgr.deregister_allocation(CONFLICT);
        assert_eq!(mgr.peak_bytes(), 1_500_000);
        assert_eq!(mgr.active_bytes(), 1_000_000);
    }

    #[test]
    fn bounded_admission_evicts_lru_and_reports_reclamation() {
        let mut mgr = CodeCacheManager::new(1_000);
        mgr.admit_allocation(CONFLICT, 400).unwrap();

        let admission = mgr.admit_allocation(PROGRAM, 700).unwrap();

        assert_eq!(admission.active_bytes, 700);
        assert_eq!(
            admission.invalidated,
            vec![CodeCacheInvalidation {
                slot: CONFLICT,
                bytes: 400,
                reason: CodeCacheInvalidationReason::Evicted,
            }]
        );
        assert_eq!(mgr.active_bytes(), 700);
        assert!(!mgr.contains(CONFLICT));
        assert!(mgr.contains(PROGRAM));

        let stats = mgr.stats();
        assert_eq!(stats.evictions, 1);
        assert_eq!(stats.bytes_evicted, 400);
        assert_eq!(stats.registrations, 2);
    }

    #[test]
    fn admission_replaces_target_before_budget_accounting() {
        let mut mgr = CodeCacheManager::new(1_000);
        mgr.admit_allocation(PROGRAM, 900).unwrap();

        let admission = mgr.admit_allocation(PROGRAM, 600).unwrap();

        assert_eq!(admission.active_bytes, 600);
        assert_eq!(
            admission.invalidated,
            vec![CodeCacheInvalidation {
                slot: PROGRAM,
                bytes: 900,
                reason: CodeCacheInvalidationReason::Replaced,
            }]
        );
        assert_eq!(mgr.stats().replacements, 1);
        assert_eq!(mgr.stats().evictions, 0);
    }

    #[test]
    fn admission_rejects_single_allocation_larger_than_budget() {
        let mut mgr = CodeCacheManager::new(1_000);
        mgr.admit_allocation(CONFLICT, 400).unwrap();

        let err = mgr.admit_allocation(PROGRAM, 1_200).unwrap_err();

        assert_eq!(
            err,
            CodeCacheAdmissionError {
                slot: PROGRAM,
                requested_bytes: 1_200,
                budget: 1_000,
                active_bytes: 400,
            }
        );
        assert_eq!(mgr.active_bytes(), 400);
        assert!(mgr.contains(CONFLICT));
        assert_eq!(mgr.stats().rejections, 1);
        assert_eq!(mgr.stats().evictions, 0);
    }

    #[test]
    fn set_budget_evicts_lru_slots_to_new_limit() {
        let mut mgr = CodeCacheManager::new(3_000);
        mgr.admit_allocation(PROGRAM, 600).unwrap();
        mgr.admit_allocation(CONFLICT, 700).unwrap();
        mgr.touch(PROGRAM);

        let reclaimed = mgr.set_budget(1_000);

        assert_eq!(
            reclaimed,
            vec![CodeCacheInvalidation {
                slot: CONFLICT,
                bytes: 700,
                reason: CodeCacheInvalidationReason::Evicted,
            }]
        );
        assert_eq!(mgr.budget(), 1_000);
        assert_eq!(mgr.active_bytes(), 600);
        assert!(mgr.contains(PROGRAM));
    }

    #[test]
    fn stats_snapshot_includes_active_peak_evictions_and_hits() {
        let mut mgr = CodeCacheManager::new(4 * 1024 * 1024);
        mgr.admit_allocation(PROGRAM, 1_000_000).unwrap();
        mgr.admit_allocation(CONFLICT, 500_000).unwrap();
        assert!(mgr.record_lookup(PROGRAM));
        let reclaimed = mgr.set_budget(1_000_000);
        assert!(!mgr.record_lookup(CONFLICT));
        assert_eq!(
            reclaimed,
            vec![CodeCacheInvalidation {
                slot: CONFLICT,
                bytes: 500_000,
                reason: CodeCacheInvalidationReason::Evicted,
            }]
        );

        let stats = mgr.stats();
        assert_eq!(stats.active_bytes, 1_000_000);
        assert_eq!(stats.peak_bytes, 1_500_000);
        assert_eq!(stats.registrations, 2);
        assert_eq!(stats.invalidations, 0);
        assert_eq!(stats.evictions, 1);
        assert_eq!(stats.bytes_evicted, 500_000);
        assert_eq!(stats.hits, 1);
        assert_eq!(stats.misses, 1);
    }

    #[test]
    fn cache_stays_within_budget_over_many_cycles() {
        let budget = 4 * 1024 * 1024; // 4MB
        let mut mgr = CodeCacheManager::new(budget);

        for i in 0..100 {
            let program_size = 800_000 + (i % 3) * 100_000;
            let conflict_size = 600_000;

            mgr.admit_allocation(PROGRAM, program_size).unwrap();
            assert!(mgr.active_bytes() <= budget, "cycle {i}");

            if i % 2 == 0 {
                mgr.admit_allocation(CONFLICT, conflict_size).unwrap();
                assert!(mgr.active_bytes() <= budget, "conflict cycle {i}");
            }

            if i % 3 == 0 {
                let _ = mgr.invalidate(CONFLICT);
            }
        }

        assert!(mgr.active_bytes() <= budget);
    }
}
