// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Per-thread memory groups: attribute live heap bytes to one solver lane.
//!
//! The process-wide signals ([`crate::process_memory_exceeded`], the hard
//! allocation ceiling) cannot tell WHICH of several concurrent solver lanes is
//! growing, so a single runaway lane ends every lane with it. A memory group
//! is entered on the lane's own thread; while it is current, every allocation
//! and deallocation that goes through [`crate::CountingAllocator`] on that
//! thread is also charged to (credited from) the group. Crossing the group's
//! SOFT limit sets its cancel flag once (the lane's own cancellation token,
//! read by the lane's cooperative checkpoints); crossing its HARD limit makes
//! [`current_memory_group_over_hard_limit`] true, for code without a
//! checkpoint to unwind on. Other lanes are unaffected; the process-wide
//! signals stay the last resort.
//!
//! Every group is also listed in a process-wide registry (weakly: a group
//! leaves it when its last owner drops it), so the memory governor
//! (`memory_governor.rs`) can see which lane holds the heap and SHED it — set
//! its cancel flag and force its hard-limit unwind — when the PROCESS nears
//! its budget although no single lane crossed its own share (measured on
//! LRA-Lin: four lanes growing together, each under half the budget, took the
//! process past it).
//!
//! Attribution is by thread: a block allocated here and freed on another
//! thread is credited to the freeing thread's group (or to none), so the
//! allocating group keeps that charge (its count runs high) and the freeing
//! group runs low. Lanes free what they build (a lane hands the portfolio
//! only its result), so the drift is small next to the shares; the limits
//! are set as fractions of the process limit, not as tight budgets.

use std::cell::Cell;
use std::sync::atomic::{AtomicBool, AtomicIsize, AtomicUsize, Ordering};
use std::sync::{Arc, Mutex, PoisonError, Weak};

/// Groups currently entered on any thread. Zero keeps the allocator hook to a
/// single relaxed load for every program that never enters a group.
static ENTERED_GROUPS: AtomicUsize = AtomicUsize::new(0);

/// Set once any group crossed its hard limit; lets hot checkers skip the
/// thread-local lookup until then.
static ANY_GROUP_OVER_HARD: AtomicBool = AtomicBool::new(false);

#[derive(Clone, Copy, Debug)]
struct Current {
    group: *const MemoryGroup,
    scope: *const u8,
}

impl Current {
    const EMPTY: Self = Self {
        group: std::ptr::null(),
        scope: std::ptr::null(),
    };
}

thread_local! {
    // `const`-initialised and drop-free: reading it inside the global
    // allocator neither allocates nor registers a thread-local destructor.
    static CURRENT: Cell<Current> = const { Cell::new(Current::EMPTY) };
}

/// Every live group, for the governor's census. Weak: a group leaves when its
/// last owner (the lane's scope) drops it; dead entries are pruned on insert.
/// Never touched from the allocator hook.
static REGISTRY: Mutex<Vec<Weak<MemoryGroup>>> = Mutex::new(Vec::new());

/// One lane's live-byte account and limits.
#[derive(Debug)]
pub struct MemoryGroup {
    live: AtomicIsize,
    peak: AtomicIsize,
    soft_limit: isize,
    hard_limit: isize,
    cancel: Arc<AtomicBool>,
    soft_tripped: Arc<AtomicBool>,
    /// Live bytes above which a charge takes the cold path ([`Self::trip`]):
    /// the soft limit, lowered to the throttle line once the lane is shed.
    trip_at: AtomicIsize,
    /// Live bytes above which every further charge is throttled
    /// ([`throttle_runaway_lane`]): the hard limit, lowered to just above the
    /// lane's heap when it is shed.
    throttle_above: AtomicIsize,
    /// Set once by the governor ([`shed_fattest_memory_group`]): the lane is
    /// cancelled and reads as over its hard limit from then on.
    shed: Arc<AtomicBool>,
    label: &'static str,
}

/// Heap a shed lane may still grow by before its allocations are throttled:
/// room to unwind and publish `Unknown`, far below what a runaway adds.
pub(crate) const SHED_GROWTH_SLACK: usize = 64 * 1024 * 1024;

/// What one throttled allocation costs its thread.
const THROTTLE_PAUSE: std::time::Duration = std::time::Duration::from_millis(1);

/// Pause the calling thread: its lane was cancelled for memory (shed, or past
/// its hard limit) and is still growing, so it is running code that polls no
/// checkpoint — measured: expression walks that never reach
/// `maybe_grow_expr_stack` pushing gigabytes after their lane was shed. It
/// cannot be unwound from inside the allocator, and refusing the allocation
/// would abort the process; pausing each further allocation bounds its growth
/// to a trickle while it runs to its next checkpoint or its end. The lane only
/// ever answers `Unknown`, so no verdict changes. Allocation-free
/// (`nanosleep`).
#[cold]
#[inline(never)]
fn throttle_runaway_lane() {
    std::thread::sleep(THROTTLE_PAUSE);
}

/// One registered group as the governor saw it.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct MemoryGroupUsage {
    /// The lane's name ([`MemoryGroup::named`]).
    pub label: &'static str,
    /// Net live bytes charged to the group.
    pub live_bytes: isize,
}

/// A retained, read-only observation of one group's sticky memory refusal.
///
/// This observes the original group even after another group becomes current
/// or its owner scope ends. Cloning and polling allocate nothing, and no
/// cancellation flag, reset operation or mutable access is exposed.
#[derive(Clone, Debug)]
pub struct MemoryGroupObservation {
    soft_tripped: Arc<AtomicBool>,
    shed: Arc<AtomicBool>,
}

impl MemoryGroupObservation {
    /// Whether the original group crossed its soft limit or was shed.
    ///
    /// Resetting the group's cancellation flag cannot clear this observation.
    #[inline]
    pub fn is_tripped(&self) -> bool {
        self.soft_tripped.load(Ordering::Relaxed) || self.shed.load(Ordering::Relaxed)
    }
}

impl MemoryGroup {
    /// A group that sets `cancel` once its live bytes exceed `soft_limit` and
    /// reports over-hard beyond `hard_limit` (clamped to at least `soft_limit`).
    ///
    /// Two shared latch allocations let read-only observations outlive this
    /// group without retaining registry ownership. Capture, polling and
    /// allocator hooks remain allocation-free; TLS attribution is unchanged.
    pub fn new(soft_limit: usize, hard_limit: usize, cancel: Arc<AtomicBool>) -> Arc<Self> {
        Self::named("lane", soft_limit, hard_limit, cancel)
    }

    /// [`MemoryGroup::new`] with the lane name the governor reports.
    pub fn named(
        label: &'static str,
        soft_limit: usize,
        hard_limit: usize,
        cancel: Arc<AtomicBool>,
    ) -> Arc<Self> {
        let soft = isize::try_from(soft_limit).unwrap_or(isize::MAX);
        let hard = isize::try_from(hard_limit).unwrap_or(isize::MAX).max(soft);
        let group = Arc::new(Self {
            live: AtomicIsize::new(0),
            peak: AtomicIsize::new(0),
            soft_limit: soft,
            hard_limit: hard,
            cancel,
            soft_tripped: Arc::new(AtomicBool::new(false)),
            trip_at: AtomicIsize::new(soft),
            throttle_above: AtomicIsize::new(hard),
            shed: Arc::new(AtomicBool::new(false)),
            label,
        });
        let mut registry = REGISTRY.lock().unwrap_or_else(PoisonError::into_inner);
        registry.retain(|entry| entry.strong_count() > 0);
        registry.push(Arc::downgrade(&group));
        drop(registry);
        group
    }

    /// The lane name given at construction.
    pub fn label(&self) -> &'static str {
        self.label
    }

    /// Whether the governor shed this lane.
    pub fn was_shed(&self) -> bool {
        self.shed.load(Ordering::Relaxed)
    }

    /// Shed the lane: cancel it and make it read as over its hard limit, so
    /// code without a cancellation checkpoint unwinds at its next
    /// hard-limit check; growth past [`SHED_GROWTH_SLACK`] above its heap now
    /// is throttled. Returns whether this call shed it.
    pub fn shed(&self) -> bool {
        if self.shed.swap(true, Ordering::Relaxed) {
            return false;
        }
        self.note_peak();
        let slack = isize::try_from(SHED_GROWTH_SLACK).unwrap_or(isize::MAX);
        let line = self.live_bytes().max(0).saturating_add(slack);
        self.throttle_above.fetch_min(line, Ordering::Relaxed);
        self.trip_at.fetch_min(line, Ordering::Relaxed);
        // Release: a reader that sees the flag raised and then reads
        // `was_shed` (acquiring) reads it set, and so names the stop memout.
        self.cancel.store(true, Ordering::Release);
        ANY_GROUP_OVER_HARD.store(true, Ordering::Relaxed);
        true
    }

    /// Net bytes charged to this group so far (may be negative, see module doc).
    pub fn live_bytes(&self) -> isize {
        self.live.load(Ordering::Relaxed)
    }

    /// Highest net live bytes observed.
    pub fn peak_bytes(&self) -> isize {
        self.peak.load(Ordering::Relaxed)
    }

    /// Whether the soft limit was ever crossed (the cancel flag was set).
    pub fn soft_tripped(&self) -> bool {
        self.soft_tripped.load(Ordering::Relaxed)
    }

    /// Whether the group is above its hard limit right now, or was shed.
    pub fn over_hard_limit(&self) -> bool {
        self.live.load(Ordering::Relaxed) > self.hard_limit || self.was_shed()
    }

    #[inline]
    fn charge(&self, bytes: usize) {
        let bytes = isize::try_from(bytes).unwrap_or(isize::MAX);
        let live = self
            .live
            .fetch_add(bytes, Ordering::Relaxed)
            .saturating_add(bytes);
        if live > self.trip_at.load(Ordering::Relaxed) {
            self.trip(live);
        }
    }

    #[cold]
    #[inline(never)]
    fn trip(&self, live: isize) {
        self.peak.fetch_max(live, Ordering::Relaxed);
        if live > self.soft_limit && !self.soft_tripped.swap(true, Ordering::Relaxed) {
            // Release, as in `shed`: the trip is read with the flag.
            self.cancel.store(true, Ordering::Release);
        }
        if live > self.hard_limit {
            ANY_GROUP_OVER_HARD.store(true, Ordering::Relaxed);
        }
        if live > self.throttle_above.load(Ordering::Relaxed) {
            throttle_runaway_lane();
        }
    }

    #[inline]
    fn credit(&self, bytes: usize) {
        let bytes = isize::try_from(bytes).unwrap_or(isize::MAX);
        self.live.fetch_sub(bytes, Ordering::Relaxed);
    }

    /// Record the current live bytes as a peak candidate (cheap; call at the
    /// end of a lane for reporting).
    pub fn note_peak(&self) {
        let live = self.live.load(Ordering::Relaxed);
        self.peak.fetch_max(live, Ordering::Relaxed);
    }
}

/// Makes a group current on this thread until dropped. Not `Send`: it must be
/// dropped on the thread that entered it. Scopes nest LIFO; dropping one out
/// of order is safe but stops attribution for the scopes still open.
#[derive(Debug)]
pub struct MemoryGroupScope {
    group: Arc<MemoryGroup>,
    // A non-ZST allocation identifies this scope, not its possibly shared
    // group. Moving the guard preserves the address; no counter can wrap.
    identity: Box<u8>,
    previous: Current,
}

/// Enter `group` on the calling thread.
pub fn enter_memory_group(group: Arc<MemoryGroup>) -> MemoryGroupScope {
    // Allocate while the old scope is still current: allocator hooks may
    // attribute this allocation, but never observe a partially entered scope.
    let identity = Box::new(0);
    let entered = Current {
        group: Arc::as_ptr(&group),
        scope: identity.as_ref(),
    };
    let previous = CURRENT.with(|current| current.replace(entered));
    ENTERED_GROUPS.fetch_add(1, Ordering::Relaxed);
    MemoryGroupScope {
        group,
        identity,
        previous,
    }
}

impl MemoryGroupScope {
    /// The entered group.
    pub fn group(&self) -> &Arc<MemoryGroup> {
        &self.group
    }
}

impl Drop for MemoryGroupScope {
    fn drop(&mut self) {
        let mine = self.identity.as_ref();
        CURRENT.with(|current| {
            if std::ptr::eq(current.get().scope, mine) {
                // LIFO drop: the previous scope is the enclosing one, still
                // alive. An out-of-order drop clears CURRENT; any later entry
                // has a different marker, even when it enters the SAME group,
                // so it cannot authorize restoring this stale predecessor.
                current.set(self.previous);
            } else {
                // Out-of-order drop (an inner scope is still current, and its
                // `previous` may be the group this scope is about to release).
                // Never leave a path back to a released group: drop attribution
                // for the rest of this thread's scopes instead. The inner
                // scope's own drop then finds CURRENT != itself and keeps null.
                current.set(Current::EMPTY);
            }
        });
        ENTERED_GROUPS.fetch_sub(1, Ordering::Relaxed);
    }
}

/// Run `f` on the calling thread's current group, if any.
#[inline]
fn with_current(f: impl FnOnce(&MemoryGroup)) {
    let _ = try_with_current(f);
}

fn try_with_current(f: impl FnOnce(&MemoryGroup)) -> Result<(), std::thread::AccessError> {
    CURRENT.try_with(|current| {
        let group = current.get().group;
        if !group.is_null() {
            // SAFETY: a non-null CURRENT is always the pointer of a live
            // scope's `Arc` on this thread. Each non-Send scope owns a distinct
            // non-ZST marker; CURRENT can match only that live scope, never a
            // later entry sharing its group. An out-of-order drop clears both
            // pointers, preventing restoration through any invalidated scope.
            // Drop restores/clears CURRENT before either owner is destroyed;
            // moving preserves both allocations and leaking keeps both alive.
            f(unsafe { &*group });
        }
    })
}

/// Allocator hook: charge `bytes` to the calling thread's group.
#[inline]
pub(crate) fn charge_current(bytes: usize) {
    if ENTERED_GROUPS.load(Ordering::Relaxed) != 0 {
        with_current(|group| group.charge(bytes));
    }
}

/// Allocator hook: credit `bytes` to the calling thread's group.
#[inline]
pub(crate) fn credit_current(bytes: usize) {
    if ENTERED_GROUPS.load(Ordering::Relaxed) != 0 {
        with_current(|group| group.credit(bytes));
    }
}

/// Whether the calling thread's group is above its hard limit. One relaxed
/// load until some group has ever crossed a hard limit.
#[inline]
pub fn current_memory_group_over_hard_limit() -> bool {
    if !ANY_GROUP_OVER_HARD.load(Ordering::Relaxed) {
        return false;
    }
    let mut over = false;
    with_current(|group| over = group.over_hard_limit());
    over
}

/// Whether the calling thread's group has crossed its SOFT limit or was shed
/// by the governor (its lane was cancelled for memory). One relaxed load until
/// some group is entered. For solver loops that poll a bare stop condition rather than the lane's
/// cancellation token — ay-dpll polls it next to [`crate::process_memory_exceeded`]
/// so an in-flight executor check on an over-share lane answers Unknown
/// instead of allocating on until its own timeout. Soundness-neutral.
#[inline]
pub fn current_memory_group_soft_tripped() -> bool {
    if ENTERED_GROUPS.load(Ordering::Relaxed) == 0 {
        return false;
    }
    let mut tripped = false;
    with_current(|group| tripped = group.soft_tripped() || group.was_shed());
    tripped
}

/// The live registered groups that were not shed, fattest first.
#[must_use]
pub fn memory_group_census() -> Vec<MemoryGroupUsage> {
    let mut census: Vec<MemoryGroupUsage> = live_groups()
        .iter()
        .filter(|group| !group.was_shed())
        .map(|group| MemoryGroupUsage {
            label: group.label,
            live_bytes: group.live_bytes(),
        })
        .collect();
    census.sort_by(|a, b| b.live_bytes.cmp(&a.live_bytes));
    census
}

/// Shed the registered group holding the most live bytes, when it holds at
/// least `min_live_bytes` and at least `keep` other unshed groups stay
/// running. Returns the shed group's usage.
///
/// The survivors keep running: shedding the lane that holds the heap is what
/// lets the others still answer instead of every lane dying with the process.
pub fn shed_fattest_memory_group(min_live_bytes: usize, keep: usize) -> Option<MemoryGroupUsage> {
    let groups: Vec<Arc<MemoryGroup>> = live_groups()
        .into_iter()
        .filter(|group| !group.was_shed())
        .collect();
    if groups.len() <= keep {
        return None;
    }
    let fattest = groups.iter().max_by_key(|group| group.live_bytes())?;
    let live = fattest.live_bytes();
    if usize::try_from(live).map_or(true, |live| live < min_live_bytes) {
        return None;
    }
    fattest.shed().then(|| MemoryGroupUsage {
        label: fattest.label,
        live_bytes: live,
    })
}

/// Strong handles to the registered groups still alive.
fn live_groups() -> Vec<Arc<MemoryGroup>> {
    REGISTRY
        .lock()
        .unwrap_or_else(PoisonError::into_inner)
        .iter()
        .filter_map(Weak::upgrade)
        .collect()
}

/// Retain the current group's sticky memory-refusal observation, if a group is
/// entered on this thread. Capture only clones two existing shared latches: it
/// neither allocates nor changes thread-local registration or attribution.
pub fn current_memory_group_observation() -> Option<MemoryGroupObservation> {
    let mut observation = None;
    with_current(|group| {
        observation = Some(MemoryGroupObservation {
            soft_tripped: Arc::clone(&group.soft_tripped),
            shed: Arc::clone(&group.shed),
        });
    });
    observation
}

/// Fallible original-owner capture; unavailable TLS is NOT an empty group.
/// This retains only refusal latches, never group membership or byte charging.
pub fn try_current_memory_group_observation(
) -> Result<Option<MemoryGroupObservation>, std::thread::AccessError> {
    let mut observation = None;
    try_with_current(|group| {
        observation = Some(MemoryGroupObservation {
            soft_tripped: Arc::clone(&group.soft_tripped),
            shed: Arc::clone(&group.shed),
        });
    })?;
    Ok(observation)
}

/// Test hook: charge `bytes` to the current group without allocating.
#[doc(hidden)]
pub fn charge_current_for_testing(bytes: usize) {
    with_current(|group| group.charge(bytes));
}

#[cfg(test)]
#[path = "memory_group_tests.rs"]
mod tests;
