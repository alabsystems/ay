// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The live-heap-byte counter behind [`crate::CountingAllocator`].
//!
//! Every allocation and free through the counting allocator lands here. The
//! counter feeds the hard allocation ceiling (checked synchronously as growth
//! is published) and the live-bytes memory signal.
//!
//! It is a striped counter. Small changes go to one of [`STRIPES`] pending
//! balances, picked by the stack window the calling thread is running in, and
//! reach the published total [`LIVE_BYTES`] only when that balance reaches
//! [`LIVE_BYTES_BATCH`] in either direction, so a single change of two
//! batches or more is always published at once.
//!
//! The counter used to take one atomic read-modify-write of the published
//! total per allocation and per free, from every thread, on one cache line.
//! With the CHC portfolio's engines running in parallel that line was the
//! largest single cost in the process (28-39% of active samples at the
//! instruction after the `ldadd`,
//! the development design notes at `9598c4206`); on
//! `faulty__barthe!_000` it held the portfolio's 2 s BMC probe to depth 6-7,
//! where the striped counter lets it reach depth 11.
//!
//! The stripe is chosen from a stack address rather than a thread-local: every
//! thread's stack is its own address range, so the window a local lives in
//! names the running thread for free, while a thread-local access is a
//! `_tlv_get_addr` call on macOS: a thread-local balance cost an
//! allocation-heavy single-threaded solve 11% of its time. A single-threaded
//! caller here pays what it paid before, one uncontended atomic add per
//! allocation, and threads running in different windows write different cache
//! lines.
//!
//! Accuracy: the published total differs from the true live bytes by the
//! pending stripe balances, each under one batch plus the changes in flight on
//! it, so by at most `STRIPES * LIVE_BYTES_BATCH` (16 MiB) and in practice by
//! one batch per active stack window. The balances belong to the process, not
//! to a thread, so nothing is lost when a thread exits.
//!
//! The published total is signed, and only a reading is clamped at zero. A
//! free is often published before the allocation it pairs with (that growth
//! still pending on the allocating thread's stripe), so the total can dip
//! below zero for a while, and it must keep the debt to stay exact. Clamping
//! the total itself, as the unstriped counter did, cannot be done in one
//! atomic step: between a `fetch_sub` and its repair the total read as about
//! 2^64, so a concurrent growth tripped the hard ceiling with a heap of a few
//! MiB, and each clamp over-counted the heap from then on by what it dropped.
//! Each stripe balance is therefore published with one signed `fetch_add`.

use std::sync::atomic::{AtomicIsize, Ordering};

use crate::memory_group;
use crate::{breach_hard_memory_ceiling, ceiling_settlement, hard_memory_ceiling_breached};

/// Live bytes published by the stripes. 0 when no counting allocator is
/// installed.
///
/// This is the **instantaneous** heap signal: a bulk allocation is published
/// the moment it happens — before the OS's RSS (`getrusage`, which we read via
/// [`crate::current_rss_bytes`]) catches up, and before an OOM-killer can
/// fire. No syscalls, no polling.
///
/// Signed: it is negative while more release than growth has been published
/// (see the module docs), and every reader goes through [`readable`].
///
/// Its own cache line, so the read-mostly statics that every allocation also
/// reads (the hard ceiling, the mimalloc arena latch) never share a line with
/// a static that is written.
static LIVE_BYTES: OwnCacheLine<AtomicIsize> = OwnCacheLine(AtomicIsize::new(0));

/// Net bytes a stripe may accumulate in either direction before its balance
/// is published to [`LIVE_BYTES`].
pub(crate) const LIVE_BYTES_BATCH: usize = 64 * 1024;

/// [`LIVE_BYTES_BATCH`] as the stripes' signed type.
const BATCH: isize = LIVE_BYTES_BATCH as isize;

/// Number of pending balances. 256 lines of 128 bytes: 32 KiB of statics, so
/// that a few dozen threads rarely share one. A power of two, so the stripe
/// index is a mask.
pub(crate) const STRIPES: usize = 256;

/// log2 of the stack window that selects a stripe (1 MiB). The solver
/// threads' stacks are larger (8 MiB engine threads, a 64 MiB SMT thread), so
/// such a thread stays in one or two windows, and two of them meet only where
/// the far ends of adjacent stacks share a window. Threads with smaller stacks
/// can share a window, and then a stripe, with their neighbours.
const STACK_WINDOW_SHIFT: u32 = 20;

/// Pending live-byte balances, each strictly inside `(-BATCH, BATCH)` apart
/// from changes in flight on it.
static PENDING: [OwnCacheLine<AtomicIsize>; STRIPES] =
    [const { OwnCacheLine(AtomicIsize::new(0)) }; STRIPES];

/// A value alone on a 128-byte line (the coherence granule on Apple silicon;
/// two 64-byte lines elsewhere), so writers to it never invalidate a
/// neighbouring static.
#[repr(align(128))]
struct OwnCacheLine<T>(T);

/// The stripe for the caller's stack window.
///
/// The window number modulo [`STRIPES`], with no hashing: this sits on every
/// allocation, and thread stacks are mapped close together, so consecutive
/// stacks take consecutive stripes and collide only 256 MiB apart.
#[inline]
fn caller_stripe() -> &'static AtomicIsize {
    let marker = 0_u8;
    let window = std::ptr::addr_of!(marker).addr() >> STACK_WINDOW_SHIFT;
    &PENDING[window % STRIPES].0
}

/// Current live heap bytes tracked by [`crate::CountingAllocator`]: the
/// published total plus the pending balance of the caller's stripe, so a
/// thread that measures its own growth from one stack depth sees it. Other
/// stripes' balances are under one 64 KiB batch each.
///
/// Returns 0 when no counting allocator is installed (e.g. library consumers
/// that keep their own allocator). Two relaxed atomic loads.
#[must_use]
pub fn current_live_bytes() -> usize {
    let own = caller_stripe().load(Ordering::Relaxed);
    readable(LIVE_BYTES.0.load(Ordering::Relaxed).saturating_add(own))
}

/// A signed live-byte total as a reading: a transient debt reads as 0, never
/// as a huge unsigned value.
#[inline]
fn readable(total: isize) -> usize {
    usize::try_from(total).unwrap_or(0)
}

/// Add to the live-bytes counter. Internal to [`crate::CountingAllocator`];
/// exposed `#[doc(hidden)]` only so the wiring is testable without performing
/// real allocations.
///
/// Every change goes to the caller's stripe. A stripe's balance stays above
/// minus one batch, so a change of two batches or more carries it past the
/// batch on its own and is published at once.
#[doc(hidden)]
#[inline]
pub fn add_live_bytes(bytes: usize) {
    memory_group::charge_current(bytes);
    grow_stripe(caller_stripe(), signed(bytes));
}

/// Subtract from the live-bytes counter. A release larger than the count
/// never wraps it to a huge value that would spuriously trip the limit: the
/// total keeps the debt and reads as 0 until growth pays it. Internal to
/// [`crate::CountingAllocator`]; see [`add_live_bytes`].
#[doc(hidden)]
#[inline]
pub fn sub_live_bytes(bytes: usize) {
    memory_group::credit_current(bytes);
    shrink_stripe(caller_stripe(), signed(bytes));
}

/// `bytes` as a stripe delta. An allocation is at most `isize::MAX` bytes
/// (`Layout`'s invariant), so the clamp only guards direct callers, without a
/// branch.
#[inline]
fn signed(bytes: usize) -> isize {
    bytes.min(isize::MAX.unsigned_abs()).cast_signed()
}

/// Add `bytes` (non-negative) to `stripe`, and publish the stripe's balance
/// once it reaches a batch.
///
/// Only growth can carry a balance up to a batch, and the change that does so
/// sees it, so this direction needs one comparison; [`shrink_stripe`] mirrors
/// it. Wrapping arithmetic keeps the allocator free of overflow panics; a
/// balance stays near `(-BATCH, BATCH)` plus one change, because every writer
/// publishes as soon as it sees one batch.
#[inline]
fn grow_stripe(stripe: &AtomicIsize, bytes: isize) {
    let balance = stripe
        .fetch_add(bytes, Ordering::Relaxed)
        .wrapping_add(bytes);
    if balance >= BATCH {
        publish_stripe(stripe);
    }
}

/// Subtract `bytes` (non-negative) from `stripe`, and publish the stripe's
/// balance once it reaches minus one batch.
#[inline]
fn shrink_stripe(stripe: &AtomicIsize, bytes: isize) {
    let balance = stripe
        .fetch_sub(bytes, Ordering::Relaxed)
        .wrapping_sub(bytes);
    if balance <= -BATCH {
        publish_stripe(stripe);
    }
}

/// Move `stripe`'s whole balance to [`LIVE_BYTES`], and enforce the hard
/// ceiling on growth.
///
/// Out of line: it runs about once per batch of net change on a stripe, and
/// every allocation site inlines the caller. The `swap` takes the balance
/// atomically, so a concurrent writer on the same stripe loses nothing: it
/// either lands before the swap and is published here, or after it and stays
/// pending. The balance then reaches the total in one signed `fetch_add`, so
/// no reader or publisher ever sees a total that is half updated.
#[cold]
#[inline(never)]
fn publish_stripe(stripe: &AtomicIsize) {
    let balance = stripe.swap(0, Ordering::Relaxed);
    let previous = LIVE_BYTES.0.fetch_add(balance, Ordering::Relaxed);
    // The only synchronous point at which growth can be refused. Every
    // observer-based signal (checkpoint polls, the watchdog thread) can only
    // *request* a stop, and the heap keeps growing until that request is read
    // — measured at 3-4x the budget on a bit-blasting burst. See
    // [`crate::arm_hard_memory_ceiling`]. Growth is published at the latest
    // when a stripe's balance reaches one batch, and an allocation of two
    // batches or more at once, so the ceiling still refuses a burst as it
    // lands.
    if balance > 0 {
        let live = readable(previous.saturating_add(balance));
        if hard_memory_ceiling_breached(live) && !ceiling_settlement::settling_here() {
            breach_hard_memory_ceiling();
        }
    }
}

/// Test view: the published total alone, without any pending balance.
#[cfg(test)]
pub(crate) fn published_live_bytes() -> usize {
    readable(LIVE_BYTES.0.load(Ordering::Relaxed))
}

/// Test view: the published total plus every pending balance — the exact
/// count, whichever stripes the caller's changes landed on.
#[cfg(test)]
pub(crate) fn exact_live_bytes() -> usize {
    let pending: isize = PENDING
        .iter()
        .map(|stripe| stripe.0.load(Ordering::Relaxed))
        .sum();
    readable(LIVE_BYTES.0.load(Ordering::Relaxed).saturating_add(pending))
}

/// Test hook: apply a sub-batch change to one chosen stripe, so the batching
/// is testable without depending on where a test thread's stack landed.
#[cfg(test)]
pub(crate) fn add_to_stripe_for_test(index: usize, delta: isize) {
    if delta >= 0 {
        grow_stripe(&PENDING[index].0, delta);
    } else {
        shrink_stripe(&PENDING[index].0, -delta);
    }
}

/// Test view: a stripe's pending balance.
#[cfg(test)]
pub(crate) fn stripe_balance_for_test(index: usize) -> isize {
    PENDING[index].0.load(Ordering::Relaxed)
}

/// Test view: the index of the stripe the calling thread writes.
#[cfg(test)]
pub(crate) fn caller_stripe_index_for_test() -> usize {
    let own = caller_stripe();
    PENDING
        .iter()
        .position(|stripe| std::ptr::eq(&raw const stripe.0, own))
        .expect("the caller's stripe is one of the pending balances")
}
