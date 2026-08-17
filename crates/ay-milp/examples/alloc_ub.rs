// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![expect(
    unsafe_code,
    reason = "the diagnostic's pooled global allocator must implement and call the unsafe allocation API"
)]

//! THE UPPER BOUND ON EVERY ALLOCATION-REMOVAL WIN.
//!
//! "Reuse a scratch buffer instead of allocating it" can only ever buy back what the
//! allocation COST. Rather than argue that number from a microbenchmark, this binary makes
//! allocation nearly free in situ and reruns the real solve: a thread-local size-class free
//! list turns `alloc`/`dealloc` of every small block into a pointer pop/push, with no call
//! into the system allocator at all once the lists are warm.
//!
//! Whatever this binary beats `mps_solve` by is MORE than any amount of scratch reuse can
//! win, because scratch reuse removes a subset of the same allocations and pays the same
//! bookkeeping. If the difference is noise, the front is refuted and no code change can
//! rescue it.
//!
//! Nothing here ships: it is a measurement binary. Reusable blocks stay cached up to a fixed
//! per-class cap; surplus blocks are returned to the system.

use std::alloc::{GlobalAlloc, Layout, System};
use std::cell::UnsafeCell;
use std::time::{Duration, Instant};

use ay_milp::{BabSession, Outcome, SolveOpts};

/// Size classes of 16 bytes up to `MAX_SIZE`; everything larger goes to `System`.
const CLASS_STEP: usize = 16;
const N_CLASS: usize = 64; // 16..=1024 bytes
const MAX_SIZE: usize = CLASS_STEP * N_CLASS;
/// Blocks parked per class. Bounded so a pathological free burst cannot pin the heap.
const CAP: usize = 2048;

struct Pool {
    head: [usize; N_CLASS],
    slot: [[*mut u8; CAP]; N_CLASS],
}

// The pool is thread-local and only ever touched through the raw pointer below, on the
// thread that owns it.
thread_local! {
    static POOL: UnsafeCell<Pool> = const {
        UnsafeCell::new(Pool { head: [0; N_CLASS], slot: [[std::ptr::null_mut(); CAP]; N_CLASS] })
    };
}

#[inline]
fn class_of(l: Layout) -> Option<usize> {
    // Pooled blocks are explicitly allocated at `CLASS_STEP` alignment; anything stricter
    // stays on the ordinary system-allocator path.
    if l.align() > CLASS_STEP || l.size() == 0 || l.size() > MAX_SIZE {
        return None;
    }
    Some((l.size() - 1) / CLASS_STEP)
}

#[inline]
fn class_layout(class: usize) -> Option<Layout> {
    Layout::from_size_align((class + 1) * CLASS_STEP, CLASS_STEP).ok()
}

struct Pooled;

// SAFETY: every pooled block comes from `System` with its class-top size and 16-byte alignment,
// while `class_of` accepts only requests that fit that size and alignment. Other requests are
// forwarded to `System` unchanged. `POOL` is thread-local and accessed only inside `with`, so
// its `UnsafeCell` is never concurrently aliased.
unsafe impl GlobalAlloc for Pooled {
    unsafe fn alloc(&self, l: Layout) -> *mut u8 {
        if let Some(c) = class_of(l) {
            let hit = POOL.with(|p| {
                // SAFETY: this thread exclusively accesses its own pool during the callback,
                // and the callback performs no allocation that could re-enter the pool.
                let p = unsafe { &mut *p.get() };
                if p.head[c] == 0 {
                    std::ptr::null_mut()
                } else {
                    p.head[c] -= 1;
                    p.slot[c][p.head[c]]
                }
            });
            if !hit.is_null() {
                return hit;
            }
            // Miss: take a block sized to the TOP of the class, so any later request in
            // this class fits it.
            let Some(top) = class_layout(c) else {
                return std::ptr::null_mut();
            };
            // SAFETY: `top` is valid and describes the class size/alignment recorded by
            // `class_of`; a null result is permitted by `GlobalAlloc`.
            return unsafe { System.alloc(top) };
        }
        // SAFETY: non-pooled requests are forwarded with the caller-provided valid layout.
        unsafe { System.alloc(l) }
    }

    unsafe fn dealloc(&self, ptr: *mut u8, l: Layout) {
        if let Some(c) = class_of(l) {
            let parked = POOL.with(|p| {
                // SAFETY: this thread exclusively accesses its own pool during the callback,
                // and the callback performs no allocation that could re-enter the pool.
                let p = unsafe { &mut *p.get() };
                if p.head[c] < CAP {
                    p.slot[c][p.head[c]] = ptr;
                    p.head[c] += 1;
                    true
                } else {
                    false
                }
            });
            if parked {
                return;
            }
            let Some(top) = class_layout(c) else {
                return;
            };
            // SAFETY: every pooled-class allocation is obtained from `System` with exactly
            // this class-top layout, including allocations later returned by same-class realloc.
            unsafe { System.dealloc(ptr, top) };
            return;
        }
        // SAFETY: non-pooled pointers were allocated by `System` with this same layout.
        unsafe { System.dealloc(ptr, l) }
    }

    unsafe fn alloc_zeroed(&self, l: Layout) -> *mut u8 {
        // SAFETY: the caller provided a valid layout; this allocator's `alloc` contract applies.
        let p = unsafe { self.alloc(l) };
        if !p.is_null() {
            // SAFETY: `p` points to at least `l.size()` initialized-or-uninitialized bytes
            // returned above, and the non-null check establishes that the allocation succeeded.
            unsafe { std::ptr::write_bytes(p, 0, l.size()) };
        }
        p
    }

    unsafe fn realloc(&self, ptr: *mut u8, l: Layout, new: usize) -> *mut u8 {
        // Same class: the block already has room, so this is a no-op.
        if let (Some(a), Ok(nl)) = (class_of(l), Layout::from_size_align(new, l.align())) {
            if class_of(nl) == Some(a) {
                return ptr;
            }
        }
        let Ok(nl) = Layout::from_size_align(new, l.align()) else {
            return std::ptr::null_mut();
        };
        // SAFETY: `nl` is valid; a null return preserves the caller's original allocation.
        let np = unsafe { self.alloc(nl) };
        if !np.is_null() {
            // SAFETY: `ptr` and fresh `np` are non-overlapping live allocations, and both
            // contain at least `min(old_size, new_size)` bytes.
            unsafe { std::ptr::copy_nonoverlapping(ptr, np, l.size().min(new)) };
            // SAFETY: `ptr` remains owned by the caller until the successful allocation above;
            // it was allocated by this allocator using `l`.
            unsafe { self.dealloc(ptr, l) };
        }
        np
    }
}

#[global_allocator]
static A: Pooled = Pooled;

fn main() {
    let mut args = std::env::args().skip(1);
    let Some(path) = args.next() else {
        eprintln!("usage: alloc_ub <file.mps> [seconds]");
        std::process::exit(2);
    };
    let secs: f64 = args.next().and_then(|s| s.parse().ok()).unwrap_or(60.0);

    let text = std::fs::read_to_string(&path).unwrap_or_else(|e| {
        eprintln!("cannot read {path}: {e}");
        std::process::exit(2);
    });
    let p = ay_milp::read_mps(&text).unwrap_or_else(|e| {
        eprintln!("PARSE_ERROR {e}");
        std::process::exit(3);
    });

    // DETERMINISTIC SAME-WORK LANE. A wall-clock-limited tree run compares different amounts
    // of work on a loaded box and is therefore useless as an A/B. The root cut loop does a
    // FIXED amount of work, and it is where 61% of this engine's allocations live, so it is
    // the honest place to price allocation. Mirrors `mps_solve`'s own `AY_ROOT_CLOSURE`.
    if std::env::var_os("AY_ROOT_CLOSURE").is_some() {
        let t = Instant::now();
        let line = ay_milp::diag_root_closure(&p.model, secs);
        println!("{line} wall={:.3}", t.elapsed().as_secs_f64());
        return;
    }

    let opts = SolveOpts::new().with_time_limit(Duration::from_secs_f64(secs));
    let mut s = match BabSession::new(p.model, &opts) {
        Ok(s) => s,
        Err(e) => {
            println!("SETUP_ERROR {e:?} - -");
            return;
        }
    };
    let t0 = Instant::now();
    let out = s.check();
    let dt = t0.elapsed().as_secs_f64();
    let nodes = ay_milp::nodes_explored();

    match out {
        Ok(Outcome::Optimal { value, .. }) => {
            println!(
                "OPTIMAL {} {dt:.3} {nodes}",
                ratio_str(&(&value / &p.obj_scale))
            );
        }
        Ok(Outcome::Feasible { model_values, .. }) => {
            let v = s.model().objective_value_at(&model_values);
            println!(
                "FEASIBLE {} {dt:.3} {nodes}",
                ratio_str(&(&v / &p.obj_scale))
            );
        }
        Ok(Outcome::Infeasible { .. }) => println!("INFEASIBLE - {dt:.3} {nodes}"),
        Ok(Outcome::Unbounded) => println!("UNBOUNDED - {dt:.3} {nodes}"),
        Ok(Outcome::Unknown { reason }) => println!("UNKNOWN {reason:?} {dt:.3} {nodes}"),
        Err(e) => println!("ERROR {e:?} {dt:.3} {nodes}"),
        Ok(other) => println!("OTHER {other:?} {dt:.3} {nodes}"),
    }
}

/// A rational objective as a decimal, which is what every other solver prints.
fn ratio_str(v: &num_rational::BigRational) -> String {
    use num_traits::ToPrimitive;
    v.to_f64().map_or_else(|| v.to_string(), |f| format!("{f}"))
}
