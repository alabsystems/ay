// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Entering a node on a thread (GT4).
//!
//! Entering makes the node the thread's current guard, so a loop deep inside
//! a theory that holds no handle on its check still reaches that check's
//! stop, on whichever thread it runs: a spawned worker enters its node as
//! its first statement. The same scope enters the node's memory share (its
//! `MemoryGroup`, or the nearest ancestor's when it has none, so a worker's
//! allocations on its own thread are charged where its parent's are) and
//! opens its CPU slice.
//!
//! Scopes nest. The thread keeps the entered nodes innermost last, each with
//! its scope's identity, and a scope removes ITS OWN entry when it drops, so
//! an out-of-order drop never restores a node whose scope has ended and
//! never hides one whose scope is still open.

use std::cell::RefCell;
use std::marker::PhantomData;
use std::sync::atomic::{AtomicU64, Ordering};

use ay_sys::MemoryGroupScope;

use super::Guard;

thread_local! {
    /// The nodes entered on this thread, innermost last.
    static ENTERED: RefCell<Vec<(u64, Guard)>> = const { RefCell::new(Vec::new()) };
}

/// Identities of entry scopes, unique in the process.
static NEXT_SCOPE: AtomicU64 = AtomicU64::new(0);

/// Keeps a node entered on this thread until dropped (GT4). Not `Send`: it
/// must be dropped on the thread that entered the node.
#[must_use = "the node stops being this thread's current guard when this scope is dropped"]
pub struct EnterScope {
    id: u64,
    guard: Guard,
    owns_cpu: bool,
    // Dropped after `Drop::drop` has run, on this thread.
    _memory: Option<MemoryGroupScope>,
    _thread_bound: PhantomData<*const ()>,
}

impl std::fmt::Debug for EnterScope {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("EnterScope")
            .field("id", &self.id)
            .field("guard", &self.guard)
            .finish_non_exhaustive()
    }
}

impl Guard {
    /// Make this node the calling thread's current guard until the returned
    /// scope drops; enter its memory share (else the nearest ancestor's) and
    /// open its CPU slice with it. A spawned worker calls this as its first
    /// statement.
    pub fn enter(&self) -> EnterScope {
        let memory = self
            .node
            .charged_share()
            .map(|group| ay_sys::enter_memory_group(std::sync::Arc::clone(group)));
        let owns_cpu = self.node.cpu.as_ref().is_some_and(|cpu| cpu.enter());
        let id = NEXT_SCOPE.fetch_add(1, Ordering::Relaxed);
        let _ = ENTERED.try_with(|entered| entered.borrow_mut().push((id, self.clone())));
        EnterScope {
            id,
            guard: self.clone(),
            owns_cpu,
            _memory: memory,
            _thread_bound: PhantomData,
        }
    }
}

impl EnterScope {
    /// The node this scope keeps entered.
    #[must_use]
    pub fn guard(&self) -> &Guard {
        &self.guard
    }
}

impl Drop for EnterScope {
    fn drop(&mut self) {
        let id = self.id;
        let removed = ENTERED
            .try_with(|entered| {
                let mut entered = entered.borrow_mut();
                let at = entered.iter().rposition(|(entry, _)| *entry == id)?;
                Some(entered.remove(at))
            })
            .ok()
            .flatten();
        // Dropped outside the borrow: it may be the node's last handle.
        drop(removed);
        if self.owns_cpu {
            if let Some(cpu) = self.guard.node.cpu.as_ref() {
                cpu.exit();
            }
        }
    }
}

/// The node the calling thread entered last and has not left (GT4), if any.
/// A handle of its own: [`with_current_guard`] borrows it instead.
#[must_use]
pub fn current_guard() -> Option<Guard> {
    with_current_guard(Guard::clone)
}

/// Run `f` on the node the calling thread entered last and has not left
/// (GT4), without taking a handle: a hot poll's accessor
/// (`with_current_guard(Guard::should_stop)`). `None` when the thread is in
/// no node. `f` must not enter a node or drop a scope on this thread: the
/// thread's entered nodes are borrowed while it runs.
pub fn with_current_guard<R>(f: impl FnOnce(&Guard) -> R) -> Option<R> {
    ENTERED
        .try_with(|entered| entered.borrow().last().map(|(_, guard)| f(guard)))
        .ok()
        .flatten()
}
