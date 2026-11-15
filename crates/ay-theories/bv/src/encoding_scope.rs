// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Same-thread root handoff, never a resource grant or typed stop cause.

use super::{BvEncodingGuard, BvSolver, TermStore};
use std::{cell::RefCell, marker::PhantomData, rc::Rc};

thread_local! {
    static CURRENT: RefCell<Option<BvEncodingGuard>> = const { RefCell::new(None) };
}

/// Retain one depth-zero original BV refusal root across native children.
///
/// This thread-bound scope is deliberately not Send or Sync. Nested scopes reuse
/// the same root and do not build parent chains. Any observed child encoding
/// refusal, including a shorter local query timeout, invalidates the enclosing
/// attempt generically. This deliberately declines retries; it is not evidence
/// of original Timeout/Cancelled/Memory and is never SAT or proof authority.
#[must_use = "the original encoding root is restored when this scope is dropped"]
pub struct ScopedBvEncodingOwner {
    guard: BvEncodingGuard,
    previous: Option<BvEncodingGuard>,
    thread_bound: PhantomData<Rc<()>>,
}

impl ScopedBvEncodingOwner {
    /// Capture or reuse the current original root, with no fresh allowance.
    ///
    /// None means refusal or inaccessible/borrowed TLS, never healthy absence.
    pub fn enter(terms: &TermStore) -> Option<Self> {
        let inherited = current().ok()?;
        let guard = inherited.unwrap_or_else(|| BvSolver::new(terms).encoding_guard());
        if !guard.open() {
            return None;
        }
        let previous = CURRENT
            .try_with(|cell| {
                cell.try_borrow_mut()
                    .map(|mut current| current.replace(guard.clone()))
            })
            .ok()?
            .ok()?;
        Some(Self {
            guard,
            previous,
            thread_bound: PhantomData,
        })
    }

    /// Borrow the same resource-only root for a final observed-refusal fence.
    #[must_use]
    pub fn guard(&self) -> BvEncodingGuard {
        self.guard.clone()
    }
}

impl Drop for ScopedBvEncodingOwner {
    fn drop(&mut self) {
        let previous = self.previous.take();
        let _ = CURRENT.try_with(|cell| {
            if let Ok(mut current) = cell.try_borrow_mut() {
                *current = previous;
            }
        });
    }
}

// Keep inaccessible TLS distinct from genuine absence. No typed cause is guessed.
fn current() -> Result<Option<BvEncodingGuard>, ()> {
    CURRENT
        .try_with(|cell| {
            cell.try_borrow()
                .map(|current| current.clone())
                .map_err(|_| ())
        })
        .map_err(|_| ())?
}

impl BvSolver<'_> {
    /// Use the original root for native temporary encodings of this attempt.
    ///
    /// Ordinary calls without a scope retain the fresh per-query owner. Capture
    /// errors and this temporary's exact refusal fail closed and never create a
    /// replacement allowance. The temporary still retains its own callback/raw.
    #[must_use]
    pub fn original_encoding_guard(&self) -> BvEncodingGuard {
        match current() {
            Ok(Some(root)) => {
                if !self.encoding_complete() {
                    root.refuse_with_cut(self.encoding.blast_cut());
                }
                root
            }
            Ok(None) => self.encoding_guard(),
            Err(()) => {
                self.encoding.refuse();
                self.encoding_guard()
            }
        }
    }

    /// Attach this fresh child once to the current original root, if present.
    #[must_use]
    pub fn inherit_current_encoding_guard(&mut self) -> bool {
        match current() {
            Ok(Some(parent)) => self.inherit_encoding_guard(&parent),
            Ok(None) => {}
            Err(()) => self.encoding.refuse(),
        }
        self.encoding_complete()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use ay_core::resource::enter_check_stop;
    use ay_core::time::Instant;
    use std::sync::{
        atomic::{AtomicBool, Ordering},
        Arc, Mutex,
    };

    #[test]
    fn nested_scopes_reuse_exact_depth_zero_root_and_restore_it() {
        let terms = TermStore::new();
        assert!(current().unwrap().is_none());
        let first = ScopedBvEncodingOwner::enter(&terms).unwrap();
        let root = first.guard();
        let nested = ScopedBvEncodingOwner::enter(&terms).unwrap();
        assert!(root.same_owner(&nested.guard()));
        drop(nested);
        assert!(root.same_owner(&current().unwrap().unwrap()));
        drop(first);
        assert!(current().unwrap().is_none());
    }

    #[test]
    fn borrowed_encoding_tls_refuses_capture_and_never_means_no_parent() {
        let terms = TermStore::new();
        let solver = BvSolver::new(&terms);
        CURRENT.with(|cell| {
            let _borrowed = cell.borrow_mut();
            assert!(current().is_err());
            assert!(ScopedBvEncodingOwner::enter(&terms).is_none());
            assert!(solver.original_encoding_guard().was_stopped());
        });
        assert!(!solver.encoding_complete());
    }

    #[test]
    fn destroyed_encoding_tls_is_a_capture_refusal_not_healthy_absence() {
        struct Probe(RefCell<Option<Arc<AtomicBool>>>);
        impl Drop for Probe {
            fn drop(&mut self) {
                if let Some(observed) = self.0.borrow().as_ref() {
                    observed.store(current().is_err(), Ordering::Relaxed);
                }
            }
        }
        thread_local! {
            static PROBE: Probe = const { Probe(RefCell::new(None)) };
        }
        let observed = Arc::new(AtomicBool::new(false));
        let output = Arc::clone(&observed);
        std::thread::spawn(move || {
            PROBE.with(|probe| *probe.0.borrow_mut() = Some(output));
            let terms = TermStore::new();
            let scope = ScopedBvEncodingOwner::enter(&terms).unwrap();
            drop(scope);
        })
        .join()
        .unwrap();
        assert!(observed.load(Ordering::Relaxed));
    }

    #[test]
    fn shorter_child_wall_invalidates_attempt_but_fresh_original_scope_is_healthy() {
        let mut terms = TermStore::new();
        let x = terms.mk_var("x", ay_core::Sort::bitvec(128));
        let scope = ScopedBvEncodingOwner::enter(&terms).unwrap();
        let root = scope.guard();
        let end = Arc::new(Mutex::new(
            Instant::now() + std::time::Duration::from_secs(20),
        ));
        let observed = Arc::clone(&end);
        let local = enter_check_stop(Arc::new(move || {
            Instant::now() >= *observed.lock().unwrap()
        }));
        let mut child = BvSolver::new(&terms);
        assert!(child.inherit_current_encoding_guard());
        assert_eq!(child.ensure_term_bits(x).unwrap().len(), 128);
        *end.lock().unwrap() = Instant::now();
        assert!(child.ensure_term_bits(x).is_none());
        assert!(root.was_stopped());
        drop(child);
        drop(local);
        assert!(!root.open());
        drop(scope);
        let fresh = ScopedBvEncodingOwner::enter(&terms).unwrap();
        assert!(!fresh.guard().was_stopped());
        let mut child = BvSolver::new(&terms);
        assert!(child.inherit_current_encoding_guard());
        assert_eq!(child.ensure_term_bits(x).unwrap().len(), 128);
    }
}
