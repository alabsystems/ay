// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::EvalValue;
use ay_core::kani_compat::DetHashMap;
use ay_core::TermId;
use std::cell::{Cell, RefCell};

struct Memo {
    currency: Option<u128>,
    /// Number of nested active sessions; caching is live iff `> 0`.
    depth: u32,
    // Retained handles let us release this RefCell before original admission
    // callbacks. This adds one allocation/indirection per entry, including
    // outside restricted reads; it is a custody tradeoff, not a speed claim.
    map: DetHashMap<TermId, std::rc::Rc<EvalValue>>,
    /// Whether a term's reachable subtree touches a retained residual array.
    ///
    /// Shares this memo's lifetime and every one of its invalidation points on
    /// purpose: the predicate is a function of the term graph and the installed
    /// residual-array batch, and `install_residual_arrays` already clears this
    /// memo. Keeping the two in one struct means a future clear site cannot
    /// invalidate evaluated values while leaving stale dependency answers.
    residual_deps: DetHashMap<TermId, bool>,
}

thread_local! {
    static NEXT_CURRENCY: Cell<Option<u128>> = const { Cell::new(Some(0)) };
    static EVAL_MEMO: RefCell<Memo> = RefCell::new(Memo {
        currency: fresh_currency(),
        depth: 0,
        map: DetHashMap::default(),
        residual_deps: DetHashMap::default(),
    });
}

fn fresh_currency() -> Option<u128> {
    NEXT_CURRENCY.with(|next| {
        let current = next.get();
        next.set(current.and_then(|value| value.checked_add(1)));
        current
    })
}

fn currency() -> Option<u128> {
    EVAL_MEMO.with(|slot| {
        let memo = slot.borrow();
        if memo.depth > 0 {
            memo.currency
        } else {
            None
        }
    })
}

/// RAII guard marking a region over which `evaluate_term` results may be
/// cached. Nesting is reference-counted; the OUTERMOST guard's `drop`
/// clears the map so no value outlives the pass that produced it.
pub(crate) struct EvalMemoSession {
    active: bool,
}

impl EvalMemoSession {
    pub(crate) fn new() -> Self {
        EVAL_MEMO.with(|c| {
            let mut memo = c.borrow_mut();
            if memo.depth == 0 {
                memo.currency = fresh_currency();
            }
            memo.depth += 1;
        });
        EvalMemoSession { active: true }
    }
}

impl Drop for EvalMemoSession {
    fn drop(&mut self) {
        if !self.active {
            return;
        }
        EVAL_MEMO.with(|c| {
            let mut m = c.borrow_mut();
            m.depth = m.depth.saturating_sub(1);
            if m.depth == 0 {
                m.currency = fresh_currency();
                m.map.clear();
                m.residual_deps.clear();
            }
        });
    }
}

/// Panic-safe isolation for an evaluation that must not read from or write
/// into an ambient fixed-model memo session.
///
/// Merely clearing the shared map is insufficient: the nested evaluation
/// would then populate the still-active outer session with values computed
/// from its own model.  Swap the complete thread-local state instead and
/// restore it verbatim on drop, including during unwinding.
pub(super) struct IsolatedEvalMemo {
    outer: Option<Memo>,
}

impl IsolatedEvalMemo {
    pub(super) fn new() -> Self {
        let outer = EVAL_MEMO.with(|cell| {
            std::mem::replace(
                &mut *cell.borrow_mut(),
                Memo {
                    currency: fresh_currency(),
                    depth: 0,
                    map: DetHashMap::default(),
                    residual_deps: DetHashMap::default(),
                },
            )
        });
        Self { outer: Some(outer) }
    }
}

impl Drop for IsolatedEvalMemo {
    fn drop(&mut self) {
        let Some(outer) = self.outer.take() else {
            return;
        };
        EVAL_MEMO.with(|cell| *cell.borrow_mut() = outer);
    }
}

/// Evaluate one exact semantic obligation in a fresh memo universe.
///
/// The closure boundary keeps callers from forgetting the isolation guard.
/// Its nested session permits local DAG memoization, while the outer session
/// and all entries are restored byte-for-byte after return or unwinding.
pub(in crate::executor) fn with_isolated_eval_memo<R>(f: impl FnOnce() -> R) -> R {
    let _isolation = IsolatedEvalMemo::new();
    let _session = EvalMemoSession::new();
    f()
}

/// Run a self-contained nested solve (a fresh `Executor::check_sat`) against
/// the memo a top-level solve starts with: empty, and with NO ambient session.
/// The caller's state is restored verbatim on return or unwinding.
///
/// A nested executor clones its caller's term store, so both use the same
/// `TermId`s, and this memo is keyed by `TermId` alone. Under a live caller
/// session the nested solve reads the caller's entries, and every value it
/// evaluates under its OWN model outlives its own sessions (the caller keeps
/// the depth above zero) and is then served to the caller as if the caller's
/// model had produced it. Measured on `test_seq_replace_decomposition_5841`:
/// the Phase-0 completion sub-solve returned `Unknown`, yet whenever it reached
/// its own validation inside its 150 ms wall, its witness for `u`, `src` and
/// `(seq.replace u src dst)` became the outer model's values; the verdict then
/// followed the CPU (fast core `sat`, slow core `unknown`).
pub(super) fn with_detached_eval_memo<R>(f: impl FnOnce() -> R) -> R {
    let _isolation = IsolatedEvalMemo::new();
    f()
}

/// Look up a cached value; `None` if no session is active or on a miss.
pub(super) fn get(term_id: TermId) -> Option<EvalValue> {
    let (original, value) = EVAL_MEMO.with(|c| {
        let m = c.borrow();
        if m.depth == 0 {
            (None, None)
        } else {
            (m.currency, m.map.get(&term_id).cloned())
        }
    });
    let value = value.map(|value| super::evaluation_copies::copy(&value));
    if original.is_some() && currency() == original {
        value
    } else {
        None
    }
}

/// Record a value; a no-op when no session is active.
pub(super) fn put(term_id: TermId, value: &EvalValue) {
    let Some(original) = currency() else {
        return;
    };
    if !super::evaluation_copies::pay(1, size_of::<(TermId, EvalValue)>() * 4) {
        return;
    }
    let value = super::evaluation_copies::copy(value);
    if super::evaluation_copies::active() && matches!(value, EvalValue::Unknown) {
        return;
    }
    if currency() != Some(original) {
        return;
    }
    let value = std::rc::Rc::new(value);
    EVAL_MEMO.with(|c| {
        let mut m = c.borrow_mut();
        if m.depth > 0 && m.currency == Some(original) {
            m.map.insert(term_id, value);
        }
    });
}

/// Drop all cached values (keeps the session open). MUST be called on every
/// mutation of the model being validated so no cached value outlives its
/// model state.
pub(super) fn clear() {
    EVAL_MEMO.with(|c| {
        let mut m = c.borrow_mut();
        m.currency = fresh_currency();
        m.map.clear();
        m.residual_deps.clear();
    });
}

/// Look up a cached residual-array dependency answer; `None` if no session is
/// active or on a miss.
pub(super) fn residual_dep_get(term_id: TermId) -> Option<bool> {
    EVAL_MEMO.with(|c| {
        let m = c.borrow();
        if m.depth == 0 {
            None
        } else {
            m.residual_deps.get(&term_id).copied()
        }
    })
}

/// Record residual-array dependency answers; a no-op when no session is active.
///
/// Only a COMPLETED walk may record. A walk that failed closed on a resource
/// cap or an external stop has not established anything about these terms.
pub(super) fn residual_dep_put(terms: impl IntoIterator<Item = TermId>, value: bool) {
    let Some(original) = currency() else {
        return;
    };
    for term in terms {
        if !super::evaluation_copies::pay(1, 4 * size_of::<(TermId, bool)>()) {
            return;
        }
        EVAL_MEMO.with(|c| {
            let mut m = c.borrow_mut();
            if m.depth > 0 && m.currency == Some(original) {
                m.residual_deps.insert(term, value);
            }
        });
    }
}

#[cfg(test)]
pub(super) fn seed_for_test(term_id: TermId, value: EvalValue) {
    EVAL_MEMO.with(|cell| {
        let mut memo = cell.borrow_mut();
        assert!(memo.depth > 0, "test memo seed requires an active session");
        memo.map.insert(term_id, std::rc::Rc::new(value));
    });
}

#[cfg(test)]
mod detached_memo_tests {
    use super::*;
    use num_bigint::BigInt;
    use num_rational::BigRational;

    fn int(v: i64) -> EvalValue {
        EvalValue::Rational(BigRational::from_integer(BigInt::from(v)))
    }

    /// The shape of a nested solve: it opens and closes its own session while
    /// its caller's session stays live. Returns what it saw before writing.
    fn nested_solve_evaluates(term: TermId, value: &EvalValue) -> Option<EvalValue> {
        let _own_session = EvalMemoSession::new();
        let seen = get(term);
        put(term, value);
        seen
    }

    #[test]
    fn detached_nested_solve_neither_reads_nor_leaks_the_caller_memo() {
        let shared = TermId(7);
        let fresh = TermId(8);
        let _caller = EvalMemoSession::new();
        put(shared, &EvalValue::Unknown);
        let seen = with_detached_eval_memo(|| {
            assert_eq!(get(shared), None, "a detached solve starts with no session");
            let seen = nested_solve_evaluates(shared, &int(2));
            nested_solve_evaluates(fresh, &int(3));
            seen
        });
        assert_eq!(
            seen, None,
            "the nested solve must not read the caller's entry"
        );
        assert_eq!(get(shared), Some(EvalValue::Unknown));
        assert_eq!(
            get(fresh),
            None,
            "nothing the nested solve evaluated may leak"
        );
    }
}
