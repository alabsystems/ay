// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::EvalValue;
use ay_core::kani_compat::DetHashMap;
use ay_core::TermId;
use std::cell::RefCell;

struct Memo {
    /// Number of nested active sessions; caching is live iff `> 0`.
    depth: u32,
    map: DetHashMap<TermId, EvalValue>,
}

thread_local! {
    static EVAL_MEMO: RefCell<Memo> = RefCell::new(Memo {
        depth: 0,
        map: DetHashMap::default(),
    });
}

/// RAII guard marking a region over which `evaluate_term` results may be
/// cached. Nesting is reference-counted; the OUTERMOST guard's `drop`
/// clears the map so no value outlives the pass that produced it.
pub(crate) struct EvalMemoSession {
    active: bool,
}

impl EvalMemoSession {
    pub(crate) fn new() -> Self {
        EVAL_MEMO.with(|c| c.borrow_mut().depth += 1);
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
                m.map.clear();
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
                    depth: 0,
                    map: DetHashMap::default(),
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

/// Look up a cached value; `None` if no session is active or on a miss.
pub(super) fn get(term_id: TermId) -> Option<EvalValue> {
    EVAL_MEMO.with(|c| {
        let m = c.borrow();
        if m.depth == 0 {
            None
        } else {
            m.map.get(&term_id).cloned()
        }
    })
}

/// Record a value; a no-op when no session is active.
pub(super) fn put(term_id: TermId, value: &EvalValue) {
    EVAL_MEMO.with(|c| {
        let mut m = c.borrow_mut();
        if m.depth > 0 {
            m.map.insert(term_id, value.clone());
        }
    });
}

/// Drop all cached values (keeps the session open). MUST be called on every
/// mutation of the model being validated so no cached value outlives its
/// model state.
pub(super) fn clear() {
    EVAL_MEMO.with(|c| c.borrow_mut().map.clear());
}

#[cfg(test)]
pub(super) fn seed_for_test(term_id: TermId, value: EvalValue) {
    EVAL_MEMO.with(|cell| {
        let mut memo = cell.borrow_mut();
        assert!(memo.depth > 0, "test memo seed requires an active session");
        memo.map.insert(term_id, value);
    });
}
