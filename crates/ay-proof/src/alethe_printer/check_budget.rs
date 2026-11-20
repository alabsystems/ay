// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! A renderability check's budget, shared with every printer built while the
//! check renders (DR-PROOF-RENDER-BUDGET-20261118).
//!
//! A check renders a step through more printers than its own: sub-printers
//! the step builds (`shadowed_stores`' override-free `raw`, the `bv_packed`
//! renderers, the circuit lemmas' inner printers, `ground_substitution`'s
//! canonical clause), the free-function screens the printer consults
//! (`clause_surface_agreement`'s comparison printer, the BV arithmetic and
//! bit-blast screens, the `let`/folded/nullary preflights, `trans`), and
//! `render_term_canonical`'s fresh printer. Each had its own budget or none,
//! ran in [`super::AssembledRendering::Cached`] mode, and the check saw only
//! what it charged afterwards: an `ArrayRowChain` leaf's `raw` peaked at
//! 453 MB inside a check whose own budget was 32 MiB (review 2 of rev 3).
//!
//! While a check printer renders a step it installs its [`CheckBudget`] here,
//! and every printer constructed on this thread meanwhile is built WITHIN it:
//! - a renderability check itself (`PrinterPurpose`), so the pre-write gate
//!   charges apply to it too;
//! - in [`super::AssembledRendering::CachedWithinBudget`] mode, so it
//!   assembles nothing past its budget;
//! - with a budget of at most what the check has left when it is built
//!   (a printer with no budget of its own gets exactly that);
//! - and when it runs out, of its own budget or the check's, the CHECK is
//!   out of budget too, and so is every other printer built within it.
//!
//! Main's check had no budget at all, so this only moves a check's verdict to
//! `OutOfBudget` (keep the `trust` leaf), never to `Renders`: below
//! exhaustion every printer writes exactly the text it wrote on main.
//!
//! Only the check's OWN work is mirrored here. What a nested printer charges
//! stays on that printer; a printer that charged a nested printer's work to
//! the check on main (`self.charge(raw.work_used())`) still does, so nothing
//! is counted twice. A thread-local is the ambient channel for the same
//! reason `dialect::current()` is one: the free-function screens are shared
//! with the publication screen and take no printer to inherit from.

use std::cell::{Cell, RefCell};
use std::rc::Rc;

/// One renderability check's budget, shared with the printers built within it.
#[derive(Debug)]
pub(crate) struct CheckBudget {
    /// The check's work budget.
    limit: u64,
    /// The check printer's own work (its `work` counter, mirrored).
    used: Cell<u64>,
    /// A printer built within the check ran out.
    nested_exhausted: Cell<bool>,
}

impl CheckBudget {
    pub(super) fn new(limit: Option<u64>) -> Rc<Self> {
        Rc::new(Self {
            limit: limit.unwrap_or(u64::MAX),
            used: Cell::new(0),
            nested_exhausted: Cell::new(false),
        })
    }

    /// Record the check printer's own work.
    pub(super) fn record_own_work(&self, used: u64) {
        self.used.set(used);
    }

    /// Record that a printer built within the check ran out.
    pub(super) fn record_nested_exhaustion(&self) {
        self.nested_exhausted.set(true);
    }

    /// What the check has left.
    pub(super) fn remaining(&self) -> u64 {
        self.limit.saturating_sub(self.used.get())
    }

    /// Whether the check, or a printer built within it, has run out.
    pub(super) fn exhausted(&self) -> bool {
        self.nested_exhausted.get() || self.used.get() > self.limit
    }
}

thread_local! {
    static ACTIVE: RefCell<Option<Rc<CheckBudget>>> = const { RefCell::new(None) };
}

/// The budget printers built now are built within, if any.
pub(super) fn active() -> Option<Rc<CheckBudget>> {
    ACTIVE.with(|active| active.borrow().clone())
}

/// Install `budget` until the guard drops (the previous one is restored).
pub(super) fn enter(budget: &Rc<CheckBudget>) -> Entered {
    let previous = ACTIVE.with(|active| active.replace(Some(Rc::clone(budget))));
    Entered { previous }
}

/// The guard [`enter`] returns.
#[must_use = "the budget is installed only while the guard lives"]
pub(super) struct Entered {
    previous: Option<Rc<CheckBudget>>,
}

impl Drop for Entered {
    fn drop(&mut self) {
        let previous = self.previous.take();
        ACTIVE.with(|active| *active.borrow_mut() = previous);
    }
}
