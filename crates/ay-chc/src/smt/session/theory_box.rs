// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! `TheoryBox` — theory ownership and the rebind discipline (design §2.3, §5;
//! contract C3; owner WP-1 / A).
//!
//! The theory is NEVER `reset`/`soft_reset` between queries: bounds are
//! retracted by `pop` down to theory scope 0 (`bridge.backtrack(0)` through the
//! `BridgeGuard` at the end of every `check_*`), tableau / values / cuts stay
//! warm, atoms stay registered. `warm_reuse_hint()` is called once after the
//! first completed query (design F21). A defensive full `soft_reset` +
//! re-register of live atoms runs only after two consecutive
//! `TheoryIncomplete` results and on every `rebuild()` (counted).
//!
//! Lifetimes (§5): LRA (Rung 1) is `'static` and re-points its raw
//! `terms_ptr` through `set_terms(&own.terms)` before each operation batch —
//! the in-tree contract (`lra/src/lib.rs`, `lifecycle.rs`), no `unsafe` here.
//! `rebind` is called at bridge construction, after every mint, after every
//! `assert_persistent` conversion batch, and before model extraction;
//! `unset_terms` only at session drop.

use ay_core::{TermId, TheorySolver};
use num_rational::BigRational;

use super::TheoryKind;
use crate::smt::SmtContext;

pub(crate) enum TheoryBox {
    /// `LraSolver::new(terms: &TermStore)` (`lifecycle.rs`); `'static`.
    Lra(ay_lra::LraSolver),
    /// Rung 2.
    Lia(LiaCell),
    /// Tests only (C3 additive arm for WP-2): a scripted `TheorySolver` that
    /// records what the bridge feeds it. Never constructed outside `cfg(test)`.
    #[cfg(test)]
    Mock(Box<dyn TheorySolver>),
}

/// Rung 2. Holds `LiaSolver<'static>` over the session's boxed store.
///
/// INVARIANTS (debug-asserted when it lands):
///  I1 the store lives in `HornSmt::own` (a `Box`) and is never moved, reset or
///     rolled back;
///  I2 `rebind(&mut own)` is called after EVERY `&mut own.terms` use and before
///     ANY theory call; the reference is re-derived from the LIVE
///     `&mut SmtContext` each time (never cached);
///  I3 no theory method runs between a mutation and the following rebind (all
///     mutation sites are inside `MintState` and `assert_persistent`, each
///     followed by `rebind`);
///  I4 `LiaCell` is dropped before `own` (field order in `HornSmt`).
/// The stale `&'static` between a write and the rebind is dead-but-unused; the
/// fresh one post-dates the write — the discipline `LraSolver::set_terms`
/// documents.
///
/// SKELETON NOTE: the design's `unsafe fn fresh_static(&TermStore) -> &'static
/// TermStore` cannot live in this crate as written — `ay-chc` is
/// `#![forbid(unsafe_code)]` (`lib.rs:5`) and the workspace denies it. Rung 2
/// must either (a) lift the crate forbid to `deny` plus ONE audited
/// `#[allow(unsafe_code)]` on that function, or (b) take the design's stretch
/// option and give `LiaSolver` LRA's raw-pointer discipline (no lifetime, no
/// `unsafe` in ay-chc). Decision deferred to Rung 2; nothing in Rung 1
/// constructs a `LiaCell`. Also needs the `#[cfg(debug_assertions)]` lifted
/// from `LiaSolver::rebind_terms` (`lia/src/lib.rs`).
pub(crate) struct LiaCell {
    lia: Option<ay_lia::LiaSolver<'static>>,
}

impl TheoryBox {
    pub(crate) fn new_for(kind: TheoryKind, own: &mut SmtContext) -> Self {
        match kind {
            TheoryKind::Lra => Self::Lra(ay_lra::LraSolver::new(&own.terms)),
            TheoryKind::Lia => todo!("Rung 2: LiaCell over the session store"),
        }
    }

    /// Tests only (C3 additive for WP-2): wrap a scripted theory.
    #[cfg(test)]
    pub(super) fn mock(theory: Box<dyn TheorySolver>) -> Self {
        Self::Mock(theory)
    }

    /// LRA: `set_terms(&own.terms)`. LIA: `rebind_terms(fresh_static(&own.terms))`.
    pub(crate) fn rebind(&mut self, own: &mut SmtContext) {
        match self {
            Self::Lra(lra) => lra.set_terms(&own.terms),
            Self::Lia(_) => todo!("Rung 2: LiaCell::rebind"),
            #[cfg(test)]
            Self::Mock(_) => {}
        }
    }

    pub(crate) fn as_dyn(&mut self) -> &mut dyn TheorySolver {
        match self {
            Self::Lra(lra) => lra,
            Self::Lia(cell) => cell
                .lia
                .as_mut()
                .expect("LiaCell is populated for the session's life"),
            #[cfg(test)]
            Self::Mock(m) => &mut **m,
        }
    }

    pub(crate) fn as_dyn_ref(&self) -> &dyn TheorySolver {
        match self {
            Self::Lra(lra) => lra,
            Self::Lia(cell) => cell
                .lia
                .as_ref()
                .expect("LiaCell is populated for the session's life"),
            #[cfg(test)]
            Self::Mock(m) => &**m,
        }
    }

    /// LRA `get_value` (`lra_model.rs`); LIA via `lra_solver()` (`lia/src/lib.rs`).
    /// Callers `rebind` first (`get_value` dereferences the store pointer).
    pub(crate) fn arith_value(&self, t: TermId) -> Option<BigRational> {
        match self {
            Self::Lra(lra) => lra.get_value(t),
            Self::Lia(cell) => cell.lia.as_ref()?.lra_solver().get_value(t),
            #[cfg(test)]
            Self::Mock(_) => None,
        }
    }

    /// LIA: `set_deadline` + `set_timeout_callback` (`solver_support.rs`).
    /// LRA: no hook (§3.5) — its per-call work is bounded by the implied-bounds
    /// budget and the bridge's `deadline_hit()` at every `propagate`/`check`.
    pub(crate) fn set_deadline(&mut self, dl: Option<ay_core::time::Instant>) {
        match self {
            Self::Lra(_) => {}
            Self::Lia(_) => todo!("Rung 2: LiaSolver::set_deadline + set_timeout_callback"),
            #[cfg(test)]
            Self::Mock(_) => {}
        }
    }

    /// LRA's `assume_eqs`-over-split preference (`LraSolver::
    /// set_assume_eqs_over_split`); the bridge turns it off for the one
    /// re-check after a model-equality round that minted nothing new.
    pub(crate) fn set_assume_eqs_over_split(&mut self, on: bool) {
        match self {
            Self::Lra(lra) => lra.set_assume_eqs_over_split(on),
            Self::Lia(_) => {}
            #[cfg(test)]
            Self::Mock(_) => {}
        }
    }

    /// `set_warm_reuse_hint(true)` (`theory/mod.rs`; design F21).
    pub(crate) fn warm_reuse_hint(&mut self) {
        self.as_dyn().set_warm_reuse_hint(true);
    }

    pub(crate) fn kind(&self) -> TheoryKind {
        match self {
            Self::Lra(_) => TheoryKind::Lra,
            Self::Lia(_) => TheoryKind::Lia,
            #[cfg(test)]
            Self::Mock(_) => TheoryKind::Lra,
        }
    }
}

impl Drop for TheoryBox {
    fn drop(&mut self) {
        // `unset_terms` only at session drop (§5): the store the pointer names
        // is dropped right after this (field order in `HornSmt`).
        if let Self::Lra(lra) = self {
            lra.unset_terms();
        }
    }
}
