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

#[cfg_attr(
    test,
    expect(
        clippy::large_enum_variant,
        reason = "the LRA solver stays inline to avoid an unmetered allocation and preserve drop-before-store custody"
    )
)]
pub(crate) enum TheoryBox {
    /// `LraSolver::new(terms: &TermStore)` (`lifecycle.rs`); `'static`.
    Lra(ay_lra::LraSolver),
    /// Tests only (C3 additive arm for WP-2): a scripted `TheorySolver` that
    /// records what the bridge feeds it. Never constructed outside `cfg(test)`.
    #[cfg(test)]
    Mock(Box<dyn TheorySolver>),
}

impl TheoryBox {
    pub(crate) fn new(own: &mut SmtContext) -> Self {
        Self::Lra(ay_lra::LraSolver::new(&own.terms))
    }

    /// Tests only (C3 additive for WP-2): wrap a scripted theory.
    #[cfg(test)]
    pub(super) fn mock(theory: Box<dyn TheorySolver>) -> Self {
        Self::Mock(theory)
    }

    /// Re-point LRA at the session-owned term store.
    pub(crate) fn rebind(&mut self, own: &mut SmtContext) {
        match self {
            Self::Lra(lra) => lra.set_terms(&own.terms),
            #[cfg(test)]
            Self::Mock(_) => {}
        }
    }

    pub(crate) fn as_dyn(&mut self) -> &mut dyn TheorySolver {
        match self {
            Self::Lra(lra) => lra,
            #[cfg(test)]
            Self::Mock(m) => &mut **m,
        }
    }

    pub(crate) fn as_dyn_ref(&self) -> &dyn TheorySolver {
        match self {
            Self::Lra(lra) => lra,
            #[cfg(test)]
            Self::Mock(m) => &**m,
        }
    }

    /// LRA `get_value` (`lra_model.rs`). Callers `rebind` first because
    /// `get_value` dereferences the store pointer.
    pub(crate) fn arith_value(&self, t: TermId) -> Option<BigRational> {
        match self {
            Self::Lra(lra) => lra.get_value(t),
            #[cfg(test)]
            Self::Mock(_) => None,
        }
    }

    /// LRA's `assume_eqs`-over-split preference (`LraSolver::
    /// set_assume_eqs_over_split`); the bridge turns it off for the one
    /// re-check after a model-equality round that minted nothing new.
    pub(crate) fn set_assume_eqs_over_split(&mut self, on: bool) {
        match self {
            Self::Lra(lra) => lra.set_assume_eqs_over_split(on),
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
            #[cfg(test)]
            Self::Mock(_) => TheoryKind::Lra,
        }
    }
}

impl Drop for TheoryBox {
    fn drop(&mut self) {
        // `unset_terms` only at session drop (§5): the store the pointer names
        // is dropped right after this (field order in `HornSmt`).
        match self {
            Self::Lra(lra) => lra.unset_terms(),
            #[cfg(test)]
            Self::Mock(_) => {}
        }
    }
}
