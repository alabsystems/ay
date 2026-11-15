// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Parsed-assertion retention as session configuration.
//!
//! Retention selects the certification funnel's lanes (see
//! [`Context::set_definitional_pass_parsed_budget`]), so it must be a function
//! of how the session is configured, never of what the session did before: a
//! script option that outlived `(reset)`, or a lane that borrowed retention for
//! one query and kept it, made the next query of a resident session certify
//! differently from the same query in a fresh process.

use super::Context;

/// The retention `assert` consults (`effective`) and the host policy that
/// `(reset)` returns to (`policy`).
///
/// The host sets both with [`Context::set_retain_parsed_assertions`]. An
/// in-script `(set-option :produce-proofs true)` arms only the effective value,
/// because `(reset)` discards script options.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ParsedRetention {
    effective: bool,
    policy: bool,
}

impl ParsedRetention {
    /// Host-configured retention: effective value and policy agree.
    pub(super) const fn host(retain: bool) -> Self {
        Self {
            effective: retain,
            policy: retain,
        }
    }

    /// Whether `assert` retains parsed ASTs right now.
    pub(super) const fn effective(self) -> bool {
        self.effective
    }

    /// A script asked for proofs: retain from here until `(reset)`.
    pub(super) fn arm_for_proofs(&mut self) {
        self.effective = true;
    }

    /// The retention a `(reset)` leaves: the host policy, with every script arm
    /// discarded.
    pub(super) const fn after_reset(self) -> Self {
        Self::host(self.policy)
    }

    /// Turn retention off for an internal query window and return the value to
    /// restore when the window closes.
    pub(super) fn suspend(&mut self) -> Self {
        let saved = *self;
        self.effective = false;
        saved
    }
}

impl Context {
    /// Snapshot the complete retention configuration.
    ///
    /// Solver code that borrows a different retention for part of ONE query
    /// restores this snapshot afterwards with [`Self::restore_parsed_retention`],
    /// so the query leaves the session configured exactly as it found it.
    #[must_use]
    pub const fn parsed_retention(&self) -> ParsedRetention {
        self.parsed_retention
    }

    /// Restore a snapshot taken by [`Self::parsed_retention`].
    pub fn restore_parsed_retention(&mut self, retention: ParsedRetention) {
        self.parsed_retention = retention;
    }
}
