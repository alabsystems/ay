// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Declared publication role of one decision query (#cert-accounting item 3).
//!
//! # What this is
//!
//! A *declaration by the caller* of who consumes the verdict of the decision
//! query it is about to run. It is a parameter of the request — supplied at
//! the call site through a typed entrypoint — and is never inferred from
//! ambient executor state.
//!
//! # What this is NOT (yet)
//!
//! In this landing the role has **no behavioural effect whatsoever**. It is
//! read by exactly one consumer, [`crate::executor::cert_accounting`], to
//! attribute certification cost to the channel that paid it. Every gate,
//! every certification lane, and every published verdict is byte-identical to
//! a build without this type. That is deliberate and load-bearing:
//!
//! - The previously attempted role-keyed *shedding* landing (skip the mint and
//!   the proof tracker for `InternalLemma`) closed the `dillig12_m` deadline
//!   regression but cost three CHC fixtures their `Safe` verdict
//!   (`test_adt_lia_isaplanner_last_singleton_safe_validates_9700`,
//!   `test_array_ghost_pair_route_certifies_safe_quantified_fixture`,
//!   `pdr_datatype::test_pdr_dt_option_enum_safe`) — a completeness loss that
//!   could not be separated from the win at call-site granularity. It was
//!   reverted in full.
//! - Splitting the *declaration* away from the *policy* lets the declaration
//!   land, be reviewed, and be measured on its own, while the policy question
//!   ("may this channel shed proof recording?") stays open and unanswered.
//!
//! A future stage that wants the role to change behaviour must add a
//! `CommandExecutionBoundary` variant so the exhaustive boundary matches force
//! every publication site to classify it, and must re-audit the three
//! `sat_chokepoint_conformance` pins that enumerate those variants. None of
//! that is required — or done — while the role only counts.
//!
//! # Why a typed entrypoint rather than an option
//!
//! `InternalLemma` is unreachable from parsed SMT-LIB text: there is no
//! `Command`, no `(set-option ...)`, and no environment variable that selects
//! it. A user's own `.smt2` file therefore cannot label its top-level
//! `(check-sat)` as internal. This mirrors the reason
//! [`crate::Executor::execute_authored`] is a method rather than a command
//! shape. It matters now only for the accounting's honesty, and it will matter
//! for soundness the moment any policy keys on the role.

/// Declared consumer of one decision query's verdict.
///
/// `Published` is the only [`Default`], so any code path that fails to declare
/// a role is accounted to the published channel — the conservative direction
/// for a counter whose purpose is to show how much work the *internal* channel
/// causes.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub(crate) enum QueryPublicationRole {
    /// The verdict leaves the process as an answer, or is consumed by a caller
    /// that treats it as its own certificate.
    #[default]
    Published,
    /// The verdict is consumed only as search guidance by the caller's own
    /// engine, whose eventual claim is certified by separate obligations that
    /// it re-derives itself.
    ///
    /// Declaring this today changes nothing about how the query is decided,
    /// certified, or published. It records which channel the query ran on.
    InternalLemma,
}

impl QueryPublicationRole {
    /// Stable short name used in statistics keys and diagnostics.
    pub(crate) const fn label(self) -> &'static str {
        match self {
            Self::Published => "published",
            Self::InternalLemma => "internal-lemma",
        }
    }

    /// Whether this role names the internal search channel.
    pub(crate) const fn is_internal_lemma(self) -> bool {
        matches!(self, Self::InternalLemma)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn default_role_is_published() {
        assert_eq!(
            QueryPublicationRole::default(),
            QueryPublicationRole::Published
        );
        assert!(!QueryPublicationRole::default().is_internal_lemma());
        assert_eq!(QueryPublicationRole::default().label(), "published");
    }

    #[test]
    fn internal_lemma_role_is_labelled_and_classified() {
        assert!(QueryPublicationRole::InternalLemma.is_internal_lemma());
        assert_eq!(
            QueryPublicationRole::InternalLemma.label(),
            "internal-lemma"
        );
    }
}
