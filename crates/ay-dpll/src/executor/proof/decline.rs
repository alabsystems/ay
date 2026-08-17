// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Attributed reasons for declining to record a proof at all.
//!
//! A refutation that ships `(step t0 (cl) :rule hole)` — one line, no
//! premises, no derivation — says only "AY refuted this and kept nothing".
//! Two entirely different machines produce that artifact
//! (`install_uncertifiable_proof_poison` and `false_source`'s
//! `set_empty_hole`), and inside the first one at least three distinct
//! conditions reach it. A corpus census over the emitted artifacts therefore
//! reported ONE bucket ("step t0 uses unverified trust rule", 44 instances of
//! the measured 68) for causes whose remedies have nothing in common.
//!
//! Measured on the QF_DT `barrett-jsat/typed` family at 800b0668e, with the
//! `--proof` verdict lost on every one of them:
//!
//! | instance          | nodes in the single authored root | mechanism |
//! |-------------------|-----------------------------------|-----------|
//! | `typed_v1l80035`  | 11,054                            | root unbounded |
//! | `typed_v1l60098`  | 128,309                           | root unbounded |
//! | `typed_v2l20006`  | 48                                | fold-to-`false` |
//! | `typed_v1l20003`  | 75                                | fold-to-`false` |
//!
//! The first class is refused by a per-root RENDERING bound
//! (`MAX_SURFACE_NODES`, 8,192 nodes/root) before any proof machinery runs;
//! the second class has a bounded source, reaches a real proof, and then has
//! that proof erased because it rests on an `assume false` the preprocessor
//! manufactured. Naming them apart is the whole point: the first wants a
//! rendering budget that reflects real work, the second wants the
//! preprocessor's own argument recorded (see `authored_conjunct_eval`).
//!
//! This is deliberately NOT a weakening of any gate. The decline still
//! happens, the artifact is still fail-closed, and the verdict still
//! downgrades. Only the LABEL changes, from anonymous to attributed.

/// Why the last UNSAT refutation carries no derivation.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ProofDeclineMechanism {
    /// One authored assertion exceeds the per-root surface bound
    /// (`MAX_SURFACE_NODES` / `MAX_SURFACE_DEPTH`), so no pass can render it
    /// and proof PRODUCTION is refused before it starts.
    AuthoredSourceRootUnbounded,
    /// Every authored root is individually renderable, but the aggregate
    /// source-work envelope (`MAX_AGGREGATE_SOURCE_WORK`) cannot afford the
    /// build pass.
    AuthoredSourceAggregateBudget,
    /// More than `MAX_PROOF_SOURCE_ROOTS` authored roots / provenance entries.
    AuthoredSourceRootCount,
    /// The proof rested on an `assume false` that the PREPROCESSOR produced by
    /// folding an authored assertion, keeping no record of the rewrite. The
    /// refutation is real and the argument is expressible; it was discarded.
    PreprocessorFoldToFalseUnrecorded,
}

impl ProofDeclineMechanism {
    /// Stable census tag. Kept kebab-case and machine-greppable on purpose:
    /// this string is what a corpus scan buckets on.
    #[must_use]
    pub const fn tag(self) -> &'static str {
        match self {
            Self::AuthoredSourceRootUnbounded => "authored-source-root-unbounded",
            Self::AuthoredSourceAggregateBudget => "authored-source-aggregate-budget",
            Self::AuthoredSourceRootCount => "authored-source-root-count",
            Self::PreprocessorFoldToFalseUnrecorded => "preprocessor-fold-to-false",
        }
    }

    /// One sentence naming the machinery that would close this gap.
    #[must_use]
    pub const fn explanation(self) -> &'static str {
        match self {
            Self::AuthoredSourceRootUnbounded => {
                "an authored assertion exceeds the per-root surface bound, so no proof pass can render it"
            }
            Self::AuthoredSourceAggregateBudget => {
                "authored roots are individually renderable but the aggregate source-work envelope cannot afford the build pass"
            }
            Self::AuthoredSourceRootCount => {
                "the query has more authored assertion roots than proof reconstruction admits"
            }
            Self::PreprocessorFoldToFalseUnrecorded => {
                "preprocessing refuted an authored assertion by folding it to `false` and kept no derivation for the rewrite"
            }
        }
    }
}
