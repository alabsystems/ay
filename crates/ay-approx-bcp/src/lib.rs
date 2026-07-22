// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! `ay-approx-bcp` — standalone approximate BCP filter kernel.
//!
//! The crate exposes a small pure-function API and has no dependency on
//! `ay-sat`.  `ay-sat` can run it behind the `approx-bcp-filter` feature
//! as a measurement-only observer; that integration does not yet skip
//! solver work based on the approximate verdict.
//!
//! # Model
//!
//! Each literal `l` (encoded as a signed DIMACS integer) is hashed to a
//! single bit position in a 64-bit word via a splitmix-style mixer.
//! Two running bitmaps drive the filter:
//!
//! * [`ClauseSignature`] — per-clause `OR` of `bit(l)` for each literal
//!   `l` in the clause.
//! * [`AssignmentMask`] — `OR` of `bit(l)` for every literal `l` that is
//!   *currently falsified* by the assignment (i.e., the negation of `l`
//!   is assigned true on the SAT trail).
//!
//! The filter computes `popcount(clause_sig & !assignment)`.  When the
//! assignment mask contains the signature bit of every currently
//! falsified literal, this popcount is a lower bound on the number of
//! clause literals that are **not** currently falsified.  Hash
//! collisions can only reduce it.
//!
//! > If the clause is *actually* unit or falsified under the current
//! > assignment, then `popcount(clause_sig & !assignment) ≤ 1`.
//!
//! So returning "maybe unit or falsified" (`true`) whenever the popcount
//! is ≤ 1 cannot miss a real unit or conflict; it only over-approximates
//! the work queue handed to the exact BCP pass.  This guarantee depends
//! on rebuilding the lossy assignment mask after backtracking (or using
//! per-bit reference counts); clearing one colliding bit is not sound.
//!
//! See [`filter::may_be_unit_or_falsified`] for the scan kernel and
//! `tests` for a deterministic randomized soundness check.
//!
//! # Integration status
//!
//! * The feature-gated `ay-sat` observer rebuilds the assignment mask
//!   from the current trail and compares filter results with an exact
//!   classification.  It never changes a solver decision.
//! * Using the verdict to suppress BCP work remains future work and
//!   requires benchmark evidence plus the exact-mask invariant above.
//!
//! # Non-goals (explicitly deferred)
//!
//! * Dynamic re-hashing / 128-bit signatures.
//! * Heuristic cost-model gating on small formulas.

#![forbid(unsafe_code)]

pub mod filter;
pub mod metrics;
pub mod signature;

#[cfg(test)]
mod tests;

pub use filter::{may_be_unit_or_falsified, AssignmentMask};
pub use metrics::FilterMetrics;
pub use signature::{literal_bit, ClauseSignature};
