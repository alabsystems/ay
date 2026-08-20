// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The justification registry: one place that answers "why may this UNSAT
//! publish?".
//!
//! # Why this exists
//!
//! A quantified UNSAT is refused unless something independent of the
//! (possibly unsound) instance-driven derivation vouches for it. Historically
//! each gate hand-rolled its own answer, so a single logical property had to be
//! re-encoded at every gate that could benefit from it. That is not a
//! stylistic complaint — it is a measured defect. The property "this refutation
//! does not depend on any quantifier instance" had to be written TWICE, at
//! `quantified_semantic_unsat_or_unknown` and again at the CEGQI clash gate,
//! before the #8759-era ghost-pair obligation could publish; a gate that had
//! not been taught the property kept failing closed on a verdict two of its
//! siblings would have accepted.
//!
//! A registry makes the property the unit of reuse instead of the gate:
//! establish each justification ONCE, and let every gate consult the same set.
//! The next gate that needs one costs a call, not a re-derivation.
//!
//! # What a justification is (and is not)
//!
//! Each variant names an INDEPENDENT reason the verdict holds — independent in
//! the strict sense that it does not rest on the enclosing solve's instance
//! set. None of them is a rescue of a doubted verdict: each is a separate
//! derivation that happens to reach the same conclusion. Consulting the
//! registry therefore never widens what publishes; it only stops a gate from
//! discarding a verdict some OTHER gate could already have justified.
//!
//! Every leg fails closed. `establish` returns `None` when nothing applies, and
//! the caller must then degrade exactly as it did before.

use super::Executor;
use crate::logic_detection::LogicCategory;
use ay_core::TermId;

/// An independent reason a quantified UNSAT may be published.
///
/// Ordered cheapest-first in [`Justification::establish`]: every variant below
/// the first hit costs nothing, which matters because these run on the
/// rejection path of a MANDATORY gate (see the certification-cost accounting —
/// the mint is cheap except where it reaches a whole-problem re-solve).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(in crate::executor) enum Justification {
    /// The AUTHORED quantifier-free conjuncts refute on their own.
    ///
    /// Entailment: dropping hypotheses only weakens, so a refutation of a
    /// SUBSET of the authored assertions refutes the authored problem. No
    /// instance and no CE lemma participates, so an instance-driven gate's
    /// concerns are simply inapplicable.
    AuthoredGroundCore,
    /// The quantifier-free core of the pre-instantiation snapshot refutes.
    ///
    /// Weaker provenance than [`Self::AuthoredGroundCore`] (a snapshot, not the
    /// authored roots), so it is consulted second and only where the caller
    /// already holds a snapshot it trusts.
    SnapshotGroundCore,
    /// The core PLUS the instance closure of UNCONDITIONALLY-asserted foralls
    /// refutes. Universal instantiation entails each such instance, so they
    /// hold in every model.
    InstanceClosure,
}

impl Justification {
    /// Consult the registry. `snapshot` is the pre-instantiation view when the
    /// caller has one; `None` disables the two snapshot-provenance legs.
    ///
    /// Cheapest-first and short-circuiting. Returns `None` when no
    /// justification applies — the caller MUST then fail closed unchanged.
    pub(in crate::executor) fn establish(
        exec: &mut Executor,
        snapshot: Option<&[TermId]>,
        category: LogicCategory,
    ) -> Option<Self> {
        if exec.authored_ground_core_refutes() {
            return Some(Self::AuthoredGroundCore);
        }
        let snapshot = snapshot?;
        // Owned: the probes below take `&mut Executor`.
        let snapshot = snapshot.to_vec();
        if exec.ground_core_is_unsat(&snapshot, category) {
            return Some(Self::SnapshotGroundCore);
        }
        if exec.instance_closure_ground_unsat(&snapshot, category) {
            return Some(Self::InstanceClosure);
        }
        None
    }

    /// Stable tag for diagnostics and the certification accounting.
    pub(in crate::executor) fn tag(self) -> &'static str {
        match self {
            Self::AuthoredGroundCore => "authored-ground-core",
            Self::SnapshotGroundCore => "snapshot-ground-core",
            Self::InstanceClosure => "instance-closure",
        }
    }
}
