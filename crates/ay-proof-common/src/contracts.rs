// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// Dual-compilation contract stubs for VerifierConsumer verification.
//
// Under vanilla rustc (default): macros expand to nothing.
// Under VerifierConsumer with deductive-contracts: macros expand to nothing TODAY,
// but Phase 2 will replace them with real deductive_contract_macros attributes
// that the -Zverify pass picks up for VC generation.
//
// See the development design notes

#[allow(unused_macros)]
macro_rules! requires {
    ($($tt:tt)*) => {};
}

#[allow(unused_macros)]
macro_rules! ensures {
    ($($tt:tt)*) => {};
}

#[allow(unused_macros)]
macro_rules! invariant {
    ($($tt:tt)*) => {};
}

#[allow(unused_macros)]
macro_rules! decreases {
    ($($tt:tt)*) => {};
}

#[allow(unused_imports)]
pub(crate) use {decreases, ensures, invariant, requires};

// ---------------------------------------------------------------------------
// Propagation-redundancy (PR) functional contract — shared documentation anchor
// for the DPR/LPR symmetry-breaking emitter (the lex-leader SBP PR route).
// ---------------------------------------------------------------------------

/// The propagation-redundancy (PR) clause-addition contract (Heule–Kiesl–Biere,
/// "Short Proofs Without New Variables", CADE 2017).
///
/// A clause `C` is **PR-redundant** in a formula `F` with a *witness assignment*
/// `w` iff
///   1. `w ⊨ C` (the witness satisfies the added clause), and
///   2. for every clause `D ∈ F`: `F | α  ⊢_RUP  D | w`,
///      where `α = ¬C` is the assignment falsifying `C`.
///
/// PR generalises RAT: a RAT clause on pivot `p` is the special case where the
/// witness flips only `p`. The DRAT checker in `ay-drat-check` verifies RUP and
/// RAT only and therefore **must reject** a clause that is PR-but-not-RAT — it is
/// not in the checker's trusted fragment. The trust anchor for PR additions is an
/// external verified LPR checker (cake_lpr); a buggy emitter is *caught* (the
/// checker rejects), never silently trusted.
///
/// ## Symmetry-breaking instantiation (the lex-leader SBP)
///
/// For a verified formula automorphism `σ` (a permutation of the variables under
/// which `F` is invariant as a clause multiset) the lex-leader clause
/// `C = (x_{w_j} ∨ ¬x_{σ⁻¹(w_j)} ∨ …)` is PR with witness `w = σ(α)`, the image
/// of `α = ¬C` under `σ`:
///   * `w ⊨ C` because the σ-image of the negated deciding literal lands back on
///     the clause's own original-variable literal with satisfying polarity, and
///   * `F | α` and `F | w` are isomorphic under `σ` (an automorphism), so the
///     required RUP entailments hold.
///
/// This is sound **only when every literal of `C` lies in `σ`'s support** (i.e.
/// the clause is *aux-free*): fresh equal-prefix Tseitin aux variables `e_j` are
/// outside `σ`'s domain, so the σ-image witness does not constrain them and the
/// clause is not certifiable by this construction alone. Those aux-carrying lex
/// clauses (and the `e_j ↔ prefix-equal` definitions) must be emitted on the
/// RAT/blocked route instead (the `#8011` tower concern): only the aux-free lex
/// clauses carry `σ` as a PR witness.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PrRedundancyContract;

impl PrRedundancyContract {
    /// Necessary syntactic precondition for the σ-image PR witness to be valid:
    /// the witness must satisfy the clause via at least one shared literal, and
    /// the clause must be non-empty. This is *not* a full PR verification (that is
    /// the external LPR checker's job) — it is the cheap local guard the emitter
    /// applies before writing a PR `a`-line, so a structurally malformed witness
    /// is never emitted.
    ///
    /// `clause` and `witness` are DIMACS-signed literal lists.
    #[must_use]
    pub fn witness_satisfies_clause(clause: &[i32], witness: &[i32]) -> bool {
        !clause.is_empty() && clause.iter().any(|c| witness.contains(c))
    }
}
