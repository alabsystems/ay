// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Solve result types.

use ay_sat::proof_certificate::ProofCertificate;
use ay_sat::SatResult;

use crate::executor::{SatCertificate, UnsatCertificate};

/// SMT-level proof certificate wrapping the SAT-level [`ProofCertificate`].
///
/// Always present on `SolveResult::Unsat`. Like the SAT certificate, proof
/// materialization is lazy: no reconstruction work occurs until the consumer
/// explicitly requests it via [`sat_certificate()`](Self::sat_certificate).
/// Some independently checked semantic UNSAT lanes have no LRAT derivation;
/// those carry the existing explicitly-incomplete empty payload, while
/// [`VerifiedSolveResult`] separately records the exact certification kind and
/// never reports strict-proof verification for them.
///
/// # Zero-cost path
///
/// If the consumer never inspects the proof, no reconstruction work is
/// performed beyond the reference-counted wrapper.
#[derive(Debug, Clone)]
pub struct SmtProofCertificate {
    /// The underlying SAT-level proof certificate.
    sat_cert: ProofCertificate,
}

impl std::fmt::Display for SmtProofCertificate {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let complete = self.sat_cert.is_complete();
        let materialized = !self.sat_cert.is_deferred();
        if materialized {
            let steps = self.sat_cert.materialize();
            write!(
                f,
                "SmtProofCertificate({} clauses, LRAT {})",
                steps.len(),
                if complete { "complete" } else { "incomplete" },
            )
        } else {
            write!(
                f,
                "SmtProofCertificate(deferred, LRAT {})",
                if complete { "complete" } else { "incomplete" },
            )
        }
    }
}

impl SmtProofCertificate {
    /// Create an SMT proof certificate wrapping a SAT-level certificate.
    pub(crate) fn new(sat_cert: ProofCertificate) -> Self {
        Self { sat_cert }
    }

    /// Create an empty SMT proof certificate (placeholder for cases where
    /// no proof data is available, e.g., UNSAT detected during preprocessing).
    pub fn empty() -> Self {
        Self {
            sat_cert: ProofCertificate::empty(),
        }
    }

    /// Access the underlying SAT-level proof certificate.
    #[inline]
    pub fn sat_certificate(&self) -> &ProofCertificate {
        &self.sat_cert
    }

    /// Compute a proof-minimal UNSAT core from the LRAT proof certificate.
    ///
    /// Delegates to [`ProofCertificate::minimal_core()`] on the underlying
    /// SAT-level certificate. Returns a sorted, deduplicated list of original
    /// input clause IDs that were actually used in the UNSAT derivation.
    #[must_use]
    pub fn minimal_core(&self) -> Vec<u64> {
        self.sat_cert.minimal_core()
    }

    /// Write the LRAT proof as a Lean4 proof script (Phase 1, #8253).
    ///
    /// Delegates to [`ProofCertificate::write_lean4()`]. The output is a
    /// self-contained Lean4 file encoding the LRAT proof steps.
    pub fn write_lean4(&self, w: &mut dyn std::io::Write) -> std::io::Result<()> {
        self.sat_cert.write_lean4(w)
    }
}

/// Result of a satisfiability check
#[derive(Debug, Clone)]
#[non_exhaustive]
#[must_use = "solve results must be checked — ignoring Sat/Unsat loses correctness"]
pub enum SolveResult {
    /// The constraints are satisfiable
    Sat,
    /// The constraints are unsatisfiable, with a lazily-materialized proof
    /// certificate.
    ///
    /// The certificate is zero-cost when not consumed: proof reconstruction
    /// is deferred until the consumer requests it.
    Unsat(SmtProofCertificate),
    /// The solver could not determine satisfiability
    Unknown,
}

impl PartialEq for SolveResult {
    fn eq(&self, other: &Self) -> bool {
        matches!(
            (self, other),
            (Self::Sat, Self::Sat)
                | (Self::Unsat(_), Self::Unsat(_))
                | (Self::Unknown, Self::Unknown)
        )
    }
}

impl Eq for SolveResult {}

impl SolveResult {
    /// Returns true if the result is Sat
    #[inline]
    pub fn is_sat(&self) -> bool {
        matches!(self, Self::Sat)
    }

    /// Returns true if the result is Unsat
    #[inline]
    pub fn is_unsat(&self) -> bool {
        matches!(self, Self::Unsat(_))
    }

    /// Returns the proof certificate if the result is Unsat.
    #[inline]
    pub fn proof_certificate(&self) -> Option<&SmtProofCertificate> {
        match self {
            Self::Unsat(cert) => Some(cert),
            _ => None,
        }
    }

    /// Returns true if the result is Unknown
    #[inline]
    pub fn is_unknown(&self) -> bool {
        matches!(self, Self::Unknown)
    }

    /// Convenience constructor for UNSAT with an empty proof certificate.
    ///
    /// Useful in contexts where no proof data is available (e.g., theory
    /// conflicts detected outside the main solve loop, or in test code).
    #[inline]
    pub fn unsat() -> Self {
        Self::Unsat(SmtProofCertificate::empty())
    }
}

impl std::fmt::Display for SolveResult {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Sat => write!(f, "sat"),
            Self::Unsat(_) => write!(f, "unsat"),
            Self::Unknown => write!(f, "unknown"),
        }
    }
}

impl From<SatResult> for SolveResult {
    fn from(result: SatResult) -> Self {
        match result {
            SatResult::Sat(_) => Self::Sat,
            SatResult::Unsat(cert) => Self::Unsat(SmtProofCertificate::new(cert)),
            SatResult::Unknown => Self::Unknown,
            #[allow(unreachable_patterns)]
            _ => unreachable!(),
        }
    }
}

/// Error returned when a solve result is not acceptable at a consumer boundary.
#[derive(Debug, Clone, Copy, PartialEq, Eq, thiserror::Error)]
#[non_exhaustive]
pub enum ConsumerAcceptanceError {
    /// SAT was reported without a complete sealed model-evidence lane.
    #[error("sat result rejected at consumer boundary: model evidence was not admitted")]
    SatModelNotValidated,
}

/// A `SolveResult` admitted by one of the executor's sealed evidence lanes.
///
/// For `Sat` results, this records either that ordinary final model validation
/// passed or that the independently checked quantified-projection lane proved
/// and installed its exact total model. Consumers must inspect
/// [`was_model_validated()`](Self::was_model_validated) or call
/// [`accept_for_consumer()`](Self::accept_for_consumer) before treating a SAT
/// model as trusted. For `Unsat` results, a private one-shot certificate proves
/// either that the strict checker accepted the refutation against the exact
/// authored query epoch or that the separately classified exact semantic
/// theorem discharged its narrow integer-existential fragment. The shared
/// native result boundary publishes registered `Unknown` and revokes executor
/// artifacts before wrapping any definite verdict whose exact capability is
/// missing.
///
/// The private inner fields prevent construction outside ay-dpll.
/// Within the crate, every native solve route crosses the same
/// `Solver::finish_verified_result` boundary; only token-consuming constructors
/// can create definite variants.
///
/// A downstream crate cannot manufacture a validated SAT wrapper by choosing
/// its own validation bit:
///
/// ```compile_fail
/// use ay_dpll::api::{SolveResult, VerifiedSolveResult};
///
/// let fabricated = VerifiedSolveResult::for_testing(SolveResult::Sat, true);
/// # let _ = fabricated;
/// ```
///
/// Part of #5748: structural verification invariant Phase 3.
#[derive(Debug, Clone)]
#[must_use = "solver results must be checked — ignoring Sat/Unsat loses correctness"]
pub struct VerifiedSolveResult {
    result: SolveResult,
    model_validated: bool,
    /// Records that the one-shot `SatCertificate` was present when the result
    /// crossed the private validation boundary.  The capability itself is
    /// consumed rather than retained as proof-shaped state.
    sat_emission_witness: bool,
    /// Records that the one-shot `UnsatCertificate` was consumed at this
    /// boundary. The capability itself is never exposed or cloned.
    unsat_emission_witness: bool,
    /// Records the strict checker claim separately for diagnostics. This bit
    /// can be set only by consuming the strict exact-query token.
    unsat_strictly_verified: bool,
    /// Records an independently checked SAT-refutation or fully discharged
    /// trust-family proof separately from literal strict-checker acceptance.
    unsat_independently_verified: bool,
    /// Records the narrow exact semantic theorem lane separately from strict
    /// proof checking. This is never inferred from an empty proof payload.
    unsat_exact_semantically_verified: bool,
}

impl VerifiedSolveResult {
    /// Construct the public SAT wrapper by consuming the exact one-shot token
    /// minted by the model-validation publication funnel.
    pub(crate) fn certified_sat(_certificate: SatCertificate) -> Self {
        Self {
            result: SolveResult::Sat,
            model_validated: true,
            sat_emission_witness: true,
            unsat_emission_witness: false,
            unsat_strictly_verified: false,
            unsat_independently_verified: false,
            unsat_exact_semantically_verified: false,
        }
    }

    /// Construct a certified public UNSAT wrapper by consuming its exact-query
    /// one-shot token. The token keeps literal strict-proof acceptance,
    /// independently checked refutations, and the narrow semantic theorem
    /// mutually exclusive.
    pub(crate) fn certified_unsat(
        result: SmtProofCertificate,
        certificate: UnsatCertificate,
    ) -> Self {
        let unsat_strictly_verified = certificate.strict_proof_verified();
        let unsat_independently_verified = certificate.independently_verified();
        let unsat_exact_semantically_verified = certificate.exact_semantic_verified();
        debug_assert_eq!(
            usize::from(unsat_strictly_verified)
                + usize::from(unsat_independently_verified)
                + usize::from(unsat_exact_semantically_verified),
            1
        );
        Self {
            result: SolveResult::Unsat(result),
            model_validated: false,
            sat_emission_witness: false,
            unsat_emission_witness: true,
            unsat_strictly_verified,
            unsat_independently_verified,
            unsat_exact_semantically_verified,
        }
    }

    /// Construct a public Unknown wrapper. Definite verdicts deliberately have
    /// no token-free constructor.
    pub(crate) fn unknown() -> Self {
        Self {
            result: SolveResult::Unknown,
            model_validated: false,
            sat_emission_witness: false,
            unsat_emission_witness: false,
            unsat_strictly_verified: false,
            unsat_independently_verified: false,
            unsat_exact_semantically_verified: false,
        }
    }

    /// Construct a `VerifiedSolveResult` for in-crate consumer-boundary tests
    /// (#8725).
    ///
    /// **Testing only.** This bypasses the internal model validation pipeline
    /// and is intended for tests that need to exercise the
    /// [`accept_for_consumer`](Self::accept_for_consumer) boundary — e.g.,
    /// regression tests for FFI shims that must route SAT through the boundary
    /// rather than calling [`result`](Self::result) directly.
    ///
    /// This constructor is deliberately absent from normal library builds: a
    /// public caller-chosen `model_validated` bit would let downstream code
    /// fabricate a trusted-looking SAT result without a private
    /// [`SatCertificate`] capability minted by a complete emission lane.
    #[cfg(test)]
    pub(crate) fn for_testing(result: SolveResult, model_validated: bool) -> Self {
        Self {
            result,
            model_validated,
            sat_emission_witness: false,
            unsat_emission_witness: false,
            unsat_strictly_verified: false,
            unsat_independently_verified: false,
            unsat_exact_semantically_verified: false,
        }
    }

    /// Whether complete sealed SAT-witness evidence exists for this result.
    ///
    /// For a SAT query with no assertions/assumptions this is explicit vacuous
    /// evidence, recorded only after the final output-visible unconstrained
    /// model has been completed. Other SAT results require either the ordinary
    /// validation gates, the checked total-projection evidence lane, or the
    /// exact-exists semantic theorem lane.
    #[inline]
    pub fn was_model_validated(&self) -> bool {
        self.model_validated
    }

    /// Whether this result crossed the #sat-chokepoint with its one-shot
    /// emission witness present.
    ///
    /// `true` iff construction consumed an unforgeable [`SatCertificate`]
    /// minted either by the ordinary validation funnel or by the independently
    /// checked quantified-projection funnel. The token is not retained or
    /// cloned; only its presence at the boundary is recorded. The test-only
    /// [`for_testing`](Self::for_testing) bypass records `false`.
    #[inline]
    #[must_use]
    pub fn has_sat_emission_witness(&self) -> bool {
        self.sat_emission_witness
    }

    /// Whether this UNSAT result crossed the exact-query publication boundary
    /// with a sealed one-shot certification capability.
    #[inline]
    #[must_use]
    pub fn has_unsat_emission_witness(&self) -> bool {
        self.unsat_emission_witness
    }

    /// Whether this UNSAT result carries a refutation accepted by the strict
    /// proof checker for the exact authored query epoch.
    #[inline]
    #[must_use]
    pub fn was_unsat_strictly_verified(&self) -> bool {
        self.unsat_strictly_verified
    }

    /// Whether this UNSAT result was established by an independently checked
    /// SAT-level refutation or by complete discharge of the proof's trust-family
    /// steps, after the ordinary strict checker declined that proof.
    #[inline]
    #[must_use]
    pub fn was_unsat_independently_verified(&self) -> bool {
        self.unsat_independently_verified
    }

    /// Whether this UNSAT result was established by the narrow, independently
    /// checked exact integer-existential theorem rather than by the ordinary
    /// strict proof checker.
    #[inline]
    #[must_use]
    pub fn was_unsat_exact_semantically_verified(&self) -> bool {
        self.unsat_exact_semantically_verified
    }

    /// Get the underlying solve result.
    #[inline]
    pub fn result(&self) -> &SolveResult {
        &self.result
    }

    /// Accept this solve result at a consumer-facing boundary.
    ///
    /// High-level consumers must call this before surfacing a SAT model or
    /// counterexample as trusted. SAT results where model validation did not
    /// run are rejected.
    #[must_use = "consumer boundaries must check whether SAT is acceptable before surfacing a model"]
    #[inline]
    pub fn accept_for_consumer(&self) -> Result<&SolveResult, ConsumerAcceptanceError> {
        match &self.result {
            SolveResult::Sat if !self.model_validated => {
                Err(ConsumerAcceptanceError::SatModelNotValidated)
            }
            _ => Ok(&self.result),
        }
    }

    /// Returns true if the result is Sat.
    #[inline]
    pub fn is_sat(&self) -> bool {
        self.result.is_sat()
    }

    /// Returns true if the result is Unsat.
    #[inline]
    pub fn is_unsat(&self) -> bool {
        self.result.is_unsat()
    }

    /// Returns true if the result is Unknown.
    #[inline]
    pub fn is_unknown(&self) -> bool {
        self.result.is_unknown()
    }

    /// Consume and return the inner `SolveResult`.
    ///
    /// **Trust boundary:** The returned `SolveResult` carries no compile-time
    /// proof of verification. Verification happened at construction time (via
    /// the executor's model validation pipeline). Prefer using
    /// [`.accept_for_consumer()`](Self::accept_for_consumer) at public
    /// boundaries, or [`.result()`](Self::result) / [`.is_sat()`](Self::is_sat)
    /// / [`.is_unsat()`](Self::is_unsat) when you explicitly need the raw
    /// diagnostic state.
    #[inline]
    pub fn into_inner(self) -> SolveResult {
        self.result
    }
}

impl std::fmt::Display for VerifiedSolveResult {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.result.fmt(f)
    }
}

impl PartialEq<SolveResult> for VerifiedSolveResult {
    fn eq(&self, other: &SolveResult) -> bool {
        self.result == *other
    }
}

impl PartialEq<VerifiedSolveResult> for SolveResult {
    fn eq(&self, other: &VerifiedSolveResult) -> bool {
        *self == other.result
    }
}

impl PartialEq for VerifiedSolveResult {
    fn eq(&self, other: &Self) -> bool {
        self.result == other.result
    }
}

impl Eq for VerifiedSolveResult {}

/// Convenience for constructing `SolveResult::Unsat` in tests.
#[cfg(test)]
impl SolveResult {
    /// Create an `Unsat` result with an empty proof certificate (for tests).
    pub fn unsat_for_test() -> Self {
        Self::Unsat(SmtProofCertificate::empty())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn token_free_constructor_can_only_build_unknown() {
        let result = VerifiedSolveResult::unknown();
        assert!(result.is_unknown());
        assert!(!result.was_model_validated());
        assert!(!result.has_unsat_emission_witness());
        assert!(!result.was_unsat_strictly_verified());
        assert!(!result.was_unsat_independently_verified());
        assert!(!result.was_unsat_exact_semantically_verified());
        assert_eq!(result.accept_for_consumer(), Ok(&SolveResult::Unknown));
    }
}
