// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Lazily-materialized proof certificate for UNSAT results (Phase 4a, #8077).
//!
//! A `ProofCertificate` is intended to accompany every UNSAT result from the
//! SAT solver. [`SatResult::Unsat`](crate::SatResult::Unsat) carries one. The
//! solver reconstructs its LRAT dependencies during UNSAT finalization; public
//! [`ProofStep`] conversion stays lazy until a consumer requests it.
//!
//! ## Design
//!
//! The certificate holds the LRAT steps from backward reconstruction. On first
//! access, the proof is materialized into a sequence of [`ProofStep`] values
//! and cached via `OnceCell`. Subsequent accesses return the cached result.
//!
//! ## Authority
//!
//! This type is reconstruction data, not an independently checked proof bound
//! to a particular CNF. [`ProofCompleteness`] describes only whether the
//! producer observed a gap while reconstructing its step stream. Consumers
//! that need proof authority must check the steps against the intended original
//! clauses and bind that checker verdict to those clauses.

use std::cell::OnceCell;
use std::io::{self, Write};

use crate::literal::Literal;
use crate::solver::backward_proof::LratStep;

mod completeness;
mod lrat_text;

pub use completeness::ProofCompleteness;
use lrat_text::parse_lrat_text_addition;

/// A single LRAT proof step in a materialized proof certificate.
///
/// Each step represents a derived clause and the clause IDs of its antecedents
/// (the hints that an LRAT checker needs to verify the derivation).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ProofStep {
    /// The clause ID of the derived clause.
    pub clause_id: u64,
    /// The literals of the derived clause (empty for the contradiction step).
    pub literals: Vec<Literal>,
    /// The clause IDs of the antecedent clauses (LRAT hints).
    /// Positive values are clause-ID references for RUP checking.
    /// Negative values mark RAT witness boundaries / deletion steps
    /// (needed for extended resolution and blocked clause proofs).
    pub hints: Vec<i64>,
}

impl ProofStep {
    /// Convert to DIMACS literal representation for output.
    pub(crate) fn dimacs_literals(&self) -> Vec<i32> {
        self.literals.iter().map(|lit| lit.to_dimacs()).collect()
    }
}

impl From<LratStep> for ProofStep {
    fn from(step: LratStep) -> Self {
        Self {
            clause_id: step.clause_id,
            literals: step.literals,
            hints: step.hints,
        }
    }
}

/// A lazily-materialized proof certificate.
///
/// Always present on [`SatResult::Unsat`](crate::SatResult::Unsat). Backward
/// reconstruction has already run; [`materialize()`](Self::materialize) lazily
/// converts those retained steps into the stable public representation used by
/// exporters.
///
/// # Zero-cost path
///
/// If the consumer never inspects the proof, public-step allocation and
/// conversion are avoided. [`is_deferred()`](Self::is_deferred) reports that
/// materialization state, not whether backward reconstruction ran.
///
/// # Thread safety
///
/// `ProofCertificate` uses `OnceCell` (not `OnceLock`) and is therefore `!Sync`.
/// This is intentional: SAT solver results are typically consumed on a single
/// thread. If cross-thread sharing is needed, wrap in `Arc<Mutex<_>>`.
pub struct ProofCertificate {
    /// LRAT proof steps, lazily materialized from `lrat_steps`.
    steps: OnceCell<Vec<ProofStep>>,
    /// Pre-computed proof steps from backward reconstruction.
    lrat_steps: Vec<LratStep>,
    /// Whether backward reconstruction completed without a known gap.
    completeness: ProofCompleteness,
    /// Streaming support: original clause IDs observed while conflicts were
    /// analyzed. This may include clauses outside the terminal refutation.
    streaming_support: Option<Vec<u64>>,
}

impl std::fmt::Debug for ProofCertificate {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("ProofCertificate")
            .field("materialized", &self.steps.get().is_some())
            .field("completeness", &self.completeness)
            .field(
                "streaming_support",
                &self.streaming_support.as_ref().map(Vec::len),
            )
            .finish()
    }
}

impl Clone for ProofCertificate {
    fn clone(&self) -> Self {
        let new = Self {
            steps: OnceCell::new(),
            lrat_steps: self.lrat_steps.clone(),
            completeness: self.completeness,
            streaming_support: self.streaming_support.clone(),
        };
        if let Some(steps) = self.steps.get() {
            let _ = new.steps.set(steps.clone());
        }
        new
    }
}

impl ProofCertificate {
    /// Create a proof certificate from already-materialized proof steps.
    ///
    /// This is used by proof exporters that need to preserve the exact
    /// proof-visible LRAT stream rather than the deferred backward-only steps.
    /// `completeness` records the producer's reconstruction status; this
    /// constructor does not validate the derivations.
    #[must_use]
    pub(crate) fn from_materialized_steps(
        steps: Vec<ProofStep>,
        completeness: ProofCompleteness,
    ) -> Self {
        let cert = Self {
            steps: OnceCell::new(),
            lrat_steps: Vec::new(),
            completeness,
            streaming_support: None,
        };
        let _ = cert.steps.set(steps);
        cert
    }

    /// Parse text LRAT additions into a materialized proof certificate.
    ///
    /// Deletion lines are ignored because `ProofCertificate` represents the
    /// retained addition stream used by Lean4/Alethe exporters.
    ///
    /// # Errors
    ///
    /// Returns [`io::ErrorKind::InvalidData`] if the LRAT text is malformed.
    /// Parsing does not check the proof against a CNF, so the returned
    /// certificate is marked [`ProofCompleteness::NotEstablished`]. Only
    /// the solver-owned reconstruction path can mint complete metadata.
    pub fn from_lrat_text(bytes: &[u8]) -> io::Result<Self> {
        let text = std::str::from_utf8(bytes).map_err(|err| {
            io::Error::new(
                io::ErrorKind::InvalidData,
                format!("LRAT proof is not UTF-8 text: {err}"),
            )
        })?;

        let mut steps = Vec::new();
        for (line_idx, line) in text.lines().enumerate() {
            let trimmed = line.trim();
            if trimmed.is_empty() || trimmed.starts_with('c') {
                continue;
            }
            if let Some(step) = parse_lrat_text_addition(trimmed, line_idx + 1)? {
                steps.push(step);
            }
        }
        Ok(Self::from_materialized_steps(
            steps,
            ProofCompleteness::NotEstablished,
        ))
    }

    /// Create a proof certificate from pre-computed backward reconstruction results.
    ///
    /// This is the primary constructor used by the solver after calling
    /// `reconstruct_lrat_backward()`. The proof steps are not materialized
    /// until explicitly requested.
    pub(crate) fn from_backward_result(
        lrat_steps: Vec<LratStep>,
        completeness: ProofCompleteness,
    ) -> Self {
        Self {
            steps: OnceCell::new(),
            lrat_steps,
            completeness,
            streaming_support: None,
        }
    }

    /// Attach pre-computed streaming original-clause support (#8250).
    ///
    /// The support is a sorted, deduplicated list accumulated across conflict
    /// analyses. It is an over-approximation, not a minimal UNSAT core.
    pub(crate) fn set_streaming_support(&mut self, support: Vec<u64>) {
        self.streaming_support = Some(support);
    }

    /// Create an empty proof certificate (placeholder for cases where no proof
    /// data is available, e.g., UNSAT detected during preprocessing).
    pub fn empty() -> Self {
        Self::from_backward_result(Vec::new(), ProofCompleteness::NotEstablished)
    }

    /// Materialize the full LRAT proof. First call converts the raw LRAT steps
    /// into proof steps; subsequent calls return the cached result.
    #[must_use]
    pub fn materialize(&self) -> &[ProofStep] {
        self.steps.get_or_init(|| {
            self.lrat_steps
                .iter()
                .cloned()
                .map(ProofStep::from)
                .collect()
        })
    }

    /// Write LRAT proof to the given writer.
    ///
    /// LRAT format: `clause_id lit1 lit2 ... 0 hint1 hint2 ... 0`
    ///
    /// Materializes the proof if not already done.
    pub fn write_lrat(&self, w: &mut dyn Write) -> io::Result<()> {
        let steps = self.materialize();
        for step in steps {
            write!(w, "{} ", step.clause_id)?;
            for dimacs_lit in step.dimacs_literals() {
                write!(w, "{dimacs_lit} ")?;
            }
            write!(w, "0 ")?;
            for &hint in &step.hints {
                write!(w, "{hint} ")?;
            }
            writeln!(w, "0")?;
        }
        Ok(())
    }

    /// Write DRAT proof (LRAT without clause IDs or hints) to the given writer.
    ///
    /// DRAT format: `lit1 lit2 ... 0`
    ///
    /// Materializes the proof if not already done.
    pub fn write_drat(&self, w: &mut dyn Write) -> io::Result<()> {
        let steps = self.materialize();
        for step in steps {
            for dimacs_lit in step.dimacs_literals() {
                write!(w, "{dimacs_lit} ")?;
            }
            writeln!(w, "0")?;
        }
        Ok(())
    }

    /// Number of proof steps (materializes if needed).
    #[must_use]
    pub fn step_count(&self) -> usize {
        self.materialize().len()
    }

    /// Returns true if the proof has not yet been materialized (zero cost path).
    #[must_use]
    pub fn is_deferred(&self) -> bool {
        self.steps.get().is_none()
    }

    /// Return the producer's reconstruction status.
    ///
    /// This does not say that an independent checker accepted the proof.
    #[must_use]
    pub const fn completeness(&self) -> ProofCompleteness {
        self.completeness
    }

    /// Returns true if the producer reported complete backward reconstruction.
    ///
    /// This is reconstruction metadata, not an independent checker verdict;
    /// see [`Self::completeness`].
    #[must_use]
    pub const fn is_complete(&self) -> bool {
        self.completeness.is_complete()
    }

    /// Return clause IDs tracked or syntactically classified as original support.
    ///
    /// When streaming support is present, this returns the original IDs observed
    /// across conflict analyses. Otherwise it scans every retained proof step
    /// and returns positive hint IDs that are not produced by another retained
    /// step. The result is sorted and deduplicated. On an incomplete stream, a
    /// missing derived step is indistinguishable from an original clause, so
    /// this fallback may include IDs that were actually derived.
    ///
    /// This is deliberately an over-approximate, syntactic support set. It may
    /// include redundant hints, unrelated retained branches, or conflicts that
    /// do not lie on a terminal refutation. It does not validate the proof,
    /// establish that an empty clause exists, bind IDs to a CNF, or prove that
    /// the selected clauses are themselves unsatisfiable. An empty result means
    /// only that no support IDs were tracked.
    ///
    /// [`ProofCompleteness::Complete`] does not strengthen these semantics; it
    /// reports producer reconstruction status, not checker acceptance.
    #[must_use]
    pub fn tracked_original_clause_ids(&self) -> Vec<u64> {
        // Fast path: streaming support was accumulated during conflict analysis.
        if let Some(ref support) = self.streaming_support {
            return support.clone();
        }

        // Fallback: classify hints across the entire retained step stream.
        let steps = self.materialize();
        if steps.is_empty() {
            return Vec::new();
        }

        // Build set of derived clause IDs (clauses produced by proof steps).
        let derived: crate::kani_compat::DetHashSet<u64> =
            steps.iter().map(|s| s.clause_id).collect();

        // Collect positive hint IDs not derived in the retained stream. An
        // incomplete stream may make a missing derived ID look original.
        // Negative hints are RAT witness boundaries / deletion markers and are
        // ignored for support extraction.
        let mut original_ids: Vec<u64> = steps
            .iter()
            .flat_map(|s| s.hints.iter().copied())
            .filter(|&id| id > 0)
            .map(|id| id as u64)
            .filter(|&id| !derived.contains(&id))
            .collect();

        original_ids.sort_unstable();
        original_ids.dedup();
        original_ids
    }

    /// Whether streaming original-clause support is available (#8250).
    ///
    /// When true, [`Self::tracked_original_clause_ids`] returns that support
    /// without materializing the proof steps.
    #[must_use]
    pub fn has_streaming_support(&self) -> bool {
        self.streaming_support.is_some()
    }

    /// Write the LRAT proof as a Lean4 proof script (#8253).
    ///
    /// This is the *data-only* emitter: it produces parseable Lean4 that
    /// encodes the proof as data but asserts no soundness claim (no theorem
    /// is emitted). For a soundness-grounded UNSAT theorem, use
    /// [`write_lean4_verified`](Self::write_lean4_verified), which requires the
    /// original clause table and the verified `AySoundness` project.
    ///
    /// Delegates to `crate::lean_export::write_lean4_lrat()`.
    pub fn write_lean4(&self, w: &mut dyn Write) -> io::Result<()> {
        let steps = self.materialize();
        crate::lean_export::write_lean4_lrat(steps, w)
    }

    /// Write a self-contained Lean4 checker-acceptance artifact.
    ///
    /// Emits a self-contained Lean4 file that defines a propositional RUP
    /// checker, encodes the original clauses + proof steps, and asserts
    /// `theorem proof_valid : lratCheck originalClauses proofSteps = true
    /// := by native_decide`. Running `lean <file.lean4>` exits with
    /// status 1 if that embedded checker returns false. This does **not** prove
    /// that checker acceptance implies UNSAT; it is not verdict authority. Use
    /// [`Self::write_lean4_verified`] for the soundness theorem.
    ///
    /// # Arguments
    ///
    /// * `original_clauses` - slice of `(clause_id, dimacs_literals)` for
    ///   every input clause referenced by the proof. The caller is
    ///   responsible for ensuring every hint clause-id is either produced
    ///   by a proof step or present in this table.
    /// * `w` - output destination.
    ///
    /// # Errors
    ///
    /// Returns [`io::Error`] if writing fails.
    ///
    /// Delegates to `crate::lean_export::write_lean4_lrat_kernel()`.
    pub fn write_lean4_kernel(
        &self,
        original_clauses: &[(u64, Vec<i32>)],
        w: &mut dyn Write,
    ) -> io::Result<()> {
        let steps = self.materialize();
        crate::lean_export::write_lean4_lrat_kernel(original_clauses, steps, w)
    }

    /// Write a Lean4 UNSAT proof GROUNDED in the machine-checked
    /// `AySoundness.lratCheck_sound` (see `verification/lean/`). Unlike
    /// [`Self::write_lean4_kernel`] (self-contained, unverified `lratCheck`),
    /// the emitted file `import`s the verified checker and concludes
    /// `theorem unsat : Unsat (clauses original)`, so soundness rests only on
    /// the verified checker + Lean's kernel. Must be checked with the
    /// `AySoundness` library on `LEAN_PATH`. Delegates to
    /// `crate::lean_export::write_lean4_verified()`.
    ///
    /// # Errors
    /// Returns [`io::Error`] if writing fails.
    pub fn write_lean4_verified(
        &self,
        original_clauses: &[(u64, Vec<i32>)],
        w: &mut dyn Write,
    ) -> io::Result<()> {
        let steps = self.materialize();
        crate::lean_export::write_lean4_verified(original_clauses, steps, w)
    }

    /// Refuse the retired SAT-level Alethe adapter.
    ///
    /// A `ProofCertificate` does not retain the literals of original DIMACS
    /// clauses, so it cannot bind Alethe assumptions to the input problem.
    /// Earlier versions emitted `true` placeholders for those assumptions;
    /// that text was not proof authority. Use [`Self::write_lrat`] or
    /// [`Self::write_drat`] for independently checkable SAT evidence. This
    /// does not affect the input-bound SMT Alethe exporter in `ay-proof`.
    #[deprecated(
        note = "SAT Alethe export is unavailable without original DIMACS clauses; use write_lrat or write_drat"
    )]
    pub fn write_alethe(&self, w: &mut dyn Write) -> io::Result<()> {
        crate::alethe_export::refuse_unbound_alethe(w)
    }
}

#[cfg(test)]
#[path = "proof_certificate/tests.rs"]
mod tests;
