// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Lazily-materialized proof certificate for UNSAT results (Phase 4a, #8077).
//!
//! A `ProofCertificate` is intended to accompany every UNSAT result from the
//! SAT solver. The proof is not reconstructed until the consumer explicitly
//! requests it via [`ProofCertificate::materialize()`] or
//! [`ProofCertificate::write_lean4()`]. Crate-internal helpers
//! `write_lrat()` and `write_drat()` are also available for testing.
//!
//! This module defines the certificate type and its public API. The actual
//! integration with `SatResult::Unsat` is deferred to a later phase to avoid
//! a breaking API change.
//!
//! ## Design
//!
//! The certificate holds the LRAT steps from backward reconstruction. On first
//! access, the proof is materialized into a sequence of [`ProofStep`] values
//! and cached via `OnceCell`. Subsequent accesses return the cached result.

use std::cell::OnceCell;
use std::io::{self, Write};

use crate::literal::Literal;
use crate::solver::backward_proof::LratStep;

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
/// Always present on UNSAT results. The proof is not reconstructed
/// until the consumer explicitly requests it via [`materialize()`](Self::materialize)
/// or [`write_lean4()`](Self::write_lean4).
///
/// # Zero-cost path
///
/// If the consumer never inspects the proof (the common case in production),
/// no reconstruction work is performed. Call [`is_deferred()`](Self::is_deferred)
/// to check whether materialization has occurred.
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
    /// Whether the backward reconstruction was complete.
    complete: bool,
    /// Streaming UNSAT core: pre-computed set of original clause IDs that
    /// participated in the proof, tracked incrementally during conflict
    /// analysis (#8250). When `Some`, `minimal_core()` returns this directly
    /// instead of walking the proof DAG.
    streaming_core: Option<Vec<u64>>,
}

impl std::fmt::Debug for ProofCertificate {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("ProofCertificate")
            .field("materialized", &self.steps.get().is_some())
            .field("complete", &self.complete)
            .field(
                "streaming_core",
                &self.streaming_core.as_ref().map(Vec::len),
            )
            .finish()
    }
}

impl Clone for ProofCertificate {
    fn clone(&self) -> Self {
        let new = Self {
            steps: OnceCell::new(),
            lrat_steps: self.lrat_steps.clone(),
            complete: self.complete,
            streaming_core: self.streaming_core.clone(),
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
    #[must_use]
    pub fn from_materialized_steps(steps: Vec<ProofStep>, complete: bool) -> Self {
        let cert = Self {
            steps: OnceCell::new(),
            lrat_steps: Vec::new(),
            complete,
            streaming_core: None,
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
    pub fn from_lrat_text(bytes: &[u8], complete: bool) -> io::Result<Self> {
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
        Ok(Self::from_materialized_steps(steps, complete))
    }

    /// Create a proof certificate from pre-computed backward reconstruction results.
    ///
    /// This is the primary constructor used by the solver after calling
    /// `reconstruct_lrat_backward()`. The proof steps are not materialized
    /// until explicitly requested.
    pub(crate) fn from_backward_result(lrat_steps: Vec<LratStep>, complete: bool) -> Self {
        Self {
            steps: OnceCell::new(),
            lrat_steps,
            complete,
            streaming_core: None,
        }
    }

    /// Attach a pre-computed streaming UNSAT core to this certificate (#8250).
    ///
    /// The streaming core is a sorted, deduplicated list of original clause IDs
    /// that participated in the proof. When present, `minimal_core()` returns
    /// this directly instead of walking the proof DAG.
    pub(crate) fn set_streaming_core(&mut self, core: Vec<u64>) {
        self.streaming_core = Some(core);
    }

    /// Create an empty proof certificate (placeholder for cases where no proof
    /// data is available, e.g., UNSAT detected during preprocessing).
    pub fn empty() -> Self {
        Self::from_backward_result(Vec::new(), false)
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

    /// Returns true if the backward reconstruction was complete.
    ///
    /// A complete proof means all antecedent clauses were resolved. An
    /// incomplete proof may have gaps (e.g., clauses lost to garbage collection
    /// or binary clause reasons not yet tracked).
    #[must_use]
    pub fn is_complete(&self) -> bool {
        self.complete
    }

    /// Compute a proof-minimal UNSAT core from the LRAT proof certificate.
    ///
    /// Walks the proof DAG backward from the empty clause (the contradiction
    /// step), collecting all original input clause IDs that were actually used
    /// in the derivation. Original clauses are those whose clause IDs appear
    /// as hints in proof steps but are not themselves derived by any proof step.
    ///
    /// Returns a sorted, deduplicated list of original clause IDs that are
    /// necessary to derive the contradiction. This is a subset of the full set
    /// of input clauses and represents a proof-minimal UNSAT core.
    ///
    /// # Returns
    ///
    /// - An empty `Vec` if the proof is empty or contains no resolvable steps.
    /// - A subset of the original clause IDs if the proof is complete.
    /// - A possibly incomplete subset if the proof is incomplete (some
    ///   antecedent clauses were lost to garbage collection).
    ///
    /// # Algorithm
    ///
    /// 1. Build a set of all derived clause IDs (clause IDs that appear as the
    ///    `clause_id` field of a proof step).
    /// 2. Walk all proof steps, collecting hints (antecedent clause IDs).
    /// 3. Any hint that is NOT in the derived set is an original input clause.
    /// 4. Return the sorted, deduplicated set of original clause IDs.
    #[must_use]
    pub fn minimal_core(&self) -> Vec<u64> {
        // Fast path: streaming core is pre-computed during conflict analysis (#8250).
        // Returns immediately without materializing the proof DAG.
        if let Some(ref core) = self.streaming_core {
            return core.clone();
        }

        // Slow path: walk the proof DAG to extract original clause IDs.
        let steps = self.materialize();
        if steps.is_empty() {
            return Vec::new();
        }

        // Build set of derived clause IDs (clauses produced by proof steps).
        let derived: crate::kani_compat::DetHashSet<u64> =
            steps.iter().map(|s| s.clause_id).collect();

        // Collect all hint clause IDs that are NOT derived -- these are original
        // input clauses used in the proof. Negative hints are RAT witness
        // boundaries / deletion markers and are ignored for core extraction.
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

    /// Returns true if a streaming UNSAT core is available (#8250).
    ///
    /// When true, `minimal_core()` returns immediately without materializing
    /// the proof DAG.
    #[must_use]
    pub fn has_streaming_core(&self) -> bool {
        self.streaming_core.is_some()
    }

    /// Write the LRAT proof as a Lean4 proof script (#8253).
    ///
    /// This is the *data-only* emitter: it produces parseable Lean4 that
    /// encodes the proof as data but asserts no soundness claim (no theorem
    /// is emitted). For a kernel-checked proof, use
    /// [`write_lean4_kernel`](Self::write_lean4_kernel), which requires the
    /// original clause table.
    ///
    /// Delegates to `crate::lean_export::write_lean4_lrat()`.
    pub fn write_lean4(&self, w: &mut dyn Write) -> io::Result<()> {
        let steps = self.materialize();
        crate::lean_export::write_lean4_lrat(steps, w)
    }

    /// Write a kernel-checked Lean4 LRAT proof (#8697 Phase 1).
    ///
    /// Emits a self-contained Lean4 file that defines a propositional RUP
    /// checker, encodes the original clauses + proof steps, and asserts
    /// `theorem proof_valid : lratCheck originalClauses proofSteps = true
    /// := by native_decide`. Running `lean <file.lean4>` exits with
    /// status 1 if the proof is unsound.
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

    /// Write the LRAT proof as an Alethe proof (#8296).
    ///
    /// Converts LRAT resolution steps to Alethe format suitable for
    /// verification by carcara or clean certification pipelines.
    ///
    /// Delegates to `crate::alethe_export::write_alethe_lrat()`.
    pub fn write_alethe(&self, w: &mut dyn Write) -> io::Result<()> {
        let steps = self.materialize();
        crate::alethe_export::write_alethe_lrat(steps, w)
    }
}

fn invalid_lrat(line_number: usize, message: impl Into<String>) -> io::Error {
    io::Error::new(
        io::ErrorKind::InvalidData,
        format!(
            "malformed LRAT text at line {line_number}: {}",
            message.into()
        ),
    )
}

fn parse_lrat_text_addition(line: &str, line_number: usize) -> io::Result<Option<ProofStep>> {
    let tokens: Vec<&str> = line.split_whitespace().collect();
    if tokens.is_empty() {
        return Ok(None);
    }
    if tokens.len() >= 2 && tokens[1] == "d" {
        return Ok(None);
    }
    let clause_id = tokens[0]
        .parse::<u64>()
        .map_err(|err| invalid_lrat(line_number, format!("invalid clause id: {err}")))?;

    let first_zero = tokens
        .iter()
        .position(|&token| token == "0")
        .ok_or_else(|| invalid_lrat(line_number, "missing literal terminator 0"))?;
    if first_zero == 0 {
        return Err(invalid_lrat(
            line_number,
            "missing clause id before literals",
        ));
    }
    if tokens.last().copied() != Some("0") {
        return Err(invalid_lrat(line_number, "missing final hint terminator 0"));
    }

    let mut literals = Vec::with_capacity(first_zero.saturating_sub(1));
    for token in &tokens[1..first_zero] {
        let raw = token
            .parse::<i32>()
            .map_err(|err| invalid_lrat(line_number, format!("invalid literal: {err}")))?;
        if raw == 0 {
            return Err(invalid_lrat(line_number, "literal 0 before terminator"));
        }
        literals.push(Literal::from_dimacs(raw));
    }

    let mut hints = Vec::with_capacity(tokens.len().saturating_sub(first_zero + 2));
    for token in &tokens[first_zero + 1..tokens.len() - 1] {
        hints.push(
            token
                .parse::<i64>()
                .map_err(|err| invalid_lrat(line_number, format!("invalid hint: {err}")))?,
        );
    }

    Ok(Some(ProofStep {
        clause_id,
        literals,
        hints,
    }))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::literal::Variable;

    fn make_test_steps() -> Vec<LratStep> {
        let v0 = Variable(0);
        let v1 = Variable(1);
        vec![
            LratStep {
                clause_id: 4,
                literals: vec![Literal::positive(v0), Literal::negative(v1)],
                hints: vec![1i64, 2],
            },
            LratStep {
                clause_id: 5,
                literals: vec![Literal::negative(v0)],
                hints: vec![3i64, 4],
            },
            LratStep {
                clause_id: 6,
                literals: vec![],
                hints: vec![4i64, 5],
            },
        ]
    }

    #[test]
    fn test_proof_certificate_is_deferred_before_materialization() {
        let cert = ProofCertificate::from_backward_result(make_test_steps(), true);
        assert!(
            cert.is_deferred(),
            "certificate should be deferred before materialization"
        );
    }

    #[test]
    fn test_proof_certificate_not_deferred_after_materialization() {
        let cert = ProofCertificate::from_backward_result(make_test_steps(), true);
        let _ = cert.materialize();
        assert!(
            !cert.is_deferred(),
            "certificate should not be deferred after materialization"
        );
    }

    #[test]
    fn test_proof_certificate_materialize_returns_steps() {
        let cert = ProofCertificate::from_backward_result(make_test_steps(), true);
        let steps = cert.materialize();
        assert_eq!(steps.len(), 3);
        assert_eq!(steps[0].clause_id, 4);
        assert_eq!(steps[0].hints, vec![1i64, 2]);
        assert_eq!(steps[1].clause_id, 5);
        assert_eq!(steps[2].clause_id, 6);
        assert!(
            steps[2].literals.is_empty(),
            "last step should be empty clause"
        );
    }

    #[test]
    fn test_proof_certificate_materialize_is_idempotent() {
        let cert = ProofCertificate::from_backward_result(make_test_steps(), true);
        let steps1 = cert.materialize();
        let steps2 = cert.materialize();
        assert_eq!(steps1.len(), steps2.len());
        // Same pointer -- OnceCell caching
        assert!(std::ptr::eq(steps1, steps2));
    }

    #[test]
    fn test_proof_certificate_step_count() {
        let cert = ProofCertificate::from_backward_result(make_test_steps(), true);
        assert_eq!(cert.step_count(), 3);
        // After step_count, no longer deferred
        assert!(!cert.is_deferred());
    }

    #[test]
    fn test_proof_certificate_write_lrat_produces_output() {
        let cert = ProofCertificate::from_backward_result(make_test_steps(), true);
        let mut buf = Vec::new();
        cert.write_lrat(&mut buf)
            .expect("write_lrat should succeed");
        let output = String::from_utf8(buf).expect("should be valid UTF-8");
        assert!(!output.is_empty(), "LRAT output should not be empty");
        // Each line ends with "0\n" (the hint terminator)
        let lines: Vec<&str> = output.lines().collect();
        assert_eq!(lines.len(), 3, "should have 3 proof steps");
        // First line should start with clause_id 4
        assert!(
            lines[0].starts_with("4 "),
            "first line should start with clause ID 4, got: {}",
            lines[0]
        );
        // Last line should be for the empty clause (clause_id 6, no literals)
        assert!(
            lines[2].starts_with("6 0 "),
            "last line should start with '6 0 ' (empty clause), got: {}",
            lines[2]
        );
    }

    #[test]
    fn test_proof_certificate_write_drat_produces_output() {
        let cert = ProofCertificate::from_backward_result(make_test_steps(), true);
        let mut buf = Vec::new();
        cert.write_drat(&mut buf)
            .expect("write_drat should succeed");
        let output = String::from_utf8(buf).expect("should be valid UTF-8");
        assert!(!output.is_empty(), "DRAT output should not be empty");
        let lines: Vec<&str> = output.lines().collect();
        assert_eq!(lines.len(), 3, "should have 3 proof steps");
        // DRAT has no clause IDs or hints -- just literals terminated by 0
        // Last line should be "0" (empty clause, no literals)
        assert_eq!(
            lines[2].trim(),
            "0",
            "last line should be '0' (empty clause), got: {}",
            lines[2]
        );
    }

    #[test]
    fn test_proof_certificate_empty() {
        let cert = ProofCertificate::empty();
        assert!(cert.is_deferred());
        assert!(!cert.is_complete());
        assert_eq!(cert.step_count(), 0);
        assert!(!cert.is_deferred()); // step_count materialized it
    }

    #[test]
    fn test_proof_certificate_from_lrat_text_materializes_additions() {
        let lrat = b"3 1 0 1 0\n4 0 3 -2 0\n5 d 3 0\n";
        let cert = ProofCertificate::from_lrat_text(lrat, true).expect("valid LRAT text");
        let steps = cert.materialize();

        assert_eq!(steps.len(), 2);
        assert_eq!(steps[0].clause_id, 3);
        assert_eq!(steps[0].dimacs_literals(), vec![1]);
        assert_eq!(steps[0].hints, vec![1]);
        assert_eq!(steps[1].clause_id, 4);
        assert!(steps[1].literals.is_empty());
        assert_eq!(steps[1].hints, vec![3, -2]);
        assert!(cert.is_complete());
    }

    #[test]
    fn test_proof_certificate_from_lrat_text_rejects_missing_terminator() {
        let err = ProofCertificate::from_lrat_text(b"3 1 0 1\n", true)
            .expect_err("missing final 0 must fail");
        assert_eq!(err.kind(), io::ErrorKind::InvalidData);
    }

    #[test]
    fn test_proof_certificate_is_complete() {
        let complete = ProofCertificate::from_backward_result(make_test_steps(), true);
        assert!(complete.is_complete());

        let incomplete = ProofCertificate::from_backward_result(make_test_steps(), false);
        assert!(!incomplete.is_complete());
    }

    #[test]
    fn test_proof_certificate_debug_format() {
        let cert = ProofCertificate::from_backward_result(make_test_steps(), true);
        let debug_str = format!("{cert:?}");
        assert!(
            debug_str.contains("materialized: false"),
            "debug should show unmaterialized state"
        );
        let _ = cert.materialize();
        let debug_str = format!("{cert:?}");
        assert!(
            debug_str.contains("materialized: true"),
            "debug should show materialized state"
        );
    }

    #[test]
    fn test_proof_step_from_lrat_step() {
        let v0 = Variable(0);
        let lrat_step = LratStep {
            clause_id: 42,
            literals: vec![Literal::positive(v0)],
            hints: vec![10i64, 20],
        };
        let proof_step = ProofStep::from(lrat_step);
        assert_eq!(proof_step.clause_id, 42);
        assert_eq!(proof_step.literals.len(), 1);
        assert_eq!(proof_step.hints, vec![10i64, 20]);
    }

    #[test]
    fn test_minimal_core_extracts_original_clause_ids() {
        let cert = ProofCertificate::from_backward_result(make_test_steps(), true);
        let core = cert.minimal_core();
        assert_eq!(
            core,
            vec![1, 2, 3],
            "minimal core should contain original clause IDs 1, 2, 3"
        );
    }

    #[test]
    fn test_minimal_core_empty_proof() {
        let cert = ProofCertificate::empty();
        let core = cert.minimal_core();
        assert!(core.is_empty(), "empty proof should yield empty core");
    }

    #[test]
    fn test_minimal_core_single_step_no_hints() {
        let steps = vec![LratStep {
            clause_id: 1,
            literals: vec![],
            hints: vec![],
        }];
        let cert = ProofCertificate::from_backward_result(steps, true);
        let core = cert.minimal_core();
        assert!(
            core.is_empty(),
            "proof step with no hints should yield empty core"
        );
    }

    #[test]
    fn test_minimal_core_all_original() {
        let steps = vec![LratStep {
            clause_id: 10,
            literals: vec![],
            hints: vec![1i64, 2, 3],
        }];
        let cert = ProofCertificate::from_backward_result(steps, true);
        let core = cert.minimal_core();
        assert_eq!(
            core,
            vec![1, 2, 3],
            "all hints should be original clause IDs"
        );
    }

    #[test]
    fn test_minimal_core_dedup_and_sort() {
        let steps = vec![
            LratStep {
                clause_id: 10,
                literals: vec![Literal::positive(Variable(0))],
                hints: vec![3i64, 1, 2, 1, 3],
            },
            LratStep {
                clause_id: 11,
                literals: vec![],
                hints: vec![10i64, 2],
            },
        ];
        let cert = ProofCertificate::from_backward_result(steps, true);
        let core = cert.minimal_core();
        assert_eq!(core, vec![1, 2, 3], "core should be sorted and deduped");
    }

    // ── Streaming UNSAT core tests (#8250) ──────────────────────────────

    #[test]
    fn test_streaming_core_not_present_by_default() {
        let cert = ProofCertificate::from_backward_result(make_test_steps(), true);
        assert!(
            !cert.has_streaming_core(),
            "default certificate should not have streaming core"
        );
    }

    #[test]
    fn test_streaming_core_overrides_dag_walk() {
        let mut cert = ProofCertificate::from_backward_result(make_test_steps(), true);
        // DAG walk would produce [1, 2, 3], but streaming core overrides.
        cert.set_streaming_core(vec![1, 3]);
        assert!(cert.has_streaming_core());
        let core = cert.minimal_core();
        assert_eq!(
            core,
            vec![1, 3],
            "streaming core should override DAG walk result"
        );
    }

    #[test]
    fn test_streaming_core_returns_without_materializing() {
        let mut cert = ProofCertificate::from_backward_result(make_test_steps(), true);
        cert.set_streaming_core(vec![2, 5]);
        assert!(
            cert.is_deferred(),
            "proof should still be deferred before minimal_core"
        );
        let core = cert.minimal_core();
        assert_eq!(core, vec![2, 5]);
        // Streaming core path does NOT materialize the proof
        assert!(
            cert.is_deferred(),
            "streaming core should not trigger materialization"
        );
    }

    #[test]
    fn test_streaming_core_empty_certificate() {
        let mut cert = ProofCertificate::empty();
        assert!(!cert.has_streaming_core());
        cert.set_streaming_core(vec![1]);
        assert!(cert.has_streaming_core());
        assert_eq!(cert.minimal_core(), vec![1]);
    }

    #[test]
    fn test_streaming_core_debug_includes_size() {
        let mut cert = ProofCertificate::from_backward_result(make_test_steps(), true);
        cert.set_streaming_core(vec![1, 2, 3]);
        let debug_str = format!("{cert:?}");
        assert!(
            debug_str.contains("streaming_core: Some(3)"),
            "debug should show streaming core size, got: {debug_str}"
        );
    }

    #[test]
    fn test_streaming_core_clone_preserves() {
        let mut cert = ProofCertificate::from_backward_result(make_test_steps(), true);
        cert.set_streaming_core(vec![1, 2]);
        let cloned = cert.clone();
        assert!(cloned.has_streaming_core());
        assert_eq!(cloned.minimal_core(), vec![1, 2]);
    }
}
