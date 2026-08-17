// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Constructors and mutation helpers for proof DAGs.

use super::{
    AletheRule, FarkasAnnotation, LiaAnnotation, Proof, ProofId, ProofStep, TheoryLemmaKind,
};
use crate::term::TermId;

impl Proof {
    /// Create a new empty proof
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    /// Rebuild a proof from an ordered list of steps, leaving `named_steps`
    /// empty. `ProofId(i)` resolves to `steps[i]` (the same positional invariant
    /// [`add_step`](Self::add_step) maintains), so the step DAG is preserved.
    /// `named_steps` only resolves `assume` *names* for the Alethe printer and is
    /// never consulted by [`check_proof`](crate) / `check_proof_strict`, so a
    /// proof rebuilt this way re-checks identically. This is the deserialization
    /// counterpart used to reconstruct a [`Proof`] from a serialized step list.
    #[must_use]
    pub fn from_steps(steps: Vec<ProofStep>) -> Self {
        Self {
            steps,
            named_steps: crate::kani_compat::KaniHashMap::default(),
        }
    }

    /// Add a proof step
    #[allow(clippy::cast_possible_truncation)] // Proof step count is bounded well under u32::MAX
    pub fn add_step(&mut self, step: ProofStep) -> ProofId {
        debug_assert!(
            self.steps.len() < u32::MAX as usize,
            "BUG: proof exceeds u32::MAX steps ({})",
            self.steps.len()
        );
        let id = ProofId(self.steps.len() as u32);
        self.steps.push(step);
        id
    }

    /// Add an assumption and optionally name it
    pub fn add_assume(&mut self, term: TermId, name: Option<String>) -> ProofId {
        let id = self.add_step(ProofStep::Assume(term));
        if let Some(n) = name {
            self.named_steps.insert(n, id);
        }
        id
    }

    /// Add a generic step with a rule
    pub fn add_rule_step(
        &mut self,
        rule: AletheRule,
        clause: Vec<TermId>,
        premises: Vec<ProofId>,
        args: Vec<TermId>,
    ) -> ProofId {
        self.add_step(ProofStep::Step {
            rule,
            clause,
            premises,
            args,
        })
    }

    /// Add a resolution step
    pub fn add_resolution(
        &mut self,
        clause: Vec<TermId>,
        pivot: TermId,
        clause1: ProofId,
        clause2: ProofId,
    ) -> ProofId {
        self.add_step(ProofStep::Resolution {
            clause,
            pivot,
            clause1,
            clause2,
        })
    }

    /// Add a theory lemma with default kind
    pub fn add_theory_lemma(&mut self, theory: impl Into<String>, clause: Vec<TermId>) -> ProofId {
        self.add_step(ProofStep::TheoryLemma {
            theory: theory.into(),
            clause,
            farkas: None,
            kind: TheoryLemmaKind::Generic,
            lia: None,
        })
    }

    /// Add a theory lemma with specified kind
    pub fn add_theory_lemma_with_kind(
        &mut self,
        theory: impl Into<String>,
        clause: Vec<TermId>,
        kind: TheoryLemmaKind,
    ) -> ProofId {
        debug_assert!(
            !matches!(kind, TheoryLemmaKind::LraFarkas),
            "BUG: LraFarkas requires Farkas :args; use add_theory_lemma_with_farkas_and_kind"
        );
        self.add_step(ProofStep::TheoryLemma {
            theory: theory.into(),
            clause,
            farkas: None,
            kind,
            lia: None,
        })
    }

    /// Add a theory lemma with Farkas annotation (for arithmetic theories)
    pub fn add_theory_lemma_with_farkas(
        &mut self,
        theory: impl Into<String>,
        clause: Vec<TermId>,
        farkas: FarkasAnnotation,
    ) -> ProofId {
        self.add_step(ProofStep::TheoryLemma {
            theory: theory.into(),
            clause,
            farkas: Some(farkas),
            kind: TheoryLemmaKind::LraFarkas,
            lia: None,
        })
    }

    /// Add a theory lemma with Farkas annotation and explicit kind
    pub fn add_theory_lemma_with_farkas_and_kind(
        &mut self,
        theory: impl Into<String>,
        clause: Vec<TermId>,
        farkas: FarkasAnnotation,
        kind: TheoryLemmaKind,
    ) -> ProofId {
        // Farkas certificates must have non-negative coefficients.
        // A negative coefficient indicates a bug in the arithmetic solver's
        // conflict explanation. Catch early before emitting into the proof.
        debug_assert!(
            farkas.is_valid(),
            "BUG: Farkas certificate has negative coefficient(s): {:?}",
            farkas.coefficients,
        );
        self.add_step(ProofStep::TheoryLemma {
            theory: theory.into(),
            clause,
            farkas: Some(farkas),
            kind,
            lia: None,
        })
    }

    /// Add a theory lemma with optional Farkas annotation and explicit kind (#6031 Phase 4).
    ///
    /// Like `add_theory_lemma_with_farkas_and_kind` but accepts `Option<FarkasAnnotation>`,
    /// used by `SatProofManager` when wiring theory lemma annotations from the clause trace.
    pub fn add_theory_lemma_with_farkas_and_kind_opt(
        &mut self,
        theory: impl Into<String>,
        clause: Vec<TermId>,
        farkas: Option<FarkasAnnotation>,
        kind: TheoryLemmaKind,
    ) -> ProofId {
        if let Some(ref f) = farkas {
            debug_assert!(
                f.is_valid(),
                "BUG: Farkas certificate has negative coefficient(s): {:?}",
                f.coefficients,
            );
        }
        self.add_step(ProofStep::TheoryLemma {
            theory: theory.into(),
            clause,
            farkas,
            kind,
            lia: None,
        })
    }

    /// Add a theory lemma with LIA annotation and explicit kind.
    ///
    /// Used by the LIA solver when it can provide a specific proof shape
    /// (bounds gap, divisibility, or cutting plane).
    pub fn add_theory_lemma_with_lia(
        &mut self,
        theory: impl Into<String>,
        clause: Vec<TermId>,
        farkas: Option<FarkasAnnotation>,
        kind: TheoryLemmaKind,
        lia: LiaAnnotation,
    ) -> ProofId {
        if let Some(ref f) = farkas {
            debug_assert!(
                f.is_valid(),
                "BUG: Farkas certificate has negative coefficient(s): {:?}",
                f.coefficients,
            );
        }
        self.add_step(ProofStep::TheoryLemma {
            theory: theory.into(),
            clause,
            farkas,
            kind,
            lia: Some(lia),
        })
    }
}
