// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Strict proof completion for same-context consequence probes.

use super::{Executor, TermId};
use ay_core::{AletheRule, Proof, ProofStep};

impl Executor {
    /// Complete and strictly check a provisional consequence-probe refutation.
    pub(super) fn finish_consequence_probe_unsat_proof(
        &mut self,
        assertions: &[TermId],
    ) -> Option<Proof> {
        if self.last_proof.is_none() {
            self.build_unsat_proof();
        }
        let mut proof = self.last_proof.take()?;
        self.promote_consequence_probe_conjunct_trust_leaves(&mut proof, assertions);
        // The ordinary cascade ran while the probe-local conjuncts were still
        // trust leaves. Its EUF promotion is atomic, so those leaves correctly
        // made it revert. Once exact probe assertions derive the conjuncts,
        // give the unchanged certified promotion one fresh pass.
        self.promote_certified_generic_euf_leaves(&mut proof);

        match self.check_proof_strict_with_datatypes(&proof) {
            Ok(quality) if quality.is_complete() => Some(proof),
            Ok(_) => {
                if ay_core::misc_cli_flags().trace_cegqi_attr {
                    eprintln!("[consequence-replay] probe strict check incomplete");
                }
                None
            }
            Err(error) => {
                if ay_core::misc_cli_flags().trace_cegqi_attr {
                    self.trace_consequence_probe_strict_refusal(&proof, &error);
                }
                None
            }
        }
    }

    fn trace_consequence_probe_strict_refusal(
        &self,
        proof: &Proof,
        error: &impl std::fmt::Display,
    ) {
        eprintln!("[consequence-replay] probe strict check refused: {error}");
        for (index, step) in proof.steps.iter().enumerate() {
            let residual_trust = match step {
                ProofStep::TheoryLemma { kind, .. } => kind.is_trust(),
                ProofStep::Step {
                    rule: AletheRule::Trust,
                    ..
                } => true,
                _ => false,
            };
            if !residual_trust {
                continue;
            }
            eprintln!("[consequence-replay] probe[{index}] = {step:?}");
            if let ProofStep::TheoryLemma { clause, .. } | ProofStep::Step { clause, .. } = step {
                for &lit in clause {
                    eprintln!(
                        "[consequence-replay]    lit {:?} = {}",
                        lit,
                        ay_proof::render_term_canonical(&self.ctx.terms, lit)
                    );
                }
            }
        }
    }
}
