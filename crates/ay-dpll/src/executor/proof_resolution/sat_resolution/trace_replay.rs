// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use ay_core::{Proof, ProofStep};

use super::extract_theory_lemma_proofs;
use crate::executor::Executor;

// Proof-reconstruction introspection (`--proof-introspect=<path>`).
//
// Trust fallbacks are the reason a computed UNSAT can be rejected by the
// strict publication gate, but the CAUSE lives back in conflict analysis:
// a level-0 literal whose reason has no stable clause ID contributes no
// resolution hint, so replay cannot resolve it away and the derived clause
// ends up a strict superclause of its target. This report joins both ends
// so the chain is visible without a rebuild. Writes to a FILE because
// consumers (e.g. model-checker-consumer's driver) capture and discard the solver's
// stderr, and ay's own `c` markers go to stdout.
fn write_proof_introspection(
    trace: &ay_sat::ClauseTrace,
    manager: &crate::SatProofManager<'_>,
    trust_count: u32,
) {
    let Some(path) = ay_core::misc_cli_flags().proof_introspect.as_deref() else {
        return;
    };
    use std::io::Write as _;
    let stats = trace.hint_omission_stats();
    // Hint-CAPTURE coverage: a learned clause recorded with an empty hint
    // list gives replay nothing to resolve with, which is the other way a
    // reconstruction can end up short of its target.
    let (mut learned, mut learned_no_hints, mut originals) = (0usize, 0usize, 0usize);
    for entry in trace.entries() {
        if entry.is_original {
            originals += 1;
        } else {
            learned += 1;
            if entry.resolution_hints.is_empty() {
                learned_no_hints += 1;
            }
        }
    }
    if let Ok(mut fh) = std::fs::OpenOptions::new()
        .create(true)
        .append(true)
        .open(&path)
    {
        // Format first, then ONE `write_all`: several solver threads may
        // append concurrently, and a multi-call `writeln!` interleaves
        // their output into unparseable lines.
        let line = format!(
            "PROOF_INTROSPECT trust_fallbacks={} hint_queries={} hint_resolved={} omitted_total={} omitted_not_clause_reason={} omitted_lazy_theory_reason={} omitted_zero_clause_id={} trace_entries={} trace_truncated={} proof_work_exhausted={} \
learned={} learned_no_hints={} originals={} untranslatable_entries={} unmapped_min={:?} unmapped_max={:?} mapped_vars={}\n",
            trust_count,
            stats.queries,
            stats.resolved,
            stats.omitted_total(),
            stats.omitted_not_clause_reason,
            stats.omitted_lazy_theory_reason,
            stats.omitted_zero_clause_id,
            trace.len(),
            trace.is_truncated(),
            trace.proof_work_exhausted(),
            learned,
            learned_no_hints,
            originals,
            manager.untranslatable_entries(),
            manager.unmapped_var_range().0,
            manager.unmapped_var_range().1,
            manager.unmapped_var_range().2,
        );
        let _ = fh.write_all(line.as_bytes());
    }
}

impl Executor {
    /// Try to derive the empty clause via SAT resolution reconstruction.
    ///
    /// Returns true if successful, false if the clause trace is not available or
    /// doesn't lead to an empty-clause derivation.
    pub(super) fn try_derive_empty_via_sat_resolution(&mut self, proof: &mut Proof) -> bool {
        let trace = match self.last_clause_trace.take() {
            Some(t) => t,
            None => return false,
        };
        if !trace.has_empty_clause() {
            self.last_clause_trace = Some(trace);
            return false;
        }

        let var_to_term = match self.last_var_to_term.take() {
            Some(m) => m,
            None => {
                self.last_clause_trace = Some(trace);
                return false;
            }
        };

        let _negations = match self.last_negations.take() {
            Some(m) => m,
            None => {
                self.last_clause_trace = Some(trace);
                self.last_var_to_term = Some(var_to_term);
                return false;
            }
        };

        let theory_lemma_map = extract_theory_lemma_proofs(proof);

        // Best-effort budget for synthesized-default certificates (#A2b):
        // `None` (explicit proof requests) keeps reconstruction unbounded.
        // An in-script `(set-option :produce-proofs true)` is an explicit
        // SMT-LIB demand for a proof and overrides any CLI-default budget.
        let script_demands_proof = matches!(
            self.ctx.get_option("produce-proofs"),
            Some(ay_frontend::OptionValue::Bool(true))
        );
        let mut manager = crate::SatProofManager::new(&var_to_term, &mut self.ctx.terms);
        let scope_assumptions = trace.scope_assumptions().unwrap_or_default();
        if manager.set_scope_assumptions(scope_assumptions).is_err() {
            self.last_clause_trace = Some(trace);
            self.last_var_to_term = Some(var_to_term);
            return false;
        }
        if !script_demands_proof {
            manager.set_step_budget(self.proof_reconstruction_step_budget);
        }
        if let Some(ref cp) = self.last_clausification_proofs {
            manager.set_clausification_proofs(cp);
        }
        if let Some(ref tp) = self.last_original_clause_theory_proofs {
            manager.set_original_clause_theory_proofs(tp);
        }
        if !theory_lemma_map.is_empty() {
            manager.set_theory_lemma_proofs(&theory_lemma_map);
        }

        if !manager.can_process(&trace) {
            return false;
        }

        let result = manager.process_trace(&trace, proof);
        let trust_count = manager.trust_fallback_count();
        if trust_count > 0 {
            tracing::warn!(
                trust_fallbacks = trust_count,
                "SAT proof reconstruction used {trust_count} trust fallback(s) — \
                 proof contains unverified steps"
            );
        }
        write_proof_introspection(&trace, &manager, trust_count);
        result.is_some_and(|empty_id| {
            let step = proof.get_step(empty_id);
            matches!(
                step,
                Some(ProofStep::Resolution { clause, .. } | ProofStep::Step { clause, .. })
                    if clause.is_empty()
            )
        })
    }
}
