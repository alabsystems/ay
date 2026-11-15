// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use ay_core::{Proof, ProofStep};

use super::extract_theory_lemma_proofs;
use crate::executor::{Executor, SatReconstructionOutcome};
// The per-trace-entry rate of the best-effort (#A2b) budget's floor below,
// shared with the re-derivation attempts inside the replay.
use crate::sat_proof_manager::RECONSTRUCTION_STEPS_PER_TRACE_ENTRY;

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
        .open(path)
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

/// The step budget a budgeted (#A2b, synthesized-default) reconstruction
/// runs under: the configured budget, but never less than a linear
/// allowance over the trace it has to replay.
///
/// The meter charges clause inspections during RUP replay, whose cost
/// grows with the trace itself (every derivation re-asserts the indexed
/// unit clauses and inspects watchers over a growing clause database).
/// A flat budget therefore abandons EVERY sufficiently large trace
/// mid-replay regardless of how cheap its entries are: measured on
/// QF_UF NEQ004_size7 (32,089 trace entries), the flat 1M budget
/// exhausted at entry 12,016 and the lane's genuine refutation fell
/// through to the whole-query trust closer, which mandatory strict
/// certification correctly refuses. Scaling the floor linearly with the
/// trace keeps the bound a bound — a replay whose cost grows
/// superlinearly in the trace still exhausts it — while a replay that
/// is merely large completes. `None` (explicit proof requests) stays
/// unbounded. The search-time bookkeeping budget is a different meter
/// and is deliberately untouched: its calibration (degrade early on
/// pathological BOOKKEEPING, e.g. pointer-safe-5) does not apply to a
/// replay that starts only after the verdict is decided.
fn reconstruction_step_budget(configured: Option<u64>, trace_entries: u32) -> Option<u64> {
    configured.map(|budget| {
        budget.max(u64::from(trace_entries).saturating_mul(RECONSTRUCTION_STEPS_PER_TRACE_ENTRY))
    })
}

impl Executor {
    /// Try to derive the empty clause via SAT resolution reconstruction.
    ///
    /// Returns true if successful, false if the clause trace is not available or
    /// doesn't lead to an empty-clause derivation.
    pub(super) fn try_derive_empty_via_sat_resolution(&mut self, proof: &mut Proof) -> bool {
        // #closer-population. Every exit of this function is a fork in the
        // evidence story and none of them said anything. `no-trace` and
        // `trace-without-empty-clause` mean AY has no propositional refutation
        // to carry; the four below them mean it HAS one and cannot express it,
        // which is a translation gap with a completely different remedy. The
        // record is write-only and the returns are unchanged.
        let mut note = crate::executor::SatReconstructionRecord::default();
        let trace = match self.last_clause_trace.take() {
            Some(t) => t,
            None => {
                self.note_sat_reconstruction(SatReconstructionOutcome::NoTrace, note);
                return false;
            }
        };
        note.trace_entries = u32::try_from(trace.len()).unwrap_or(u32::MAX);
        note.trace_has_empty = trace.has_empty_clause();
        note.proof_work_exhausted = trace.proof_work_exhausted();
        note.trace_truncated = trace.is_truncated();
        // #destroyed-trace. Carry the clear-site census forward. `clear_entries`
        // leaves `trace.len() == 0`, so these are the ONLY numbers that say what
        // the #A2b budget actually threw away.
        if let Some(snap) = trace.exhaustion_snapshot() {
            note.destroyed_entries = snap.entries;
            note.destroyed_originals = snap.originals;
            note.destroyed_learned = snap.learned;
            note.destroyed_learned_with_hints = snap.learned_with_hints;
            note.destroyed_has_empty = snap.has_empty;
        }
        if !trace.has_empty_clause() {
            self.last_clause_trace = Some(trace);
            self.note_sat_reconstruction(SatReconstructionOutcome::TraceWithoutEmptyClause, note);
            return false;
        }

        let var_to_term = match self.last_var_to_term.take() {
            Some(m) => m,
            None => {
                self.last_clause_trace = Some(trace);
                self.note_sat_reconstruction(SatReconstructionOutcome::NoVariableMap, note);
                return false;
            }
        };
        note.mapped_vars = u32::try_from(var_to_term.len()).unwrap_or(u32::MAX);

        let _negations = match self.last_negations.take() {
            Some(m) => m,
            None => {
                self.last_clause_trace = Some(trace);
                self.last_var_to_term = Some(var_to_term);
                self.note_sat_reconstruction(SatReconstructionOutcome::NoVariableMap, note);
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
        let should_stop = self.make_proof_assembly_should_stop();
        let mut manager = crate::SatProofManager::new(&var_to_term, &mut self.ctx.terms);
        manager.set_should_stop(&should_stop);
        let scope_assumptions = trace.scope_assumptions().unwrap_or_default();
        if manager.set_scope_assumptions(scope_assumptions).is_err() {
            self.last_clause_trace = Some(trace);
            self.last_var_to_term = Some(var_to_term);
            self.note_sat_reconstruction(SatReconstructionOutcome::ScopeAssumptionsRejected, note);
            return false;
        }
        if !script_demands_proof {
            manager.set_step_budget(reconstruction_step_budget(
                self.proof_reconstruction_step_budget,
                note.trace_entries,
            ));
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
            self.note_sat_reconstruction(SatReconstructionOutcome::ManagerDeclinedTrace, note);
            return false;
        }

        let result = manager.process_trace(&trace, proof);
        note.untranslatable_entries =
            u32::try_from(manager.untranslatable_entries()).unwrap_or(u32::MAX);
        let trust_count = manager.trust_fallback_count();
        if trust_count > 0 {
            tracing::warn!(
                trust_fallbacks = trust_count,
                "SAT proof reconstruction used {trust_count} trust fallback(s) — \
                 proof contains unverified steps"
            );
        }
        write_proof_introspection(&trace, &manager, trust_count);
        let closed = result.is_some_and(|empty_id| {
            let step = proof.get_step(empty_id);
            matches!(
                step,
                Some(ProofStep::Resolution { clause, .. } | ProofStep::Step { clause, .. })
                    if clause.is_empty()
            )
        });
        self.note_sat_reconstruction(
            if closed {
                SatReconstructionOutcome::Reconstructed
            } else {
                SatReconstructionOutcome::ReconstructionShort
            },
            note,
        );
        closed
    }

    /// Keep the furthest reconstruction attempt this query made.
    ///
    /// #closer-population. The empty-clause pipeline runs more than once on
    /// some queries and this function CONSUMES the trace, so a later attempt
    /// reports `no-trace` whatever the earlier one held. Overwriting would turn
    /// a consumed trace into a claim that AY never had a refutation, which is
    /// exactly the misreading the record exists to prevent.
    fn note_sat_reconstruction(
        &mut self,
        outcome: SatReconstructionOutcome,
        mut record: crate::executor::SatReconstructionRecord,
    ) {
        record.outcome = Some(outcome);
        self.last_sat_reconstruction.keep_furthest(record);
    }
}

#[cfg(test)]
#[path = "trace_replay_stop_tests.rs"]
mod stop_tests;

#[cfg(test)]
mod budget_tests {
    use super::reconstruction_step_budget;

    #[test]
    fn unbudgeted_reconstruction_stays_unbounded() {
        assert_eq!(reconstruction_step_budget(None, 32_089), None);
    }

    #[test]
    fn small_traces_keep_the_configured_budget() {
        assert_eq!(
            reconstruction_step_budget(Some(1_000_000), 100),
            Some(1_000_000)
        );
    }

    #[test]
    fn large_traces_get_the_linear_floor() {
        // NEQ004_size7 measured: the flat 1M budget exhausted at entry
        // 12,016 of 32,089; the floor must cover the whole trace.
        assert_eq!(
            reconstruction_step_budget(Some(1_000_000), 32_089),
            Some(32_089 * 512)
        );
    }

    #[test]
    fn floor_saturates_instead_of_wrapping() {
        assert_eq!(
            reconstruction_step_budget(Some(1), u32::MAX),
            Some(u64::from(u32::MAX) * 512)
        );
    }
}
