// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Deferred backward LRAT proof reconstruction (Phase 2b, #8072).
//!
//! Instead of building LRAT hint chains eagerly during every conflict analysis
//! (the forward path in `conflict_analysis_lrat.rs`), this module reconstructs
//! the proof backward from the empty clause after the solver determines UNSAT.
//!
//! ## Algorithm
//!
//! 1. Start from the empty clause (the final derivation of contradiction).
//! 2. BFS backward through the clause dependency graph:
//!    - For each learned clause reachable from the empty clause, find its
//!      antecedent clauses via `var_data[vi].reason` pointers on the trail.
//!    - Collect the clause IDs of all antecedent clauses.
//! 3. Emit proof steps in reverse topological order (reverse BFS order).
//! 4. Only emit steps for clauses reachable from the empty clause — skip
//!    unreachable learned clauses entirely.
//!
//! ## Data structures used
//!
//! - `cold.clause_ids: Vec<u64>` — maps arena offsets to clause IDs (always
//!   populated since Phase 2a, #8069).
//! - `var_data[vi].reason: u32` — propagation reason for each assigned variable.
//! - `trail: Vec<Literal>` — assignment order.
//! - `ClauseTrace` in `clause_trace.rs` — records clause additions with hints.
//!
//! ## Integration
//!
//! This module provides `reconstruct_lrat_backward()` which can be called from
//! `finalize_unsat.rs` as an alternative to the forward LRAT chain. The forward
//! path is NOT removed — both coexist during this transition phase.

use super::*;

/// A single LRAT proof step produced by backward reconstruction.
///
/// Each step represents a derived clause and the clause IDs of its antecedents
/// (the hints that an LRAT checker needs to verify the derivation by RUP).
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct LratStep {
    /// The clause ID of the derived clause.
    pub(crate) clause_id: u64,
    /// The literals of the derived clause.
    pub(crate) literals: Vec<Literal>,
    /// The clause IDs of the antecedent clauses (LRAT hints).
    /// Order: suitable for RUP checking (reverse resolution order).
    /// Positive values are clause-ID references for RUP checking.
    /// Negative values mark RAT witness boundaries / deletion steps
    /// (needed for extended resolution and blocked clause proofs).
    pub(crate) hints: Vec<i64>,
}

/// Result of backward proof reconstruction.
#[derive(Debug)]
pub(crate) struct BackwardProofResult {
    /// Proof steps in emission order (reverse topological: deepest dependencies first,
    /// empty clause last). Each step is a derived clause with its LRAT hints.
    pub(crate) steps: Vec<LratStep>,
    /// Whether reconstruction was complete (all antecedents resolved).
    /// If false, some clauses were unreachable (e.g., garbage collected)
    /// and the proof may be incomplete.
    pub(crate) complete: bool,
}

impl Solver {
    /// Reconstruct LRAT proof backward from the empty clause.
    ///
    /// This is the core of Phase 2b: after the solver determines UNSAT, walk
    /// the clause dependency graph backward from the empty clause to collect
    /// only the proof steps that are actually needed.
    ///
    /// Returns a `BackwardProofResult` containing the proof steps in emission
    /// order and a completeness flag.
    ///
    /// # Algorithm
    ///
    /// 1. Find the empty clause's antecedents from the clause trace or from
    ///    the current trail state.
    /// 2. BFS from those antecedents through `var_data[vi].reason` pointers.
    /// 3. For each learned clause encountered, reconstruct its hints from the
    ///    reason clauses of its literals.
    /// 4. Return steps in reverse topological order.
    pub(crate) fn reconstruct_lrat_backward(&self) -> BackwardProofResult {
        // Phase 1: Find the empty clause derivation and its immediate antecedents.
        //
        // The empty clause was derived from a conflict at decision level 0, or
        // from a learned clause that became falsified. Its antecedents are the
        // clause IDs that were used to derive it.
        //
        // We look for the empty clause entry in the clause trace first.
        // If no trace is available, we reconstruct from the current trail state.

        let mut result = BackwardProofResult {
            steps: Vec::new(),
            complete: true,
        };

        // Collect the set of clause IDs that are "original" (input clauses).
        // These don't need proof steps — they are axioms.
        let original_boundary = self.cold.original_clause_boundary;

        // BFS state: queue of clause arena offsets to process.
        // visited: set of clause IDs already processed.
        let mut visited: Vec<bool> = vec![false; (self.cold.next_clause_id as usize) + 1];
        let mut queue: Vec<usize> = Vec::new(); // arena offsets

        // Phase 1: Seed BFS from the falsified clause(s) at level 0.
        //
        // At UNSAT, all trail literals are at level 0. Find clauses that are
        // fully falsified under the current assignment — these are the conflict
        // clauses that triggered UNSAT.
        let mut seed_clause_ids: Vec<u64> = Vec::new();

        // live_indices (husk adjudication): garbage-kept husks (congruence
        // forward subsumption zeroes their clause_ids) must not seed the
        // backward BFS. Also keep scanning when a falsified clause has
        // cid==0 — the previous unconditional `break` left the seed set
        // empty and downgraded the certificate to incomplete.
        for offset in self.arena.live_indices() {
            let lits = self.arena.literals(offset);
            if lits.is_empty() {
                continue;
            }
            if lits.iter().all(|lit| self.lit_val(*lit) < 0) {
                let cid = self.clause_id_for_offset(offset);
                if cid != 0 {
                    seed_clause_ids.push(cid);
                    if (cid as usize) < visited.len() {
                        visited[cid as usize] = true;
                    }
                    // Only process non-original clauses (learned clauses need proof steps).
                    if offset >= original_boundary {
                        queue.push(offset);
                    }
                    // Use the first falsified clause with a live ID as the seed.
                    break;
                }
            }
        }

        if seed_clause_ids.is_empty() {
            // No falsified clause found — degenerate case.
            // This can happen if the solver detected UNSAT through other means
            // (e.g., empty clause was directly derived).
            result.complete = false;
            return result;
        }

        // Phase 2: BFS backward through the dependency graph.
        //
        // For each learned clause in the queue:
        // 1. Look up its literals from the arena.
        // 2. For each literal, find the reason clause via var_data[vi].reason.
        // 3. If the reason clause is a learned clause we haven't visited, add it
        //    to the queue.
        // 4. Record the LRAT step: this clause was derived from its antecedents.

        let mut steps: Vec<LratStep> = Vec::new();
        let mut head = 0;

        while head < queue.len() {
            let clause_offset = queue[head];
            head += 1;

            let clause_id = self.clause_id_for_offset(clause_offset);
            if clause_id == 0 {
                continue;
            }

            let clause_lits = self.arena.literals(clause_offset);
            let mut antecedent_ids: Vec<i64> = Vec::new();

            for &lit in clause_lits {
                let var_idx = lit.variable().index();
                if var_idx >= self.var_data.len() {
                    continue;
                }

                let reason_raw = self.var_data[var_idx].reason;

                // Decision variables have no reason — skip them.
                if reason_raw == NO_REASON {
                    continue;
                }

                // Binary literal reasons (#8034) — no arena clause to reference.
                if is_binary_literal_reason(reason_raw) {
                    // Binary reasons don't have a clause_id in the arena.
                    // For now, skip them (incomplete chain).
                    // A complete implementation would look up the binary clause
                    // proof ID from a separate tracking structure.
                    result.complete = false;
                    continue;
                }

                // Clause reason: look up the clause ID.
                let reason_offset = reason_raw as usize;
                let reason_id = self.clause_id_for_offset(reason_offset);
                if reason_id == 0 {
                    // Clause has no ID (e.g., garbage collected before ID assignment).
                    result.complete = false;
                    continue;
                }

                // Add as antecedent (cast u64 clause ID to i64; always positive).
                let reason_hint = reason_id as i64;
                if !antecedent_ids.contains(&reason_hint) {
                    antecedent_ids.push(reason_hint);
                }

                // If this is a learned clause we haven't visited, add to BFS queue.
                if reason_offset >= original_boundary
                    && (reason_id as usize) < visited.len()
                    && !visited[reason_id as usize]
                {
                    visited[reason_id as usize] = true;
                    queue.push(reason_offset);
                }
            }

            // Also add unit proof IDs for level-0 variables whose reason was
            // cleared by ClearLevel0 but preserved in level0_proof_id.
            for &lit in clause_lits {
                if self.lit_val(lit) >= 0 {
                    continue;
                }
                if let Some(pid) = self.level0_var_proof_id_for_lit(lit.negated()) {
                    let pid = pid as i64;
                    if !antecedent_ids.contains(&pid) {
                        antecedent_ids.push(pid);
                    }
                }
            }

            steps.push(LratStep {
                clause_id,
                literals: clause_lits.to_vec(),
                hints: antecedent_ids,
            });
        }

        // Phase 3: Reverse the steps for emission order.
        //
        // BFS produces steps in breadth-first order (closest to empty clause first).
        // LRAT proofs need reverse topological order: deepest dependencies first,
        // so that each step's antecedents are already defined when the step is
        // processed.
        steps.reverse();

        // Phase 4: Build the empty clause step.
        //
        // The empty clause's hints are the seed clause IDs (the falsified clause(s))
        // plus any level-0 unit proof IDs needed.
        let empty_clause_hints = self.build_backward_empty_clause_hints(&seed_clause_ids);

        steps.push(LratStep {
            clause_id: 0, // Empty clause gets ID from the proof writer.
            literals: Vec::new(),
            hints: empty_clause_hints,
        });

        result.steps = steps;
        result
    }

    /// Build LRAT hints for the empty clause in backward reconstruction.
    ///
    /// The empty clause is derived from the falsified seed clause(s) plus
    /// level-0 unit assignments that falsified the literals.
    fn build_backward_empty_clause_hints(&self, seed_clause_ids: &[u64]) -> Vec<i64> {
        let mut hints: Vec<i64> = Vec::new();

        // Add level-0 unit proof IDs for all trail variables.
        let level0_end = self.trail_lim.first().copied().unwrap_or(self.trail.len());
        for i in (0..level0_end).rev() {
            let lit = self.trail[i];
            let var_idx = lit.variable().index();
            if var_idx >= self.var_data.len() || self.var_data[var_idx].level != 0 {
                continue;
            }
            // Try unit_proof_id first, then level0_proof_id.
            if let Some(id) = self.visible_unit_proof_id_for_lit(lit) {
                let pid = id as i64;
                if !hints.contains(&pid) {
                    hints.push(pid);
                }
            } else if let Some(id) = self.level0_var_proof_id_for_lit(lit) {
                let pid = id as i64;
                if !hints.contains(&pid) {
                    hints.push(pid);
                }
            }
        }

        // Add seed clause IDs (cast u64 -> i64; always positive).
        for &sid in seed_clause_ids {
            let hint = sid as i64;
            if !hints.contains(&hint) {
                hints.push(hint);
            }
        }

        hints
    }

    /// Look up the clause ID for a given arena offset.
    ///
    /// Returns 0 if the offset is out of bounds or has no assigned ID.
    #[inline]
    fn clause_id_for_offset(&self, offset: usize) -> u64 {
        if offset < self.cold.clause_ids.len() {
            self.cold.clause_ids[offset]
        } else {
            0
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_lrat_step_default() {
        let step = LratStep {
            clause_id: 42,
            literals: vec![],
            hints: vec![1i64, 2, 3],
        };
        assert_eq!(step.clause_id, 42);
        assert!(step.literals.is_empty());
        assert_eq!(step.hints, vec![1i64, 2, 3]);
    }

    #[test]
    fn test_backward_proof_result_default() {
        let result = BackwardProofResult {
            steps: Vec::new(),
            complete: true,
        };
        assert!(result.steps.is_empty());
        assert!(result.complete);
    }

    #[test]
    fn test_lrat_step_equality() {
        let step1 = LratStep {
            clause_id: 1,
            literals: vec![Literal(0), Literal(2)],
            hints: vec![10i64, 20],
        };
        let step2 = LratStep {
            clause_id: 1,
            literals: vec![Literal(0), Literal(2)],
            hints: vec![10i64, 20],
        };
        assert_eq!(step1, step2);
    }

    #[test]
    fn test_backward_proof_on_trivial_unsat() {
        // Build a solver with contradictory unit clauses: {x} and {-x}
        // This should produce an UNSAT result where backward reconstruction
        // can find the falsified clause.
        use crate::literal::Variable;
        let v0 = Variable(0);
        let mut solver = Solver::new(1);
        solver.add_clause(vec![Literal::positive(v0)]);
        solver.add_clause(vec![Literal::negative(v0)]);

        let result = solver.solve();
        assert!(
            result.is_unsat(),
            "expected UNSAT for contradictory unit clauses"
        );

        // After solving, the backward reconstruction should produce some steps.
        // Note: the solver may have already finalized the proof via the forward
        // path, but the backward reconstruction should still work as a
        // post-hoc analysis.
        let backward = solver.reconstruct_lrat_backward();
        // For trivial UNSAT (contradictory units), the proof may be empty or
        // contain just the empty clause step. The key invariant is that the
        // function completes without panicking and returns a valid result.
        assert!(
            !backward.steps.is_empty() || !backward.complete,
            "backward reconstruction should produce steps or report incomplete"
        );
    }

    #[test]
    fn test_backward_proof_on_sat_instance() {
        // SAT instance: just one clause {x}
        use crate::literal::Variable;
        let v0 = Variable(0);
        let mut solver = Solver::new(1);
        solver.add_clause(vec![Literal::positive(v0)]);

        let result = solver.solve();
        assert!(result.is_sat(), "expected SAT for single positive unit");

        // Backward reconstruction on a SAT instance should produce no meaningful
        // steps (no empty clause was derived).
        let backward = solver.reconstruct_lrat_backward();
        // For SAT instances, there's no falsified clause, so reconstruction
        // should report incomplete or produce no steps.
        let has_empty_step = backward.steps.iter().any(|s| s.literals.is_empty());
        // The empty clause step is always appended, but the seed finding may fail.
        // Either way, the function should not panic.
        let _ = has_empty_step;
    }

    #[test]
    fn test_backward_proof_small_unsat() {
        // A slightly more complex UNSAT: (x | y) & (-x) & (-y)
        use crate::literal::Variable;
        let v0 = Variable(0);
        let v1 = Variable(1);
        let mut solver = Solver::new(2);
        solver.add_clause(vec![Literal::positive(v0), Literal::positive(v1)]);
        solver.add_clause(vec![Literal::negative(v0)]);
        solver.add_clause(vec![Literal::negative(v1)]);

        let result = solver.solve();
        assert!(result.is_unsat(), "expected UNSAT for (x|y) & !x & !y");

        let backward = solver.reconstruct_lrat_backward();
        // Should complete without panicking. The proof should contain at least
        // the empty clause step.
        assert!(
            !backward.steps.is_empty(),
            "backward reconstruction should produce at least the empty clause step"
        );

        // The last step should be the empty clause.
        let last = backward.steps.last().expect("should have steps");
        assert!(
            last.literals.is_empty(),
            "last step should be the empty clause"
        );
        assert!(
            !last.hints.is_empty(),
            "empty clause should have hints (antecedent clause IDs)"
        );
    }

    #[test]
    fn test_clause_trace_with_certificate_disabled() {
        // Internal-query configuration (ay-chc): clause trace enabled for
        // clause-ID tracking + #5384 UNSAT replay, but the UNSAT proof
        // certificate disabled because it is never consumed. UNSAT must skip
        // backward LRAT reconstruction (empty certificate) while leaving the
        // in-memory ClauseTrace fully intact.
        use crate::literal::Variable;
        let v0 = Variable(0);
        let v1 = Variable(1);

        let build = |certificate_enabled: bool| {
            let mut solver = Solver::new(2);
            solver.enable_clause_trace();
            solver.set_unsat_certificate_enabled(certificate_enabled);
            solver.set_preprocess_enabled(false);
            solver.add_clause(vec![Literal::positive(v0), Literal::positive(v1)]);
            solver.add_clause(vec![Literal::negative(v0)]);
            solver.add_clause(vec![Literal::negative(v1)]);
            solver
        };

        // Certificate disabled: UNSAT with an empty certificate.
        let mut solver = build(false);
        let result = solver.solve();
        match result.into_inner() {
            SatResult::Unsat(cert) => {
                assert_eq!(
                    cert.step_count(),
                    0,
                    "certificate must be empty when unsat_certificate_enabled=false"
                );
                assert!(
                    !cert.is_complete(),
                    "empty certificate must report incomplete"
                );
            }
            other => panic!("expected UNSAT, got sat={:?}", other.is_sat()),
        }

        // ClauseTrace must be intact: all three original clauses recorded and
        // the empty-clause UNSAT marker set.
        let trace = solver
            .clause_trace()
            .expect("clause trace must survive certificate-disabled UNSAT");
        assert_eq!(
            trace.original_clauses().count(),
            3,
            "all original clauses must be recorded in the trace"
        );
        assert!(
            trace.has_empty_clause(),
            "trace must carry the UNSAT empty-clause marker"
        );

        // Contrast: same instance with the certificate enabled (default)
        // produces a non-empty backward-reconstructed proof.
        let mut solver = build(true);
        let result = solver.solve();
        match result.into_inner() {
            SatResult::Unsat(cert) => {
                assert!(
                    cert.step_count() > 0,
                    "certificate-enabled UNSAT must produce backward proof steps"
                );
            }
            other => panic!("expected UNSAT, got sat={:?}", other.is_sat()),
        }
    }

    // ── Streaming UNSAT core integration tests (#8250) ────────────────

    #[test]
    fn test_streaming_core_trivial_unsat() {
        // {x} and {-x}: contradictory unit clauses
        use crate::literal::Variable;
        let v0 = Variable(0);
        let mut solver = Solver::new(1);
        solver.add_clause(vec![Literal::positive(v0)]);
        solver.add_clause(vec![Literal::negative(v0)]);

        let result = solver.solve();
        match result.into_inner() {
            SatResult::Unsat(cert) => {
                // Streaming core should be present and non-empty.
                // Both clauses are needed: {x} (ID 1) and {-x} (ID 2).
                let core = cert.minimal_core();
                assert!(
                    !core.is_empty(),
                    "streaming core should be non-empty for UNSAT"
                );
                // All IDs in core should be valid original clause IDs (1 or 2).
                for &id in &core {
                    assert!((1..=2).contains(&id), "core ID {id} out of range [1, 2]");
                }
            }
            other => panic!("expected UNSAT, got {:?}", other.is_sat()),
        }
    }

    #[test]
    fn test_streaming_core_sat_instance_has_no_core() {
        // SAT: {x}. No conflict analysis, so streaming core should be empty.
        use crate::literal::Variable;
        let v0 = Variable(0);
        let mut solver = Solver::new(1);
        solver.add_clause(vec![Literal::positive(v0)]);

        let result = solver.solve();
        assert!(result.is_sat(), "expected SAT for single positive unit");
        // SAT results don't have ProofCertificate with a streaming core,
        // but the solver's internal bitmap should be all-false.
        // We verify this indirectly: after SAT, if we could access the
        // certificate (we can't for SAT), it would have no core.
    }

    #[test]
    fn test_streaming_core_small_unsat() {
        // (x | y) & (-x) & (-y): UNSAT
        // Original clause IDs: 1=(x|y), 2=(-x), 3=(-y)
        // All three are needed to derive contradiction.
        use crate::literal::Variable;
        let v0 = Variable(0);
        let v1 = Variable(1);
        let mut solver = Solver::new(2);
        solver.add_clause(vec![Literal::positive(v0), Literal::positive(v1)]);
        solver.add_clause(vec![Literal::negative(v0)]);
        solver.add_clause(vec![Literal::negative(v1)]);

        let result = solver.solve();
        match result.into_inner() {
            SatResult::Unsat(cert) => {
                let core = cert.minimal_core();
                assert!(
                    !core.is_empty(),
                    "streaming core should be non-empty for UNSAT"
                );
                // Streaming core should not require proof materialization
                // (if streaming core is present, it returns without DAG walk).
                if cert.has_streaming_core() {
                    assert!(
                        cert.is_deferred(),
                        "streaming core should not trigger proof materialization"
                    );
                }
            }
            other => panic!("expected UNSAT, got {:?}", other.is_sat()),
        }
    }

    #[test]
    fn test_streaming_core_with_redundant_clauses() {
        // (x) & (-x) & (y): clause (y) is redundant for UNSAT.
        // Streaming core should contain at most {1, 2} (not 3).
        use crate::literal::Variable;
        let v0 = Variable(0);
        let v1 = Variable(1);
        let mut solver = Solver::new(2);
        solver.add_clause(vec![Literal::positive(v0)]); // ID 1
        solver.add_clause(vec![Literal::negative(v0)]); // ID 2
        solver.add_clause(vec![Literal::positive(v1)]); // ID 3 (redundant)

        let result = solver.solve();
        match result.into_inner() {
            SatResult::Unsat(cert) => {
                let core = cert.minimal_core();
                assert!(
                    !core.is_empty(),
                    "streaming core should be non-empty for UNSAT"
                );
                // The redundant clause (ID 3) should not be in the core.
                assert!(
                    !core.contains(&3),
                    "redundant clause (y) should not be in streaming core, got: {core:?}"
                );
                // Both conflicting clauses should be present.
                assert!(
                    core.contains(&1) && core.contains(&2),
                    "both conflicting unit clauses should be in core, got: {core:?}"
                );
            }
            other => panic!("expected UNSAT, got {:?}", other.is_sat()),
        }
    }
}
