// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Failed-literal probing: the empty-clause closer for a refutation whose
//! traced hint chain runs through bit-level variables (#aig-bridged-empty).
//!
//! The eager bit-blaster encodes a Boolean structure over bit-vector atoms
//! twice: once as the Tseitin layer over term-mapped variables, and once as an
//! and-inverter graph over the comparator outputs, linked to the Tseitin layer
//! by `(¬g ∨ n)` clauses. The AIG nodes have no term, so every trace clause
//! that mentions one is untranslatable and dropped from replay.
//!
//! Measured on the model-checker-consumer realloc validation query (r1/r3, 2026-10-23):
//! thirteen top-level `(or ule_a ule_b)` conjuncts and the authored
//! `(not (and ..))` over `(not (= b68 0))` and twelve of the same
//! disjunctions, which preprocessing turns into
//! `(or (= b68 0) (and ¬ule_a ¬ule_b) ..)`. The SAT core refutes at level 0
//! THROUGH the AIG: the asserted `or` becomes the original unit `¬n` on the
//! node of `(and ¬ule_a ¬ule_b)`, and `(¬g ∨ n)` carries it to the Tseitin
//! literal `g` of that `and` term. Twenty-four of the empty clause's
//! twenty-seven hints are such clauses. Replay keeps only three of them and
//! ends on the thirteen-literal residual `(¬or ∨ g1 ∨ .. ∨ g12)`.
//!
//! The term-level clauses that DID translate still refute the problem, but not
//! by unit propagation alone. Each `¬g_i` needs a one-literal case split:
//! `g_i` forces `¬ule_a` and `¬ule_b` through its `and_pos` clauses, and that
//! falsifies the asserted `(or ule_a ule_b)`. So `derive_empty_via_level0_rup`
//! stalls. The bounded DPLL closer cannot learn, so it re-splits the same
//! disjunctions in every branch, including the thirteenth one that no gate
//! needs, and its tree passes the 4096-node cap. The
//! empty clause then fell to the premise-bearing `trust` step that mandatory
//! strict certification rejects ("step t7 uses unverified trust rule"), and
//! `--proof` answered `unknown`.
//!
//! This closer finds the missing units directly. It assumes one candidate
//! literal `l` and unit-propagates. A conflict is folded into a resolution
//! derivation of `(cl ¬l)` over existing proof nodes, and that unit joins the
//! database. When a round of probes has learned all it can, the level-0
//! closure is re-run, and a conflict there folds to `(cl)`. Every emitted step
//! is an ordinary `resolution` over clause versions the proof already
//! derives. Versions proved by `trust` are excluded, as in the other honest
//! closers. No fact is assumed and none is read from the untranslatable
//! clauses.
//!
//! Fail-closed. If the database is not refuted within the probe budget, the
//! stop predicate fires, the #A2b step budget runs out, or a fold fails, every
//! step this closer added is truncated and `None` lets the caller's existing
//! fallback run unchanged.

use super::*;

/// Unit propagations one probing call may spend, level-0 closures included.
/// Each costs what one bounded-DPLL node costs (a propagation to fixpoint over
/// the same database), and this closer runs only after that search failed, so
/// the cap is the same `DPLL_MAX_NODES`.
const PROBE_MAX_PROPAGATIONS: usize = DPLL_MAX_NODES;

/// The outcome of one budgeted propagation: the conflicting version, if any,
/// and the implications recorded on the way.
type ProbeOutcome = (Option<usize>, Vec<(usize, Literal)>);

impl SatProofManager<'_> {
    /// Derive the empty clause over the processed clause database by
    /// failed-literal probing (see the module documentation).
    ///
    /// Returns the proof node of `(cl)` built from genuine `resolution` steps,
    /// or `None` with `proof` restored to its entry length.
    pub(in crate::sat_proof_manager) fn derive_empty_via_failed_literal_probing(
        &mut self,
        clause_versions: &[SatClauseVersion],
        proof: &mut Proof,
    ) -> Option<ProofId> {
        if clause_versions.is_empty() || clause_versions.len() > MAX_RUP_WIDENING_VERSIONS {
            return None;
        }
        // Honest closers only: the empty clause must not ride on a version a
        // `trust` step proves (the very kind of step this closer replaces).
        let mut versions: Vec<SatClauseVersion> = clause_versions
            .iter()
            .filter(|(_, pid)| {
                !matches!(
                    proof.get_step(*pid),
                    Some(ProofStep::Step {
                        rule: AletheRule::Trust,
                        ..
                    })
                )
            })
            .cloned()
            .collect();
        let steps_snapshot = proof.steps.len();
        let derived = self.probe_until_empty(&mut versions, proof);
        if derived.is_none() {
            proof.steps.truncate(steps_snapshot);
        } else {
            tracing::debug!(
                learned = versions.len().saturating_sub(clause_versions.len()),
                "failed-literal probing closed the empty clause"
            );
        }
        derived
    }

    /// Rounds of probes, each followed by a level-0 closure, until the
    /// closure conflicts (success), a round learns nothing (`None`), or the
    /// budget runs out (`None`).
    fn probe_until_empty(
        &mut self,
        versions: &mut Vec<SatClauseVersion>,
        proof: &mut Proof,
    ) -> Option<ProofId> {
        let mut engine = RupEngine::default();
        let mut propagations = 0usize;
        let mut learned: HashSet<Literal> = HashSet::default();
        loop {
            let (conflict, implications) =
                self.probe_propagate(&mut engine, versions, None, &mut propagations)?;
            if let Some(conflict_version) = conflict {
                let folded = self.fold_conflict_to_assumption_clause(
                    conflict_version,
                    &implications,
                    &[],
                    versions,
                    &engine,
                    proof,
                );
                return folded
                    .filter(|(_, sat)| sat.is_empty())
                    .map(|(empty, _)| empty);
            }
            let candidates = Self::probe_candidates(&engine, versions);
            engine.reset();
            let mut learned_this_round = false;
            for literal in candidates {
                if learned.contains(&literal) || learned.contains(&literal.negated()) {
                    continue;
                }
                let (conflict, implications) =
                    self.probe_propagate(&mut engine, versions, Some(literal), &mut propagations)?;
                let Some(conflict_version) = conflict else {
                    engine.reset();
                    continue;
                };
                let folded = self.fold_conflict_to_assumption_clause(
                    conflict_version,
                    &implications,
                    &[literal],
                    versions,
                    &engine,
                    proof,
                );
                engine.reset();
                // The fold returns a clause over the negated assumptions:
                // `(cl ¬literal)`, or `(cl)` when the conflict never used the
                // probe.
                let (derived_proof, derived_sat) = folded?;
                if derived_sat.is_empty() {
                    return Some(derived_proof);
                }
                learned.insert(literal.negated());
                versions.push((derived_sat, derived_proof));
                learned_this_round = true;
            }
            if !learned_this_round {
                return None;
            }
        }
    }

    /// Propagate to fixpoint from the database's units plus `probe`. `None`
    /// means the probe budget, the caller's stop, or the #A2b step budget ran
    /// out, so the caller abandons the search.
    fn probe_propagate(
        &mut self,
        engine: &mut RupEngine,
        versions: &[SatClauseVersion],
        probe: Option<Literal>,
        propagations: &mut usize,
    ) -> Option<ProbeOutcome> {
        if *propagations >= PROBE_MAX_PROPAGATIONS || self.should_stop.is_some_and(|stop| stop()) {
            return None;
        }
        *propagations += 1;
        if let Some(literal) = probe {
            engine.assign(literal);
        }
        let mut implications: Vec<(usize, Literal)> = Vec::new();
        let mut used: HashSet<usize> = HashSet::default();
        let mut budget = self.step_budget;
        let conflict = engine.propagate(versions, &mut implications, &mut used, &mut budget);
        self.step_budget = budget;
        // An exhausted budget stalls propagation, so "no conflict" would be
        // unfounded. A conflict found before exhaustion is still genuine.
        if conflict.is_none() && matches!(budget, Some(0)) {
            return None;
        }
        Some((conflict, implications))
    }

    /// The literals a probe may assume: every literal still unassigned at
    /// level 0 in a clause level 0 does not satisfy, in database order.
    fn probe_candidates(engine: &RupEngine, versions: &[SatClauseVersion]) -> Vec<Literal> {
        let mut seen: HashSet<Literal> = HashSet::default();
        let mut candidates = Vec::new();
        for (clause, _) in versions {
            if clause.iter().any(|&lit| engine.value(lit) == Some(true)) {
                continue;
            }
            for &lit in clause {
                if engine.value(lit).is_none() && seen.insert(lit) {
                    candidates.push(lit);
                }
            }
        }
        candidates
    }
}
