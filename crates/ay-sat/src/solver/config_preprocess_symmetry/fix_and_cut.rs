// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0
//! The fix-and-cut branch of the composite symmetry route (symmetry fixing,
//! steps 3 and 4): `--sat-symmetry-fix-and-cut`.
//!
//! Every derived clause carries its certificate: an SR step whose witness is
//! the automorphism justifying it (a fix's carrier, a cut's transversal
//! element, a flip), or a RUP step (a fixed unit after its binaries, an
//! exclusive clause's other literals). Under a proof the steps go to the
//! witnessed SR surface the aux-free route uses (`proof_emit_add_sr`), in
//! derivation order, which is what makes each witness valid: it fixes every
//! base point before it, so the constraints already derived map onto
//! themselves.

use crate::proof_manager::ProofAddKind;
use crate::solver::mutate::AddResult;
use crate::solver::Solver;
use crate::symmetry::detector::SymmetryDetector;
use crate::Literal;

impl Solver {
    /// Run the walk over the root formula and install its steps, emitting
    /// each to the proof first. Returns `(unsat, changed)`.
    pub(super) fn symmetry_fix_and_cut_install(
        &mut self,
        detector: &SymmetryDetector,
        clauses: &[Vec<Literal>],
    ) -> (bool, bool) {
        let (walk, chain) = detector.detect_fix_and_cut(clauses, self.num_vars as u32);
        let stats = &mut self.cold.symmetry_stats;
        stats.chain_generators = chain.generators;
        stats.chain_base_len = chain.base_len;
        stats.chain_orbits = chain.orbits;
        stats.fixcut_fixings = walk.fixings;
        stats.fixcut_cuts = walk.cuts;
        stats.fixcut_levels = walk.base.len() as u64;
        stats.fixcut_work = walk.work;
        stats.fixcut_budget_hit = u64::from(walk.budget_hit);
        stats.fixcut_rounds = u64::from(walk.rounds);
        // A step on a variable the root already assigned would contradict
        // or duplicate a fact the residual snapshot did not carry: abort the
        // whole route rather than install any of it.
        if walk
            .steps
            .iter()
            .flat_map(|s| s.clause.iter())
            .any(|&l| self.lit_value(l).is_some())
        {
            self.cold
                .symmetry_stats
                .skip(crate::symmetry::SymmetrySkipReason::NoPairs);
            return (false, false);
        }
        let mut changed = false;
        for step in walk.steps {
            let emitted = if step.witness.is_empty() {
                self.proof_emit_add(&step.clause, &[], ProofAddKind::Derived)
                    .map(|_| ())
            } else {
                self.proof_emit_add_sr(&step.clause, &step.witness)
            };
            if emitted.is_err() {
                break;
            }
            let mut lits = step.clause;
            match self.add_clause_watched_trusted(&mut lits) {
                AddResult::Added(_) | AddResult::Unit(_) => {
                    changed = true;
                    self.cold.symmetry_stats.sb_clauses_added =
                        self.cold.symmetry_stats.sb_clauses_added.saturating_add(1);
                }
                AddResult::Empty => return (true, true),
            }
        }
        if !changed {
            self.cold
                .symmetry_stats
                .skip(crate::symmetry::SymmetrySkipReason::NoPairs);
        }
        (false, changed)
    }
}
