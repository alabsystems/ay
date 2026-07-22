// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Backbone and equivalence probing for kitten-based sweep.

use super::Sweeper;
use crate::clause_arena::ClauseArena;
#[cfg(debug_assertions)]
use crate::kitten::Kitten;
use crate::literal::Literal;

impl Sweeper {
    /// Probe for backbone literals and equivalences in the current kitten model.
    ///
    /// After kitten returns SAT on the COI:
    /// 1. Try flipping each COI variable — if flip fails, it's a backbone candidate
    /// 2. For backbone candidates: assume negation → if UNSAT, it's a backbone literal
    /// 3. For remaining pairs: probe for equivalences
    pub(super) fn probe_backbone_and_equivalences(
        &mut self,
        clauses: &ClauseArena,
        vals: &[i8],
        frozen: &[u32],
        new_units: &mut Vec<Literal>,
        equivalences: &mut Vec<(u32, u32)>,
    ) {
        // Phase 1: Collect COI variables as backbone candidates and build the
        // signed candidate partition from the current kitten model. Each
        // variable contributes the literal that is currently true in the COI
        // model, matching CaDiCaL sweep.cpp:init_backbone_and_partition().
        //
        // This must stay as a single signed partition instead of separate
        // positive/negative buckets. Otherwise sweep can never discover
        // equivalences like x <-> !y because the true literals end up in
        // different buckets and are never probed together.
        let mut backbone_candidates: Vec<u32> = Vec::new();
        let mut partition_candidates: Vec<u32> = Vec::new();

        for &var_idx in &self.coi_vars {
            let pos_lit = (var_idx as u32) * 2;
            let neg_lit = pos_lit + 1;
            if var_idx < frozen.len() && frozen[var_idx] > 0 {
                continue;
            }
            let pos_val = self.kitten.value(pos_lit);
            if pos_val == 0 {
                continue; // unassigned in kitten
            }
            let true_lit = if pos_val > 0 { pos_lit } else { neg_lit };
            backbone_candidates.push(true_lit);
            partition_candidates.push(true_lit);
        }

        // Phase 2: Backbone probing with flip filter.
        // CaDiCaL sweep.cpp:770-821: flip_backbone_literals is a cheap O(watchlist)
        // filter that eliminates ~90% of candidates. If flipping a literal's value
        // succeeds (all clauses still satisfied), it's NOT a backbone.
        // Only candidates that survive the flip filter need full probing.
        let mut surviving_candidates: Vec<u32> = Vec::new();
        for &true_lit in &backbone_candidates {
            if self.kitten.flip_literal(true_lit) {
                // Flip succeeded: literal is not a backbone. CaDiCaL: sweep.cpp:793.
                // Note: flip_literal modifies the model in-place, which refines
                // subsequent flip checks (other candidates see the updated model).
            } else {
                // Flip failed: candidate survives, needs full probe.
                surviving_candidates.push(true_lit);
            }
        }

        // Full probe surviving candidates: assume negation, solve.
        // CaDiCaL sweep.cpp:839-897: sweep_backbone_candidate.
        // Cap at 32 probes to bound cost.
        let max_backbone_probes = surviving_candidates.len().min(32);
        for &true_lit in surviving_candidates.iter().take(max_backbone_probes) {
            if self.kitten.fixed_value(true_lit) > 0 {
                new_units.push(Literal(true_lit));
                self.stats.kitten_backbone += 1;
                continue;
            }
            self.kitten.assume(true_lit ^ 1); // assume negation
            let res = self.randomized_kitten_solve();
            if res == 20 {
                // Backbone candidate: ¬lit is UNSAT in the COI. This is sound by
                // monotonicity: a contradiction on a clause subset remains a
                // contradiction in the full formula.
                new_units.push(Literal(true_lit));
                self.stats.kitten_backbone += 1;
            }
        }

        // Phase 3: Equivalence probing on the signed candidate partition.
        // Reuses the kitten COI instance incrementally (no rebuild per probe).
        self.probe_partition_classes(clauses, vals, &partition_candidates, equivalences);
    }

    /// Refine the signed candidate partition until no further splits remain.
    ///
    /// The partition stores signed literals that are currently plausible
    /// equivalence candidates. For each class we keep the first literal as the
    /// representative, probe every other member against it, and split all
    /// non-equivalent members into a new class. Repeating this produces the
    /// representative-driven partition refinement loop described in #5046.
    ///
    /// Signed literals are used instead of unsigned variables so sweep can
    /// discover mixed-polarity equivalences such as `x <-> !y`.
    #[cfg_attr(not(debug_assertions), allow(unused_variables))]
    pub(super) fn probe_partition_classes(
        &mut self,
        clauses: &ClauseArena,
        vals: &[i8],
        class: &[u32],
        equivalences: &mut Vec<(u32, u32)>,
    ) {
        if class.len() < 2 {
            return;
        }

        let mut partition: Vec<Vec<u32>> = vec![class.to_vec()];
        while let Some(current_class) = partition.pop() {
            if current_class.len() < 2 || equivalences.len() >= 1000 {
                continue;
            }

            let rep = current_class[0];
            let mut active_class = current_class;
            let mut idx = 1;

            while idx < active_class.len() && equivalences.len() < 1000 {
                let other = active_class[idx];
                match self.probe_equivalence_against_rep(rep, other) {
                    EquivalenceProbe::Equivalent => {
                        equivalences.push((rep, other));
                        self.stats.kitten_equivalences += 1;
                        active_class.remove(idx);

                        // Defense-in-depth: verify against full formula in
                        // debug builds. Zero cost in release.
                        #[cfg(debug_assertions)]
                        debug_assert!(
                            self.debug_verify_equivalence_claim(rep, other, clauses, vals),
                            "BUG: kitten claimed false equivalence {rep} = {other}"
                        );
                    }
                    EquivalenceProbe::NotEquivalent => {
                        // The SAT result is a countermodel for this class.
                        // Split all still-active signed candidates by their
                        // value in that model, matching CaDiCaL's
                        // sweep_refine_partition() true/false buckets.
                        let refined = self.refine_partition_class_from_current_model(&active_class);
                        self.stats.kitten_partition_refinements += 1;
                        partition.extend(refined);
                        break;
                    }
                    EquivalenceProbe::Unknown => {
                        idx += 1;
                    }
                }
            }
        }
    }

    /// Split a signed candidate class by the current kitten model.
    ///
    /// SAT countermodels are random simulations of the COI. Candidates that
    /// remain equivalent must keep the same signed truth value; candidates that
    /// differ are separated, unassigned literals are dropped, and singleton
    /// buckets are discarded.
    pub(super) fn refine_partition_class_from_current_model(&self, class: &[u32]) -> Vec<Vec<u32>> {
        let mut true_class = Vec::new();
        let mut false_class = Vec::new();

        for &lit in class {
            match self.kitten.value(lit) {
                value if value > 0 => true_class.push(lit),
                value if value < 0 => false_class.push(lit),
                _ => {}
            }
        }

        let mut refined = Vec::new();
        if true_class.len() > 1 {
            refined.push(true_class);
        }
        if false_class.len() > 1 {
            refined.push(false_class);
        }
        refined
    }

    /// Probe whether `lit` and `rep` are equivalent inside the current COI.
    ///
    /// The two implication checks are the sweep queries from #5046:
    /// - `lit ∧ !rep` UNSAT proves `lit -> rep`
    /// - `!lit ∧ rep` UNSAT proves `rep -> lit`
    fn probe_equivalence_against_rep(&mut self, rep: u32, lit: u32) -> EquivalenceProbe {
        self.kitten.assume(lit);
        self.kitten.assume(rep ^ 1);
        let forward = self.randomized_kitten_solve();
        if forward == 10 {
            return EquivalenceProbe::NotEquivalent;
        }
        if forward != 20 {
            return EquivalenceProbe::Unknown;
        }

        self.kitten.assume(lit ^ 1);
        self.kitten.assume(rep);
        let backward = self.randomized_kitten_solve();
        if backward == 10 {
            return EquivalenceProbe::NotEquivalent;
        }
        if backward != 20 {
            return EquivalenceProbe::Unknown;
        }

        EquivalenceProbe::Equivalent
    }

    /// Debug-only: verify a single equivalence claim against the full clause set.
    ///
    /// Builds a fresh kitten with ALL non-garbage clauses plus current level-0
    /// assignments. Returns true if `lit_a ≡ lit_b` holds on the full formula.
    /// Called only under `debug_assertions` — zero cost in release.
    ///
    /// Use this to diagnose kitten CDCL false-UNSAT bugs (#7049). If the COI
    /// probing claims an equivalence but this function rejects it, kitten
    /// produced an incorrect UNSAT result on the bounded neighborhood.
    #[cfg(debug_assertions)]
    pub(super) fn debug_verify_equivalence_claim(
        &self,
        lit_a: u32,
        lit_b: u32,
        clauses: &ClauseArena,
        vals: &[i8],
    ) -> bool {
        let build_verifier = || {
            let mut verifier = Kitten::new();
            for idx in clauses.indices() {
                if clauses.is_garbage(idx) || clauses.is_empty_clause(idx) {
                    continue;
                }
                let ext_lits: Vec<u32> = clauses.literals(idx).iter().map(|lit| lit.0).collect();
                verifier.add_clause_with_id(idx as u32, &ext_lits, u32::MAX);
            }
            for var_idx in 0..(vals.len() / 2) {
                let pos_idx = var_idx * 2;
                if vals[pos_idx] > 0 {
                    verifier.add_clause_with_id(u32::MAX, &[pos_idx as u32], u32::MAX);
                } else if vals[pos_idx + 1] > 0 {
                    verifier.add_clause_with_id(u32::MAX, &[(pos_idx + 1) as u32], u32::MAX);
                }
            }
            verifier.seal_original();
            verifier
        };

        // Direction 1: ¬a ∧ b should be UNSAT (proves b → a).
        let mut v1 = build_verifier();
        v1.assume(lit_a ^ 1);
        v1.assume(lit_b);
        let d1 = v1.solve();
        if d1 != 20 {
            eprintln!(
                "[sweep-verify] FAILED direction 1: ¬{lit_a} ∧ {lit_b} gave {d1} (expected 20/UNSAT)"
            );
            return false;
        }

        // Direction 2: a ∧ ¬b should be UNSAT (proves a → b).
        let mut v2 = build_verifier();
        v2.assume(lit_a);
        v2.assume(lit_b ^ 1);
        let d2 = v2.solve();
        if d2 != 20 {
            eprintln!(
                "[sweep-verify] FAILED direction 2: {lit_a} ∧ ¬{lit_b} gave {d2} (expected 20/UNSAT)"
            );
            return false;
        }
        true
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum EquivalenceProbe {
    Equivalent,
    NotEquivalent,
    Unknown,
}
