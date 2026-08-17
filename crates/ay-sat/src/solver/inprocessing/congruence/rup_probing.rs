// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//\! RUP-based probing helpers for congruence LRAT proof generation.

use super::super::super::*;

fn probe_triage_matches(lits: &[Literal]) -> bool {
    use std::sync::OnceLock;
    static T: OnceLock<Option<Vec<i64>>> = OnceLock::new();
    let t = T.get_or_init(|| {
        ay_core::misc_cli_flags()
            .ab_triage_probe
            .as_deref()
            .map(|s| {
                let mut v: Vec<i64> = s.split(',').filter_map(|x| x.trim().parse().ok()).collect();
                v.sort_unstable();
                v
            })
    });
    match t {
        Some(t) => {
            let mut mine: Vec<i64> = lits
                .iter()
                .map(|l| {
                    let d = i64::from(l.variable().0) + 1;
                    if l.is_positive() {
                        d
                    } else {
                        -d
                    }
                })
                .collect();
            mine.sort_unstable();
            &mine == t
        }
        None => false,
    }
}

impl Solver {
    /// Drain pending root-level propagations before probe decisions.
    #[inline]
    fn probe_has_root_conflict(&mut self) -> bool {
        if self.qhead == self.trail.len() {
            return false;
        }
        self.search_propagate().is_some()
    }

    /// Choose a polarity for a congruence contradiction witness that is RUP.
    ///
    /// The congruence engine reports a literal whose variable satisfies `x ≡ ¬x`.
    /// Depending on merge orientation, either polarity may be the direct
    /// conflict-triggering unit. Probe both and pick a robust proof literal.
    pub(super) fn pick_congruence_contradiction_unit(&mut self, witness: Literal) -> Literal {
        for candidate in [witness, witness.negated()] {
            if self.unit_forces_conflict(candidate) {
                return candidate;
            }
        }
        for candidate in [witness, witness.negated()] {
            if self.is_rup_unit_under_negation(candidate) {
                return candidate;
            }
        }
        witness
    }

    /// Return true if `unit` is RUP by checking whether assuming `¬unit`
    /// immediately produces a conflict via unit propagation.
    pub(crate) fn is_rup_unit_under_negation(&mut self, unit: Literal) -> bool {
        debug_assert_eq!(
            self.decision_level, 0,
            "BUG: RUP probe for congruence unit must start at level 0"
        );
        if self.probe_has_root_conflict() {
            return true;
        }

        let negated = unit.negated();
        match self.lit_value(negated) {
            Some(false) => return true,
            Some(true) => return false,
            None => {}
        }

        self.decide(negated);
        let conflict = self.search_propagate().is_some();
        self.backtrack(0);
        conflict
    }

    /// Return true if adding `unit` immediately causes a propagation conflict.
    fn unit_forces_conflict(&mut self, unit: Literal) -> bool {
        debug_assert_eq!(
            self.decision_level, 0,
            "BUG: unit-for-conflict probe must start at level 0"
        );
        if self.probe_has_root_conflict() {
            return true;
        }

        match self.lit_value(unit) {
            Some(false) => return true,
            Some(true) => return false,
            None => {}
        }

        self.decide(unit);
        let conflict = self.search_propagate().is_some();
        self.backtrack(0);
        conflict
    }

    /// Return true if binary clause `(lit0 ∨ lit1)` is RUP under current state.
    ///
    /// RUP check for a binary clause assumes both negated literals and asks
    /// whether unit propagation reaches conflict.
    pub(super) fn is_rup_binary_under_negation(&mut self, lit0: Literal, lit1: Literal) -> bool {
        debug_assert_eq!(
            self.decision_level, 0,
            "BUG: binary RUP probe must start at level 0"
        );
        if self.probe_has_root_conflict() {
            return true;
        }

        let mut conflict = false;
        for assumption in [lit0.negated(), lit1.negated()] {
            match self.lit_value(assumption) {
                Some(false) => {
                    conflict = true;
                    break;
                }
                Some(true) => {}
                None => {
                    self.decide(assumption);
                    if self.search_propagate().is_some() {
                        conflict = true;
                        break;
                    }
                }
            }
        }
        self.backtrack(0);
        conflict
    }

    /// Return true if clause `lits` is RUP under the current state: assume
    /// the negation of every literal and ask whether unit propagation reaches
    /// conflict. Generalizes `is_rup_binary_under_negation` to arbitrary
    /// width (#15 T3 ladder rungs).
    pub(super) fn is_rup_clause_under_negation(&mut self, lits: &[Literal]) -> bool {
        debug_assert_eq!(
            self.decision_level, 0,
            "BUG: clause RUP probe must start at level 0"
        );
        if self.probe_has_root_conflict() {
            return true;
        }

        let triage = probe_triage_matches(lits);
        let mut conflict = false;
        for &lit in lits {
            let assumption = lit.negated();
            match self.lit_value(assumption) {
                Some(false) => {
                    conflict = true;
                    if triage {
                        eprintln!(
                            "TRIAGE_PROBE: pre-falsified assumption {}",
                            assumption.index()
                        );
                    }
                    break;
                }
                Some(true) => {}
                None => {
                    self.decide(assumption);
                    if let Some(conflict_ref) = self.search_propagate() {
                        conflict = true;
                        if triage {
                            self.dump_probe_conflict_for_triage(conflict_ref);
                        }
                        break;
                    }
                }
            }
        }
        self.backtrack(0);
        conflict
    }

    /// Soundness-triage: dump the probe's conflict clause and every
    /// decision-level reason with garbage flags (--sat-ab-triage-probe).
    fn dump_probe_conflict_for_triage(&mut self, conflict_ref: ClauseRef) {
        let dump_clause = |arena: &ClauseArena, off: usize| -> String {
            let lits: Vec<String> = arena
                .literals(off)
                .iter()
                .map(|l| l.index().to_string())
                .collect();
            format!(
                "off={} garbage={} lits=[{}]",
                off,
                arena.is_garbage(off),
                lits.join(" ")
            )
        };
        eprintln!(
            "TRIAGE_PROBE: CONFLICT {}",
            dump_clause(&self.arena, conflict_ref.0 as usize)
        );
        let trail_snapshot: Vec<Literal> = self.trail().to_vec();
        for tl in trail_snapshot {
            let vi = tl.variable().index();
            if self.var_data[vi].level == 0 {
                continue;
            }
            match self.var_reason_kind(vi) {
                ReasonKind::Clause(r) => {
                    eprintln!(
                        "TRIAGE_PROBE: reason lit={} {}",
                        tl.index(),
                        dump_clause(&self.arena, r.0 as usize)
                    );
                }
                ReasonKind::BinaryLiteral(other) => {
                    eprintln!(
                        "TRIAGE_PROBE: reason lit={} BINARY other={}",
                        tl.index(),
                        other.index()
                    );
                }
                _ => {
                    eprintln!("TRIAGE_PROBE: reason lit={} DECISION/OTHER", tl.index());
                }
            }
        }
    }

    /// Build a scratch forward checker from the current active clause DB.
    ///
    /// Collect LRAT resolution hints for a binary clause (lit0 v lit1).
    ///
    /// Assumes both negated literals, propagates, and on conflict collects the
    /// resolution chain. Returns empty if LRAT is not enabled or not RUP.
    ///
    /// Design: #5419 Phase A. Follows the probe pattern from
    /// `collect_probe_conflict_lrat_hints` but handles the two-assumption
    /// (level-2) case by using `collect_resolution_chain` directly.
    pub(crate) fn collect_rup_binary_lrat_hints(
        &mut self,
        lit0: Literal,
        lit1: Literal,
    ) -> Vec<u64> {
        if !self.cold.lrat_enabled {
            return Vec::new();
        }
        debug_assert_eq!(self.decision_level, 0);

        if self.probe_has_root_conflict() {
            return Vec::new();
        }

        // First assumption: negate lit0
        let neg0 = lit0.negated();
        match self.lit_value(neg0) {
            Some(false) => {
                // neg0 is already false => lit0 is true => clause is satisfied
                return Vec::new();
            }
            Some(true) => {
                // neg0 already true, proceed to second assumption
            }
            None => {
                self.decide(neg0);
                if let Some(conflict_ref) = self.search_propagate() {
                    // Conflict at level 1: standard probe pattern
                    let hints =
                        self.collect_probe_conflict_lrat_hints(conflict_ref, neg0, Some(lit0));
                    self.backtrack(0);
                    return hints;
                }
            }
        }

        // Second assumption: negate lit1
        let neg1 = lit1.negated();
        match self.lit_value(neg1) {
            Some(false) => {
                // neg1 is already false => lit1 was propagated true by BCP
                // from the neg0 decision (or level-0 assignment) => clause
                // (lit0 ∨ lit1) is RUP.
                //
                // Use the reason clause for neg1's variable as the conflict
                // seed for collect_resolution_chain. Under the RUP assumption
                // {¬lit0, ¬lit1}, this reason clause becomes all-false
                // (conflict), since it propagated lit1 to true when all its
                // other literals were already false.
                //
                // The rup_satisfied set contains {neg0, neg1} — the literals
                // that are TRUE under the RUP assumption. Any hint clause
                // containing these is trivially satisfied and must be excluded
                // from the LRAT chain (#5026, #7108).
                let target_vi = neg1.variable().index();
                let mut rup_satisfied = crate::kani_compat::det_hash_set_new();
                rup_satisfied.insert(neg0);
                rup_satisfied.insert(neg1);

                if let Some(reason_ref) = self.var_reason(target_vi) {
                    let chain = self.collect_resolution_chain(reason_ref, None, &rup_satisfied);
                    let hints = Self::lrat_reverse_hints(&chain);
                    self.backtrack(0);
                    return hints;
                }
                // No reason clause (unit at level 0): use unit_proof_id
                // directly as the sole hint.
                if let Some(unit_id) = self.visible_unit_proof_id_for_lit(neg1) {
                    self.backtrack(0);
                    return vec![unit_id];
                }
                // No proof chain available — fall through to return empty
                // (caller will use TrustedTransform).
                self.backtrack(0);
                return Vec::new();
            }
            Some(true) => {
                // neg1 already true => no conflict possible
                self.backtrack(0);
                return Vec::new();
            }
            None => {
                self.decide(neg1);
                if let Some(conflict_ref) = self.search_propagate() {
                    // Conflict at level 1 or 2 (level 1 when neg0 was already
                    // true at level 0). Use collect_resolution_chain directly
                    // since collect_probe_conflict_lrat_hints asserts level 1.
                    // rup_satisfied: under the RUP assumption for (lit0 ∨ lit1),
                    // ¬lit0 and ¬lit1 are TRUE. Hint clauses containing these
                    // are trivially satisfied and must be excluded (#7108).
                    let mut rup_satisfied = crate::kani_compat::det_hash_set_new();
                    rup_satisfied.insert(neg0);
                    rup_satisfied.insert(neg1);
                    let chain = self.collect_resolution_chain(conflict_ref, None, &rup_satisfied);
                    let hints = Self::lrat_reverse_hints(&chain);
                    self.backtrack(0);
                    return hints;
                }
            }
        }

        self.backtrack(0);
        Vec::new() // Not RUP
    }

    /// Collect LRAT resolution hints for a unit clause.
    ///
    /// Assumes the negated unit at level 1, propagates, and on conflict
    /// collects the resolution chain. Returns empty if LRAT is not enabled
    /// or the unit is not RUP.
    ///
    /// Design: #5419 Phase C. Follows the standard probe pattern exactly.
    pub(crate) fn collect_rup_unit_lrat_hints(&mut self, unit: Literal) -> Vec<u64> {
        if !self.cold.lrat_enabled {
            return Vec::new();
        }
        debug_assert_eq!(self.decision_level, 0);

        // Materialize unit proof IDs for level-0 BCP-implied variables
        // before collecting LRAT hints. Without this, level-0 variables
        // implied by multi-literal clauses have no unit_proof_id, and
        // collect_probe_conflict_lrat_hints falls back to multi-literal
        // reason clause IDs which fail strict RUP verification (#7108).
        self.ensure_level0_unit_proof_ids();

        if self.probe_has_root_conflict() {
            return Vec::new();
        }

        let negated = unit.negated();
        match self.lit_value(negated) {
            Some(false) => return Vec::new(), // unit already true
            Some(true) => return Vec::new(),  // negation already true, no conflict
            None => {}
        }

        self.decide(negated);
        let hints = if let Some(conflict_ref) = self.search_propagate() {
            self.collect_probe_conflict_lrat_hints(conflict_ref, negated, Some(unit))
        } else {
            Vec::new()
        };
        self.backtrack(0);
        hints
    }
}
