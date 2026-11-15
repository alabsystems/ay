// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Root shapes and witness sources of the implied-universal lane beyond the
//! authored implication (#iff-split-implied-authority).
//!
//! THE GAP THIS CLOSES, MEASURED. `9d021601f` splits a Boolean `=` with a
//! quantifier on one side before Skolemizing, so
//!
//! ```smt2
//! (assert (= q (forall ((v Int)) (> (+ (* v (ite p 0 2)) v) (- 2)))))
//! (assert q)
//! ```
//!
//! now reaches the solver as `(or (not q) F)` with `q` a unit: the universal
//! is ENTAILED. E-matching instantiates it over the ground Int terms (`0`,
//! `2`, `-2`, the Skolem constant of the other copy), the instance at `-2` is
//! false for either value of `p`, and the counterexample-free re-solve
//! refutes the query. That refutation reaches the artifact firewall
//! (`translated_unsat_proof_or_downgrade`), which publishes only an
//! authored-scope strict certificate, and every leg declined: this lane read
//! only `(=> A F)` roots, and its only witness sources were the body's ground
//! argument slots and the authored ground scan, which never descends under a
//! binder, while the refuting value exists only as an E-matched binder value.
//! The w1_51 files 13, 49 and 92 went from `unsat` to `unknown
//! (quantifier-unhandled)`. Before the split the universal sat in a Boolean
//! position, and `unsat` was admitted as `discharged-trust`: a one-step `hole`
//! certificate corroborated by a fresh-executor re-solve
//! (`--debug-cert` on `89aaebc1c`). `(=> q F)` with `(assert q)` was `unknown`
//! before the split, for the witness reason alone.
//!
//! TWO ADDITIONS, SAME LANE, NO KNOB:
//!
//! * an authored `(= A F)` (or `(= F A)`) with authored `A` yields `F` by
//!   `equiv_pos2` (`equiv_pos1`) and two resolutions — the same three-step
//!   prologue as `implies_pos`, re-derived by the strict validator from the
//!   equality itself;
//! * when the body has no ground slot witness, the binder values of this
//!   decision's CEGQI rounds and E-matched instances (`cegqi_witness_hints`,
//!   `instance_witness_hints`) are proposed before the authored scan, each
//!   kept only if every free symbol in it is authored
//!   (`authored_witness_hint_terms`), so neither a counterexample constant
//!   nor a Skolem constant reaches a certificate. `forall_inst` holds for ANY
//!   closed term, so a wrong hint is a declined candidate, never a wrong step.

use super::*;

/// Hinted values proposed per binder and per ledger when no slot witness
/// exists.
const MAX_HINT_WITNESSES: usize = 8;

impl Executor {
    /// The `(antecedent, consequent)` readings under which the authored `root`
    /// yields `consequent` once `antecedent` holds: the implication (or its
    /// desugared `or`), or either side of a Boolean equality. The caller picks
    /// the reading whose antecedent is an authored root and whose consequent is
    /// a universal; nothing here carries authority.
    pub(super) fn implied_forall_root_orientations(
        terms: &TermStore,
        root: TermId,
    ) -> Vec<(TermId, TermId)> {
        if let Some(reading) = Self::decode_implication_local(terms, root) {
            return vec![reading];
        }
        match terms.get(root) {
            TermData::App(symbol, args)
                if symbol.name() == "="
                    && args.len() == 2
                    && matches!(terms.sort(args[0]), Sort::Bool) =>
            {
                vec![(args[0], args[1]), (args[1], args[0])]
            }
            _ => Vec::new(),
        }
    }

    /// Derive `(cl consequent)` from the ALREADY-DERIVED units of the authored
    /// `root` and its `antecedent`: `implies_pos` for an implication,
    /// `equiv_pos2` for `(= antecedent consequent)`, `equiv_pos1` for
    /// `(= consequent antecedent)`, each followed by two resolutions. `None`
    /// when `root` is none of these over exactly this pair.
    pub(super) fn apply_implied_root_unit(
        &mut self,
        candidate: &mut Proof,
        root: TermId,
        root_unit: ProofId,
        antecedent: TermId,
        antecedent_unit: ProofId,
        consequent: TermId,
    ) -> Option<ProofId> {
        if Self::decode_implication_local(&self.ctx.terms, root) == Some((antecedent, consequent)) {
            return Some(self.apply_implication_unit(
                candidate,
                root,
                root_unit,
                antecedent,
                antecedent_unit,
                consequent,
            ));
        }
        let sides = match self.ctx.terms.get(root) {
            TermData::App(symbol, args)
                if symbol.name() == "="
                    && args.len() == 2
                    && matches!(self.ctx.terms.sort(antecedent), Sort::Bool) =>
            {
                (args[0], args[1])
            }
            _ => return None,
        };
        let rule = if sides == (antecedent, consequent) {
            AletheRule::EquivPos2
        } else if sides == (consequent, antecedent) {
            AletheRule::EquivPos1
        } else {
            return None;
        };
        let not_root = self.ctx.terms.mk_not_raw(root);
        let not_antecedent = self.ctx.terms.mk_not_raw(antecedent);
        let clause = match rule {
            AletheRule::EquivPos2 => vec![not_root, not_antecedent, consequent],
            _ => vec![not_root, consequent, not_antecedent],
        };
        let tautology = candidate.add_rule_step(rule, clause, Vec::new(), Vec::new());
        let open =
            candidate.add_resolution(vec![not_antecedent, consequent], root, tautology, root_unit);
        Some(candidate.add_resolution(vec![consequent], antecedent, open, antecedent_unit))
    }

    /// Ground witness candidates for one binder of an implied universal.
    ///
    /// Trigger discipline, MEASURED: the generic subterm scan proposes every
    /// Int-sorted authored subterm, and on #7956 that is 8 witnesses — 7 junk
    /// instances whose nested select/offset terms push the same-context probe
    /// past its unchanged 2000 ms grant (2003 ms, `Ok(Unknown)`). Witnesses
    /// drawn from ground ARGUMENT positions of the very symbols the body
    /// applies to the binder (there `seq_index_logic _ 0`, giving exactly `0`)
    /// leave the probe the 31-formula load measured to close in 317 ms. Only
    /// when no slot witness exists do the hints come next — the closed CEGQI
    /// binder values, then the E-matched ones smallest first — and then the
    /// authored scan, smallest first.
    pub(super) fn implied_binder_witnesses(
        &self,
        authored: &[TermId],
        slots: &ay_core::kani_compat::DetHashSet<(Symbol, usize, String)>,
        binder: &str,
        sort: &Sort,
        bound_names: &ay_core::kani_compat::DetHashSet<String>,
    ) -> Vec<TermId> {
        let slot = self.slot_ground_witnesses(authored, slots, binder, sort, bound_names);
        if !slot.is_empty() {
            return slot;
        }
        let mut candidates = self.authored_witness_hint_terms(
            &self.cegqi_witness_hints,
            authored,
            sort,
            bound_names,
            MAX_HINT_WITNESSES,
        );
        let mut matched = self.authored_witness_hint_terms(
            &self.instance_witness_hints,
            authored,
            sort,
            bound_names,
            usize::MAX,
        );
        Self::order_witnesses_smallest_first(&self.ctx.terms, &mut matched);
        let mut scanned = self.ground_witnesses_for_sort(authored, sort, bound_names);
        Self::order_witnesses_smallest_first(&self.ctx.terms, &mut scanned);
        for candidate in matched.into_iter().take(MAX_HINT_WITNESSES).chain(scanned) {
            if !candidates.contains(&candidate) {
                candidates.push(candidate);
            }
        }
        candidates
    }
}

#[cfg(test)]
#[path = "implied_ground_inst_roots_tests.rs"]
mod tests;
