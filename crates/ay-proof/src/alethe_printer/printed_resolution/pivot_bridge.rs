// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Every repair a printed resolution's diverged pivot can reach.
//!
//! [`AlethePrinter::printed_pivot_bridge`] is the single entry point
//! [`super::AlethePrinter::judge_printed_resolution`] calls once its RUP
//! replay has failed; each arm below answers `None` for a shape it does not
//! understand, and an unbridged divergence is still the refusal it was.
//!
//! The arithmetic arm (one linear comparison in two spellings) lives in the
//! parent module. This one is its sibling for the other spelling family the
//! surface-override ledger produces: one EQUALITY printed in both operand
//! orders.
//!
//! # The divergence
//!
//! `purge_surface_overrides_for_certified_proof` drops every authored spelling
//! attached to a term a certified proof PRINTS, and
//! `restore_reachable_authored_assume_surface_overrides` then puts back the
//! problem file's spelling for the reachable `assume` ROOTS only
//! (`collect_root_surface_term_override`: root-only, so a certified theory
//! step's operands keep the rendering the strict checker validated). When the
//! restored root is a NEGATED equality whose operands elaboration reordered —
//! `TermStore::mk_eq` orders by term identity, so `(assert (not (= (select b
//! idx) val)))` interns as `(not (= val (select b idx)))` — the override
//! respells that literal wherever the document prints it, while the SAME
//! atom's positive occurrences (a different `TermId`) keep printing
//! canonically. Nothing is wrong internally; on the wire the two are not
//! complements and no resolution can eliminate the pivot.
//!
//! MEASURED on `benchmarks/smt/QF_ABV/csplit_repro_indirect_store_unsat.smt2`
//! (2026-09-23): the Tseitin block around the assumed literal resolves
//! `equiv_neg2`'s `(not (= (select b idx) val))` against the derived
//! `(= val (select b idx))`, pinned carcara 1.1.0 answers
//! `checking failed on step 't19' with rule 'th_resolution': pivot was not
//! eliminated`, and the export was refused outright — `unsat` with no
//! document at all.
//!
//! # The repair
//!
//! Equality symmetry is a tautology the pinned checker has rules for, so the
//! bridge STATES it rather than inheriting it from a term identity carcara
//! cannot see — the same discipline, and the same two-rule shape, the
//! `or_pos` leaf bridge already uses:
//!
//! ```text
//! (step t19.sy (cl (= A B)) :rule eq_symmetric)
//! (step t19.sy.p (cl (not (= A B)) (not A) B) :rule equiv_pos2)
//! (step t19 (cl ..) :rule resolution :premises (t18 t19.sy t19.sy.p t16))
//! ```
//!
//! Both added steps are premise-free tautologies over the PRINTED text, and
//! the whole repaired step is replayed by the same RUP model that judged it
//! before anything is emitted — so this never turns a step that was wrong for
//! another reason into one that merely looks repaired. Measured against
//! pinned carcara 1.1.0 on the document above: `valid`.
//!
//! # A pivot respelled by elaboration
//!
//! The third arm serves one atom whose two printed spellings are DIFFERENT
//! terms to carcara's parser that elaboration made one `TermId`. `mk_select`
//! folds `(select (store a i v1) i)` to `v1`, so `(assert (= (select (store a
//! i v1) i) v2))` is the internal `(= v1 v2)` under an authored override,
//! while `(assert (distinct v1 v2))` reaches the wire through the confined
//! `distinct_elim` bridge as its canonical `(not (= v1 v2))`. The refutation
//! resolves the two, and the export was refused (`conformance/QF_AX/
//! unsat_store_mismatch.smt2`: "the printed premises do not eliminate the
//! printed resolution pivot, starting at `(= (select (store a i v1) i) v2)`").
//! The arm proves the two spellings equal with the `eq_transitive` repair's
//! planner (`arrays_idx` for a same-index read over a write, `evaluate` for a
//! closed bit-vector term, `cong` over either), turns that into the
//! implication with `equiv_pos2` (`equiv_pos1` for the mirrored equality),
//! and replays the repaired step before emitting anything:
//!
//! ```text
//! (step t4.rw.gb0 (cl (= (select (store a i v1) i) v1)) :rule arrays_idx)
//! (step t4.rw.gb1 (cl (= (= (select (store a i v1) i) v2) (= v1 v2))) :rule cong :premises (t4.rw.gb0))
//! (step t4.rw.p (cl (not (= ..)) (not (= (select (store a i v1) i) v2)) (= v1 v2)) :rule equiv_pos2)
//! (step t4 (cl) :rule resolution :premises (t3 t4.rw.gb1 t4.rw.p t0))
//! ```

use super::super::eq_transitive::bridged_printed_equality;
use super::super::{split_application, AlethePrinter};
use super::PrintedLiteral;
use ay_core::kani_compat::DetHashSet;
use ay_core::ProofId;
use std::rc::Rc;

impl AlethePrinter<'_> {
    /// Try every bridge a printed resolution's unpaired pivot can reach, in
    /// the order that makes at most one of them applicable: a linear
    /// comparison is never an equality, and an equality is never a literal
    /// `la_generic` can read.
    ///
    /// `None` leaves the caller exactly where it was — the printer-channel
    /// floor, then the refusal.
    pub(super) fn printed_pivot_bridge(
        &self,
        id: ProofId,
        clause_str: &str,
        premises: &[ProofId],
        printed_premises: &[super::Tracked<Vec<super::OwnedText>>],
        decoded_premises: &[Vec<PrintedLiteral>],
        decoded_conclusion: &[PrintedLiteral],
    ) -> Option<String> {
        self.printed_arithmetic_pivot_bridge(
            id,
            clause_str,
            premises,
            printed_premises,
            decoded_premises,
            decoded_conclusion,
        )
        .or_else(|| {
            self.printed_symmetric_equality_pivot_bridge(
                id,
                clause_str,
                premises,
                printed_premises,
                decoded_premises,
                decoded_conclusion,
            )
        })
        .or_else(|| {
            self.printed_respelled_pivot_bridge(
                id,
                clause_str,
                premises,
                decoded_premises,
                decoded_conclusion,
            )
        })
    }

    /// Bridge a printed two-premise resolution whose ONLY unpaired literals
    /// are one atom asserted in one premise and denied in the other under a
    /// spelling the `eq_transitive` repair's planner proves equal, or `None`.
    ///
    /// Exactly one unpaired literal per premise, of opposite polarity, so the
    /// pivot is unambiguous; and the WHOLE repaired step must replay before
    /// anything is emitted.
    fn printed_respelled_pivot_bridge(
        &self,
        id: ProofId,
        clause_str: &str,
        premises: &[ProofId],
        decoded_premises: &[Vec<PrintedLiteral>],
        decoded_conclusion: &[PrintedLiteral],
    ) -> Option<String> {
        let [left_premise, right_premise] = premises else {
            return None;
        };
        let [left, right] = decoded_premises else {
            return None;
        };
        let (left_unpaired, right_unpaired) = (
            unpaired_literals(left, right, decoded_conclusion),
            unpaired_literals(right, left, decoded_conclusion),
        );
        let ([left_literal], [right_literal]) =
            (left_unpaired.as_slice(), right_unpaired.as_slice())
        else {
            return None;
        };
        let (positive, negative, positive_premise, negative_premise) =
            match (left_literal.depth, right_literal.depth) {
                (0, 1) => (
                    &left_literal.atom,
                    &right_literal.atom,
                    left_premise,
                    right_premise,
                ),
                (1, 0) => (
                    &right_literal.atom,
                    &left_literal.atom,
                    right_premise,
                    left_premise,
                ),
                _ => return None,
            };
        let bridge = bridged_printed_equality(&format!("{id}.rw"), positive, negative)?;
        self.charge(bridge.steps.len() as u64);
        let (equivalence, implication) = if bridge.mirrored {
            let equivalence = format!("(= {negative} {positive})");
            let implication = format!(
                "(step {id}.rw.p (cl (not {equivalence}) {negative} (not {positive})) \
                 :rule equiv_pos1)"
            );
            (equivalence, implication)
        } else {
            let equivalence = format!("(= {positive} {negative})");
            let implication = format!(
                "(step {id}.rw.p (cl (not {equivalence}) (not {positive}) {negative}) \
                 :rule equiv_pos2)"
            );
            (equivalence, implication)
        };
        let mut repaired = self.replay_copy(decoded_premises, 2)?;
        repaired.push_replay(vec![self.printed_literal_identity(&equivalence)?])?;
        repaired.push_replay(vec![
            self.printed_literal_identity(&format!("(not {equivalence})"))?,
            self.printed_literal_identity(&format!("(not {positive})"))?,
            self.printed_literal_identity(negative)?,
        ])?;
        repaired.seal_replay(&self.printed_replay_budget())?;
        if !self.printed_rup_entail(&repaired, decoded_conclusion)? {
            return None;
        }
        Some(format!(
            "{}{implication}\n(step {id} {clause_str} :rule resolution :premises \
             ({positive_premise} {} {id}.rw.p {negative_premise}))",
            bridge.steps, bridge.step
        ))
    }

    /// Bridge a printed resolution whose only unpaired pivot is one equality
    /// printed in both orientations, or `None` when that is not the shape.
    ///
    /// Only a two-premise step is repaired, and only when adding the two
    /// bridge clauses makes the WHOLE printed step replay.
    fn printed_symmetric_equality_pivot_bridge(
        &self,
        id: ProofId,
        clause_str: &str,
        premises: &[ProofId],
        printed_premises: &[super::Tracked<Vec<super::OwnedText>>],
        decoded_premises: &[Vec<PrintedLiteral>],
        decoded_conclusion: &[PrintedLiteral],
    ) -> Option<String> {
        let [left_premise, right_premise] = premises else {
            return None;
        };
        let [left, right] = decoded_premises else {
            return None;
        };

        let mut candidate: Option<(super::OwnedText, super::OwnedText, ProofId, ProofId)> = None;
        for (left_index, left_literal) in left.iter().enumerate() {
            for (right_index, right_literal) in right.iter().enumerate() {
                // Exactly one side asserts the atom, under no `not` shell, and
                // the other denies it under exactly one. A deeper shell is a
                // spelling this bridge does not reproduce, so it is left to the
                // refusal below it.
                let (positive, negative, positive_premise, negative_premise) =
                    match (left_literal.depth, right_literal.depth) {
                        (0, 1) => (
                            printed_premises[0][left_index].clone(),
                            right_literal.atom.clone(),
                            *left_premise,
                            *right_premise,
                        ),
                        (1, 0) => (
                            printed_premises[1][right_index].clone(),
                            left_literal.atom.clone(),
                            *right_premise,
                            *left_premise,
                        ),
                        _ => continue,
                    };
                // Two printed spellings of one atom, or the replay above would
                // already have discharged the pair.
                if !printed_equalities_are_reversed_with_budget(
                    &positive,
                    &negative,
                    &self.printed_replay_budget(),
                )? {
                    continue;
                }
                // Deterministic and unambiguous: two different repairs for one
                // step is a shape this bridge does not understand.
                if candidate
                    .as_ref()
                    .is_some_and(|prior| prior.0 != positive || prior.1 != negative)
                {
                    return None;
                }
                candidate = Some((positive, negative, positive_premise, negative_premise));
            }
        }
        let (positive, negative, positive_premise, negative_premise) = candidate?;

        // Replay the repaired step exactly as the checker will see it: the
        // equivalence the `eq_symmetric` step states, and the implication the
        // `equiv_pos2` step turns it into.
        let equivalence = format!("(= {positive} {negative})");
        let symmetry = vec![self.printed_literal_identity(&equivalence)?];
        let implication = vec![
            self.printed_literal_identity(&format!("(not {equivalence})"))?,
            self.printed_literal_identity(&format!("(not {positive})"))?,
            self.printed_literal_identity(&negative)?,
        ];
        let mut repaired = self.replay_copy(decoded_premises, 2)?;
        repaired.push_replay(symmetry)?;
        repaired.push_replay(implication)?;
        repaired.seal_replay(&self.printed_replay_budget())?;
        if !self.printed_rup_entail(&repaired, decoded_conclusion)? {
            return None;
        }

        Some(format!(
            "(step {id}.sy (cl {equivalence}) :rule eq_symmetric)\n\
             (step {id}.sy.p (cl (not {equivalence}) (not {positive}) {negative}) \
             :rule equiv_pos2)\n\
             (step {id} {clause_str} :rule resolution :premises ({positive_premise} {id}.sy {id}.sy.p {negative_premise}))"
        ))
    }
}

/// `true` when two printed atoms are the two orientations of ONE binary
/// equality: `(= A B)` and `(= B A)`, with `A` and `B` printed the same way on
/// both sides.
///
/// Read off the printed TEXT, never the term store — the divergence this
/// serves is precisely a term whose occurrences print differently, so a
/// term-identity comparison is blind to it by construction. Compared through
/// [`normalise_printed_spelling`], so the bit-vector literal collapse the
/// replay already honours is honoured here too.
///
/// Identical spellings answer `false`: they are not a divergence, and a step
/// whose pivot already pairs never reaches this module.
#[cfg(test)]
fn printed_equalities_are_reversed(left: &str, right: &str) -> bool {
    printed_equalities_are_reversed_with_budget(
        left,
        right,
        &super::TextBudget::new(super::super::printed_command::MAX_STEP_BYTES),
    )
    .unwrap_or(false)
}

fn printed_equalities_are_reversed_with_budget(
    left: &str,
    right: &str,
    budget: &super::TextBudget,
) -> Option<bool> {
    let Some((left_first, left_second)) = super::wire_text::binary_application(left, "=") else {
        return Some(false);
    };
    let Some((right_first, right_second)) = super::wire_text::binary_application(right, "=") else {
        return Some(false);
    };
    let mut nodes = 0;
    let left_first = super::wire_text::normalise_owned(left_first, 0, &mut nodes, budget)?;
    let left_second = super::wire_text::normalise_owned(left_second, 0, &mut nodes, budget)?;
    let right_first = super::wire_text::normalise_owned(right_first, 0, &mut nodes, budget)?;
    let right_second = super::wire_text::normalise_owned(right_second, 0, &mut nodes, budget)?;
    Some(left_first != left_second && left_first == right_second && left_second == right_first)
}

/// The distinct literals of `clause` that neither the printed conclusion
/// repeats nor `other` complements: what the replay could not discharge.
fn unpaired_literals<'a>(
    clause: &'a [PrintedLiteral],
    other: &[PrintedLiteral],
    conclusion: &[PrintedLiteral],
) -> Vec<&'a PrintedLiteral> {
    let in_conclusion: DetHashSet<(&str, bool)> = conclusion
        .iter()
        .map(|literal| (&*literal.spelling, literal.positive()))
        .collect();
    let in_other: DetHashSet<(&str, bool)> = other
        .iter()
        .map(|literal| (&*literal.spelling, literal.positive()))
        .collect();
    let mut seen: DetHashSet<(&str, bool)> = DetHashSet::default();
    clause
        .iter()
        .filter(|literal| {
            let key = (&*literal.spelling, literal.positive());
            !in_conclusion.contains(&key)
                && !in_other.contains(&(key.0, !key.1))
                && seen.insert(key)
        })
        .collect()
}

#[cfg(test)]
mod tests;

#[cfg(test)]
mod respelled_tests;
