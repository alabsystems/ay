// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The checked lowering of a guarded arithmetic disequality split.
//!
//! The strict checker certifies `(cl B_1 B_2 G)`, where the guard `G` is an
//! equality and the two branches bracket its linear form with the one-value
//! integer gap (`C <= T - 1`, `C >= T + 1`) or, over `Real`, are the two strict
//! orders. The lowering re-derives it through the operands `A`, `B` of the
//! guard AS PRINTED, `(= A B)`:
//!
//! ```text
//! (step t.split (cl (or (= A B) (not (<= A B)) (not (<= B A)))) :rule la_disequality)
//! (step t.flat  (cl (= A B) (not (<= A B)) (not (<= B A))) :rule or :premises (t.split))
//! (step t.b0    (cl (<= A B) X_fwd) :rule la_generic :args (1 k))
//! (step t.b1    (cl (<= B A) X_rev) :rule la_generic :args (1 k))
//! (step t.mid   (cl (= A B) (not (<= B A)) X_fwd) :rule resolution :premises (t.flat t.b0))
//! (step t       (cl B_1 B_2 (= A B)) :rule resolution :premises (t.mid t.b1))
//! ```
//!
//! `X_fwd` is the branch `(<= A B)` excludes and `X_rev` the other one. At
//! c57bd8481 (and until this change) the lowering read `A`, `B` from the
//! guard's TermId and always paired `(<= A B)` with `B_2`. Both assumptions fail in practice:
//!
//! * The document may print the guard through an override. `(assert (not (= 1
//!   x)))` is stored as `(= x 1)` and printed as the authored `(= 1 x)`, so the
//!   split read `(or (= 1 x) (not (<= x 1)) (not (<= 1 x)))`. No printed
//!   judgement read `la_disequality`, so the document shipped `invalid`
//!   (MEASURED end to end at c57bd8481 on the five-assertion QF_LIA problem
//!   `carcara_external_check/printed_split_guard.rs` pins; pinned carcara
//!   1.1.0: "checking failed on step 't7.split' with rule 'la_disequality':
//!   expected terms to be equal: '1' and 'x'").
//! * The strict checker compares the guard's SIGN-NORMALIZED form with the
//!   branches, so `(= C T)` and `(= T C)` are both primitive guards, and for
//!   `(= T C)` the forward order excludes `B_1`. The `u64`-guarded array-frame
//!   fixture (`carcara_external_check/frame_ite_lift.rs`) certifies
//!   `(cl (<= W 0) (<= 2 W) (= 1 W))`, and the lowering printed
//!   `(cl (<= 1 W) (<= 2 W)) :rule la_generic`, false at `W = 0`;
//!   `judge_printed_la_generic` holed the step.
//!
//! The orientation is now read from the clause
//! ([`ay_core::proof_validation::arith_disequality_split_primitive_guard_is_reversed`])
//! and carried onto the printed operands. The checked positive integer `k`
//! scales the guard's canonical form relative to the branches. A guard printed as anything other
//! than its own equality, either way round, keeps the honest `hole`. Every
//! sub-step is still judged over the bytes it ships (`la_generic`,
//! `la_disequality`).

use super::*;

/// Ask the same bounded, byte-checked rendering used by the exporter. In
/// particular, native validity alone does not admit a changed surface or a
/// scaled guard whose two checked positive-coefficient steps are unavailable.
#[must_use]
pub fn arith_disequality_split_lowering_supported(
    terms: &TermStore,
    kind: &ay_core::TheoryLemmaKind,
    clause: &[TermId],
    overrides: Option<&HashMap<TermId, String>>,
) -> bool {
    if !matches!(
        kind,
        ay_core::TheoryLemmaKind::ArithDisequalitySplit
            | ay_core::TheoryLemmaKind::ArithClauseTautology
    ) || clause.len() != 3
    {
        return false;
    }
    let printer =
        AlethePrinter::new_with_overrides_and_budget(terms, overrides, Some(4 * 1024 * 1024));
    let step = ProofStep::TheoryLemma {
        theory: "arith".into(),
        clause: clause.to_vec(),
        farkas: None,
        kind: *kind,
        lia: None,
    };
    printer
        .format_step(&step, ProofId(0))
        .is_ok_and(|text| text.contains(":rule la_disequality") && !text.contains(":rule hole"))
}

/// Return a permutation in the strict recognizer's branch/branch/guard order.
/// The input literals themselves are never rewritten: the final `reordering`
/// step restores the exact clause the producer recorded.
fn checked_split_order(
    terms: &TermStore,
    clause: &[TermId],
) -> Option<(
    [TermId; 3],
    ay_core::proof_validation::ArithDisequalitySplitLoweringWitness,
)> {
    let [a, b, c] = clause else { return None };
    for ordered in [
        [*a, *b, *c],
        [*b, *a, *c],
        [*a, *c, *b],
        [*c, *a, *b],
        [*b, *c, *a],
        [*c, *b, *a],
    ] {
        if let Some(witness) =
            ay_core::proof_validation::arith_disequality_split_lowering_witness(terms, &ordered)
        {
            return Some((ordered, witness));
        }
    }
    None
}

impl AlethePrinter<'_> {
    /// The checked lowering of an `ArithDisequalitySplit` lemma, including
    /// the same exact schema carried by an `ArithClauseTautology` in arbitrary
    /// literal order. Every candidate goes through the strict split
    /// recognizer; unsupported schemas keep the honest `hole` wire.
    ///
    /// The shared strict checker recovers the positive scale `k` of the
    /// guard's form relative to the branch form. Weighting the guard bound by
    /// one and the opposite branch by `k` cancels every variable and preserves
    /// the contradiction's strict/integer gap. Each emitted `la_generic` step
    /// is still independently judged over its actual printed operands.
    pub(super) fn format_arith_disequality_split(
        &self,
        id: ProofId,
        kind: &ay_core::TheoryLemmaKind,
        clause: &[TermId],
    ) -> Option<String> {
        if !matches!(
            kind,
            ay_core::TheoryLemmaKind::ArithDisequalitySplit
                | ay_core::TheoryLemmaKind::ArithClauseTautology
        ) {
            return None;
        }
        let (ordered, witness) = checked_split_order(self.terms, clause)?;
        let reversed = witness.guard_is_reversed;
        let multiplier = witness.guard_multiplier;
        let [first, second, guard] = ordered;
        let TermData::App(_, operands) = self.terms.get(guard) else {
            return None;
        };
        let [lhs, rhs] = operands.as_slice() else {
            return None;
        };
        let (lhs, rhs) = (self.format_term(*lhs), self.format_term(*rhs));
        let equality = self.format_term(guard);
        // `la_disequality` matches its operands against the PRINTED equality,
        // so the orientation follows the operands onto the text.
        let (left, right, reversed) = if equality == format!("(= {lhs} {rhs})") {
            (lhs, rhs, reversed)
        } else if equality == format!("(= {rhs} {lhs})") {
            (rhs, lhs, !reversed)
        } else {
            return None;
        };
        let first = self.format_term(first);
        let second = self.format_term(second);
        let (excluded_by_forward, excluded_by_reverse) = if reversed {
            (&first, &second)
        } else {
            (&second, &first)
        };
        let le_forward = format!("(<= {left} {right})");
        let le_reverse = format!("(<= {right} {left})");
        let packed = format!("(or {equality} (not {le_forward}) (not {le_reverse}))");
        let ordered_id = if ordered.as_slice() == clause {
            id.to_string()
        } else {
            format!("{id}.ordered")
        };
        let mut text = format!(
            "(step {id}.split (cl {packed}) :rule la_disequality)\n\
             (step {id}.flat (cl {equality} (not {le_forward}) (not {le_reverse})) :rule or :premises ({id}.split))\n\
             (step {id}.b0 (cl {le_forward} {excluded_by_forward}) :rule la_generic :args (1 {multiplier}))\n\
             (step {id}.b1 (cl {le_reverse} {excluded_by_reverse}) :rule la_generic :args (1 {multiplier}))\n\
             (step {id}.mid (cl {equality} (not {le_reverse}) {excluded_by_forward}) :rule resolution :premises ({id}.flat {id}.b0))\n\
             (step {ordered_id} (cl {first} {second} {equality}) :rule resolution :premises ({id}.mid {id}.b1))"
        );
        if ordered.as_slice() != clause {
            text.push_str(&format!(
                "\n(step {id} {} :rule reordering :premises ({ordered_id}))",
                self.format_clause(clause)
            ));
        }
        Some(text)
    }
}
