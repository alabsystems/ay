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
//! (step t.b0    (cl (<= A B) X_fwd) :rule la_generic :args (1 1))
//! (step t.b1    (cl (<= B A) X_rev) :rule la_generic :args (1 1))
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
//! and carried onto the printed operands; a guard printed as anything other
//! than its own equality, either way round, keeps the honest `hole`. Every
//! sub-step is still judged over the bytes it ships (`la_generic`,
//! `la_disequality`).

use super::*;

impl AlethePrinter<'_> {
    /// The checked lowering of an `ArithDisequalitySplit` lemma, or `None` when
    /// it is not exactly reconstructible from the pinned checker's own
    /// primitives and must keep the honest `hole` wire.
    ///
    /// The pairing holds only while the guard and the branches share ONE linear
    /// form, i.e. the PRIMITIVE `k = 1` guard. The strict checker also
    /// certifies a guard scaled by a positive integer `k >= 2`
    /// (`q <= -1 ∨ q >= 1 ∨ 2q+1 = 4q+1`). Its operands scale the branch form
    /// by `k`, so the `(1 1)` combinations above are not the `la_generic`
    /// instances that would derive it, and it is not lowered.
    pub(super) fn format_arith_disequality_split(
        &self,
        id: ProofId,
        kind: &ay_core::TheoryLemmaKind,
        clause: &[TermId],
    ) -> Option<String> {
        if !matches!(kind, ay_core::TheoryLemmaKind::ArithDisequalitySplit) {
            return None;
        }
        let reversed =
            ay_core::proof_validation::arith_disequality_split_primitive_guard_is_reversed(
                self.terms, clause,
            )?;
        let [first, second, guard] = clause else {
            return None;
        };
        let TermData::App(_, operands) = self.terms.get(*guard) else {
            return None;
        };
        let [lhs, rhs] = operands.as_slice() else {
            return None;
        };
        let (lhs, rhs) = (self.format_term(*lhs), self.format_term(*rhs));
        let equality = self.format_term(*guard);
        // `la_disequality` matches its operands against the PRINTED equality,
        // so the orientation follows the operands onto the text.
        let (left, right, reversed) = if equality == format!("(= {lhs} {rhs})") {
            (lhs, rhs, reversed)
        } else if equality == format!("(= {rhs} {lhs})") {
            (rhs, lhs, !reversed)
        } else {
            return None;
        };
        let first = self.format_term(*first);
        let second = self.format_term(*second);
        let (excluded_by_forward, excluded_by_reverse) = if reversed {
            (&first, &second)
        } else {
            (&second, &first)
        };
        let le_forward = format!("(<= {left} {right})");
        let le_reverse = format!("(<= {right} {left})");
        let packed = format!("(or {equality} (not {le_forward}) (not {le_reverse}))");
        Some(format!(
            "(step {id}.split (cl {packed}) :rule la_disequality)\n\
             (step {id}.flat (cl {equality} (not {le_forward}) (not {le_reverse})) :rule or :premises ({id}.split))\n\
             (step {id}.b0 (cl {le_forward} {excluded_by_forward}) :rule la_generic :args (1 1))\n\
             (step {id}.b1 (cl {le_reverse} {excluded_by_reverse}) :rule la_generic :args (1 1))\n\
             (step {id}.mid (cl {equality} (not {le_reverse}) {excluded_by_forward}) :rule resolution :premises ({id}.flat {id}.b0))\n\
             (step {id} (cl {first} {second} {equality}) :rule resolution :premises ({id}.mid {id}.b1))"
        ))
    }
}
