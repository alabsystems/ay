// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Checked repairs for resolution pivots whose authored equality orientation
//! differs from the canonical positive equality used later in the proof.

use super::*;

impl AlethePrinter<'_> {
    /// Resolve a unit equality against the exact negation of its symmetric
    /// spelling. Carcara treats equality orientation syntactically at
    /// resolution, so insert the stock `symm` rule before cancelling it.
    pub(super) fn symmetric_equality_resolution_bridge(
        &self,
        id: ProofId,
        clause: &[TermId],
        clause1: ProofId,
        clause2: ProofId,
    ) -> Option<String> {
        if !clause.is_empty() {
            return None;
        }
        let clauses = self.proof_clauses.borrow();
        let [left] = clauses.get(&clause1)?.as_slice() else {
            return None;
        };
        let [right] = clauses.get(&clause2)?.as_slice() else {
            return None;
        };
        let left = self.format_term(*left);
        let right = self.format_term(*right);
        let (positive_id, negative_id, positive, negative) = match (
            printed_positive_equality(&left),
            printed_negative_equality(&right),
        ) {
            (Some(positive), Some(negative)) => (clause1, clause2, positive, negative),
            _ => {
                let positive = printed_positive_equality(&right)?;
                let negative = printed_negative_equality(&left)?;
                (clause2, clause1, positive, negative)
            }
        };
        let [positive_left, positive_right] = positive.as_slice() else {
            return None;
        };
        let [negative_left, negative_right] = negative.as_slice() else {
            return None;
        };
        if !surface_literal::equal_modulo_bitvec_literal_spelling(positive_left, negative_right)
            || !surface_literal::equal_modulo_bitvec_literal_spelling(positive_right, negative_left)
        {
            return None;
        }
        let oriented = format!("(= {negative_left} {negative_right})");
        Some(format!(
            "(step {id}.s (cl {oriented}) :rule symm :premises ({positive_id}))\n\
             (step {id} (cl) :rule resolution :premises ({id}.s {negative_id}))"
        ))
    }
}

fn printed_positive_equality(surface: &str) -> Option<Vec<String>> {
    split_application(surface, "=")
}

fn printed_negative_equality(surface: &str) -> Option<Vec<String>> {
    let [inner] = <[String; 1]>::try_from(split_application(surface, "not")?).ok()?;
    split_application(&inner, "=")
}
