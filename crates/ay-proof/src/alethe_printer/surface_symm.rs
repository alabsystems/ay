// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Surface-safe Alethe rendering for equality symmetry steps.

use super::surface_tokens::split_smt_terms;
use super::{AlethePrintError, AlethePrinter};
use ay_core::{ProofId, TermId};

impl AlethePrinter<'_> {
    /// Render one internally checked `symm` without letting an authored
    /// equality override collapse or corrupt its operand orientation.
    pub(super) fn format_surface_symm(
        &self,
        id: ProofId,
        clause: &[TermId],
        premises: &[ProofId],
        args: &[TermId],
    ) -> Result<String, AlethePrintError> {
        let [conclusion] = clause else {
            return Err(invalid_symm(id, "symm requires a singleton conclusion"));
        };
        let [premise_id] = premises else {
            return Err(invalid_symm(id, "symm requires exactly one premise"));
        };
        if !args.is_empty() {
            return Err(invalid_symm(id, "symm does not accept proof arguments"));
        }

        let premise_clauses = self.proof_clauses.borrow();
        let Some(premise_clause) = premise_clauses.get(premise_id) else {
            return Err(invalid_symm(
                id,
                "symm premise does not name a proof clause",
            ));
        };
        crate::checker::validate_symm(self.terms, id, clause, &[premise_clause.as_slice()])
            .map_err(|error| invalid_symm(id, format!("native symm shape is invalid: {error}")))?;
        let [premise] = premise_clause.as_slice() else {
            unreachable!("validated symm premise")
        };

        let printed_premise = self.format_term(*premise);
        let printed_conclusion = self.format_term(*conclusion);
        let compared_bytes =
            (printed_premise.len() as u64).saturating_add(printed_conclusion.len() as u64);
        self.charge(compared_bytes);
        if self.work_budget_exhausted() {
            return Err(self.work_budget_error(id.0));
        }

        if printed_premise == printed_conclusion {
            return Ok(format!(
                "(step {id} (cl {printed_conclusion}) :rule weakening :premises ({premise_id}))"
            ));
        }

        // Each literal is scanned at most twice (one optional `not`, then the
        // equality). `split_smt_terms` holds a `Vec<char>` (up to four bytes
        // per scalar) plus owned token strings on each pass, so ten units per
        // input byte conservatively bound its parsing/copying allocation.
        self.charge(compared_bytes.saturating_mul(10));
        if self.work_budget_exhausted() {
            return Err(self.work_budget_error(id.0));
        }
        let Some((premise_negated, premise_left, premise_right)) =
            split_printed_equality_literal(&printed_premise)
        else {
            return Err(invalid_symm(
                id,
                "printed symm premise is not a binary equality literal",
            ));
        };
        let Some((conclusion_negated, conclusion_left, conclusion_right)) =
            split_printed_equality_literal(&printed_conclusion)
        else {
            return Err(invalid_symm(
                id,
                "printed symm conclusion is not a binary equality literal",
            ));
        };
        if premise_negated != conclusion_negated
            || premise_left != conclusion_right
            || premise_right != conclusion_left
        {
            return Err(invalid_symm(
                id,
                "printed symm conclusion is neither identical to nor the exact reverse of its premise",
            ));
        }

        let wire_rule = if premise_negated { "not_symm" } else { "symm" };
        Ok(format!(
            "(step {id} (cl {printed_conclusion}) :rule {wire_rule} :premises ({premise_id}))"
        ))
    }
}

fn invalid_symm(id: ProofId, reason: impl Into<String>) -> AlethePrintError {
    AlethePrintError::InvalidSurfaceStep {
        id,
        reason: reason.into(),
    }
}

/// Decode the exact printed literal shapes accepted by Alethe `symm`: a
/// binary equality, optionally under one `not`. The balanced splitter handles
/// nested operands, quoted symbols, and SMT strings (including doubled quotes).
fn split_printed_equality_literal(input: &str) -> Option<(bool, String, String)> {
    let (negated, equality) = match split_smt_application(input, "not") {
        Some(mut operands) => {
            if operands.len() != 1 {
                return None;
            }
            (true, operands.pop()?)
        }
        None => (false, input.to_string()),
    };
    let operands = split_smt_application(&equality, "=")?;
    let [left, right] = operands.as_slice() else {
        return None;
    };
    Some((negated, left.clone(), right.clone()))
}

fn split_smt_application(input: &str, head: &str) -> Option<Vec<String>> {
    let inner = input.strip_prefix('(')?.strip_suffix(')')?;
    let mut fields = split_smt_terms(inner)?;
    if fields.first().map(String::as_str) != Some(head) {
        return None;
    }
    fields.remove(0);
    Some(fields)
}
