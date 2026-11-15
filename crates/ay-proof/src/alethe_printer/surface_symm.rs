// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Surface-safe Alethe rendering for equality symmetry steps.

use super::surface_tokens::split_smt_terms;
use super::{AlethePrintError, AlethePrinter};
use ay_core::{AletheRule, ProofId, TermData, TermId, TermStore};

impl AlethePrinter<'_> {
    /// Render one internally checked `symm` or `eq_symmetric` without letting
    /// an authored equality override collapse or corrupt its operand
    /// orientation.
    pub(super) fn format_surface_symm(
        &self,
        id: ProofId,
        rule: &AletheRule,
        clause: &[TermId],
        premises: &[ProofId],
        args: &[TermId],
    ) -> Result<String, AlethePrintError> {
        if matches!(rule, AletheRule::EqSymmetric) {
            return self.format_surface_eq_symmetric(id, clause, premises, args);
        }
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

impl AlethePrinter<'_> {
    /// Judge one premise-free `eq_symmetric` on the text that ships.
    ///
    /// `(cl (= (= a b) (= b a)))` is purely syntactic: pinned carcara decodes
    /// the PRINTED conclusion and requires `a == d` and `b == c`. AY's strict
    /// checker validates the term DAG, but the source-override channel
    /// re-spells a `TermId` independently of it. MEASURED on
    /// `(assert (= (g (- 5)) 0))`, whose canonical root is `(= 0 (g (- 5)))`
    /// carrying the authored spelling: the checked
    /// `(= (= 0 (g (- 5))) (= (g (- 5)) 0))` printed as
    /// `(= (= (g (- 5)) 0) (= (g (- 5)) 0))`, the certificate line said
    /// `ay_self_checkable=yes carcara_surface=supported`, and carcara answered
    /// `invalid` ("expected terms to be equal"). Two identical printed sides
    /// are an instance of `refl`; an exact printed reversal stays
    /// `eq_symmetric` (byte-identical to the default rendering); anything
    /// else is refused rather than shipped under a rule it does not
    /// instantiate.
    fn format_surface_eq_symmetric(
        &self,
        id: ProofId,
        clause: &[TermId],
        premises: &[ProofId],
        args: &[TermId],
    ) -> Result<String, AlethePrintError> {
        let [conclusion] = clause else {
            return Err(invalid_symm(
                id,
                "eq_symmetric requires a singleton conclusion",
            ));
        };
        if !premises.is_empty() || !args.is_empty() {
            return Err(invalid_symm(
                id,
                "eq_symmetric takes no premises or proof arguments",
            ));
        }
        // Judge the native step first, as `format_surface_symm` does: a step
        // the strict checker would refuse is never laundered into `refl`.
        if !native_eq_symmetric_shape(self.terms, *conclusion) {
            return Err(invalid_symm(id, "native eq_symmetric shape is invalid"));
        }
        let clause_str = self.format_clause(clause);
        // The same ten-units-per-byte allocation bound `format_surface_symm`
        // charges for its balanced splits (three passes here).
        self.charge((clause_str.len() as u64).saturating_mul(30));
        if self.work_budget_exhausted() {
            return Err(self.work_budget_error(id.0));
        }
        let Some(printed) = clause_str
            .strip_prefix("(cl ")
            .and_then(|rest| rest.strip_suffix(')'))
        else {
            return Err(invalid_symm(
                id,
                "printed eq_symmetric clause is not a unit",
            ));
        };
        let decoded =
            split_smt_application(printed, "=").and_then(|sides| match sides.as_slice() {
                [left, right] => Some((
                    split_smt_application(left, "=")?,
                    split_smt_application(right, "=")?,
                    left == right,
                )),
                _ => None,
            });
        // Two literal rule names, so the wire-rule inventory reads both.
        let reversal = decoded.as_ref().is_some_and(|(left, right, _)| {
            matches!((left.as_slice(), right.as_slice()), ([a, b], [c, d]) if a == d && b == c)
        });
        if reversal {
            return Ok(format!("(step {id} {clause_str} :rule eq_symmetric)"));
        }
        if decoded.is_some_and(|(_, _, identical)| identical) {
            return Ok(format!("(step {id} {clause_str} :rule refl)"));
        }
        Err(invalid_symm(
            id,
            "printed eq_symmetric conclusion is neither an exact reversal nor an identity",
        ))
    }
}

/// The two equality-symmetry rules whose printed text this module judges.
pub(super) fn is_symmetry_rule(rule: &AletheRule) -> bool {
    matches!(rule, AletheRule::Symm | AletheRule::EqSymmetric)
}

/// `(= (= a b) (= b a))` over the term DAG: the strict checker's
/// `eq_symmetric` shape.
fn native_eq_symmetric_shape(terms: &TermStore, literal: TermId) -> bool {
    let binary_equality = |term: TermId| match terms.get(term) {
        TermData::App(symbol, args) if symbol.name() == "=" && args.len() == 2 => {
            Some((args[0], args[1]))
        }
        _ => None,
    };
    let Some((left, right)) = binary_equality(literal) else {
        return false;
    };
    matches!(
        (binary_equality(left), binary_equality(right)),
        (Some((a, b)), Some((c, d))) if a == d && b == c
    )
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
