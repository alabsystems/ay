// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Checked printing of flattened implications with a conjunctive antecedent.

use super::{
    split_alethe_application_bounded, AlethePrintError, AlethePrinter, AletheSurfaceParseError,
    PRINTED_NESTING_NODE_BUDGET,
};
use ay_core::{AletheRule, ProofId, TermData, TermId};

const MAX_SURFACE_BYTES: usize = 1024 * 1024;

impl AlethePrinter<'_> {
    /// Reconstruct the printed implication from standard tautologies. The
    /// internal clause must contain exactly the original OR operands and raw
    /// negated gate; its printed literals must also match the authored source.
    /// Only flat conjunctions and one explicit double negation are bridged.
    pub(super) fn format_conjunctive_implies_pos(
        &self,
        id: ProofId,
        rule: &AletheRule,
        clause: &[TermId],
        premises: &[ProofId],
        args: &[TermId],
    ) -> Result<Option<String>, AlethePrintError> {
        if !matches!(rule, AletheRule::OrPos(_)) {
            return Ok(None);
        }
        let Some(&source) = args.first() else {
            return Ok(None);
        };
        let printed_source = self.format_term(source);
        if !has_head(&printed_source, "=>") {
            return Ok(None);
        }
        self.charge(printed_source.len() as u64);
        if self.work_budget_exhausted() {
            return Err(self.work_budget_error(id.0));
        }
        let parts =
            match split_alethe_application_bounded(&printed_source, "=>", 2, MAX_SURFACE_BYTES) {
                Ok(parts) => parts,
                Err(AletheSurfaceParseError::Malformed) => return Ok(None),
                Err(AletheSurfaceParseError::BudgetExceeded) => {
                    return Err(invalid(
                        id,
                        "implication source exceeds the surface parsing limit",
                    ));
                }
            };
        let [antecedent, consequent] = parts.as_slice() else {
            return Ok(None);
        };
        if !has_head(antecedent, "and") {
            return Ok(None);
        }
        let conjuncts = match split_alethe_application_bounded(
            antecedent,
            "and",
            PRINTED_NESTING_NODE_BUDGET,
            MAX_SURFACE_BYTES,
        ) {
            Ok(conjuncts) => conjuncts,
            Err(AletheSurfaceParseError::Malformed) => return Ok(None),
            Err(AletheSurfaceParseError::BudgetExceeded) => {
                return Err(invalid(
                    id,
                    "implication conjunction exceeds the surface parsing limit",
                ));
            }
        };
        if conjuncts.len() < 2 || args.len() != 1 || !premises.is_empty() {
            return Err(invalid(
                id,
                "conjunctive implication requires one source and no premises",
            ));
        }
        self.validate_implication_gate(id, source, clause)?;
        let printed: Vec<_> = clause.iter().map(|&term| self.format_term(term)).collect();
        self.charge(printed.iter().map(|literal| literal.len() as u64).sum());
        if self.work_budget_exhausted() {
            return Err(self.work_budget_error(id.0));
        }
        let (negative_conjuncts, bridges) =
            match_conjuncts(id, &printed_source, consequent, &conjuncts, &printed)?;
        Ok(Some(render(
            id,
            &printed_source,
            antecedent,
            consequent,
            &negative_conjuncts,
            &bridges,
            &printed,
        )))
    }

    fn validate_implication_gate(
        &self,
        id: ProofId,
        source: TermId,
        clause: &[TermId],
    ) -> Result<(), AlethePrintError> {
        let TermData::App(operator, operands) = self.terms.get(source) else {
            return Err(invalid(id, "implication source is not an internal OR"));
        };
        if operator.name() != "or"
            || operands.len() + 1 != clause.len()
            || operands.len() > PRINTED_NESTING_NODE_BUDGET
        {
            return Err(invalid(id, "implication internal OR/clause arity mismatch"));
        }
        let gate = clause
            .iter()
            .position(
                |&term| matches!(self.terms.get(term), TermData::Not(inner) if *inner == source),
            )
            .ok_or_else(|| invalid(id, "implication clause lacks its raw negated gate"))?;
        let mut actual = clause.to_vec();
        actual.remove(gate);
        let mut expected = operands.clone();
        actual.sort_unstable();
        expected.sort_unstable();
        if actual != expected {
            return Err(invalid(
                id,
                "implication clause differs from its internal OR operands",
            ));
        }
        Ok(())
    }
}

fn match_conjuncts(
    id: ProofId,
    source: &str,
    consequent: &str,
    conjuncts: &[&str],
    printed: &[String],
) -> Result<(Vec<String>, Vec<String>), AlethePrintError> {
    let mut expected = vec![format!("(not {source})"), consequent.to_string()];
    let mut negative_conjuncts = Vec::with_capacity(conjuncts.len());
    let mut bridges = Vec::new();
    for &conjunct in conjuncts {
        let negated = format!("(not {conjunct})");
        let inner = split_alethe_application_bounded(conjunct, "not", 1, MAX_SURFACE_BYTES)
            .ok()
            .and_then(|parts| match parts.as_slice() {
                [inner] => Some(*inner),
                _ => None,
            });
        if let Some(inner) = inner.filter(|inner| printed.iter().any(|lit| lit == inner)) {
            expected.push(inner.to_string());
            bridges.push(inner.to_string());
        } else {
            expected.push(negated.clone());
        }
        negative_conjuncts.push(negated);
    }
    let mut actual = printed.to_vec();
    actual.sort_unstable();
    expected.sort_unstable();
    if actual != expected {
        return Err(invalid(
            id,
            "flattened implication literals differ from the authored source",
        ));
    }
    Ok((negative_conjuncts, bridges))
}

fn invalid(id: ProofId, reason: &str) -> AlethePrintError {
    AlethePrintError::InvalidSurfaceStep {
        id,
        reason: reason.to_string(),
    }
}

fn has_head(input: &str, head: &str) -> bool {
    input
        .strip_prefix('(')
        .and_then(|rest| rest.strip_prefix(head))
        .and_then(|rest| rest.chars().next())
        .is_some_and(|ch| ch.is_ascii_whitespace())
}

fn render(
    id: ProofId,
    source: &str,
    antecedent: &str,
    consequent: &str,
    negative_conjuncts: &[String],
    bridges: &[String],
    printed_clause: &[String],
) -> String {
    let mut out = format!(
        "(step {id}.imp (cl (not {source}) (not {antecedent}) {consequent}) :rule implies_pos)\n\
         (step {id}.and (cl {antecedent} {}) :rule and_neg)\n",
        negative_conjuncts.join(" ")
    );
    let mut premises = vec![format!("{id}.imp"), format!("{id}.and")];
    for (index, inner) in bridges.iter().enumerate() {
        let step = format!("{id}.nn{index}");
        out.push_str(&format!(
            "(step {step} (cl (not (not (not {inner}))) {inner}) :rule not_not)\n"
        ));
        premises.push(step);
    }
    out.push_str(&format!(
        "(step {id} (cl {}) :rule resolution :premises ({}))",
        printed_clause.join(" "),
        premises.join(" ")
    ));
    out
}

#[cfg(test)]
#[path = "surface_implies_pos_tests.rs"]
mod tests;
