// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Term-ITE projection via the existing ite_intro definition and Boolean
//! ite1/ite2 unit-premise rules. Every role is checked again on printed text.
use super::*;

#[derive(Clone, Copy)]
pub(super) enum EqualityOrientation {
    IteFirst,
    BranchFirst,
}

/// Shared with the existing Shannon-lift derivation, without changing its
/// original steps or labels. These are the two guarded definition clauses.
pub(super) fn emit_definition_branches(
    id: &str,
    ite: &str,
    condition: &str,
    then_value: &str,
    else_value: &str,
    orientation: EqualityOrientation,
    steps: &mut Vec<String>,
) {
    let reflexive = format!("(= {ite} {ite})");
    let equality = |branch: &str| match orientation {
        EqualityOrientation::BranchFirst => format!("(= {branch} {ite})"),
        EqualityOrientation::IteFirst => format!("(= {ite} {branch})"),
    };
    let then_equality = equality(then_value);
    let else_equality = equality(else_value);
    let definition = format!("(ite {condition} {then_equality} {else_equality})");
    let conjunction = format!("(and {reflexive} {definition})");
    let introduced = format!("(= {reflexive} {conjunction})");
    steps.push(format!("(step {id}.ii (cl {introduced}) :rule ite_intro)"));
    steps.push(format!(
        "(step {id}.rs (cl {reflexive}) :rule eq_reflexive)"
    ));
    steps.push(format!(
        "(step {id}.ep (cl (not {introduced}) (not {reflexive}) {conjunction}) :rule equiv_pos2)"
    ));
    steps.push(format!(
        "(step {id}.k (cl {conjunction}) :rule resolution :premises ({id}.ep {id}.ii {id}.rs))"
    ));
    steps.push(format!(
        "(step {id}.d (cl {definition}) :rule and :premises ({id}.k) :args (1))"
    ));
    steps.push(format!(
        "(step {id}.t (cl (not {condition}) {then_equality}) :rule ite2 :premises ({id}.d))"
    ));
    steps.push(format!(
        "(step {id}.f (cl {condition} {else_equality}) :rule ite1 :premises ({id}.d))"
    ));
}

impl AlethePrinter<'_> {
    pub(super) fn format_ite_branch_projection(
        &self,
        id: ProofId,
        clause: &[TermId],
    ) -> Option<String> {
        // The strict recognizer flattens packed ORs. Reject an unsupported
        // arity by header before it can copy a wide malformed argument list.
        match clause {
            [_, _] => (),
            [packed] => match self.terms.get(*packed) {
                TermData::App(Symbol::Named(name), args) if name == "or" && args.len() == 2 => (),
                _ => return None,
            },
            _ => return None,
        }
        if !crate::recognize_ite_branch_projection(self.terms, clause) {
            return None;
        }
        let packed = if let [term] = clause {
            Some(self.format_derived_literal(*term))
        } else {
            None
        };
        let literals = match &packed {
            Some(text) => split_application(text, "or")?,
            None => self.format_derived_clause_literals(clause),
        };
        if literals.len() != 2 {
            return None;
        }
        // Pay for repeated emitted definitions before constructing them. This
        // conservative bound shares the caller's unchanged emission allowance.
        let work = literals.iter().try_fold(4096u64, |work, text| {
            work.checked_add(u64::try_from(text.len()).ok()?.checked_mul(64)?)
        })?;
        self.charge(work);
        if self.work_budget_exhausted() {
            return None;
        }
        for (guard_index, equality_index) in [(0, 1), (1, 0)] {
            let guard = &literals[guard_index];
            let equality = &literals[equality_index];
            let Some(parts) = split_application(equality, "=") else {
                continue;
            };
            let [left, right] = parts.as_slice() else {
                continue;
            };
            if format!("(= {left} {right})") != *equality {
                continue;
            }
            for (ite, selected, orientation) in [
                (left, right, EqualityOrientation::IteFirst),
                (right, left, EqualityOrientation::BranchFirst),
            ] {
                let Some(parts) = split_application(ite, "ite") else {
                    continue;
                };
                let [condition, then_value, else_value] = parts.as_slice() else {
                    continue;
                };
                if format!("(ite {condition} {then_value} {else_value})") != *ite {
                    continue;
                }
                let branch = if *guard == format!("(not {condition})")
                    && surface_literal::same_printed_term(selected, then_value)
                {
                    "t"
                } else if guard == condition
                    && surface_literal::same_printed_term(selected, else_value)
                {
                    "f"
                } else {
                    continue;
                };
                let mut lines = Vec::new();
                let label = id.to_string();
                emit_definition_branches(
                    &label,
                    ite,
                    condition,
                    then_value,
                    else_value,
                    orientation,
                    &mut lines,
                );
                let premise = format!("{id}.{branch}");
                let flat_id = if packed.is_some() {
                    format!("{id}.flat")
                } else {
                    label
                };
                lines.push(format!(
                    "(step {flat_id} (cl {}) :rule reordering :premises ({premise}))",
                    literals.join(" ")
                ));
                if let Some(packed) = &packed {
                    let mut premises = vec![flat_id];
                    for (position, literal) in literals.iter().enumerate() {
                        let label = format!("{id}.o{position}");
                        lines.push(format!("(step {label} (cl {packed} (not {literal})) :rule or_neg :args ({position}))"));
                        premises.push(label);
                    }
                    lines.push(format!(
                        "(step {id} (cl {packed}) :rule resolution :premises ({}))",
                        premises.join(" ")
                    ));
                }
                let text = lines.join("\n");
                self.charge(text.len() as u64);
                return (!self.work_budget_exhausted()).then_some(text);
            }
        }
        None
    }
}

/// The strict publication screen asks the exact same bounded printer. The
/// allowance is shared with other guarded-definition lemmas across the proof.
#[must_use]
pub fn checked_ite_branch_projection_lowering_supported(
    terms: &TermStore,
    clause: &[TermId],
    overrides: Option<&HashMap<TermId, String>>,
    remaining_work: &mut u64,
) -> bool {
    if *remaining_work == 0 {
        return false;
    }
    let printer =
        AlethePrinter::new_with_overrides_and_budget(terms, overrides, Some(*remaining_work));
    let supported = printer
        .format_ite_branch_projection(ProofId(0), clause)
        .is_some();
    *remaining_work = remaining_work.saturating_sub(printer.work_used());
    supported && !printer.work_budget_exhausted()
}

#[cfg(test)]
#[path = "ite_branch_projection_tests.rs"]
mod tests;
