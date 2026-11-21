// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Re-prove an inconsistent subset of integer equalities, then weaken back to
//! the exact original clause through checked Boolean rules.

use num_traits::Zero as _;
use std::fmt::Write as _;

use super::lia_equality_chain::int_equality;
use super::*;

const MAX_LITERALS: usize = 64;
const MAX_ROWS: usize = 8;
const SCREEN_WORK: u64 = 4 * 1024 * 1024;

#[must_use]
pub fn checked_affine_equality_cycle_lowering_supported(
    terms: &TermStore,
    kind: &ay_core::TheoryLemmaKind,
    clause: &[TermId],
    overrides: Option<&HashMap<TermId, String>>,
    remaining_work: &mut u64,
) -> bool {
    if *remaining_work == 0
        || !matches!(kind, ay_core::TheoryLemmaKind::LiaGeneric)
        || !(2..=MAX_LITERALS).contains(&clause.len())
    {
        return false;
    }
    let Ok(stop) = ay_core::resource::current_check_stop() else {
        return false;
    };
    let guard = ay_core::resource::current_guard();
    let mut progress = || {
        !stop.as_ref().is_some_and(|stop| stop())
            && !guard.as_ref().is_some_and(|guard| guard.poll().is_some())
    };
    let printer = AlethePrinter::new_with_overrides_and_budget(
        terms,
        overrides,
        Some((*remaining_work).min(SCREEN_WORK)),
    )
    .with_emission_progress(&mut progress);
    // No external premise is admitted: every reference must resolve to a
    // checked command emitted inside this standalone rendering.
    printer.printed_clause_ledger_active.set(true);
    // Validate and render this codec before the general formatter visits any
    // other producer family. Malformed public inputs must decline here.
    if printer
        .format_affine_equality_cycle(ProofId(0), kind, clause)
        .is_none()
    {
        *remaining_work = remaining_work.saturating_sub(printer.work_used());
        return false;
    }
    let step = ProofStep::TheoryLemma {
        theory: "arith".into(),
        clause: clause.to_vec(),
        farkas: None,
        kind: *kind,
        lia: None,
    };
    let supported = printer
        .format_step(&step, ProofId(0))
        .is_ok_and(|text| text.contains(".cycle.ar") && !text.contains(":rule hole"));
    *remaining_work = remaining_work.saturating_sub(printer.work_used());
    supported && !printer.work_budget_exhausted()
}

impl AlethePrinter<'_> {
    pub(super) fn format_affine_equality_cycle(
        &self,
        id: ProofId,
        kind: &ay_core::TheoryLemmaKind,
        clause: &[TermId],
    ) -> Option<String> {
        if !matches!(kind, ay_core::TheoryLemmaKind::LiaGeneric)
            || !(2..=MAX_LITERALS).contains(&clause.len())
            || !self.admit_emission_work(clause.len() as u64)
        {
            return None;
        }
        if !self.admit_integer_clause_rendering_dag(clause) {
            return None;
        }
        for &literal in clause {
            self.terms.entry_stamp(literal)?;
            if self.terms.sort(literal) != &ay_core::Sort::Bool {
                return None;
            }
        }
        let witness =
            ay_core::proof_validation::arith_inconsistent_equality_subset_witness_with_progress(
                self.terms,
                clause,
                &mut |work, bytes| {
                    self.admit_emission_work((work as u64).saturating_add(bytes as u64))
                },
            )?;
        if witness.literal_indices.is_empty()
            || witness.literal_indices.len() > MAX_ROWS
            || witness.literal_indices.len() != witness.coefficients.len()
            || witness
                .literal_indices
                .windows(2)
                .any(|pair| pair[0] >= pair[1])
            || witness.coefficients.iter().any(|weight| weight.is_zero())
        {
            return None;
        }
        let canonical =
            AlethePrinter::new_with_overrides_and_budget(self.terms, None, Some(SCREEN_WORK))
                .with_parent_emission_progress(self);
        let mut selected = Vec::with_capacity(witness.literal_indices.len());
        let mut coefficients = Vec::with_capacity(witness.literal_indices.len());
        for (&index, weight) in witness.literal_indices.iter().zip(&witness.coefficients) {
            let literal = *clause.get(index)?;
            let TermData::Not(atom) = self.terms.get(literal) else {
                return None;
            };
            let (left, right) = int_equality(self.terms, *atom)?;
            let before = canonical.work_used();
            let left_text = canonical.format_term(left);
            let right_text = canonical.format_term(right);
            self.charge(canonical.work_used().saturating_sub(before));
            if canonical.work_budget_exhausted()
                || self.work_budget_exhausted()
                || self.format_term(left) != left_text
                || self.format_term(right) != right_text
            {
                return None;
            }
            let printed = self.format_derived_literal(literal);
            let weight = if printed == format!("(not (= {left_text} {right_text}))") {
                weight.clone()
            } else if printed == format!("(not (= {right_text} {left_text}))") {
                -weight
            } else {
                return None;
            };
            selected.push(printed);
            coefficients.push(Self::format_constant(&Constant::Rational(
                ay_core::term::RationalWrapper(weight),
            )));
        }
        let parsed: Vec<_> = selected.iter().map(String::as_str).collect();
        let args: Vec<_> = coefficients.iter().map(String::as_str).collect();
        let bytes: usize = selected.iter().chain(&coefficients).map(String::len).sum();
        if !self.admit_emission_work(bytes as u64)
            || !la_generic_surface::printed_la_generic_holds(&parsed, &args)
            || self.work_budget_exhausted()
        {
            return None;
        }
        let printed = self.format_derived_clause_literals(clause);
        for (index, &literal) in clause.iter().enumerate() {
            if witness.literal_indices.binary_search(&index).is_ok() {
                continue;
            }
            let before = canonical.work_used();
            let native = canonical.format_derived_literal(literal);
            self.charge(canonical.work_used().saturating_sub(before));
            // Weakening admits any typed Boolean literal, not an untyped
            // replacement string. Unselected literals retain their own
            // canonical surface in this bounded codec.
            if printed[index] != native
                || canonical.work_budget_exhausted()
                || self.work_budget_exhausted()
            {
                return None;
            }
        }
        let clause_text = printed.join(" ");
        let quoted = (witness.literal_indices.len() as u64).saturating_add(3);
        if !self.admit_emission_work((clause_text.len() as u64).saturating_mul(quoted)) {
            return None;
        }
        let full_or = format!("(or {clause_text})");
        let mut out = format!(
            "(step {id}.cycle.ar (cl {}) :rule la_generic :args ({}))\n",
            selected.join(" "),
            coefficients.join(" "),
        );
        let mut premises = format!("{id}.cycle.ar");
        for (ordinal, &index) in witness.literal_indices.iter().enumerate() {
            let _ =
                writeln!(out,
                "(step {id}.cycle.w{ordinal} (cl {full_or} (not {})) :rule or_neg :args ({index}))",
                printed[index],
            );
            let _ = write!(premises, " {id}.cycle.w{ordinal}");
        }
        let _ = writeln!(
            out,
            "(step {id}.cycle.weak (cl {full_or}) :rule resolution :premises ({premises}))",
        );
        let _ = write!(
            out,
            "(step {id} (cl {clause_text}) :rule or :premises ({id}.cycle.weak))"
        );
        (!self.work_budget_exhausted()).then_some(out)
    }
}

#[cfg(test)]
mod tests;
