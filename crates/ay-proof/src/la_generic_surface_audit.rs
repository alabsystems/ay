// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Bounded replay of the exact printed `la_generic` surface.

use ay_core::kani_compat::DetHashMap as HashMap;
use ay_core::term::TermData;
use ay_core::{FarkasAnnotation, Symbol, TermId, TermStore};
use num_rational::Rational64;
use num_traits::{Signed, Zero};

use super::{coeffs_valid, hypothesis};
use crate::alethe_printer::AlethePrintError;
use crate::alethe_printer::AlethePrinter;

const MAX_PRINTED_ATOM_BYTES: usize = 64 * 1024;
const MAX_PRINTED_ATOM_DEPTH: usize = 256;

type RenderedTermBatches = (HashMap<TermId, String>, HashMap<TermId, String>);
type RenderedTermBatchesWithWork = (HashMap<TermId, String>, HashMap<TermId, String>, u64);

pub(super) fn printed_atom_is_bounded(atom: &str) -> bool {
    #[derive(Clone, Copy, PartialEq, Eq)]
    enum Mode {
        Normal,
        String,
        QuotedSymbol,
    }

    if atom.len() > MAX_PRINTED_ATOM_BYTES {
        return false;
    }
    let bytes = atom.as_bytes();
    let mut index = 0usize;
    let mut depth = 0usize;
    let mut mode = Mode::Normal;
    while index < bytes.len() {
        match (mode, bytes[index]) {
            (Mode::Normal, b'(') => {
                depth += 1;
                if depth > MAX_PRINTED_ATOM_DEPTH {
                    return false;
                }
            }
            (Mode::Normal, b')') => {
                let Some(next) = depth.checked_sub(1) else {
                    return false;
                };
                depth = next;
            }
            (Mode::Normal, b'"') => mode = Mode::String,
            (Mode::Normal, b'|') => mode = Mode::QuotedSymbol,
            (Mode::String, b'"') if bytes.get(index + 1) == Some(&b'"') => index += 1,
            (Mode::String, b'"') => mode = Mode::Normal,
            (Mode::QuotedSymbol, b'|') => mode = Mode::Normal,
            _ => {}
        }
        index += 1;
    }
    depth == 0 && mode == Mode::Normal
}

fn format_term_batch(
    printer: &AlethePrinter<'_>,
    term_ids: &[TermId],
) -> Result<HashMap<TermId, String>, AlethePrintError> {
    let mut rendered = HashMap::default();
    for &term in term_ids {
        if rendered.contains_key(&term) {
            continue;
        }
        let text = printer.format_term(term);
        if printer.work_budget_exhausted() {
            return Err(printer.work_budget_error(0));
        }
        rendered.insert(term, text);
    }
    Ok(rendered)
}

/// Render a deduplicated term batch through one cached, work-budgeted printer.
pub fn format_terms_alethe_with_overrides_bounded(
    terms: &TermStore,
    term_ids: &[TermId],
    term_overrides: &HashMap<TermId, String>,
    work_budget: u64,
) -> Result<HashMap<TermId, String>, AlethePrintError> {
    let printer = AlethePrinter::new_with_overrides_and_budget(
        terms,
        Some(term_overrides),
        Some(work_budget),
    );
    format_term_batch(&printer, term_ids)
}

/// Render effective and canonical batches against one shared actual-work cap.
pub fn format_terms_alethe_with_overrides_and_canonical_bounded(
    terms: &TermStore,
    effective_term_ids: &[TermId],
    term_overrides: &HashMap<TermId, String>,
    canonical_term_ids: &[TermId],
    work_budget: u64,
) -> Result<RenderedTermBatches, AlethePrintError> {
    format_terms_alethe_with_overrides_and_canonical_bounded_with_work(
        terms,
        effective_term_ids,
        term_overrides,
        canonical_term_ids,
        work_budget,
    )
    .map(|(effective, canonical, _)| (effective, canonical))
}

/// Render effective and canonical batches against one shared cap and return
/// the exact printer work consumed by both batches.
pub fn format_terms_alethe_with_overrides_and_canonical_bounded_with_work(
    terms: &TermStore,
    effective_term_ids: &[TermId],
    term_overrides: &HashMap<TermId, String>,
    canonical_term_ids: &[TermId],
    work_budget: u64,
) -> Result<RenderedTermBatchesWithWork, AlethePrintError> {
    let (effective, effective_work) = {
        let printer = AlethePrinter::new_with_overrides_and_budget(
            terms,
            Some(term_overrides),
            Some(work_budget),
        );
        let rendered = format_term_batch(&printer, effective_term_ids)?;
        (rendered, printer.work_used())
    };
    let Some(remaining_work) = work_budget.checked_sub(effective_work) else {
        return Err(AlethePrintError::EmissionBudgetExhausted {
            budget: work_budget,
            steps_rendered: 0,
        });
    };
    let printer = AlethePrinter::new_with_overrides_and_budget(terms, None, Some(remaining_work));
    let canonical = format_term_batch(&printer, canonical_term_ids)?;
    let total_work = effective_work.checked_add(printer.work_used()).ok_or(
        AlethePrintError::EmissionBudgetExhausted {
            budget: work_budget,
            steps_rendered: 0,
        },
    )?;
    Ok((effective, canonical, total_work))
}

/// Check the exact `la_generic` certificate that proof export will print,
/// charging every candidate sign-vector replay by its row count against
/// `remaining_checks`.
///
/// The clause is formatted through the real printer and follows export's sign
/// search exactly. Budget exhaustion rejects instead of falling back.
#[must_use]
pub fn printed_la_generic_certificate_is_valid_bounded(
    terms: &TermStore,
    clause: &[TermId],
    farkas: &FarkasAnnotation,
    rendered_terms: &HashMap<TermId, String>,
    remaining_checks: &mut usize,
    remaining_parse_bytes: &mut usize,
) -> bool {
    if clause.len() != farkas.coefficients.len() {
        return false;
    }
    let conflict: Vec<ay_core::TheoryLit> = clause
        .iter()
        .map(|&literal| match terms.get(literal) {
            TermData::Not(inner) => ay_core::TheoryLit::new(*inner, true),
            _ => ay_core::TheoryLit::new(literal, false),
        })
        .collect();
    // Export first performs AY's internal equality-orientation search (capped
    // at 2^10). Charge its complete search space up front so an accepted set
    // of lemmas also bounds the later printer's aggregate work.
    let equality_rows = conflict
        .iter()
        .zip(&farkas.coefficients)
        .filter(|(literal, coefficient)| {
            !coefficient.is_zero()
                && matches!(
                    terms.get(literal.term),
                    TermData::App(Symbol::Named(op), args) if op == "=" && args.len() == 2
                )
        })
        .count();
    let internal_vectors = if (1..=10).contains(&equality_rows) {
        1usize << equality_rows
    } else {
        1
    };
    let Some(internal_work) = internal_vectors.checked_mul(conflict.len().max(1)) else {
        return false;
    };
    let Some(next) = remaining_checks.checked_sub(internal_work) else {
        return false;
    };
    *remaining_checks = next;
    let existing =
        ay_core::proof_validation::resolve_equality_coefficient_signs(terms, &conflict, farkas)
            .unwrap_or_else(|| farkas.coefficients.clone());
    let Some(printed_atoms) = conflict
        .iter()
        .map(|literal| {
            rendered_terms
                .get(&literal.term)
                .map(|rendered| (rendered.as_str(), literal.value))
        })
        .collect::<Option<Vec<_>>>()
    else {
        return false;
    };
    if !printed_atoms
        .iter()
        .all(|(atom, _)| printed_atom_is_bounded(atom))
    {
        return false;
    }
    let Some(parse_bytes) = printed_atoms
        .iter()
        .try_fold(0usize, |total, (atom, _)| total.checked_add(atom.len()))
    else {
        return false;
    };
    let Some(next) = remaining_parse_bytes.checked_sub(parse_bytes) else {
        return false;
    };
    *remaining_parse_bytes = next;
    let Some(hypotheses) = printed_atoms
        .iter()
        .map(|(atom, value)| hypothesis(atom, *value))
        .collect::<Option<Vec<_>>>()
    else {
        return false;
    };
    let mut check = |coefficients: &[Rational64]| {
        let next = remaining_checks.checked_sub(hypotheses.len().max(1))?;
        *remaining_checks = next;
        Some(coeffs_valid(&hypotheses, coefficients))
    };
    if check(&existing) == Some(true) {
        return true;
    }
    let equality_indices: Vec<usize> = hypotheses
        .iter()
        .enumerate()
        .filter_map(|(index, (_, _, equality))| equality.then_some(index))
        .collect();
    if equality_indices.len() > 16 {
        return false;
    }
    let base: Vec<Rational64> = farkas.coefficients.iter().map(|c| c.abs()).collect();
    for mask in 0u32..(1u32 << equality_indices.len()) {
        let mut candidate = base.clone();
        for (bit, &index) in equality_indices.iter().enumerate() {
            if mask & (1u32 << bit) != 0 {
                candidate[index] = -candidate[index];
            }
        }
        match check(&candidate) {
            Some(true) => return true,
            Some(false) => {}
            None => return false,
        }
    }
    false
}

#[cfg(test)]
mod tests {
    use ay_core::kani_compat::DetHashMap as HashMap;
    use ay_core::{FarkasAnnotation, Sort, Symbol, TermStore};

    use super::{
        format_terms_alethe_with_overrides_and_canonical_bounded,
        format_terms_alethe_with_overrides_and_canonical_bounded_with_work,
        format_terms_alethe_with_overrides_bounded, printed_atom_is_bounded,
        printed_la_generic_certificate_is_valid_bounded, MAX_PRINTED_ATOM_BYTES,
        MAX_PRINTED_ATOM_DEPTH,
    };

    #[test]
    fn effective_and_canonical_batches_share_actual_render_work() {
        let mut terms = TermStore::new();
        let x = terms.mk_var("x", Sort::Int);
        let root = terms.mk_app(Symbol::named("+"), [x, x], Sort::Int);
        let mut effective = HashMap::default();
        effective.insert(root, "(+ x x)".to_string());
        let empty = HashMap::default();

        assert!(format_terms_alethe_with_overrides_bounded(&terms, &[root], &effective, 9).is_ok());
        assert!(format_terms_alethe_with_overrides_bounded(&terms, &[root], &empty, 9).is_ok());
        assert!(format_terms_alethe_with_overrides_and_canonical_bounded(
            &terms,
            &[root],
            &effective,
            &[root],
            9,
        )
        .is_err());
        assert!(format_terms_alethe_with_overrides_and_canonical_bounded(
            &terms,
            &[root],
            &effective,
            &[root],
            16,
        )
        .is_ok());
        let (_, _, work) = format_terms_alethe_with_overrides_and_canonical_bounded_with_work(
            &terms,
            &[root],
            &effective,
            &[root],
            16,
        )
        .expect("the work-reporting wrapper shares the same successful cap");
        assert!(work > 9 && work <= 16);
    }

    #[test]
    fn printed_atom_bounds_reject_large_or_deep_inputs() {
        assert!(printed_atom_is_bounded("(< x 1)"));
        assert!(!printed_atom_is_bounded(
            &"x".repeat(MAX_PRINTED_ATOM_BYTES + 1)
        ));

        let deep = format!(
            "{}x{}",
            "(".repeat(MAX_PRINTED_ATOM_DEPTH + 1),
            ")".repeat(MAX_PRINTED_ATOM_DEPTH + 1)
        );
        assert!(!printed_atom_is_bounded(&deep));
        assert!(printed_atom_is_bounded("(< |name(with parens)| 1)"));
    }

    #[test]
    fn certificate_budget_charges_rows_and_internal_equality_search() {
        let mut terms = TermStore::new();
        let zero = terms.mk_int(0.into());
        let one = terms.mk_int(1.into());
        let valid = terms.mk_app(Symbol::named("<"), [zero, one], Sort::Bool);
        let mut rendered = HashMap::default();
        rendered.insert(valid, crate::format_term_alethe(&terms, valid));
        let unit = FarkasAnnotation::from_ints(&[1]);
        let mut one_row_pass = 1;
        let mut parse = usize::MAX;
        assert!(!printed_la_generic_certificate_is_valid_bounded(
            &terms,
            &[valid],
            &unit,
            &rendered,
            &mut one_row_pass,
            &mut parse,
        ));
        let mut two_row_passes = 2;
        assert!(printed_la_generic_certificate_is_valid_bounded(
            &terms,
            &[valid],
            &unit,
            &rendered,
            &mut two_row_passes,
            &mut parse,
        ));

        let x = terms.mk_var("surface_budget_x", Sort::Int);
        let eq_zero = terms.mk_app(Symbol::named("="), [x, zero], Sort::Bool);
        let eq_one = terms.mk_app(Symbol::named("="), [x, one], Sort::Bool);
        let not_zero = terms.mk_not_raw(eq_zero);
        let not_one = terms.mk_not_raw(eq_one);
        rendered.insert(eq_zero, crate::format_term_alethe(&terms, eq_zero));
        rendered.insert(eq_one, crate::format_term_alethe(&terms, eq_one));
        let equalities = FarkasAnnotation::from_ints(&[1, 1]);
        let mut insufficient = 9;
        assert!(!printed_la_generic_certificate_is_valid_bounded(
            &terms,
            &[not_zero, not_one],
            &equalities,
            &rendered,
            &mut insufficient,
            &mut parse,
        ));

        let many_equalities: Vec<_> = (0..11)
            .map(|index| {
                let numeral = terms.mk_int(index.into());
                terms.mk_app(Symbol::named("="), [x, numeral], Sort::Bool)
            })
            .collect();
        for &equality in &many_equalities {
            rendered.insert(equality, crate::format_term_alethe(&terms, equality));
        }
        let many_coefficients = FarkasAnnotation::from_ints(&[1; 11]);
        let mut less_than_one_setup_pass = 10;
        assert!(!printed_la_generic_certificate_is_valid_bounded(
            &terms,
            &many_equalities,
            &many_coefficients,
            &rendered,
            &mut less_than_one_setup_pass,
            &mut parse,
        ));
        assert_eq!(less_than_one_setup_pass, 10);
    }
}
