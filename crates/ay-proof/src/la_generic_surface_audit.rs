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
    // Replay the complete effective clause literals. Rendering stripped
    // internal atoms would miss an override keyed on `Not(atom)`, even though
    // that override is exactly what the emitted clause prints. Each complete
    // clause literal is negated by Carcara's rule, hence the uniform `false`
    // truth value passed to the printed-hypothesis reconstruction.
    let Some(printed_literals) = clause
        .iter()
        .map(|literal| {
            rendered_terms
                .get(literal)
                .map(|rendered| (rendered.as_str(), false))
        })
        .collect::<Option<Vec<_>>>()
    else {
        return false;
    };
    if !printed_literals.iter().all(|(literal, _)| {
        printed_atom_is_bounded(literal)
            && super::carcara_printed_la_generic_literal_supported(literal)
    }) {
        return false;
    }
    let Some(parse_bytes) = printed_literals
        .iter()
        .try_fold(0usize, |total, (literal, _)| {
            total.checked_add(literal.len())
        })
    else {
        return false;
    };
    let Some(next) = remaining_parse_bytes.checked_sub(parse_bytes) else {
        return false;
    };
    *remaining_parse_bytes = next;
    let Some(hypotheses) = printed_literals
        .iter()
        .map(|(literal, value)| hypothesis(literal, *value))
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
        rendered.insert(not_zero, crate::format_term_alethe(&terms, not_zero));
        rendered.insert(not_one, crate::format_term_alethe(&terms, not_one));
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

    #[test]
    fn quoted_symbol_delimiters_cannot_alias_distinct_farkas_rows() {
        let mut terms = TermStore::new();
        let x = terms.mk_var("quoted_surface_x", Sort::Int);
        let zero = terms.mk_int(0.into());
        let lower = terms.mk_app(Symbol::named("<="), [x, zero], Sort::Bool);
        let upper = terms.mk_app(Symbol::named(">="), [x, zero], Sort::Bool);
        let clause = [lower, upper];
        let farkas = FarkasAnnotation::from_ints(&[1, 1]);
        let mut rendered = HashMap::default();
        rendered.insert(lower, "(<= |(| |) |)".to_string());
        rendered.insert(upper, "(>= |(| |)  |)".to_string());
        let mut checks = 100;
        let mut parse_bytes = 1_000_000;
        assert!(
            !printed_la_generic_certificate_is_valid_bounded(
                &terms,
                &clause,
                &farkas,
                &rendered,
                &mut checks,
                &mut parse_bytes,
            ),
            "quoted-symbol parentheses and whitespace must stay inside their own tokens"
        );
    }

    #[test]
    fn carcara_invalid_quoted_symbol_escapes_cannot_gain_farkas_authority() {
        let mut terms = TermStore::new();
        let x = terms.mk_var("a|b", Sort::Int);
        let zero = terms.mk_int(0.into());
        let lower = terms.mk_app(Symbol::named("<="), [x, zero], Sort::Bool);
        let upper = terms.mk_app(Symbol::named(">="), [x, zero], Sort::Bool);
        let clause = [lower, upper];
        let farkas = FarkasAnnotation::from_ints(&[1, 1]);
        let mut rendered = HashMap::default();
        rendered.insert(lower, crate::format_term_alethe(&terms, lower));
        rendered.insert(upper, crate::format_term_alethe(&terms, upper));
        assert!(
            rendered.values().all(|literal| literal.contains("\\|")),
            "the fixture must exercise AY/Z3 quoted-symbol escaping: {rendered:?}"
        );
        let mut checks = 100;
        let mut parse_bytes = 1_000_000;
        assert!(
            !printed_la_generic_certificate_is_valid_bounded(
                &terms,
                &clause,
                &farkas,
                &rendered,
                &mut checks,
                &mut parse_bytes,
            ),
            "a proof Carcara cannot lex must never receive la_generic authority"
        );
    }

    #[test]
    fn dot_prefixed_symbols_remain_variables_in_exact_farkas_replay() {
        let mut terms = TermStore::new();
        let x = terms.mk_var("dot_surface_x", Sort::Real);
        let zero = terms.mk_rational(num_rational::BigRational::from_integer(0.into()));
        let equality = terms.mk_app(Symbol::named("="), [x, zero], Sort::Bool);
        let bound = terms.mk_app(Symbol::named("<="), [x, zero], Sort::Bool);
        let not_equality = terms.mk_not_raw(equality);
        let clause = [not_equality, bound];
        let farkas = FarkasAnnotation::from_ints(&[1, 1]);
        let mut rendered = HashMap::default();
        rendered.insert(not_equality, "(not (= .5 1.5))".to_string());
        rendered.insert(bound, "(<= .5 0.5)".to_string());
        let mut checks = 100;
        let mut parse_bytes = 1_000_000;
        assert!(
            !printed_la_generic_certificate_is_valid_bounded(
                &terms,
                &clause,
                &farkas,
                &rendered,
                &mut checks,
                &mut parse_bytes,
            ),
            "Carcara lexes `.5` as a symbol, so these two rows are satisfiable"
        );

        let mut unit_rendered = HashMap::default();
        unit_rendered.insert(bound, "(<= .5 0.5)".to_string());
        let mut checks = 10;
        let mut parse_bytes = 1_000_000;
        assert!(!printed_la_generic_certificate_is_valid_bounded(
            &terms,
            &[bound],
            &FarkasAnnotation::from_ints(&[1]),
            &unit_rendered,
            &mut checks,
            &mut parse_bytes,
        ));
    }

    #[test]
    fn alethe_reserved_variable_is_quoted_and_bare_override_is_rejected() {
        let mut terms = TermStore::new();
        let x = terms.mk_var("cl", Sort::Int);
        let zero = terms.mk_int(0.into());
        let lower = terms.mk_app(Symbol::named("<="), [zero, x], Sort::Bool);
        let upper = terms.mk_app(Symbol::named("<"), [x, zero], Sort::Bool);
        let not_lower = terms.mk_not_raw(lower);
        let not_upper = terms.mk_not_raw(upper);
        let clause = [not_lower, not_upper];
        let farkas = FarkasAnnotation::from_ints(&[1, 1]);

        let mut canonical = HashMap::default();
        for literal in clause {
            canonical.insert(literal, crate::format_term_alethe(&terms, literal));
        }
        assert!(
            canonical.values().all(|literal| literal.contains("|cl|")),
            "Alethe-reserved user symbols must be quoted: {canonical:?}"
        );
        let mut checks = 100;
        let mut parse_bytes = 1_000_000;
        assert!(printed_la_generic_certificate_is_valid_bounded(
            &terms,
            &clause,
            &farkas,
            &canonical,
            &mut checks,
            &mut parse_bytes,
        ));

        let mut bare = HashMap::default();
        bare.insert(not_lower, "(not (<= 0 cl))".to_string());
        bare.insert(not_upper, "(not (< cl 0))".to_string());
        let mut checks = 100;
        let mut parse_bytes = 1_000_000;
        assert!(
            !printed_la_generic_certificate_is_valid_bounded(
                &terms,
                &clause,
                &farkas,
                &bare,
                &mut checks,
                &mut parse_bytes,
            ),
            "bare `cl` tokenizes as Alethe syntax, not a term symbol"
        );
    }
}
