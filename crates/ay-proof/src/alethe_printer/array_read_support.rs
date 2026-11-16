// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Ask the actual array renderer under the caller's shared work allowance.

use super::*;

/// An internal ROW tag alone has no checkable wire rule. Recognize support
/// only by running the same checked lowering that the exporter will use,
/// with the same effective source spellings. Failed renders spend work too;
/// a completed derivation also spends its actual returned text length.
#[must_use]
pub fn checked_array_read_lowering_supported(
    terms: &TermStore,
    kind: &ay_core::TheoryLemmaKind,
    clause: &[TermId],
    term_overrides: Option<&HashMap<TermId, String>>,
    remaining_work: &mut u64,
) -> bool {
    use ay_core::TheoryLemmaKind;

    if *remaining_work == 0
        || !matches!(
            kind,
            TheoryLemmaKind::ArraySelectStore { .. } | TheoryLemmaKind::ArrayRowChain
        )
    {
        return false;
    }
    let printer =
        AlethePrinter::new_with_overrides_and_budget(terms, term_overrides, Some(*remaining_work));
    let rendered = dialect::discarding_notes(|| match kind {
        TheoryLemmaKind::ArraySelectStore { index_eq } => printer
            .format_array_select_store(ProofId(0), clause, *index_eq)
            .ok(),
        TheoryLemmaKind::ArrayRowChain => printer.format_array_row_chain(ProofId(0), clause),
        _ => None,
    });
    // Some existing array formatter returns account for term rendering but
    // not the resulting derivation's text. The support question constructs
    // that text too, including repeated packed guards; debit it before success.
    if let Some(text) = rendered.as_ref() {
        printer.charge(text.len() as u64);
    }
    *remaining_work = remaining_work.saturating_sub(printer.work_used());
    rendered.is_some() && !printer.work_budget_exhausted()
}

#[cfg(test)]
mod tests {
    use super::*;
    use ay_core::{Symbol, TheoryLemmaKind};

    fn app(terms: &mut TermStore, name: &str, args: Vec<TermId>, sort: Sort) -> TermId {
        terms.mk_app(Symbol::named(name), args, sort)
    }

    #[test]
    fn actual_row_render_support_requires_the_checked_shape_and_surface() {
        let mut terms = TermStore::new();
        let byte = Sort::bitvec(8);
        let array_sort = Sort::array(byte.clone(), byte.clone());
        let a = terms.mk_var("a", array_sort.clone());
        let i = terms.mk_var("i", byte.clone());
        let j = terms.mk_var("j", byte.clone());
        let v = terms.mk_var("v", byte.clone());
        let w = terms.mk_var("w", byte.clone());
        let store = app(&mut terms, "store", vec![a, i, v], array_sort.clone());
        let read = app(&mut terms, "select", vec![store, i], byte.clone());
        let hit = app(&mut terms, "=", vec![read, v], Sort::Bool);
        let wrong = app(&mut terms, "=", vec![read, w], Sort::Bool);
        let guard = app(&mut terms, "=", vec![i, j], Sort::Bool);
        let outer = app(&mut terms, "store", vec![store, j, w], array_sort);
        let chained = app(&mut terms, "select", vec![outer, i], byte);
        let chain = app(&mut terms, "=", vec![chained, v], Sort::Bool);
        let mut work = 1024 * 1024;
        let row = TheoryLemmaKind::ArraySelectStore { index_eq: true };
        assert!(checked_array_read_lowering_supported(
            &terms,
            &row,
            &[hit],
            None,
            &mut work
        ));
        assert!(work < 1024 * 1024);
        let renderer = AlethePrinter::new(&terms);
        let text = renderer
            .format_array_select_store(ProofId(0), &[hit], true)
            .unwrap();
        assert_ne!(text, "");
        let mut term_work_only = renderer.work_used();
        assert!(term_work_only > 0);
        assert!(!checked_array_read_lowering_supported(
            &terms,
            &row,
            &[hit],
            None,
            &mut term_work_only,
        ));
        assert_eq!(term_work_only, 0);
        assert!(checked_array_read_lowering_supported(
            &terms,
            &TheoryLemmaKind::ArrayRowChain,
            &[guard, chain],
            None,
            &mut work,
        ));
        assert!(!checked_array_read_lowering_supported(
            &terms,
            &row,
            &[wrong],
            None,
            &mut work
        ));
        assert!(!checked_array_read_lowering_supported(
            &terms,
            &TheoryLemmaKind::ArrayRowChain,
            &[chain],
            None,
            &mut work,
        ));
        let mut overrides = HashMap::default();
        overrides.insert(read, "(select a j)".to_string());
        assert!(!checked_array_read_lowering_supported(
            &terms,
            &row,
            &[hit],
            Some(&overrides),
            &mut work,
        ));
        assert!(!checked_array_read_lowering_supported(
            &terms,
            &TheoryLemmaKind::Generic,
            &[hit],
            None,
            &mut work,
        ));
        let mut tiny = 1;
        assert!(!checked_array_read_lowering_supported(
            &terms,
            &row,
            &[hit],
            None,
            &mut tiny
        ));
        assert_eq!(tiny, 0);
        assert!(!checked_array_read_lowering_supported(
            &terms,
            &row,
            &[hit],
            None,
            &mut tiny
        ));
    }
}
