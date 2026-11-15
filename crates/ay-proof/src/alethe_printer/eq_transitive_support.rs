// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Share the actual printed-chain decision with publication policy.

use super::*;

/// Render the exact EUF transitivity clause under its effective source
/// spelling. A valid native chain can print as a disconnected one; the
/// renderer's honest hole must remain a publication refusal too.
#[must_use]
pub fn checked_euf_transitive_lowering_supported(
    terms: &TermStore,
    clause: &[TermId],
    term_overrides: Option<&HashMap<TermId, String>>,
    remaining_work: &mut u64,
) -> bool {
    use std::io::Write;

    if *remaining_work == 0 {
        return false;
    }
    let printer =
        AlethePrinter::new_with_overrides_and_budget(terms, term_overrides, Some(*remaining_work));
    let rendered = dialect::discarding_notes(|| {
        printer.format_theory_lemma(
            ProofId(0),
            "euf",
            clause,
            None,
            &ay_core::TheoryLemmaKind::EufTransitive,
            None,
        )
    });
    let mut supported = false;
    if let Ok(text) = rendered {
        // Account for the returned derivation and the actual streaming scan
        // before scanning. Neither a failed render nor a refused scan refunds.
        if let Some(work) = (text.len() as u64).checked_mul(2) {
            if printer.admit_emission_work(work) {
                let mut scan = crate::AletheDocumentScan::default();
                supported = scan.write_all(text.as_bytes()).is_ok()
                    && !scan.overflowed
                    && scan.unproved == 0;
            }
        } else {
            printer.charge(u64::MAX);
        }
    }
    *remaining_work = remaining_work.saturating_sub(printer.work_used());
    supported && !printer.work_budget_exhausted()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn printed_chain_support_rejects_disconnected_source_and_exhausted_work() {
        let mut terms = TermStore::new();
        let a = terms.mk_var("a", Sort::Int);
        let b = terms.mk_var("b", Sort::Int);
        let c = terms.mk_var("c", Sort::Int);
        let _x = terms.mk_var("x", Sort::Int);
        let ab = terms.mk_eq(a, b);
        let bc = terms.mk_eq(b, c);
        let ac = terms.mk_eq(a, c);
        let clause = [terms.mk_not_raw(ab), terms.mk_not_raw(bc), ac];
        let mut work = 1024 * 1024;
        assert!(checked_euf_transitive_lowering_supported(
            &terms, &clause, None, &mut work,
        ));
        assert!(work < 1024 * 1024);
        let mut overrides = HashMap::default();
        overrides.insert(bc, "(= x c)".to_string());
        let before = work;
        assert!(!checked_euf_transitive_lowering_supported(
            &terms,
            &clause,
            Some(&overrides),
            &mut work,
        ));
        assert!(work < before);
        let mut tiny = 1;
        assert!(!checked_euf_transitive_lowering_supported(
            &terms, &clause, None, &mut tiny,
        ));
        assert_eq!(tiny, 0);
        assert!(!checked_euf_transitive_lowering_supported(
            &terms, &clause, None, &mut tiny,
        ));
    }
}
