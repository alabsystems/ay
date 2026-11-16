// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use ay_core::{Proof, TermStore, TheoryLemmaKind};

/// Refusal logging must not spend/cache through the live printer: the
/// same finite allowance still has to emit and replay the next theorem.
#[test]
fn debug_rejection_preserves_same_printer_budget_cache_and_next_certificate() {
    fn run(debug_cert: bool, probe_cert_reject: bool) -> (String, u64, (u64, usize)) {
        let _flags = ay_core::misc_test_override::set(ay_core::MiscCliFlags {
            debug_cert,
            probe_cert_reject,
            ..Default::default()
        });
        let mut terms = TermStore::new();
        // The old logger rendered and cached this long identifier after
        // the lowering had already refused its unsupported integer sort.
        let unsupported = terms.mk_var("unprintable_".repeat(512), Sort::Int);
        let x = terms.mk_var("x", Sort::bitvec(3));
        let y = terms.mk_var("y", Sort::bitvec(3));
        let left = terms.mk_app(Symbol::named("bvadd"), [x, y], Sort::bitvec(3));
        let right = terms.mk_app(Symbol::named("bvadd"), [y, x], Sort::bitvec(3));
        let equality = terms.mk_app(Symbol::named("="), [left, right], Sort::Bool);
        let assertion = terms.mk_not_raw(equality);
        let literal = terms.mk_not_raw(assertion);
        let polls = std::cell::Cell::new(0usize);
        let mut progress = || {
            polls.set(polls.get() + 1);
            true
        };
        let printer = AlethePrinter::new_with_overrides_and_budget(&terms, None, Some(100_000))
            .with_emission_progress(&mut progress);
        let cache_before = printer.format_cache.borrow().clone();
        let mut blaster = Blaster::new(&printer, ProofId(9), "@diagnostic_reject".into());
        let before_rejection = (printer.work_used(), polls.get());
        assert!(blaster.build(unsupported).is_none());
        drop(blaster);
        let rejection_observations = (
            printer.work_used() - before_rejection.0,
            polls.get() - before_rejection.1,
        );
        assert_eq!(*printer.format_cache.borrow(), cache_before);
        assert_eq!(printer.work_budget, Some(100_000));
        let document = printer
            .format_bv_complete_blast_refutation(ProofId(10), &[literal])
            .expect("the next real theorem uses the same unreset ledger");
        assert!(!document.contains(":rule hole"));
        assert!(!document.contains(":rule trust"));
        assert!(document.contains(":rule resolution"));
        // Separately validate the native authored-scope refutation. A
        // syntactically complete document is not itself proof authority.
        let mut proof = Proof::new();
        let assume = proof.add_assume(assertion, None);
        let lemma =
            proof.add_theory_lemma_with_kind("bv", vec![literal], TheoryLemmaKind::BvBitBlast);
        proof.add_resolution(Vec::new(), assertion, assume, lemma);
        crate::check_proof_strict_with_context(&proof, &terms, None, None, Some(&[assertion]))
            .expect("the native refutation remains strictly checked");
        // Later proof emission can reuse the thread's exact-CNF refutation
        // memo. Compare its document and charged work; progress equality
        // belongs to the rejection phase observed above.
        (document, printer.work_used(), rejection_observations)
    }
    let ordinary = run(false, false);
    for (debug, probe) in [(true, false), (false, true), (true, true)] {
        assert_eq!(run(debug, probe), ordinary);
    }
}
