// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! A render that eliminates a problem `let` with `:rule let` reports it, and
//! its surface is `WithoutLetExpansion`, never `Supported`.
//!
//! REGRESSION (measured 2026-09-30 at c57bd8481 on
//! `benchmarks/smt/QF_BV_extract_concat/ext_con_004_001_0016.smt2`): the
//! certificate said `trust_free=yes carcara_surface=supported`; pinned Carcara
//! 1.1.0 printed `valid` for `carcara check -- PROOF PROBLEM` and, under
//! `--expand-let-bindings` (then the corpus runner's), `checking failed on
//! step 't0.l' with rule 'let': term '(and ..)' is of the wrong form,
//! expected '(let ...)'`. The flag expands the `let` before the rule sees it,
//! and no spelling is valid in both invocations. NEGATIVE CONTROLS: the same
//! proof with no `let` in the problem, and the uncertified bridge that prints
//! a `hole` instead of `:rule let`, report nothing.

use super::super::{capture_alethe_dialect_report, note_clean_only, AletheDialectReport};
use crate::{CarcaraSurface, CleanOnlySpelling};
use ay_core::kani_compat::DetHashMap;
use ay_core::{AletheRule, Proof, Sort, TermId, TermStore};

/// `(and p q r)` assumed and projected to `p`: the proof shape of the
/// printer's own `let`-bridge regression (`lib_tests.rs`), rendered with the
/// authored spelling `surface` for the conjunction, if any.
fn render(surface: Option<&str>) -> (String, AletheDialectReport) {
    let mut terms = TermStore::new();
    let p = terms.mk_var("p".to_string(), Sort::Bool);
    let q = terms.mk_var("q".to_string(), Sort::Bool);
    let r = terms.mk_var("r".to_string(), Sort::Bool);
    let and_term = terms.mk_and(vec![p, q, r]);
    let gate = terms.mk_not(and_term);
    let mut overrides: DetHashMap<TermId, String> = DetHashMap::default();
    if let Some(surface) = surface {
        overrides.insert(and_term, surface.to_string());
    }
    let mut proof = Proof::new();
    let assumed = proof.add_assume(and_term, None);
    let projection =
        proof.add_rule_step(AletheRule::AndPos(0), vec![gate, p], vec![], vec![and_term]);
    proof.add_resolution(vec![p], and_term, assumed, projection);
    let (document, report) = capture_alethe_dialect_report(|| {
        crate::try_export_alethe_with_problem_scope_and_overrides(
            &proof,
            &terms,
            &[and_term],
            Some(&overrides),
        )
    });
    (document.expect("the document renders"), report)
}

#[test]
fn a_certified_let_bridge_is_reported_and_is_not_supported() {
    let (document, report) = render(Some("(let ((?v_0 q)) (and p ?v_0 r))"));
    assert!(document.contains(":rule let)"), "{document}");
    assert!(report.eliminates_problem_let(), "{report:?}");
    assert!(
        report.is_pinned_spelling(),
        "a let step is pinned Carcara's: {report:?}"
    );
    let surface = CarcaraSurface::Supported.with_dialect_report(&report);
    assert_eq!(surface, CarcaraSurface::WithoutLetExpansion);
    assert!(!surface.is_supported());
    assert!(
        surface
            .unsupported_reason()
            .is_some_and(|reason| reason.contains("--expand-let-bindings")),
        "{surface:?}"
    );
    assert_eq!(surface.to_string(), "without-let-expansion");
}

#[test]
fn a_document_without_a_let_step_reports_nothing() {
    // NEGATIVE: no `let` in the problem, so no bridge.
    let (document, report) = render(None);
    assert!(!document.contains("(let "), "{document}");
    assert_eq!(report, AletheDialectReport::default());
    assert_eq!(
        CarcaraSurface::Supported.with_dialect_report(&report),
        CarcaraSurface::Supported
    );
    // NEGATIVE: a `let` whose expansion is not the document's spelling takes
    // the bridge's `hole` arm, which prints no `:rule let` step.
    let (document, report) = render(Some("(let ((?v_0 (and q r))) (and p ?v_0))"));
    assert!(document.contains(":rule hole"), "{document}");
    assert!(!document.contains(":rule let"), "{document}");
    assert!(!report.eliminates_problem_let(), "{report:?}");
}

#[test]
fn a_clean_only_spelling_outranks_the_let_invocation_and_unparseable_stays_unsupported() {
    let ((), report) = capture_alethe_dialect_report(|| {
        super::super::note_problem_let_rule();
        note_clean_only(CleanOnlySpelling::ZeroExtendAsConcat);
    });
    assert!(report.eliminates_problem_let());
    // Pinned Carcara refuses the Clean-only step in either invocation.
    assert_eq!(
        CarcaraSurface::Supported.with_dialect_report(&report),
        CarcaraSurface::CleanDialect {
            spelling: CleanOnlySpelling::ZeroExtendAsConcat
        }
    );
    let unparseable = CarcaraSurface::Unsupported {
        reason: "the problem declares `step`".to_string(),
    };
    assert_eq!(
        unparseable.clone().with_dialect_report(&report),
        unparseable
    );
}
