// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! `CleanOnlySpelling::DatatypeSelectorProject`: a selector over a
//! constructor checked by Clean's `dt_project`, which pinned Carcara 9a352ee
//! does not implement.
//!
//! The Clean dialect prints `dt_project` and reports the spelling, so the
//! certificate is `carcara_surface=clean-dialect` and the library surface is
//! `CarcaraSurface::CleanDialect { DatatypeSelectorProject }`; the pinned
//! dialect prints the hole and reports nothing. Pinned Carcara on `PATH`
//! replays the Clean document and must refuse it exactly at `dt_project`.
//! The rule vocabulary of each dialect (`AletheDialect::implements_rule`)
//! is pinned here too, since the round-trip self-check reads it.

use super::*;

const PROJECT: CleanOnlySpelling = CleanOnlySpelling::DatatypeSelectorProject;

/// `(= (fst (mk a b)) a)` as a bare `DatatypeSelectorProject` step and as a
/// closed refutation: `[problem, proof, step]`, in `dialect`, with the report.
fn projection(dialect: AletheDialect) -> ([String; 3], AletheDialectReport) {
    let mut terms = TermStore::new();
    terms.register_constructor_fields("mk", vec!["fst".to_string(), "snd".to_string()]);
    let a = terms.mk_var("a", Sort::Int);
    let b = terms.mk_var("b", Sort::Int);
    let built = terms.mk_app(
        Symbol::named("mk"),
        [a, b],
        Sort::Uninterpreted("Pair".to_string()),
    );
    let selection = terms.mk_app(Symbol::named("fst"), [built], Sort::Int);
    let equality = terms.mk_app(Symbol::named("="), [selection, a], Sort::Bool);
    let step = ay_core::ProofStep::TheoryLemma {
        theory: "datatype".to_string(),
        clause: vec![equality],
        farkas: None,
        kind: ay_core::TheoryLemmaKind::DatatypeSelectorProject,
        lia: None,
    };
    capture_alethe_dialect_report(|| {
        with_alethe_dialect(dialect, || {
            let printer = AlethePrinter::new(&terms);
            let text = printer.format_step(&step, ProofId(1)).expect("renders");
            let assertion = format!("(not {})", printer.format_term(equality));
            let problem = format!(
                "(set-logic QF_DT)\n\
                 (declare-datatypes ((Pair 0)) (((mk (fst Int) (snd Int)))))\n\
                 (declare-const a Int)\n(declare-const b Int)\n(assert {assertion})\n(check-sat)\n"
            );
            let proof = format!(
                "(assume a0 {assertion})\n{text}\n(step done (cl) :rule resolution :premises (a0 t1))\n"
            );
            [problem, proof, text]
        })
    })
}

#[test]
fn the_clean_dialect_discloses_dt_project_and_pinned_carcara_refuses_it_there() {
    let ([problem, proof, step], report) = projection(AletheDialect::Clean);
    assert_eq!(step, "(step t1 (cl (= (fst (mk a b)) a)) :rule dt_project)");
    assert_eq!(report.first_clean_only(), Some(PROJECT));
    assert_eq!(
        crate::CarcaraSurface::Supported.with_dialect_report(&report),
        crate::CarcaraSurface::CleanDialect { spelling: PROJECT }
    );
    assert_pinned_refuses_at("dt-project-clean", &problem, &proof, "dt_project");

    let ([_, pinned_proof, pinned_step], pinned_report) = projection(AletheDialect::PinnedCarcara);
    assert_eq!(
        pinned_step,
        "(step t1 (cl (= (fst (mk a b)) a)) :rule hole)"
    );
    assert!(pinned_report.is_pinned_spelling(), "{pinned_report:?}");
    assert_eq!(
        crate::CarcaraSurface::Supported.with_dialect_report(&pinned_report),
        crate::CarcaraSurface::Supported
    );
    if let Some((verdict, stderr)) = carcara_verdict("dt-project-pinned", &problem, &pinned_proof) {
        assert_eq!(verdict, "holey", "{stderr}\n{pinned_proof}");
    }
}

#[test]
fn the_dt_project_disclosure_says_the_pinned_dialect_prints_a_hole() {
    assert!(!PROJECT.has_pinned_spelling());
    assert!(PROJECT.describe().contains("dt_project"));
    assert!(PROJECT.pinned_dialect_note().contains("hole"));
    let disclosed = crate::CarcaraSurface::CleanDialect { spelling: PROJECT };
    assert!(!disclosed.is_supported());
    assert_eq!(disclosed.unsupported_reason(), Some(PROJECT.describe()));
    assert!(disclosed.to_string().starts_with("clean-dialect("));
}

/// The round-trip self-check reads a document in its own dialect's rule
/// vocabulary: Clean's adds `dt_project`, pinned Carcara's does not.
#[test]
fn each_dialect_implements_its_own_rule_vocabulary() {
    for rule in ay_core::CHECKABLE_ALETHE_RULES {
        assert!(AletheDialect::Clean.implements_rule(rule), "{rule}");
        assert!(AletheDialect::PinnedCarcara.implements_rule(rule), "{rule}");
    }
    for rule in ay_core::CLEAN_DIALECT_ALETHE_RULES {
        assert!(AletheDialect::Clean.implements_rule(rule), "{rule}");
        assert!(
            !AletheDialect::PinnedCarcara.implements_rule(rule),
            "{rule}"
        );
    }
    for dialect in [AletheDialect::Clean, AletheDialect::PinnedCarcara] {
        for rule in ["trust", "dt_clash", "dt_distinct", "ay_unknown"] {
            assert!(!dialect.implements_rule(rule), "{dialect:?} {rule}");
        }
    }
}
