// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The library's surface verdicts say what the render printed:
//! `UnsatProofArtifact::carcara_surface`, and the verdict
//! `Executor::try_export_last_proof_alethe_for_problem_scope_with_carcara_surface`
//! returns beside its document.
//!
//! REGRESSION (630842a86 left it open, measured 2026-09-30): since 630842a86
//! the CLI's certificate line says `carcara_surface=clean-dialect` for a
//! document that keeps a spelling only Clean's vendored Carcara checks, but
//! both library verdicts were computed from sorts and symbols alone and said
//! `CarcaraSurface::Supported` for the same document, which pinned Carcara
//! 9a352ee refuses. A consumer that claims a pinned Carcara check refuses
//! anything but `Supported`, so the lie reached it as a checkable artifact.
//! Now the render's dialect report is captured and a kept Clean-only spelling
//! is `CarcaraSurface::CleanDialect`. NEGATIVE CONTROLS: the pinned dialect's
//! `bitblast_ashr` document and a logical-shift document stay `Supported`,
//! and each is a literal `valid`.

use super::{exact_carcara_verdict, parse, require_carcara_or_skip, Executor};
use ay_dpll::api::{
    AletheDialect, CarcaraSurface, CleanOnlySpelling, Logic, Solver, StrictProofVerdict,
    UnsatProofArtifact,
};
use ntest::timeout;

/// p01: `bitblast_ashr` over a symbolic sign bit.
const ASHR: &str = "(declare-const x (_ BitVec 8))\n\
    (assert (not (= (bvashr x #x03) ((_ sign_extend 3) ((_ extract 7 3) x)))))\n";
/// A symbolic dividend: Clean's divider in both dialects. Four bits: pinned
/// Carcara prints the whole expected divider term when it refuses the step,
/// and at eight bits that print alone takes minutes.
const DIVIDE: &str = "(declare-const x (_ BitVec 4))\n(assert (bvult x (bvudiv x #x3)))\n";
/// No Clean-only spelling at all.
const LOGICAL: &str = "(declare-const x (_ BitVec 8))\n\
    (assert (not (= (bvlshr (bvshl x #x03) #x03) (bvand x #x1f))))\n";

const PINNED: Option<AletheDialect> = Some(AletheDialect::PinnedCarcara);
const SIGN: Option<CleanOnlySpelling> = Some(CleanOnlySpelling::SignFilledAshrOvershift);
const DIVIDER: Option<CleanOnlySpelling> = Some(CleanOnlySpelling::FixedDivider);

/// Label, script, dialect (default when `None`), the Clean-only spelling the
/// document keeps, and the rule pinned Carcara refuses it at.
const CASES: [(
    &str,
    &str,
    Option<AletheDialect>,
    Option<CleanOnlySpelling>,
    &str,
); 5] = [
    ("ashr-clean", ASHR, None, SIGN, "bitblast_ashr"),
    ("ashr-pinned", ASHR, PINNED, None, ""),
    ("udiv-clean", DIVIDE, None, DIVIDER, "bitblast_udiv"),
    ("udiv-pinned", DIVIDE, PINNED, DIVIDER, "bitblast_udiv"),
    ("logical", LOGICAL, None, None, ""),
];

fn expected(spelling: Option<CleanOnlySpelling>) -> CarcaraSurface {
    spelling.map_or(CarcaraSurface::Supported, |spelling| {
        CarcaraSurface::CleanDialect { spelling }
    })
}

fn artifact(label: &str, dialect: Option<AletheDialect>, script: &str) -> UnsatProofArtifact {
    let mut solver = Solver::try_new(Logic::QfBv).expect("QF_BV solver");
    solver.set_produce_proofs(true);
    if let Some(dialect) = dialect {
        solver.set_alethe_dialect(dialect);
        assert_eq!(solver.alethe_dialect(), dialect);
    }
    solver.parse_smtlib2(script).expect("parse the fixture");
    let verdict = solver.check_sat();
    assert!(verdict.is_unsat(), "{label}: {verdict:?}");
    solver
        .export_last_unsat_artifact()
        .unwrap_or_else(|| panic!("{label}: a strict-checked QF_BV refutation publishes"))
}

#[test]
#[timeout(300_000)]
fn the_unsat_artifact_discloses_the_clean_only_spelling_its_document_keeps() {
    let carcara = require_carcara_or_skip();
    for (label, script, dialect, spelling, rule) in CASES {
        let artifact = artifact(label, dialect, script);
        assert!(
            matches!(artifact.strict_verdict, StrictProofVerdict::Verified(_)),
            "{label}: {:?}",
            artifact.strict_verdict
        );
        assert_eq!(artifact.carcara_surface, expected(spelling), "{label}");
        assert_eq!(
            artifact.carcara_surface.is_supported(),
            spelling.is_none(),
            "{label}: only a document with no Clean-only spelling is pinned-checkable"
        );
        let Some(carcara) = carcara.as_ref() else {
            continue;
        };
        let problem = artifact
            .alethe_problem_smt2
            .as_deref()
            .unwrap_or_else(|| panic!("{label}: QF_BV carries its exact problem"));
        let (valid, diagnostic) = exact_carcara_verdict(carcara, problem, &artifact.alethe);
        if spelling.is_none() {
            assert!(
                valid,
                "{label}: a Supported artifact is a literal `valid`: {diagnostic}"
            );
        } else {
            assert!(
                !valid && diagnostic.contains(&format!("with rule '{rule}'")),
                "{label}: the disclosed step is the one pinned Carcara refuses: {diagnostic}"
            );
        }
    }
}

#[test]
#[timeout(300_000)]
fn the_problem_scoped_export_reports_the_same_surface_as_the_artifact() {
    for (label, script, dialect, spelling, _) in CASES {
        let full =
            format!("(set-option :produce-proofs true)\n(set-logic QF_BV)\n{script}(check-sat)\n");
        let mut exec = Executor::new();
        if let Some(dialect) = dialect {
            exec.set_alethe_dialect(dialect);
        }
        let outputs = exec
            .execute_all(&parse(&full).expect("parse SMT-LIB script"))
            .expect("execute SMT-LIB script");
        assert_eq!(
            outputs.first().map(String::as_str),
            Some("unsat"),
            "{label}"
        );
        let (document, surface) = exec
            .try_export_last_proof_alethe_for_problem_scope_with_carcara_surface()
            .unwrap_or_else(|| panic!("{label}: a retained proof"))
            .unwrap_or_else(|error| panic!("{label}: {error:?}"));
        assert_eq!(surface, expected(spelling), "{label}");
        assert_eq!(
            exec.try_export_last_proof_alethe_for_problem_scope()
                .and_then(Result::ok)
                .as_deref(),
            Some(document.as_str()),
            "{label}: the verdict describes the plain export's bytes"
        );
    }
}
