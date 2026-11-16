// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! No `Executor` surface reader says `Supported` for a document pinned
//! Carcara 9a352ee refuses because of what the render printed.
//! (`ay_proof::carcara_proof_surface` is the parse half by design, and its
//! doc says so: what a render prints is known only around that render.)
//!
//! REGRESSION (6835fec57 left it open; reported by the bv-frontier review,
//! 2026-10-06): `Executor::last_unsat_proof_carcara_surface` scanned only the
//! proof's sorts and symbols and never rendered, so it read
//! `CarcaraSurface::Supported` for [`UMULL`], the `zero_extend` twin of
//! `tests/bv_frontier_source.rs`'s SMULL obligation, whose document checks
//! `zero_extend` as `concat` (Clean-only), while the paired export said
//! `CleanDialect { ZeroExtendAsConcat }`; and for [`LET_ROOTED`], whose
//! document eliminates the problem's `let` with `:rule let`. Now it returns
//! the paired export's verdict, and the CLI reads the verdict its streamed
//! export captures around exactly the bytes it streamed
//! (`try_export_last_proof_alethe_for_problem_scope_to_with_carcara_surface`),
//! so no caller can pair a verdict with the report of other bytes.
//!
//! NEGATIVE CONTROLS: [`SMULL`] and the `let`-free twin stay `Supported`, and
//! each is a literal `valid`. The strict gate is unchanged: it reads only what
//! pinned Carcara cannot parse, so `:check-proofs-strict` still publishes the
//! Clean-dialect UMULL refutation (external-codegen promotes on Clean).

use super::{exact_carcara_verdict, parse, require_carcara_or_skip, Executor};
use ay_dpll::api::{AletheDialect, CarcaraSurface, CleanOnlySpelling};
use ntest::timeout;

/// external-codegen's SMULL obligation (`tests/bv_frontier_source.rs`).
const SMULL: &str = "(set-logic QF_BV)
(declare-const x7 (_ BitVec 64))
(declare-const x12 (_ BitVec 64))
(assert (not (= (bvmul (concat (ite (= ((_ extract 31 31) ((_ extract 31 0) x12)) (_ bv1 1)) (_ bv4294967295 32) (_ bv0 32)) ((_ extract 31 0) x12)) (concat (ite (= ((_ extract 31 31) ((_ extract 31 0) x7)) (_ bv1 1)) (_ bv4294967295 32) (_ bv0 32)) ((_ extract 31 0) x7))) (bvmul ((_ sign_extend 32) ((_ extract 31 0) x12)) ((_ sign_extend 32) ((_ extract 31 0) x7))))))
(check-sat)
";

/// Its UMULL twin: spelled-out zero extensions against `zero_extend`.
const UMULL: &str = "(set-logic QF_BV)
(declare-const x7 (_ BitVec 64))
(declare-const x12 (_ BitVec 64))
(assert (not (= (bvmul (concat (_ bv0 32) ((_ extract 31 0) x12)) (concat (_ bv0 32) ((_ extract 31 0) x7))) (bvmul ((_ zero_extend 32) ((_ extract 31 0) x12)) ((_ zero_extend 32) ((_ extract 31 0) x7))))))
(check-sat)
";

/// The smallest problem whose refutation eliminates a `let`
/// (`problem_surface_invocation.rs`).
const LET_ROOTED: &str = "(set-logic QF_UF)
(declare-fun p () Bool)
(declare-fun q () Bool)
(assert (let ((a p)) (and a q)))
(assert (not p))
(check-sat)
";

const ZERO_EXTEND: CarcaraSurface = CarcaraSurface::CleanDialect {
    spelling: CleanOnlySpelling::ZeroExtendAsConcat,
};

fn solved(label: &str, options: &str, problem: &str) -> (Executor, Vec<String>) {
    let commands = parse(&format!("{options}{problem}")).unwrap_or_else(|e| panic!("{label}: {e}"));
    let mut exec = Executor::new();
    let outputs = exec
        .execute_all(&commands)
        .unwrap_or_else(|e| panic!("{label}: {e}"));
    (exec, outputs)
}

/// The problem-scoped document and the verdict every `Executor` reader gives
/// it.
fn readers(label: &str, dialect: AletheDialect, problem: &str) -> (String, CarcaraSurface) {
    let commands = parse(&format!("(set-option :produce-proofs true)\n{problem}"))
        .unwrap_or_else(|e| panic!("{label}: {e}"));
    let mut exec = Executor::new();
    exec.set_alethe_dialect(dialect);
    let outputs = exec
        .execute_all(&commands)
        .unwrap_or_else(|e| panic!("{label}: {e}"));
    assert_eq!(outputs, vec!["unsat"], "{label}");
    let (document, paired) = exec
        .try_export_last_proof_alethe_for_problem_scope_with_carcara_surface()
        .unwrap_or_else(|| panic!("{label}: a retained proof"))
        .unwrap_or_else(|error| panic!("{label}: {error:?}"));
    assert!(
        !document.contains(":rule hole") && !document.contains(":rule trust"),
        "{label}: {document}"
    );
    assert_eq!(
        exec.last_unsat_proof_carcara_surface().as_ref(),
        Some(&paired),
        "{label}: the public reader is the verdict on the document the export renders"
    );
    let mut bytes = Vec::new();
    let streamed = exec
        .try_export_last_proof_alethe_for_problem_scope_to_with_carcara_surface(&mut bytes)
        .unwrap_or_else(|| panic!("{label}: the stream renders"))
        .unwrap_or_else(|error| panic!("{label}: {error}"));
    assert_eq!(
        String::from_utf8(bytes).expect("UTF-8 document"),
        document,
        "{label}: the streamed bytes are the problem-scoped document"
    );
    assert_eq!(
        streamed, paired,
        "{label}: the CLI's streamed verdict, captured around its own render"
    );
    (document, paired)
}

#[test]
#[timeout(300_000)]
fn every_public_surface_reader_says_what_the_render_printed() {
    let carcara = require_carcara_or_skip();
    let let_free = LET_ROOTED.replace("(let ((a p)) (and a q))", "(and p q)");
    for (label, dialect, problem, expected) in [
        ("umull", AletheDialect::Clean, UMULL, ZERO_EXTEND),
        // The pinned dialect has no spelling for a 32-bit symbolic source.
        (
            "umull-pinned",
            AletheDialect::PinnedCarcara,
            UMULL,
            ZERO_EXTEND,
        ),
        (
            "let-rooted",
            AletheDialect::Clean,
            LET_ROOTED,
            CarcaraSurface::WithoutLetExpansion,
        ),
        (
            "smull",
            AletheDialect::Clean,
            SMULL,
            CarcaraSurface::Supported,
        ),
        (
            "let-free",
            AletheDialect::Clean,
            let_free.as_str(),
            CarcaraSurface::Supported,
        ),
    ] {
        let (document, surface) = readers(label, dialect, problem);
        assert_eq!(surface, expected, "{label}");
        let Some(carcara) = carcara.as_ref() else {
            continue;
        };
        // AY's canonical invocation, `carcara check -- PROOF PROBLEM`.
        let (valid, diagnostic) = exact_carcara_verdict(carcara, problem, &document);
        match expected {
            // Measured: `checking failed on step 't1.cbb6.cg' with rule 'cong':
            // term is not an application or operation: '((_ zero_extend 32) ..)'`.
            CarcaraSurface::CleanDialect { .. } => assert!(
                !valid && diagnostic.contains("with rule '") && diagnostic.contains("zero_extend"),
                "{label}: pinned Carcara refuses the Clean-only step: {diagnostic}"
            ),
            _ => assert!(
                valid,
                "{label}: the canonical invocation accepts it: {diagnostic}"
            ),
        }
    }
}

/// The CLI's streamed verdict folds in the report of exactly its own render,
/// and a parse gap outranks it: beside a declaration pinned Carcara's lexer
/// reserves (`step`), the UMULL document still keeps its Clean-only spelling,
/// yet the verdict is `Unsupported`, as the strict gate refuses it. With no
/// proof output requested nothing streams, so no verdict is reported.
#[test]
#[timeout(300_000)]
fn the_streamed_verdict_is_its_own_render_and_a_parse_gap_outranks_it() {
    let produce = "(set-option :produce-proofs true)\n";
    let reserved = UMULL.replace(
        "(declare-const x7 (_ BitVec 64))",
        "(declare-const step (_ BitVec 8))\n(declare-const x7 (_ BitVec 64))",
    );
    let (exec, outputs) = solved("umull+step", produce, &reserved);
    assert_eq!(outputs, vec!["unsat"]);
    let mut bytes = Vec::new();
    let (streamed, report) = ay_proof::capture_alethe_dialect_report(|| {
        exec.try_export_last_proof_alethe_for_problem_scope_to_with_carcara_surface(&mut bytes)
    });
    assert_eq!(
        report.first_clean_only(),
        Some(CleanOnlySpelling::ZeroExtendAsConcat),
        "witness: the render kept the Clean-only spelling"
    );
    let surface = streamed
        .expect("a retained proof")
        .expect("the stream renders");
    assert!(
        matches!(&surface, CarcaraSurface::Unsupported { reason }
            if reason.contains("the problem declares `step`")),
        "{surface:?}"
    );
    assert_eq!(exec.last_unsat_proof_carcara_surface(), Some(surface));

    // `:check-proofs-strict` alone retains the proof for its gate but asks
    // for no document: nothing streams, and no reader reports a verdict.
    let strict_only = "(set-option :check-proofs-strict true)\n";
    let (exec, outputs) = solved("umull-strict-only", strict_only, UMULL);
    assert_eq!(outputs, vec!["unsat"], "{:?}", exec.unknown_detail());
    let mut bytes = Vec::new();
    assert!(exec
        .try_export_last_proof_alethe_for_problem_scope_to_with_carcara_surface(&mut bytes)
        .is_none());
    assert_eq!(bytes, [] as [u8; 0]);
    assert_eq!(exec.last_unsat_proof_carcara_surface(), None);
}

/// The strict gate reads what pinned Carcara cannot PARSE, not the dialect:
/// external-codegen promotes on Clean's Carcara under `--strict-proofs`, so the
/// Clean-dialect UMULL refutation still publishes (a problem pinned Carcara
/// cannot parse is withheld: `authored_source_surface`'s strict tests).
#[test]
#[timeout(300_000)]
fn the_strict_gate_still_admits_a_clean_dialect_refutation() {
    let strict = "(set-option :produce-proofs true)\n(set-option :check-proofs-strict true)\n";
    let (exec, outputs) = solved("umull-strict", strict, UMULL);
    assert_eq!(outputs, vec!["unsat"], "{:?}", exec.unknown_detail());
    assert!(!exec.unsat_proof_references_uncheckable_seq_theory());
    assert_eq!(exec.last_unsat_proof_carcara_surface(), Some(ZERO_EXTEND));
    assert_eq!(
        exec.try_export_last_proof_alethe_for_problem_scope_to_with_carcara_surface(&mut Vec::new())
            .and_then(Result::ok),
        Some(ZERO_EXTEND)
    );
}
