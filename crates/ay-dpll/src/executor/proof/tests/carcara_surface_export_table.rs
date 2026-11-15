// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! D7 precision: the external-recheck surface a consumer reads must be the
//! verdict on the document it hands the external checker.
//!
//! The problem-scoped export renders with `proof_export_term_overrides` (the
//! source-syntax table with the invented datatype-field renderings merged in)
//! or with the sealed finite-enum table. `UnsatProofArtifact` reads its
//! surface on that same table (`carcara_surface_for_last_export`). The strict
//! gates' verdict `strict_gate_carcara_surface` scans the source-syntax table
//! alone, so on an input where the two tables differ, a consumer that paired
//! it with the exported document read a verdict about a different rendering.
//! The consumer read is now
//! `try_export_last_proof_alethe_for_problem_scope_with_carcara_surface`,
//! which returns the document and its verdict from one rendering, and the
//! public `last_unsat_proof_carcara_surface` returns that same verdict.

use super::*;
use ay_proof::CarcaraSurface;

/// A datatype constant whose name needs the AY/Z3 `\|` escape extension,
/// declared beside an unrelated integer refutation. Eager datatype
/// elimination mints its field constants and records their renderings
/// (`(fst |a\|b|)`), which only the export table carries.
const ESCAPED_DATATYPE_ROOT_BESIDE_INT_REFUTATION: &str = r"(set-option :produce-proofs true)
(set-logic ALL)
(declare-datatypes ((P 0)) (((mk (fst Int) (snd Int)))))
(declare-const |a\|b| P)
(declare-const x Int)
(assert (> x 0))
(assert (< x 0))
(check-sat)
";

/// Positive control: plain field names, so every table is inside pinned
/// Carcara's grammar.
const PLAIN_DATATYPE_FIELDS_REFUTATION: &str = r"(set-option :produce-proofs true)
(set-logic ALL)
(declare-datatypes ((P 0)) (((mk (fst Int) (snd Int)))))
(declare-const s P)
(declare-const t P)
(assert (= s t))
(assert (> (fst s) 0))
(assert (< (fst t) 0))
(check-sat)
";

fn solved_unsat(script: &str) -> Executor {
    let commands = parse(script).expect("fixture parses");
    let mut exec = Executor::new();
    assert_eq!(
        exec.execute_all(&commands).expect("fixture solves"),
        vec!["unsat"]
    );
    exec
}

/// The surface verdict a consumer pairs with the problem-scoped document,
/// read from the same call that renders it. The paired document must be the
/// plain export's bytes exactly, or the verdict describes some other text.
fn consumer_surface(exec: &Executor) -> Option<CarcaraSurface> {
    let (document, surface) = exec
        .try_export_last_proof_alethe_for_problem_scope_with_carcara_surface()?
        .expect("the paired export renders whenever the plain one does");
    assert_eq!(
        Some(document),
        exec.try_export_last_proof_alethe_for_problem_scope()
            .and_then(Result::ok),
        "the paired document is the plain problem-scoped export"
    );
    Some(surface)
}

#[test]
fn problem_scope_surface_is_read_on_the_table_the_document_renders_with() {
    let exec = solved_unsat(ESCAPED_DATATYPE_ROOT_BESIDE_INT_REFUTATION);

    // Witness check: the two tables really disagree on this input, so the
    // assertion below is not vacuous.
    let proof = exec.last_proof().expect("retained UNSAT proof");
    let source_table_surface = ay_proof::carcara_proof_surface(
        proof,
        &exec.ctx.terms,
        exec.last_proof_term_overrides.as_ref(),
    );
    assert_eq!(source_table_surface, CarcaraSurface::Supported);
    let document_table_surface = exec
        .carcara_surface_for_last_export(false)
        .expect("the export renders, so its table has a verdict");
    assert!(
        document_table_surface
            .unsupported_reason()
            .is_some_and(|reason| reason.contains(r"(fst |a\|b|)")),
        "the export table carries the escaped field rendering: {document_table_surface}"
    );

    assert_eq!(
        consumer_surface(&exec),
        Some(document_table_surface.clone()),
        "the consumer's surface must be the verdict on the export's own table"
    );
    assert_eq!(
        exec.last_unsat_proof_carcara_surface(),
        Some(document_table_surface),
        "the public reader is the verdict on the export's own table"
    );
}

#[test]
fn problem_scope_surface_positive_control_plain_fields() {
    let exec = solved_unsat(PLAIN_DATATYPE_FIELDS_REFUTATION);
    assert_eq!(
        exec.carcara_surface_for_last_export(false),
        Some(CarcaraSurface::Supported)
    );
    assert_eq!(consumer_surface(&exec), Some(CarcaraSurface::Supported));
}

/// A refutation that never mentions `step`, in a problem that declares it.
/// The proof document is inside pinned Carcara's grammar, but the checker is
/// handed the problem too, and its lexer reserves `step`.
const RESERVED_WORD_DECLARED_BESIDE_INT_REFUTATION: &str = r"(set-option :produce-proofs true)
(set-logic ALL)
(declare-const step Int)
(declare-const x Int)
(assert (> x 0))
(assert (< x 0))
(check-sat)
";

/// The paired export's verdict covers the problem's declarations, like the
/// gate and artifact verdicts: the consumer that claims an external check
/// hands the checker the problem beside the document. Measured before the
/// join: this read `Supported` while `carcara_surface_for_last_export` and
/// the strict gates' verdict both named the declaration.
#[test]
fn problem_scope_surface_covers_the_problems_own_declarations() {
    let exec = solved_unsat(RESERVED_WORD_DECLARED_BESIDE_INT_REFUTATION);

    // Witness check: the proof alone is inside the grammar.
    let proof = exec.last_proof().expect("retained UNSAT proof");
    assert_eq!(
        ay_proof::carcara_proof_surface(
            proof,
            &exec.ctx.terms,
            exec.proof_export_term_overrides().as_ref(),
        ),
        CarcaraSurface::Supported
    );

    let names_step = |surface: &CarcaraSurface| {
        surface
            .unsupported_reason()
            .is_some_and(|reason| reason.contains("the problem declares `step`"))
    };
    let artifact = exec
        .carcara_surface_for_last_export(false)
        .expect("the export renders, so its table has a verdict");
    assert!(names_step(&artifact), "artifact surface: {artifact}");
    let gate = exec
        .strict_gate_carcara_surface()
        .expect("retained UNSAT proof");
    assert!(names_step(&gate), "gate surface: {gate}");
    let consumer = consumer_surface(&exec).expect("the paired export renders");
    assert!(names_step(&consumer), "consumer surface: {consumer}");
    assert_eq!(consumer, artifact);
    assert_eq!(exec.last_unsat_proof_carcara_surface(), Some(consumer));
}

/// The UMULL twin of `tests/bv_frontier_source.rs`'s SMULL obligation: its
/// document checks `zero_extend` as the `concat` Clean's parser normalizes it
/// to, which pinned Carcara 9a352ee refuses.
const UMULL_ZERO_EXTEND_TWIN: &str = "(set-option :produce-proofs true)
(set-logic QF_BV)
(declare-const x7 (_ BitVec 64))
(declare-const x12 (_ BitVec 64))
(assert (not (= (bvmul (concat (_ bv0 32) ((_ extract 31 0) x12)) (concat (_ bv0 32) ((_ extract 31 0) x7))) (bvmul ((_ zero_extend 32) ((_ extract 31 0) x12)) ((_ zero_extend 32) ((_ extract 31 0) x7))))))
(check-sat)
";

/// REGRESSION witness (6835fec57 left it open): the strict gates' parse
/// verdict, which was the public `last_unsat_proof_carcara_surface` until
/// 2026-10-06, reads `Supported` for a document that keeps a Clean-only
/// spelling, and so does `ay_proof::carcara_proof_surface`, the parse half by
/// design. The public readers are the render's verdict.
#[test]
fn the_public_reader_is_the_render_verdict_not_the_parse_only_gate() {
    let exec = solved_unsat(UMULL_ZERO_EXTEND_TWIN);
    assert_eq!(
        exec.strict_gate_carcara_surface(),
        Some(CarcaraSurface::Supported),
        "witness: the parse-only verdict cannot see what the render printed"
    );
    let proof = exec.last_proof().expect("retained UNSAT proof");
    assert_eq!(
        ay_proof::carcara_proof_surface(
            proof,
            &exec.ctx.terms,
            exec.last_proof_term_overrides.as_ref()
        ),
        CarcaraSurface::Supported,
        "the parse half alone, as its doc says"
    );
    let clean = CarcaraSurface::CleanDialect {
        spelling: ay_proof::CleanOnlySpelling::ZeroExtendAsConcat,
    };
    assert_eq!(consumer_surface(&exec), Some(clean.clone()));
    assert_eq!(exec.last_unsat_proof_carcara_surface(), Some(clean.clone()));
    let mut streamed = Vec::new();
    assert_eq!(
        exec.try_export_last_proof_alethe_for_problem_scope_to_with_carcara_surface(&mut streamed)
            .and_then(Result::ok),
        Some(clean),
        "the CLI's streamed verdict"
    );
    assert_eq!(
        Some(String::from_utf8(streamed).expect("UTF-8 document")),
        exec.try_export_last_proof_alethe_for_problem_scope()
            .and_then(Result::ok),
        "the streamed bytes are the problem-scoped document"
    );
    assert!(!exec.unsat_proof_references_uncheckable_seq_theory());
}
