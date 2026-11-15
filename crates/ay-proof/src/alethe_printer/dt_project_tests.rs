// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The `dt_project` lowering of a datatype selector over a constructor.
//!
//! REGRESSION (measured 2026-10-02 at 11b79efe7): `(assert (not (= (fst (mk a
//! b)) a)))` published `unsat` with `(step t1 (cl (= (fst (mk a b)) a)) :rule
//! hole)`, `unproved_steps=1`, in both dialects, though Clean's vendored
//! Carcara (4dc90e8ea) checks the step as `dt_project`. Now the Clean dialect
//! prints the rule (and `symm` for the reversed equality) and reports the
//! Clean-only spelling; the pinned dialect, and every clause or printed text
//! outside the axiom, keeps the hole byte for byte.
//!
//! The document round trips run Trust's checker when `CLEAN_BIN` names it
//! (`clean cert verify-external`: a literal `PASSED`, and a refusal of the
//! wrong-field twin) and pinned Carcara when `CARCARA_PATH` names it or
//! `carcara` is on `PATH` (refused exactly at `dt_project`: `unknown rule`).

use super::super::dialect::{
    capture_alethe_dialect_report, with_alethe_dialect, AletheDialect, AletheDialectReport,
    CleanOnlySpelling,
};
use super::super::AlethePrinter;
use super::{printed_dt_project, PrintedProjection};
use crate::checker::ProjectionOrientation;
use ay_core::{Proof, ProofId, ProofStep, Sort, Symbol, TermId, TermStore, TheoryLemmaKind};
use std::path::PathBuf;
use std::process::Command;

const PROJECT: Option<CleanOnlySpelling> = Some(CleanOnlySpelling::DatatypeSelectorProject);

/// `Pair = (mk (fst Int) (snd Int)) | (other (oth Int))` and the free `a`,
/// `b`, with the constructor-field registry the frontend installs.
struct Pair {
    terms: TermStore,
    a: TermId,
    b: TermId,
    mk: TermId,
}

impl Pair {
    fn new() -> Self {
        let mut terms = TermStore::new();
        terms.register_constructor_fields("mk", vec!["fst".to_string(), "snd".to_string()]);
        terms.register_constructor_fields("other", vec!["oth".to_string()]);
        let a = terms.mk_var("a", Sort::Int);
        let b = terms.mk_var("b", Sort::Int);
        let mk = terms.mk_app(
            Symbol::named("mk"),
            [a, b],
            Sort::Uninterpreted("Pair".to_string()),
        );
        Self { terms, a, b, mk }
    }

    /// `(selector of)`, raw: the folding builders would collapse it.
    fn select(&mut self, selector: &str, of: TermId) -> TermId {
        self.terms.mk_app(Symbol::named(selector), [of], Sort::Int)
    }

    fn equal(&mut self, left: TermId, right: TermId) -> TermId {
        self.terms
            .mk_app(Symbol::named("="), [left, right], Sort::Bool)
    }

    /// `(= (selector (mk a b)) value)`, or reversed.
    fn projection(&mut self, selector: &str, value: TermId, selector_first: bool) -> TermId {
        let selection = self.select(selector, self.mk);
        if selector_first {
            self.equal(selection, value)
        } else {
            self.equal(value, selection)
        }
    }
}

fn lemma(clause: Vec<TermId>) -> ProofStep {
    ProofStep::TheoryLemma {
        theory: "datatype".to_string(),
        clause,
        farkas: None,
        kind: TheoryLemmaKind::DatatypeSelectorProject,
        lia: None,
    }
}

/// The step `t1` for `clause`, rendered in `dialect`, with its report.
fn render(
    terms: &TermStore,
    clause: Vec<TermId>,
    dialect: AletheDialect,
) -> (String, AletheDialectReport) {
    capture_alethe_dialect_report(|| {
        with_alethe_dialect(dialect, || {
            AlethePrinter::new(terms)
                .format_step(&lemma(clause), ProofId(1))
                .expect("a selector-projection lemma renders")
        })
    })
}

#[test]
fn the_clean_dialect_prints_dt_project_and_discloses_it() {
    let mut pair = Pair::new();
    for (selector, value, spelled) in [("fst", pair.a, "a"), ("snd", pair.b, "b")] {
        let literal = pair.projection(selector, value, true);
        let (text, report) = render(&pair.terms, vec![literal], AletheDialect::Clean);
        assert_eq!(
            text,
            format!("(step t1 (cl (= ({selector} (mk a b)) {spelled})) :rule dt_project)")
        );
        assert_eq!(report.first_clean_only(), PROJECT, "{text}");
    }
}

#[test]
fn the_pinned_dialect_keeps_the_hole_byte_for_byte() {
    let mut pair = Pair::new();
    for selector_first in [true, false] {
        let literal = pair.projection("fst", pair.a, selector_first);
        let (text, report) = render(&pair.terms, vec![literal], AletheDialect::PinnedCarcara);
        let clause = if selector_first {
            "(= (fst (mk a b)) a)"
        } else {
            "(= a (fst (mk a b)))"
        };
        assert_eq!(text, format!("(step t1 (cl {clause}) :rule hole)"));
        assert!(report.is_pinned_spelling(), "{text}");
    }
}

/// Clean's rule concludes only the selector-first orientation; the reversed
/// equality is the rule's conclusion under a sub-step id, then `symm`.
#[test]
fn the_reversed_orientation_goes_through_symm() {
    let mut pair = Pair::new();
    let literal = pair.projection("snd", pair.b, false);
    let (text, report) = render(&pair.terms, vec![literal], AletheDialect::Clean);
    assert_eq!(
        text,
        "(step t1.dt (cl (= (snd (mk a b)) b)) :rule dt_project)\n\
         (step t1 (cl (= b (snd (mk a b)))) :rule symm :premises (t1.dt))"
    );
    assert_eq!(report.first_clean_only(), PROJECT);
}

/// The IR judgement is the strict checker's own matcher: anything it refuses,
/// and the `(or ..)`-packed unit the checker unwraps but no `dt_project`
/// conclusion spells, keeps the hole and reports nothing.
#[test]
fn a_clause_outside_the_axiom_keeps_the_hole() {
    let mut pair = Pair::new();
    let wrong_field = pair.projection("fst", pair.b, true);
    let other_constructor = pair.projection("oth", pair.a, true);
    let free = pair
        .terms
        .mk_var("x", Sort::Uninterpreted("Pair".to_string()));
    let over_a_variable = {
        let selection = pair.select("fst", free);
        pair.equal(selection, pair.a)
    };
    let unregistered = {
        let built = pair.terms.mk_app(
            Symbol::named("free"),
            [pair.a, pair.b],
            Sort::Uninterpreted("Pair".to_string()),
        );
        let selection = pair.select("fst", built);
        pair.equal(selection, pair.a)
    };
    let valid = pair.projection("fst", pair.a, true);
    let packed = pair.terms.mk_app(Symbol::named("or"), [valid], Sort::Bool);
    let cases: [(&str, Vec<TermId>); 6] = [
        ("wrong field", vec![wrong_field]),
        ("another constructor's selector", vec![other_constructor]),
        ("a selector over a variable", vec![over_a_variable]),
        ("an unregistered constructor", vec![unregistered]),
        ("two literals", vec![valid, wrong_field]),
        ("an or-packed unit", vec![packed]),
    ];
    for (label, clause) in cases {
        let (text, report) = render(&pair.terms, clause, AletheDialect::Clean);
        assert!(text.ends_with(":rule hole)"), "{label}: {text}");
        assert!(!text.contains("dt_project"), "{label}: {text}");
        assert!(report.is_pinned_spelling(), "{label}: {text}");
    }
}

/// Clean refuses every parametric datatype. The frontend names an instance's
/// carrier `D!{T..}` and its members `member@D!{T..}`.
#[test]
fn a_parametric_instance_keeps_the_hole() {
    for (carrier, constructor, selector) in [
        ("Opt!{Int}", "some@Opt!{Int}", "val@Opt!{Int}"),
        ("Opt", "some@Opt", "val@Opt"),
    ] {
        let mut terms = TermStore::new();
        terms.register_constructor_fields(constructor, vec![selector.to_string()]);
        let a = terms.mk_var("a", Sort::Int);
        let built = terms.mk_app(
            Symbol::named(constructor),
            [a],
            Sort::Uninterpreted(carrier.to_string()),
        );
        let selection = terms.mk_app(Symbol::named(selector), [built], Sort::Int);
        let literal = terms.mk_app(Symbol::named("="), [selection, a], Sort::Bool);
        let (text, report) = render(&terms, vec![literal], AletheDialect::Clean);
        assert!(text.ends_with(":rule hole)"), "{carrier}: {text}");
        assert!(report.is_pinned_spelling(), "{carrier}: {text}");
    }
}

/// The printed-text judgement, alone: the IR fixed field 0 of a two-field
/// constructor, selector first.
#[test]
fn the_printed_text_must_be_exactly_the_projection() {
    let projection = PrintedProjection {
        orientation: ProjectionOrientation::SelectorFirst,
        field: 0,
        arity: 2,
    };
    let unbound = |_: &str| false;
    let print = |clause: &str| printed_dt_project(ProofId(4), clause, projection, &unbound);
    assert_eq!(
        print("(cl (= (fst (mk a b)) a))").as_deref(),
        Some("(step t4 (cl (= (fst (mk a b)) a)) :rule dt_project)")
    );
    assert_eq!(
        print("(cl (= (|f s| (|m k| (+ a 1) b)) (+ a 1)))").as_deref(),
        Some("(step t4 (cl (= (|f s| (|m k| (+ a 1) b)) (+ a 1))) :rule dt_project)"),
        "quoted symbols are symbols, and a compound argument is compared whole"
    );
    for (label, clause) in [
        (
            "the value spelled differently",
            "(cl (= (fst (mk a b)) |a|))",
        ),
        ("the other field's value", "(cl (= (fst (mk a b)) b))"),
        (
            "a qualified constructor",
            "(cl (= (fst ((as mk Pair) a b)) a))",
        ),
        ("an indexed selector", "(cl (= ((_ fst 0) (mk a b)) a))"),
        ("another arity", "(cl (= (fst (mk a b c)) a))"),
        ("fewer arguments", "(cl (= (fst (mk a)) a))"),
        ("a nullary constructor", "(cl (= (fst mk) a))"),
        ("two literals", "(cl (= (fst (mk a b)) a) p)"),
        ("not an equality", "(cl (distinct (fst (mk a b)) a))"),
        ("the other orientation", "(cl (= a (fst (mk a b))))"),
        ("a numeral head", "(cl (= (0 (mk a b)) a))"),
        ("not a clause", "(= (fst (mk a b)) a)"),
    ] {
        assert_eq!(print(clause), None, "{label}: {clause}");
    }
    for bound_name in ["fst", "mk"] {
        let bound = |name: &str| name == bound_name;
        assert_eq!(
            printed_dt_project(ProofId(4), "(cl (= (fst (mk a b)) a))", projection, &bound),
            None,
            "an anchor binds {bound_name}"
        );
    }
}

/// `prepare_proof` records every IR anchor binder's printed name.
#[test]
fn prepare_proof_records_the_anchor_binders() {
    let pair = Pair::new();
    let mut proof = Proof::default();
    proof.steps.push(ProofStep::Anchor {
        end_step: ProofId(1),
        variables: vec![
            ("fst".to_string(), Sort::Int),
            ("a b".to_string(), Sort::Int),
        ],
    });
    let printer = AlethePrinter::new(&pair.terms);
    let _ = printer.prepare_proof(&proof);
    let binders = printer.anchor_binder_names.borrow();
    assert!(
        binders.contains("fst") && binders.contains("|a b|"),
        "{binders:?}"
    );
}

/// A whole refutation of `(not literal)`: assume, the lemma, resolution.
fn refutation(pair: &mut Pair, literal: TermId) -> (Proof, TermId) {
    let negated = pair.terms.mk_not_raw(literal);
    let mut proof = Proof::default();
    let assumed = proof.add_assume(negated, None);
    let projected = proof.add_theory_lemma_with_kind(
        "datatype",
        vec![literal],
        TheoryLemmaKind::DatatypeSelectorProject,
    );
    proof.add_resolution(vec![], literal, assumed, projected);
    (proof, negated)
}

fn export(pair: &Pair, proof: &Proof, negated: TermId, dialect: AletheDialect) -> String {
    with_alethe_dialect(dialect, || {
        crate::try_export_alethe_with_problem_scope_overrides_and_budget(
            proof,
            &pair.terms,
            &[negated],
            None,
            None,
        )
        .expect("the refutation exports")
    })
}

fn problem(pair: &Pair, negated: TermId) -> String {
    format!(
        "(set-logic QF_DT)\n\
         (declare-datatypes ((Pair 0)) (((mk (fst Int) (snd Int)) (other (oth Int)))))\n\
         (declare-const a Int)\n(declare-const b Int)\n(assert {})\n(check-sat)\n",
        AlethePrinter::new(&pair.terms).format_term(negated)
    )
}

fn clean_bin() -> Option<PathBuf> {
    let path = PathBuf::from(std::env::var_os("CLEAN_BIN")?);
    assert!(
        path.is_file(),
        "CLEAN_BIN names no file: {}",
        path.display()
    );
    Some(path)
}

/// `clean cert verify-external`: `true` only for a literal `PASSED`.
fn clean_passes(clean: &PathBuf, case: &str, problem: &str, proof: &str) -> (bool, String) {
    let dir = std::env::temp_dir().join(format!("ay-dt-project-{}-{case}", std::process::id()));
    std::fs::create_dir_all(&dir).expect("certificate directory");
    let path = dir.join("certificate.json");
    let certificate = serde_json::json!({
        "type": "alethe_certificate",
        "version": "1.0",
        "problem": problem,
        "proof": proof,
    });
    std::fs::write(&path, certificate.to_string()).expect("write the certificate");
    let output = Command::new(clean)
        .args(["cert", "verify-external"])
        .arg(&path)
        .output()
        .expect("run clean cert verify-external");
    let _ = std::fs::remove_dir_all(&dir);
    let stdout = String::from_utf8_lossy(&output.stdout).to_string();
    let diagnostic = format!("{stdout}{}", String::from_utf8_lossy(&output.stderr));
    (
        output.status.success() && stdout.contains("External certificate verification: PASSED"),
        diagnostic,
    )
}

/// Pinned Carcara, from `CARCARA_PATH` or `PATH`, or `None`.
fn pinned_carcara() -> Option<PathBuf> {
    if let Some(path) = std::env::var_os("CARCARA_PATH") {
        return Some(PathBuf::from(path));
    }
    let probe = Command::new("carcara").arg("--version").output();
    probe
        .is_ok_and(|probe| probe.status.success())
        .then(|| PathBuf::from("carcara"))
}

/// Pinned Carcara's verdict line and its diagnostics.
fn pinned_verdict(carcara: &PathBuf, case: &str, problem: &str, proof: &str) -> (String, String) {
    if let Err(misjudged) = ay_core::pinned_carcara::pinned_carcara_can_judge(problem, proof) {
        panic!("{case}: {misjudged}\n{proof}");
    }
    let dir = std::env::temp_dir().join(format!("ay-dt-project-pin-{}-{case}", std::process::id()));
    std::fs::create_dir_all(&dir).expect("replay directory");
    std::fs::write(dir.join("p.smt2"), problem).expect("write the problem");
    std::fs::write(dir.join("p.alethe"), proof).expect("write the proof");
    let output = Command::new(carcara)
        .args(["check", "--no-color", "--"])
        .arg(dir.join("p.alethe"))
        .arg(dir.join("p.smt2"))
        .output()
        .expect("run carcara");
    let _ = std::fs::remove_dir_all(&dir);
    let stdout = String::from_utf8_lossy(&output.stdout).to_string();
    let verdict = stdout.lines().last().unwrap_or("").trim().to_string();
    (
        verdict,
        format!("{stdout}{}", String::from_utf8_lossy(&output.stderr)),
    )
}

/// End to end on the printer: both orientations, both dialects, AY's own
/// document check in the matching vocabulary, and the two checkers.
#[test]
fn the_refutation_round_trips_in_each_dialect() {
    let clean = clean_bin();
    let carcara = pinned_carcara();
    if clean.is_none() && carcara.is_none() {
        eprintln!("dt_project: no CLEAN_BIN and no carcara; external replays skipped");
    }
    for selector_first in [true, false] {
        let case = if selector_first {
            "forward"
        } else {
            "reversed"
        };
        let mut pair = Pair::new();
        let literal = pair.projection("fst", pair.a, selector_first);
        let (proof, negated) = refutation(&mut pair, literal);
        let problem = problem(&pair, negated);
        let scope = crate::ProblemScope::from_smtlib_source(&problem);

        let document = export(&pair, &proof, negated, AletheDialect::Clean);
        assert!(
            document.contains(":rule dt_project)"),
            "{case}:\n{document}"
        );
        assert!(!document.contains(":rule hole"), "{case}:\n{document}");
        assert_eq!(
            document.contains(":rule symm :premises (t1.dt))"),
            !selector_first,
            "{case}:\n{document}"
        );
        crate::check_alethe_document(&document, &scope)
            .unwrap_or_else(|defect| panic!("{case}: {defect}\n{document}"));
        match crate::check_alethe_document_in_dialect(
            &document,
            &scope,
            AletheDialect::PinnedCarcara,
        ) {
            Err(crate::AletheDefect::UnknownRule { rule, .. }) => assert_eq!(rule, "dt_project"),
            other => panic!("{case}: the pinned vocabulary must refuse dt_project: {other:?}"),
        }

        let pinned = export(&pair, &proof, negated, AletheDialect::PinnedCarcara);
        assert_eq!(
            pinned.matches(":rule hole)").count(),
            1,
            "{case}:\n{pinned}"
        );
        assert!(!pinned.contains("dt_project"), "{case}:\n{pinned}");
        crate::check_alethe_document_in_dialect(&pinned, &scope, AletheDialect::PinnedCarcara)
            .unwrap_or_else(|defect| panic!("{case}: {defect}\n{pinned}"));

        if let Some(clean) = clean.as_ref() {
            let (passed, diagnostic) = clean_passes(clean, case, &problem, &document);
            assert!(passed, "{case}: Clean refused:\n{diagnostic}\n{document}");
            // The wrong-field twin: a SATISFIABLE problem whose only false
            // step is the projection onto `b`.
            let twin_problem = problem.replace("(fst (mk a b)) a", "(fst (mk a b)) b");
            let twin_problem = twin_problem.replace("a (fst (mk a b))", "b (fst (mk a b))");
            let twin = document
                .replace("(fst (mk a b)) a", "(fst (mk a b)) b")
                .replace("a (fst (mk a b))", "b (fst (mk a b))");
            assert_ne!(twin, document);
            let (passed, diagnostic) =
                clean_passes(clean, &format!("{case}-twin"), &twin_problem, &twin);
            assert!(
                !passed,
                "{case}: Clean accepted the wrong field:\n{diagnostic}\n{twin}"
            );
            assert!(diagnostic.contains("dt_project"), "{case}: {diagnostic}");
        }
        if let Some(carcara) = carcara.as_ref() {
            let (verdict, diagnostic) = pinned_verdict(carcara, case, &problem, &document);
            assert_ne!(verdict, "valid", "{case}: {diagnostic}");
            assert!(
                diagnostic.contains("with rule 'dt_project': unknown rule"),
                "{case}: refused, but not at dt_project: {diagnostic}"
            );
            let (verdict, diagnostic) = pinned_verdict(carcara, case, &problem, &pinned);
            assert_eq!(verdict, "holey", "{case}: {diagnostic}\n{pinned}");
        }
    }
}
