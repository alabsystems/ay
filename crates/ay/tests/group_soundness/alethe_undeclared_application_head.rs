// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! A published Alethe certificate never applies a function symbol, or spells
//! a sort, that pinned Carcara cannot resolve.
//!
//! REGRESSION (wave-37 `a1_unsat_invalid_alethe_default`): on a Bool-valued
//! array over a large index carrier, `store(K(false), i, true) = K(true)` is
//! refuted through the array-default axioms, which reached the proof as
//! `hole` steps over `(default (store ...))`. The default-posture solve wrote
//! that document beside its input and disclosed it
//! `carcara_surface=supported` with "an external checker reports it as
//! *holey*", and pinned Carcara answered `invalid`:
//! `parser error: identifier 'default' is not defined`. The exporter's
//! undeclared-symbol guard walked variables only, never application heads
//! (`ay_proof` `application_heads.rs`); it now declines such a document
//! (`mechanism=undeclarable-proof-symbols`) and keeps the verdict.
//!
//! The same class, each disclosed `supported` and `invalid` before the fix:
//! two datatypes sharing a selector name (the second spelled by its internal
//! identity `__ay_overload_1`), a datatype declared again after a `pop` (its
//! members, nullary ones included, become `__ay_overload_N`), and the members
//! of a parametric instance (`val@Opt!{Int}`, `nil@List!{Int}`). The same
//! holds for SORT identities an inline Skolem `choice` binds: a parametric
//! instance's carrier (`|Opt!{Int}|`) and a sort declared again after a `pop`
//! (`__ay_datatype_sort_0`), both answered `sort '..' is not defined`.
//!
//! Not the class: a symbol of the FloatingPoint theory, such as the
//! `(_ +zero 11 53)` a quantifier instantiation introduces, is declared by
//! the theory, so the document is written and disclosed
//! `carcara_surface=unsupported` (pinned Carcara has no FloatingPoint theory).
//!
//! The checker replays use AY's canonical invocation and are skipped with a
//! note without `carcara` (`CARCARA_PATH`, or `carcara` on `PATH`); the
//! textual assertions on the document run either way.

use std::path::PathBuf;
use std::process::Command;

use crate::alethe_dialect_disclosure::pinned_carcara_verdict;
use crate::spawn::OutputTimeout;
use crate::strict_certificate_publication::{verdict_lines, QUERY_TIMEOUT};

/// The wave-37 reproducer, verbatim.
const A1: &str = "(set-logic QF_AUFBV)
(declare-const a (Array (_ BitVec 32) Bool))
(declare-const c (Array (_ BitVec 32) Bool))
(declare-const d (Array (_ BitVec 32) Bool))
(declare-const p Bool)
(declare-const x (_ BitVec 8))
(assert (select a #x00000042))
(assert (= c (store ((as const (Array (_ BitVec 32) Bool)) false) #x00000001 true)))
(assert (or (not (select a #x00000042)) (= c ((as const (Array (_ BitVec 32) Bool)) true))))
(check-sat)
";

/// The same refutation over the integers: the default axioms take the
/// infinite-carrier rule and leaked the same symbol.
const INT_INDEX: &str = "(set-logic QF_ALIA)
(declare-const p Bool)
(declare-const c (Array Int Bool))
(assert p)
(assert (= c (store ((as const (Array Int Bool)) false) 1 true)))
(assert (or (not p) (= c ((as const (Array Int Bool)) true))))
(check-sat)
";

/// Two datatypes share the selector name `f1`; AY's identity for the second
/// is `__ay_overload_1`, which the problem never declares.
const OVERLOADED_SELECTOR: &str = "(set-logic QF_DT)
(declare-datatypes ((P 0) (Q 0)) (((mkp (f1 Int) (f2 Int))) ((mkq (f2 Int) (f1 Int)))))
(declare-const a Int)
(declare-const b Int)
(assert (not (= (f1 (mkq a b)) b)))
(check-sat)
";

/// A datatype declared inside a popped scope and declared again: the second
/// declaration's members get private identities (`__ay_overload_N`), which a
/// `hole` step printed raw (`carcara_surface=supported`, pinned Carcara
/// `invalid`: `identifier '__ay_overload_1' is not defined`).
const REDECLARED_DATATYPE: &str = "(set-logic QF_DT)
(push 1)
(declare-datatypes ((ScopedPair 0)) (((scoped-mk (scoped-fst Int) (scoped-snd Int)))))
(pop 1)
(declare-datatypes ((ScopedPair 0)) (((scoped-mk (scoped-fst Int) (scoped-snd Int)))))
(declare-const scoped-a Int)
(declare-const scoped-b Int)
(assert (not (= (scoped-fst (scoped-mk scoped-a scoped-b)) scoped-a)))
(check-sat)
";

/// The same over NULLARY constructors, which the problem itself mentions: the
/// exhaustiveness refutation printed `__ay_overload_0`/`__ay_overload_1` raw
/// (`carcara_surface=supported`, pinned Carcara `invalid`).
const REDECLARED_ENUM: &str = "(set-logic QF_DT)
(push 1)
(declare-datatypes ((C 0)) (((r) (g))))
(pop 1)
(declare-datatypes ((C 0)) (((r) (g))))
(declare-const v C)
(assert (not (= v r)))
(assert (not (= v g)))
(check-sat)
";

/// A parametric datatype instance: the frontend's identity for `val` over
/// `(Opt Int)` is `val@Opt!{Int}`. The injectivity lemma printed it raw in a
/// `hole` step (`carcara_surface=supported`, pinned Carcara `invalid`:
/// `identifier 'val@Opt!{Int}' is not defined`).
const PARAMETRIC_SELECTOR: &str = "(set-logic QF_DT)
(declare-datatypes ((Opt 1)) ((par (T) ((none) (some (val T))))))
(declare-const x (Opt Int))
(declare-const a Int)
(declare-const b Int)
(assert (= x (some a)))
(assert (= x (some b)))
(assert (not (= a b)))
(check-sat)
";

/// The same over a nullary member the problem itself mentions
/// (`(as nil (List Int))`): the declaration walk accepted `nil@List!{Int}`,
/// and a derived step printed it raw (pinned Carcara `invalid`).
const PARAMETRIC_NIL: &str = "(set-logic QF_DT)
(declare-datatypes ((List 1)) ((par (T) ((nil) (cons (hd T) (tl (List T)))))))
(declare-const l (List Int))
(declare-const a Int)
(declare-const b Int)
(assert (= l (cons a (as nil (List Int)))))
(assert (= l (cons b (as nil (List Int)))))
(assert (distinct a b))
(check-sat)
";

/// An existential over a parametric instance: the inline Skolem witness is
/// `(choice ((x |Opt!{Int}|)) (not (P x)))`, whose binder spells the
/// instance's internal carrier (`carcara_surface=supported`, pinned Carcara
/// `invalid`: `sort 'Opt!{Int}' is not defined`).
const PARAMETRIC_CHOICE_SORT: &str = "(set-logic UFDTLIA)
(declare-datatypes ((Opt 1)) ((par (T) ((none) (some (val T))))))
(declare-fun P ((Opt Int)) Bool)
(assert (exists ((x (Opt Int))) (not (P x))))
(assert (forall ((x (Opt Int))) (P x)))
(check-sat)
";

/// The same over a sort declared again after a `pop`, whose identity is
/// `__ay_datatype_sort_0` (pinned Carcara `invalid`:
/// `sort '__ay_datatype_sort_0' is not defined`).
const REDECLARED_SORT_CHOICE: &str = "(set-logic UF)
(push 1)
(declare-sort U 0)
(pop 1)
(declare-sort U 0)
(declare-fun P (U) Bool)
(assert (exists ((x U)) (not (P x))))
(assert (forall ((x U)) (P x)))
(check-sat)
";

/// NEGATIVE TWINS for the sort rule: the same sorts, refuted by instantiation
/// with a term the problem spells, ship no internal sort (pinned Carcara
/// `valid`).
const PARAMETRIC_SORT_TWIN: &str = "(set-logic UFDTLIA)
(declare-datatypes ((Opt 1)) ((par (T) ((none) (some (val T))))))
(declare-fun P ((Opt Int)) Bool)
(declare-const y (Opt Int))
(assert (forall ((x (Opt Int))) (P x)))
(assert (not (P y)))
(check-sat)
";

const REDECLARED_SORT_TWIN: &str = "(set-logic UF)
(push 1)
(declare-sort U 0)
(declare-const c U)
(pop 1)
(declare-sort U 0)
(declare-fun P (U) Bool)
(declare-const a U)
(declare-const b U)
(assert (forall ((x U)) (or (P x) (= x b))))
(assert (not (P a)))
(assert (not (= a b)))
(check-sat)
";

/// NEGATIVE TWIN for the parametric rule: every member occurrence is spelled
/// by the problem's own text, so nothing mangled ships and the certificate
/// stays (pinned Carcara `valid`).
const PARAMETRIC_TWIN: &str = "(set-logic QF_DT)
(declare-datatypes ((Opt 1)) ((par (T) ((none) (some (val T))))))
(declare-const x (Opt Int))
(declare-const y (Opt Int))
(declare-const a Int)
(assert (= x (some a)))
(assert (= y (some a)))
(assert (not (= x y)))
(check-sat)
";

/// NEGATIVE TWIN: the same store, refuted by read-over-write alone. Nothing
/// internal reaches this proof, so the guard must not touch its certificate.
const ROW_TWIN: &str = "(set-logic QF_AUFBV)
(declare-const c (Array (_ BitVec 32) Bool))
(assert (= c (store ((as const (Array (_ BitVec 32) Bool)) false) #x00000001 true)))
(assert (not (select c #x00000001)))
(check-sat)
";

/// NOT a free symbol: the FloatingPoint theory declares its own constants.
/// The refutation instantiates the quantifier at `(_ +zero 11 53)`, which the
/// problem never spells. Owner decision D7 has AY write the document its
/// strict checker accepted and disclose `carcara_surface=unsupported` (pinned
/// Carcara has no FloatingPoint theory). MEASURED before the theory rule
/// (`application_heads.rs`): the export declined it as free in `+zero`, and
/// the document was lost.
const FP_THEORY_CONSTANT: &str = "(set-logic FP)
(assert (forall ((q (_ FloatingPoint 11 53))) (fp.isNaN q)))
(check-sat)
";

struct DefaultRun {
    stdout: String,
    stderr: String,
    problem: PathBuf,
    proof: PathBuf,
    _dir: tempfile::TempDir,
}

/// `ay solve query.smt2` in the default posture, which writes
/// `query.smt2.alethe` beside its input on `unsat`.
fn solve_default_posture(script: &str) -> DefaultRun {
    let dir = tempfile::tempdir().expect("tempdir");
    let problem = dir.path().join("query.smt2");
    std::fs::write(&problem, script).expect("write query");
    let output = Command::new(env!("CARGO_BIN_EXE_ay"))
        .arg("solve")
        .arg(&problem)
        .current_dir(dir.path())
        .output_timeout(QUERY_TIMEOUT)
        .expect("ay answers");
    let proof = dir.path().join("query.smt2.alethe");
    DefaultRun {
        stdout: String::from_utf8_lossy(&output.stdout).to_string(),
        stderr: String::from_utf8_lossy(&output.stderr).to_string(),
        problem,
        proof,
        _dir: dir,
    }
}

/// The invariant this file pins, whatever later work does to the derivation:
/// a document AY writes never spells the internal symbol `internal`, and
/// pinned Carcara parses it (`valid` or `holey`, never `invalid`). No
/// document means the export declined, and then no certificate line may
/// claim a surface.
fn assert_no_unparseable_certificate(label: &str, run: &DefaultRun, internal: &str) {
    if !run.proof.exists() {
        assert!(
            !run.stderr.contains("c ay.proof.certificate "),
            "{label}: a certificate line without a certificate:\n{}",
            run.stderr
        );
        assert!(
            run.stderr.contains("c ay.proof.decline "),
            "{label}: an unpublished certificate discloses why:\n{}",
            run.stderr
        );
        return;
    }
    let document = std::fs::read_to_string(&run.proof).expect("read the certificate");
    assert!(
        !document.contains(internal),
        "{label}: the certificate spells AY's internal `{internal}`:\n{document}"
    );
    if let Some((verdict, stderr)) = pinned_carcara_verdict(&run.problem, &run.proof) {
        assert!(
            verdict == "valid" || verdict == "holey",
            "{label}: pinned Carcara answered `{verdict}`:\n{stderr}\n{document}"
        );
    }
}

#[test]
fn an_internal_symbol_never_reaches_a_published_certificate() {
    for (label, script, internal) in [
        ("a1", A1, "default"),
        ("int-index", INT_INDEX, "default"),
        (
            "overloaded-selector",
            OVERLOADED_SELECTOR,
            "__ay_overload_1",
        ),
        ("parametric-selector", PARAMETRIC_SELECTOR, "val@Opt!{Int}"),
        ("parametric-nil", PARAMETRIC_NIL, "nil@List!{Int}"),
        ("redeclared-datatype", REDECLARED_DATATYPE, "__ay_overload_"),
        ("redeclared-enum", REDECLARED_ENUM, "__ay_overload_"),
        (
            "parametric-choice-sort",
            PARAMETRIC_CHOICE_SORT,
            "Opt!{Int}",
        ),
        (
            "redeclared-sort-choice",
            REDECLARED_SORT_CHOICE,
            "__ay_datatype_sort_",
        ),
    ] {
        let run = solve_default_posture(script);
        assert_eq!(
            verdict_lines(&run.stdout),
            ["unsat"],
            "{label}: the verdict is kept\n{}",
            run.stderr
        );
        assert_no_unparseable_certificate(label, &run, internal);
        // Today's derivations need the internal symbol, so the render
        // refuses the artifact and names it.
        if !run.proof.exists() {
            let refusal = run
                .stderr
                .lines()
                .find(|line| line.starts_with("c ay.proof.artifact-refused "))
                .unwrap_or_else(|| panic!("{label}: no refusal line:\n{}", run.stderr));
            assert!(
                refusal.contains("does not declare") && refusal.contains(&format!("({internal}")),
                "{label}: {refusal}"
            );
        }
    }
}

#[test]
fn a_read_over_write_twin_keeps_its_valid_certificate() {
    let run = solve_default_posture(ROW_TWIN);
    assert_eq!(verdict_lines(&run.stdout), ["unsat"], "{}", run.stderr);
    assert!(
        run.proof.exists(),
        "the guard must not decline a certificate with no internal symbol:\n{}",
        run.stderr
    );
    assert_no_unparseable_certificate("row-twin", &run, "default");
    if let Some((verdict, stderr)) = pinned_carcara_verdict(&run.problem, &run.proof) {
        assert_eq!(verdict, "valid", "{stderr}");
    }
}

#[test]
fn a_parametric_twin_spelled_by_the_problem_keeps_its_certificate() {
    let run = solve_default_posture(PARAMETRIC_TWIN);
    assert_eq!(verdict_lines(&run.stdout), ["unsat"], "{}", run.stderr);
    assert!(
        run.proof.exists(),
        "the guard must not decline a certificate that ships no mangled identity:\n{}",
        run.stderr
    );
    assert_no_unparseable_certificate("parametric-twin", &run, "@Opt!{");
    if let Some((verdict, stderr)) = pinned_carcara_verdict(&run.problem, &run.proof) {
        assert_eq!(verdict, "valid", "{stderr}");
    }
}

#[test]
fn sort_twins_spelled_by_the_problem_keep_their_certificates() {
    for (label, script, internal) in [
        ("parametric-sort-twin", PARAMETRIC_SORT_TWIN, "!{"),
        ("redeclared-sort-twin", REDECLARED_SORT_TWIN, "__ay_"),
    ] {
        let run = solve_default_posture(script);
        assert_eq!(
            verdict_lines(&run.stdout),
            ["unsat"],
            "{label}\n{}",
            run.stderr
        );
        assert!(
            run.proof.exists(),
            "{label}: the guard must not decline a certificate that ships no internal sort:\n{}",
            run.stderr
        );
        assert_no_unparseable_certificate(label, &run, internal);
        if let Some((verdict, stderr)) = pinned_carcara_verdict(&run.problem, &run.proof) {
            assert_eq!(verdict, "valid", "{label}: {stderr}");
        }
    }
}

#[test]
fn a_floating_point_theory_constant_keeps_its_disclosed_document() {
    let run = solve_default_posture(FP_THEORY_CONSTANT);
    assert_eq!(verdict_lines(&run.stdout), ["unsat"], "{}", run.stderr);
    assert!(
        run.proof.exists(),
        "the theory's own constant is not free in the document:\n{}",
        run.stderr
    );
    let document = std::fs::read_to_string(&run.proof).expect("read the certificate");
    assert!(document.contains("(_ +zero 11 53)"), "{document}");
    let certificate = run
        .stderr
        .lines()
        .find(|line| line.starts_with("c ay.proof.certificate "))
        .unwrap_or_else(|| panic!("no certificate line:\n{}", run.stderr));
    assert!(
        certificate.contains("carcara_surface=unsupported"),
        "{certificate}"
    );
}
