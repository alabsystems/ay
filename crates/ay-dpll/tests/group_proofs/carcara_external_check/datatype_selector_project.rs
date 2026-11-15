// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! A datatype selector over a constructor, `(= (S (C a_0 .. a_n)) a_i)`, end
//! to end in both dialects.
//!
//! REGRESSION (measured 2026-10-02 at 11b79efe7): AY's strict checker
//! validates the step (`DatatypeSelectorProject`), but pinned Carcara 9a352ee
//! has no datatype rule, so every dialect printed it as `:rule hole`, the
//! certificate said `unproved_steps=1`, and a Carcara-claiming consumer
//! (Trust's four datatype rows) refused the UNSAT. Clean's vendored Carcara
//! checks it as `dt_project` (Clean 4dc90e8ea, DOWNSTREAM row C2). Now the
//! Clean dialect (the default) prints `dt_project` (then `symm` for a value
//! written first) and discloses `CarcaraSurface::CleanDialect {
//! DatatypeSelectorProject }`; AY's own document check accepts it in the
//! Clean vocabulary and refuses it in the pinned one; the pinned dialect keeps
//! the hole and `Supported`.
//!
//! With `CLEAN_BIN` naming Trust's checker each Clean document must be a
//! literal `PASSED`, and its wrong-field twin (a SATISFIABLE problem whose one
//! false step is the projection) refused at `dt_project`. With pinned Carcara
//! (`CARCARA_PATH`, `~/.cargo/bin`, `PATH`) each Clean document must be
//! refused exactly at `dt_project` (`unknown rule`), and each pinned document
//! is `holey`.

use super::{exact_carcara_verdict, find_carcara, parse, Executor};
use ay_dpll::api::{
    AletheDialect, CarcaraSurface, CleanOnlySpelling, DatatypeConstructor, DatatypeField,
    DatatypeSort, Logic, Solver, Sort, StrictProofVerdict,
};
use ntest::timeout;
use std::path::{Path, PathBuf};

const PROJECT: CarcaraSurface = CarcaraSurface::CleanDialect {
    spelling: CleanOnlySpelling::DatatypeSelectorProject,
};

const PAIR: &str = "(declare-datatypes ((Pair 0)) (((mk (fst Int) (snd Int)))))\n\
                    (declare-const a Int)\n(declare-const b Int)\n";
const TWO_CONSTRUCTORS: &str =
    "(declare-datatypes ((P 0)) (((mk (fst Int) (snd Int)) (other (oth Int)))))\n\
     (declare-const a Int)\n(declare-const b Int)\n";

/// One text-lane row: the problem asserts `(not equality)`.
struct Row {
    label: &'static str,
    declarations: &'static str,
    /// The authored equality, which the `assume` must repeat verbatim.
    equality: &'static str,
    /// The same projection selector first: `dt_project`'s conclusion.
    projection: &'static str,
    /// `projection` onto the other field's value.
    wrong: &'static str,
}

const ROWS: [Row; 4] = [
    Row {
        label: "first-field",
        declarations: PAIR,
        equality: "(= (fst (mk a b)) a)",
        projection: "(= (fst (mk a b)) a)",
        wrong: "(= (fst (mk a b)) b)",
    },
    Row {
        label: "second-field",
        declarations: PAIR,
        equality: "(= (snd (mk a b)) b)",
        projection: "(= (snd (mk a b)) b)",
        wrong: "(= (snd (mk a b)) a)",
    },
    Row {
        label: "reversed",
        declarations: PAIR,
        equality: "(= a (fst (mk a b)))",
        projection: "(= (fst (mk a b)) a)",
        wrong: "(= (fst (mk a b)) b)",
    },
    Row {
        label: "two-constructors",
        declarations: TWO_CONSTRUCTORS,
        equality: "(= (snd (mk a b)) b)",
        projection: "(= (snd (mk a b)) b)",
        wrong: "(= (snd (mk a b)) a)",
    },
];

impl Row {
    fn reversed(&self) -> bool {
        self.equality != self.projection
    }

    fn problem(&self) -> String {
        format!(
            "(set-logic QF_DT)\n{}(assert (not {}))\n(check-sat)\n",
            self.declarations, self.equality
        )
    }

    /// `text` with the projection onto the wrong field, in both orientations.
    fn wrong_field(&self, text: &str) -> String {
        let reversed_wrong = {
            // `(= (S (C ..)) v)` -> `(= v (S (C ..)))`
            let inner = &self.wrong["(= ".len()..self.wrong.len() - 1];
            let (selection, value) = inner.rsplit_once(' ').expect("a binary equality");
            format!("(= {value} {selection})")
        };
        let twin = text.replace(self.projection, self.wrong);
        if self.reversed() {
            twin.replace(self.equality, &reversed_wrong)
        } else {
            twin
        }
    }
}

/// The problem-scoped document and its surface, in `dialect`.
fn export(row: &Row, dialect: AletheDialect) -> (String, CarcaraSurface) {
    let script = format!("(set-option :produce-proofs true)\n{}", row.problem());
    let mut exec = Executor::new();
    exec.set_alethe_dialect(dialect);
    let outputs = exec
        .execute_all(&parse(&script).expect("parse SMT-LIB script"))
        .expect("execute SMT-LIB script");
    assert_eq!(
        outputs.first().map(String::as_str),
        Some("unsat"),
        "{}: {outputs:?}",
        row.label
    );
    exec.try_export_last_proof_alethe_for_problem_scope_with_carcara_surface()
        .unwrap_or_else(|| panic!("{}: a retained proof", row.label))
        .unwrap_or_else(|error| panic!("{}: {error:?}", row.label))
}

fn clean_bin() -> Option<PathBuf> {
    let path = PathBuf::from(std::env::var_os("CLEAN_BIN")?);
    assert!(
        path.is_file(),
        "CLEAN_BIN is set but does not name a file: {}",
        path.display()
    );
    Some(path)
}

/// Trust's checker on one certificate: `true` only for a literal `PASSED`
/// (it exits 1 on a holey one).
fn clean_verdict(clean: &Path, label: &str, problem: &str, proof: &str) -> (bool, String) {
    let directory = tempfile::tempdir().expect("temporary certificate directory");
    let path = directory.path().join(format!("{label}.json"));
    let certificate = serde_json::json!({
        "type": "alethe_certificate",
        "version": "1.0",
        "problem": problem,
        "proof": proof,
    });
    std::fs::write(&path, certificate.to_string()).expect("write certificate");
    let output = std::process::Command::new(clean)
        .args(["cert", "verify-external"])
        .arg(&path)
        .output()
        .expect("run clean cert verify-external");
    let stdout = String::from_utf8_lossy(&output.stdout).to_string();
    let stderr = String::from_utf8_lossy(&output.stderr).to_string();
    (
        output.status.success() && stdout.contains("External certificate verification: PASSED"),
        format!(
            "status={:?}\nstdout={stdout}\nstderr={stderr}",
            output.status.code()
        ),
    )
}

/// The Clean document is checked by Clean and refused by pinned Carcara at
/// `dt_project`; `twin` is its wrong-field twin over `twin_problem`.
fn replay_clean_document(
    label: &str,
    problem: &str,
    document: &str,
    twin_problem: &str,
    twin: &str,
) {
    if let Some(clean) = clean_bin() {
        let (passed, diagnostic) = clean_verdict(&clean, label, problem, document);
        assert!(passed, "{label}: Clean refused:\n{diagnostic}\n{document}");
        assert_ne!(twin, document, "{label}: the twin must differ");
        let (passed, diagnostic) =
            clean_verdict(&clean, &format!("{label}-twin"), twin_problem, twin);
        assert!(
            !passed && diagnostic.contains("with rule 'dt_project'"),
            "{label}: Clean must refuse the wrong field at dt_project:\n{diagnostic}\n{twin}"
        );
    }
    if let Some(carcara) = find_carcara() {
        let (valid, diagnostic) = exact_carcara_verdict(&carcara, problem, document);
        assert!(
            !valid && diagnostic.contains("with rule 'dt_project': unknown rule"),
            "{label}: pinned Carcara must refuse exactly at dt_project: {diagnostic}"
        );
    }
}

#[test]
#[timeout(120_000)]
fn the_clean_dialect_certifies_the_projection_and_the_pinned_dialect_keeps_the_hole() {
    if clean_bin().is_none() && find_carcara().is_none() {
        eprintln!(
            "datatype_selector_project: no CLEAN_BIN and no Carcara; the documents are \
             checked in-process only"
        );
    }
    for row in &ROWS {
        let label = row.label;
        let problem = row.problem();
        let scope = ay_proof::ProblemScope::from_smtlib_source(&problem);

        let (document, surface) = export(row, AletheDialect::Clean);
        assert_eq!(surface, PROJECT, "{label}:\n{document}");
        assert!(
            document.contains(&format!("(assume t0 (not {}))", row.equality)),
            "{label}: the assume is the authored assertion:\n{document}"
        );
        assert!(
            document.contains(&format!("(cl {}) :rule dt_project)", row.projection)),
            "{label}:\n{document}"
        );
        assert!(!document.contains(":rule hole"), "{label}:\n{document}");
        assert_eq!(
            document.contains(":rule symm :premises (t1.dt))"),
            row.reversed(),
            "{label}: symm exactly for the reversed equality:\n{document}"
        );
        ay_proof::check_alethe_document(&document, &scope)
            .unwrap_or_else(|defect| panic!("{label}: {defect}\n{document}"));
        match ay_proof::check_alethe_document_in_dialect(
            &document,
            &scope,
            AletheDialect::PinnedCarcara,
        ) {
            Err(ay_proof::AletheDefect::UnknownRule { rule, .. }) => {
                assert_eq!(rule, "dt_project", "{label}");
            }
            other => panic!("{label}: the pinned vocabulary refuses dt_project: {other:?}"),
        }
        replay_clean_document(
            label,
            &problem,
            &document,
            &row.wrong_field(&problem),
            &row.wrong_field(&document),
        );

        let (pinned, pinned_surface) = export(row, AletheDialect::PinnedCarcara);
        assert_eq!(
            pinned_surface,
            CarcaraSurface::Supported,
            "{label}:\n{pinned}"
        );
        assert_eq!(
            pinned.matches(":rule hole)").count(),
            1,
            "{label}: the pinned dialect keeps its one hole:\n{pinned}"
        );
        assert!(
            pinned.contains(&format!("(cl {}) :rule hole)", row.equality)),
            "{label}:\n{pinned}"
        );
        assert!(!pinned.contains("dt_project"), "{label}:\n{pinned}");
        ay_proof::check_alethe_document_in_dialect(&pinned, &scope, AletheDialect::PinnedCarcara)
            .unwrap_or_else(|defect| panic!("{label}: {defect}\n{pinned}"));
        if let Some(carcara) = find_carcara() {
            let (valid, diagnostic) = exact_carcara_verdict(&carcara, &problem, &pinned);
            assert!(
                !valid && diagnostic.contains("holey"),
                "{label}: the pinned document is holey: {diagnostic}"
            );
        }
    }
}

/// Two datatypes that share the field name `f1`. The frontend gives the
/// second `f1` the identity `__ay_overload_1`, and the printer spells that
/// identity, which the problem never declares (the `assume` beside it too, a
/// printer gap that predates `dt_project`). Measured on the dt_project
/// commit, the Clean dialect printed `(step t1 (cl (= (__ay_overload_1 (mkq
/// a b)) b)) :rule dt_project)` and disclosed `clean-dialect`; the lowering
/// now declines an AY-internal name, so both dialects keep the hole.
///
/// The holey document that remained was still unparseable: pinned Carcara
/// answered `invalid` (`identifier '__ay_overload_1' is not defined`) while
/// the CLI disclosed it `carcara_surface=supported`. The exporter now
/// declines a step that applies an internal identity (`ay_proof`
/// `application_heads.rs`), so neither dialect publishes it; a document that
/// does render must spell no internal identity and keep the hole.
#[test]
#[timeout(120_000)]
fn a_selector_two_datatypes_share_keeps_the_hole() {
    let script = "(set-option :produce-proofs true)\n(set-logic QF_DT)\n\
                  (declare-datatypes ((P 0) (Q 0)) \
                  (((mkp (f1 Int) (f2 Int))) ((mkq (f2 Int) (f1 Int)))))\n\
                  (declare-const a Int)\n(declare-const b Int)\n\
                  (assert (not (= (f1 (mkq a b)) b)))\n(check-sat)\n";
    for dialect in [AletheDialect::Clean, AletheDialect::PinnedCarcara] {
        let mut exec = Executor::new();
        exec.set_alethe_dialect(dialect);
        let outputs = exec
            .execute_all(&parse(script).expect("parse SMT-LIB script"))
            .expect("execute SMT-LIB script");
        assert_eq!(outputs, ["unsat"], "{dialect:?}");
        let (document, surface) = match exec
            .try_export_last_proof_alethe_for_problem_scope_with_carcara_surface()
            .expect("a retained proof")
        {
            Ok(rendered) => rendered,
            Err(ay_proof::AlethePrintError::UndeclarableProofSymbols { names, .. }) => {
                assert!(names.contains("__ay_overload_1"), "{dialect:?}: {names}");
                continue;
            }
            Err(error) => panic!("{dialect:?}: {error:?}"),
        };
        assert!(
            !document.contains("__ay_overload_"),
            "{dialect:?}:\n{document}"
        );
        assert!(!document.contains("dt_project"), "{dialect:?}:\n{document}");
        assert_eq!(
            document.matches(":rule hole)").count(),
            1,
            "{dialect:?}:\n{document}"
        );
        assert_ne!(surface, PROJECT, "{dialect:?}:\n{document}");
    }
}

/// The library artifact of the same text-lane problem carries the surface.
#[test]
#[timeout(120_000)]
fn the_unsat_artifact_discloses_dt_project() {
    for row in &ROWS {
        let label = row.label;
        let mut solver = Solver::try_new(Logic::QfDt).expect("QF_DT solver");
        solver.set_produce_proofs(true);
        solver
            .parse_smtlib2(&format!(
                "{}(assert (not {}))\n",
                row.declarations, row.equality
            ))
            .expect("parse the fixture");
        let verdict = solver.check_sat();
        assert!(verdict.is_unsat(), "{label}: {verdict:?}");
        let artifact = solver
            .export_last_unsat_artifact()
            .unwrap_or_else(|| panic!("{label}: a strict-checked refutation publishes"));
        assert!(
            matches!(artifact.strict_verdict, StrictProofVerdict::Verified(_)),
            "{label}: {:?}",
            artifact.strict_verdict
        );
        assert_eq!(
            artifact.carcara_surface, PROJECT,
            "{label}:\n{}",
            artifact.alethe
        );
        assert!(artifact.alethe.contains(":rule dt_project)"), "{label}");
        assert!(
            !artifact.alethe.contains(":rule hole"),
            "{label}:\n{}",
            artifact.alethe
        );
        // AY carries no problem transport for a datatype problem
        // (`alethe_problem_smt2` is `None`, measured 2026-10-02 on this lane
        // and on the native one), so the checkers read the authored problem.
        let problem = artifact
            .alethe_problem_smt2
            .clone()
            .unwrap_or_else(|| row.problem());
        replay_clean_document(
            label,
            &problem,
            &artifact.alethe,
            &row.wrong_field(&problem),
            &row.wrong_field(&artifact.alethe),
        );
    }
}

/// Trust's native recipe (the development design notes
/// carcara-for-datatype-and-skolem-refl.md`, repro 1) through the API lane
/// trust-router's `AYProgram` lowers to: `x = A(5) ∧ ¬(fld x = 5)`. At the pin
/// its 23-step document was strict-`Verified` with exactly one hole, the
/// projection `(= (__trust_s_1_A_fld (__trust_c_1_A_A 5)) 5)`.
#[test]
#[timeout(120_000)]
fn trusts_native_datatype_recipe_prints_dt_project() {
    let datatype = DatatypeSort {
        name: "__trust_d_A".to_string(),
        constructors: vec![DatatypeConstructor {
            name: "__trust_c_1_A_A".to_string(),
            fields: vec![DatatypeField {
                name: "__trust_s_1_A_fld".to_string(),
                sort: Sort::Int,
            }],
        }],
    };
    let projection = "(= (__trust_s_1_A_fld (__trust_c_1_A_A 5)) 5)";
    for dialect in [AletheDialect::Clean, AletheDialect::PinnedCarcara] {
        let mut solver = Solver::try_new(Logic::All).expect("ALL solver");
        solver.set_produce_proofs(true);
        solver.set_alethe_dialect(dialect);
        solver.declare_datatype(&datatype);
        let x = solver.declare_const("__trust_u_x", Sort::Datatype(datatype.clone()));
        let five = solver.int_const(5);
        let built = solver.datatype_constructor(&datatype, "__trust_c_1_A_A", &[five]);
        let field = solver.datatype_selector("__trust_s_1_A_fld", x, Sort::Int);
        let bound = solver.eq(x, built);
        let projected = solver.eq(field, five);
        let refuted = solver.not(projected);
        let both = solver.and(bound, refuted);
        solver.assert_term(both);
        let verdict = solver.check_sat();
        assert!(verdict.is_unsat(), "{dialect:?}: {verdict:?}");
        let artifact = solver
            .export_last_unsat_artifact()
            .unwrap_or_else(|| panic!("{dialect:?}: the native lane publishes"));
        assert!(
            matches!(artifact.strict_verdict, StrictProofVerdict::Verified(_)),
            "{dialect:?}: {:?}",
            artifact.strict_verdict
        );
        let document = &artifact.alethe;
        eprintln!(
            "native recipe [{dialect:?}]: surface={} problem_smt2={} holes={}\n{document}",
            artifact.carcara_surface,
            artifact.alethe_problem_smt2.is_some(),
            document.matches(":rule hole").count()
        );
        if dialect == AletheDialect::PinnedCarcara {
            assert!(
                document.contains(&format!("(cl {projection}) :rule hole)")),
                "{dialect:?}:\n{document}"
            );
            assert!(!document.contains("dt_project"), "{dialect:?}:\n{document}");
            continue;
        }
        assert_eq!(artifact.carcara_surface, PROJECT, "{document}");
        assert!(
            document.contains(&format!("(cl {projection}) :rule dt_project)")),
            "{document}"
        );
        assert!(!document.contains(":rule hole"), "{document}");
        // Trust's `problem_smt2` spelling of the same program (the issue's).
        let problem = "(set-logic QF_UFDTLIA)\n\
                       (declare-datatype __trust_d_A ((__trust_c_1_A_A (__trust_s_1_A_fld Int))))\n\
                       (declare-fun __trust_u_x () __trust_d_A)\n\
                       (assert (and (= __trust_u_x (__trust_c_1_A_A 5)) \
                       (not (= (__trust_s_1_A_fld __trust_u_x) 5))))\n(check-sat)\n";
        let problem = artifact.alethe_problem_smt2.as_deref().unwrap_or(problem);
        let scope = ay_proof::ProblemScope::from_smtlib_source(problem);
        ay_proof::check_alethe_document(document, &scope)
            .unwrap_or_else(|defect| panic!("{defect}\n{document}"));
        // The twin asserts `¬(fld x = 6)`, which `x = A(5)` satisfies, and
        // its only false step is the projection onto `6`. The native document
        // spells the authored literal value first, so both spellings move.
        let six = |text: &str| {
            text.replace(projection, "(= (__trust_s_1_A_fld (__trust_c_1_A_A 5)) 6)")
                .replace(
                    "(= (__trust_s_1_A_fld __trust_u_x) 5)",
                    "(= (__trust_s_1_A_fld __trust_u_x) 6)",
                )
                .replace(
                    "(= 5 (__trust_s_1_A_fld __trust_u_x))",
                    "(= 6 (__trust_s_1_A_fld __trust_u_x))",
                )
        };
        replay_clean_document(
            "native-recipe",
            problem,
            document,
            &six(problem),
            &six(document),
        );
    }
}
