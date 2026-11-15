// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Trust's native datatype recipe, verbatim: the `AYProgram` trust-router
//! builds for `x = A(5) ∧ ¬(fld x = 5)`, run by `execute_incremental`.
//!
//! REGRESSION (Trust the development design notes
//! carcara-for-datatype-and-skolem-refl.md`, repro 1, measured at ay
//! `cb87694a9`): the outcome's `unsat_proof` was strict-`Verified` and its one
//! unreconstructed step was the selector-over-constructor axiom,
//! `(step t18 (cl (= (__trust_s_1_A_fld (__trust_c_1_A_A 5)) 5)) :rule hole)`,
//! so Trust's Carcara gate refused the UNSAT. In the default (Clean) dialect
//! that step is now Clean's `dt_project`, the document has no hole, and its
//! surface is disclosed `CleanDialect { DatatypeSelectorProject }`. With
//! `CLEAN_BIN` naming Trust's checker, the document over Trust's own
//! `problem_smt2` spelling of the program must be a literal `PASSED`.

#![cfg(feature = "direct")]

use ay_bindings::constraint::Constraint;
use ay_bindings::execute_direct::{execute_incremental, ExecuteTypedResult};
use ay_bindings::{AYProgram, Expr, Sort};
use ay_dpll::api::{CarcaraSurface, CleanOnlySpelling, StrictProofVerdict};
use ntest::timeout;

/// `program.to_string()`'s problem, as Trust's `problem_smt2` spells it.
const PROBLEM: &str = "(set-logic QF_UFDTLIA)\n\
    (declare-datatype __trust_d_A ((__trust_c_1_A_A (__trust_s_1_A_fld Int))))\n\
    (declare-fun __trust_u_x () __trust_d_A)\n\
    (assert (and (= __trust_u_x (__trust_c_1_A_A 5)) (not (= (__trust_s_1_A_fld __trust_u_x) 5))))\n\
    (check-sat)\n";

fn json_string(text: &str) -> String {
    let mut quoted = String::from("\"");
    for character in text.chars() {
        match character {
            '"' => quoted.push_str("\\\""),
            '\\' => quoted.push_str("\\\\"),
            '\n' => quoted.push_str("\\n"),
            other => quoted.push(other),
        }
    }
    quoted.push('"');
    quoted
}

#[test]
#[timeout(60_000)]
fn the_native_selector_recipe_prints_dt_project_instead_of_a_hole() {
    let mut program = AYProgram::new();
    program.add_constraint(Constraint::set_option(":produce-proofs", "true"));
    program.set_logic("QF_UFDTLIA");
    let a = Sort::enum_type(
        "__trust_d_A",
        vec![("__trust_c_1_A_A", vec![("__trust_s_1_A_fld", Sort::int())])],
    );
    program
        .try_declare_datatype(a.datatype_sort().expect("a datatype sort").clone())
        .expect("declare the datatype");
    program.upgrade_logic_for_datatypes();
    let x = program
        .try_declare_const("__trust_u_x", a.clone())
        .expect("declare x");
    let ctor = Expr::datatype_constructor("__trust_d_A", "__trust_c_1_A_A", vec![Expr::int(5)], a);
    let fld = x
        .clone()
        .field_select("__trust_d_A", "__trust_s_1_A_fld", Sort::int());
    program.assert(x.eq(ctor).and(fld.eq(Expr::int(5)).not()));
    program.check_sat();
    let outcomes = execute_incremental(&program).expect("execute the program");
    let outcome = &outcomes[0];
    assert!(
        matches!(outcome.result, ExecuteTypedResult::Verified),
        "{:?}",
        outcome.result
    );
    let artifact = outcome
        .unsat_proof
        .as_ref()
        .expect("the native lane publishes its proof");
    assert!(
        matches!(artifact.strict_verdict, StrictProofVerdict::Verified(_)),
        "{:?}",
        artifact.strict_verdict
    );
    let document = &artifact.alethe;
    assert!(
        document.contains("(cl (= (__trust_s_1_A_fld (__trust_c_1_A_A 5)) 5)) :rule dt_project)"),
        "{document}"
    );
    assert!(!document.contains(":rule hole"), "{document}");
    assert_eq!(
        artifact.carcara_surface,
        CarcaraSurface::CleanDialect {
            spelling: CleanOnlySpelling::DatatypeSelectorProject
        },
        "{document}"
    );
    let Some(clean) = std::env::var_os("CLEAN_BIN").map(std::path::PathBuf::from) else {
        eprintln!("native_dt_project: CLEAN_BIN unset; Trust's checker not run");
        return;
    };
    let path =
        std::env::temp_dir().join(format!("ay-native-dt-project-{}.json", std::process::id()));
    std::fs::write(
        &path,
        format!(
            "{{\"type\":\"alethe_certificate\",\"version\":\"1.0\",\"problem\":{},\"proof\":{}}}",
            json_string(PROBLEM),
            json_string(document)
        ),
    )
    .expect("write the certificate");
    let output = std::process::Command::new(&clean)
        .args(["cert", "verify-external"])
        .arg(&path)
        .output()
        .expect("run clean cert verify-external");
    let _ = std::fs::remove_file(&path);
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(
        output.status.success() && stdout.contains("External certificate verification: PASSED"),
        "Trust's checker refused the native document:\n{stdout}{}\n{document}",
        String::from_utf8_lossy(&output.stderr)
    );
}
