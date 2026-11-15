// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

const ORIGINAL: &str = include_str!("zero-addition-index.smt2");

fn execute(problem: &str) -> (Executor, Vec<String>) {
    let mut executor = Executor::new();
    let script = format!(
        "(set-option :produce-proofs true)\n(set-option :check-proofs-strict true)\n{}",
        problem.replace("(exit)", "")
    );
    let results = executor
        .execute_all(&ay_frontend::parse(&script).unwrap())
        .unwrap();
    (executor, results)
}

#[test]
fn raw_source_zero_addition_exports_the_original_problem() {
    for (name, zero) in [
        ("decimal", "(_ bv0 64)".to_string()),
        ("hex", "#x0000000000000000".to_string()),
        ("binary", format!("#b{}", "0".repeat(64))),
    ] {
        let problem = ORIGINAL.replace("(_ bv0 64)", &zero);
        let (executor, results) = execute(&problem);
        assert_eq!(
            results,
            ["unsat"],
            "{name}: {:?}",
            executor.unknown_reason()
        );
        let proof = executor.last_proof().expect("requested proof");
        assert!(executor
            .check_proof_strict_with_datatypes(proof)
            .unwrap()
            .is_complete());
        let document = executor
            .try_export_last_proof_alethe_for_problem_scope()
            .expect("authenticated source scope")
            .expect("checked document");
        assert!(!document.contains(":rule hole") && !document.contains(":rule trust"));
        let mut streamed = Vec::new();
        executor
            .try_export_last_proof_alethe_for_problem_scope_to(&mut streamed)
            .unwrap()
            .unwrap();
        assert_eq!(streamed, document.as_bytes());
        let path =
            std::env::temp_dir().join(format!("ay-index-zero-{name}-{}.json", std::process::id()));
        std::fs::write(
            &path,
            serde_json::to_vec(&serde_json::json!({
                "type":"alethe_certificate", "version":"1.0",
                "problem":problem, "proof":document
            }))
            .unwrap(),
        )
        .unwrap();
        println!("independent replay certificate: {}", path.display());
    }
}

#[test]
fn raw_source_zero_addition_keeps_changed_addresses_and_user_functions_satisfiable() {
    let same_address = ORIGINAL.replace("18446744073709551584", "18446744073709551580");
    let arbitrary_function = ORIGINAL
        .replace("QF_BV", "QF_UFBV")
        .replace("(bvadd ", "(f ")
        .replace(
            "(declare-fun entry_sp",
            "(declare-fun f ((_ BitVec 64) (_ BitVec 64)) (_ BitVec 64))\n(declare-fun entry_sp",
        );
    for problem in [same_address, arbitrary_function] {
        let (executor, results) = execute(&problem);
        assert_eq!(results, ["sat"], "{:?}", executor.unknown_reason());
        assert!(executor.last_proof().is_none());
    }
}
