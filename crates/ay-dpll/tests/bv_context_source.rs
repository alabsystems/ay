// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use ay_dpll::Executor;
use ay_frontend::parse;

fn publish_original(name: &str, input: &str) {
    let query = input.trim_end().strip_suffix("(exit)").unwrap();
    let mut executor = Executor::new();
    executor.set_produce_proofs(true);
    let outputs = executor
        .execute_all(&parse(&format!("{query}(get-proof)\n")).unwrap())
        .unwrap();
    assert_eq!(
        outputs.first().map(String::as_str),
        Some("unsat"),
        "{outputs:?}"
    );
    let proof = outputs.get(1).expect("published proof");
    assert!(proof.contains(":rule ite_simplify"), "{proof}");
    assert!(!proof.contains(":rule hole") && !proof.contains(":rule trust"));
    let path = std::env::temp_dir().join(format!(
        "ay-context-public-{name}-{}.json",
        std::process::id()
    ));
    std::fs::write(&path, serde_json::to_vec(&serde_json::json!({"type":"alethe_certificate","version":"1.0","problem":input,"proof":proof})).unwrap()).unwrap();
    println!("independent replay certificate: {}", path.display());
}

#[test]
fn original_exception_contexts_publish_checked_source_proofs() {
    for (name, problem) in [
        ("catch-all", include_str!("fixtures/context_catch_all.smt2")),
        (
            "out-of-range",
            include_str!("fixtures/context_out_of_range.smt2"),
        ),
        (
            "landing-pad",
            include_str!("fixtures/context_landing_pad.smt2"),
        ),
    ] {
        publish_original(name, problem);
    }
}

#[test]
fn changed_exception_dispatch_branch_has_a_counterexample() {
    let original = include_str!("fixtures/context_catch_all.smt2");
    let input = original.replace(
        "(bvadd func_start landing_pad) (_ bv0 64)",
        "(_ bv0 64) (_ bv0 64)",
    );
    assert_ne!(original, input);
    let outputs = Executor::new()
        .execute_all(&parse(&input).unwrap())
        .unwrap();
    assert_eq!(
        outputs.first().map(String::as_str),
        Some("sat"),
        "{outputs:?}"
    );
}
