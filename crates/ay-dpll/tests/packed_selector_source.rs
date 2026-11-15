// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Original compiler query through parsing, reconstruction and publication.

use ay_dpll::Executor;
use ay_frontend::parse;

#[test]
fn packed_selector_retains_its_authored_source_through_publication() {
    let input = include_str!("fixtures/pblendvb_canonical.smt2");
    let query = input.strip_suffix("(exit)").expect("terminal exit");
    let commands = parse(&format!("{query}(get-proof)\n")).expect("original compiler query parses");
    let mut executor = Executor::new();
    executor.set_produce_proofs(true);
    let outputs = executor
        .execute_all(&commands)
        .expect("execute original query");
    assert_eq!(
        outputs.first().map(String::as_str),
        Some("unsat"),
        "{outputs:?}"
    );
    let proof = outputs.get(1).expect("published proof response");
    assert!(
        proof.contains(":rule bitblast_extract"),
        "checked selector export"
    );
    assert!(!proof.contains(":rule hole") && !proof.contains(":rule trust"));
    let certificate = serde_json::json!({
        "type": "alethe_certificate", "version": "1.0", "problem": input, "proof": proof,
    });
    let path =
        std::env::temp_dir().join(format!("ay-packed-publication-{}.json", std::process::id()));
    std::fs::write(&path, serde_json::to_vec(&certificate).expect("JSON"))
        .expect("certificate fixture");
    println!("independent replay certificate: {}", path.display());
}
