// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

// Exact original TY ordinal3 CoreToLir access obligations. Their 4077/3919
// frontend nodes both fell below the committed 8192-node early search hint
// and below the intermediate 4096-node candidate measured during diagnosis.
const READ: &str = include_str!(concat!(
    env!("CARGO_MANIFEST_DIR"),
    "/tests/fixtures/external_codegen_scalar_action_read.smt2"
));
const WRITE: &str = include_str!(concat!(
    env!("CARGO_MANIFEST_DIR"),
    "/tests/fixtures/external_codegen_scalar_action_write.smt2"
));

#[test]
fn original_scalar_read_and_write_keep_checked_original_geometry_and_coverage() {
    for (name, source) in [("read", READ), ("write", WRITE)] {
        let mut executor = loaded(source);
        let outputs = executor
            .execute_all(
                &ay_frontend::parse("(set-option :produce-proofs true)(check-sat)(get-proof)")
                    .unwrap(),
            )
            .unwrap();
        assert_eq!(outputs.first().map(String::as_str), Some("unsat"), "{name}");
        let proof = executor
            .last_proof()
            .expect("original-source proof retained");
        assert!(executor
            .check_proof_strict_with_datatypes(proof)
            .unwrap()
            .is_complete());
        let text = outputs.last().unwrap();
        assert!(!text.starts_with("(error"), "{name}");
        assert!(text.contains(":rule or_neg"), "{name}");
        assert!(!text.contains(":rule hole") && !text.contains(":rule trust"));
    }
}
