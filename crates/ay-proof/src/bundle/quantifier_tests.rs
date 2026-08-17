// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

#[test]
fn negated_exists_dual_kind_roundtrips_in_the_bundle_step_schema() {
    let step = ProofStep::TheoryLemma {
        theory: "QUANT".to_string(),
        clause: vec![TermId(0), TermId(1)],
        farkas: None,
        kind: TheoryLemmaKind::QuantifierNegatedExistsDual,
        lia: None,
    };
    let json = serde_json::to_string(&step).expect("serialize quantified dual step");
    let restored: ProofStep =
        serde_json::from_str(&json).expect("deserialize quantified dual step");
    assert!(matches!(
        restored,
        ProofStep::TheoryLemma {
            ref theory,
            ref clause,
            farkas: None,
            kind: TheoryLemmaKind::QuantifierNegatedExistsDual,
            lia: None,
        } if theory == "QUANT" && clause == &[TermId(0), TermId(1)]
    ));
}
