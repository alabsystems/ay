// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![cfg(test)]

use super::*;
use crate::ground_derivation::{validate_ground_derivation, GroundDerivationError};
use crate::{
    ChcGroundDerivationArtifactError, ChcGroundDerivationArtifactErrorReason as Reason,
    ChcProofRunArtifact, ChcValidatedGroundDerivation, SmtValue,
};

mod mutations;

#[derive(Clone, Copy)]
enum Version {
    V1,
    V2,
}

impl Version {
    fn encode(
        self,
        problem: &ChcProblem,
        cex: &Counterexample,
    ) -> Result<ChcProofRunArtifact, ChcGroundDerivationArtifactError> {
        match self {
            Self::V1 => cex.ground_derivation_artifact(problem),
            Self::V2 => cex.ground_derivation_artifact_v2(problem),
        }
    }

    fn replay(
        self,
        problem: &ChcProblem,
        bytes: &[u8],
    ) -> Result<ChcValidatedGroundDerivation, ChcGroundDerivationArtifactError> {
        match self {
            Self::V1 => crate::validate_chc_ground_derivation_artifact(problem, bytes),
            Self::V2 => crate::validate_chc_ground_derivation_artifact_v2(problem, bytes),
        }
    }
}

fn assert_original_values(checked: &ChcValidatedGroundDerivation, expected: &BigUint) {
    assert_eq!(checked.step_count(), 3);
    assert_eq!(checked.query_step(), 2);
    assert_eq!(checked.premise_edge_count(), 2);
    for (index, step) in checked.steps().enumerate() {
        assert_eq!(step.clause_index(), index);
        if index == 0 {
            assert_eq!(step.premises(), &[] as &[usize]);
        } else {
            assert_eq!(step.premises(), &[index - 1]);
        }
    }
    let fact = checked.step(0).expect("original fact step");
    let value = fact
        .source_binding(WORD)
        .expect("original wide source name");
    assert_eq!(value.bitvec_to_biguint(), Some((expected.clone(), 256)));
    assert!(matches!(value, SmtValue::BigBitVec(_, 256)));
    assert_eq!(fact.source_bindings().count(), 3);
    assert!(fact.source_binding("obj_valid").is_some());
    let output = fact
        .source_binding("obj_valid__out")
        .expect("original output array");
    assert_eq!(
        crate::expr::eval_array_select(output, &SmtValue::BitVec(41, 32)),
        Some(SmtValue::Bool(true)),
    );
}

pub(super) fn check_original_and_mutations(
    source: &str,
    problem: &ChcProblem,
    cex: &Counterexample,
    expected: &BigUint,
) {
    let derivation = cex.ground_derivation.as_ref().expect("actual BMC evidence");
    validate_ground_derivation(problem, derivation).expect("original source replay");
    for version in [Version::V1, Version::V2] {
        let artifact = version
            .encode(problem, cex)
            .expect("public candidate export");
        let checked = version
            .replay(problem, artifact.bytes())
            .expect("public artifact replay");
        assert_original_values(&checked, expected);
        mutations::check_transport(version, source, problem, artifact.bytes(), expected);
    }
    mutations::check_native(problem, cex, expected);
}
