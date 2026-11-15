// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// SPDX-License-Identifier: Apache-2.0

#![cfg(test)]

use super::*;

#[test]
fn controlled_artifact_construction_matches_legacy_metadata_and_bytes() {
    for bytes in [
        Vec::new(),
        b"{\"text\":\"quote\\\"\"}".to_vec(),
        vec![0x91; 12_345],
    ] {
        let expected = ChcProofRunArtifact::new("schema", "role", bytes.clone());
        let actual =
            ChcProofRunArtifact::new_with_progress("schema", "role", bytes, &mut || true).unwrap();
        assert_eq!(actual, expected);
    }
}

#[test]
fn every_hash_and_publication_refusal_prevents_artifact_construction() {
    let bytes = vec![0x83; 12_345];
    let mut polls = 0;
    let expected =
        ChcProofRunArtifact::new_with_progress("schema", "role", bytes.clone(), &mut || {
            polls += 1;
            true
        })
        .unwrap();
    assert!(polls > 4);
    for refused in 1..=polls {
        let mut observed = 0;
        let failure =
            ChcProofRunArtifact::new_with_progress("schema", "role", bytes.clone(), &mut || {
                observed += 1;
                observed != refused
            })
            .unwrap_err();
        assert_eq!(failure, IdentityHashInterrupted, "poll {refused}");
        assert_eq!(observed, refused);
    }
    assert_eq!(
        ChcProofRunArtifact::new_with_progress("schema", "role", bytes, &mut || true).unwrap(),
        expected
    );
}
