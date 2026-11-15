// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Exercise the public consumer boundary, not only a private candidate checker.

use super::Owner;
use ay_chc::{
    validate_chc_compact_ground_derivation_artifact, ChcPdrProofRun, ChcProblem,
    ChcReplayPayloadFormat, ChcValidatedCompactGroundDerivation,
};

pub(super) fn replay(run: &ChcPdrProofRun, original: &ChcProblem, k: usize, owner: &Owner) {
    owner.check("portable compact evidence admission");
    let checked = run
        .run_checked_replay(owner.remaining())
        .expect("actual compact Unsafe evidence must pass the public checked replay route");
    owner.check("checked replay publication");
    let rows: Vec<_> = checked.obligation_payloads().collect();
    assert_eq!(rows.len(), 1, "one complete original derivation");
    let row = &rows[0];
    assert_eq!(
        row.obligation().payload_format,
        ChcReplayPayloadFormat::CompactGroundDerivationV1
    );
    assert!(row.smt_query_bytes().is_none());
    assert!(row.strict_bundle_bytes().is_none());
    let bytes = row.payload_bytes();
    assert!(
        bytes.len() <= 1024 * k + 4096,
        "serialized evidence must not expand 2^k leaves: {} bytes at k={k}",
        bytes.len()
    );
    // Use the caller-parsed ORIGINAL external source, not a producer-side
    // projected problem or a bare digest. The public decoder replays every step.
    let snapshot = validate_chc_compact_ground_derivation_artifact(original, bytes)
        .expect("fresh consumer-side source-bound replay");
    assert_eq!(snapshot.step_count(), 4);
    assert_eq!(snapshot.query_step(), 3);
    inspect_all_fields(&snapshot, k);
    owner.check("borrowed complete DAG playback");
    checked
        .recheck_with_fresh_ay_with_cancellation(owner.remaining(), &owner.cancellation)
        .expect("retained compact payload must freshly recheck under the original grant");
    owner.check("fresh checked-payload recheck");
    eprintln!(
        "R26 k={k}: compact nodes={}, artifact bytes={}, original steps={}",
        snapshot.node_count(),
        bytes.len(),
        snapshot.step_count()
    );
    drop(snapshot);
    drop(rows);
    drop(checked);
    owner.check("portable evidence cleanup");
}

fn inspect_all_fields(snapshot: &ChcValidatedCompactGroundDerivation, k: usize) {
    assert!(
        snapshot.node_count() <= 2 * k + 2,
        "complete value DAG must stay linear"
    );
    for (id, node) in snapshot.nodes() {
        if let Some((sort, constructor)) = node.datatype() {
            assert_eq!(constructor, format!("{sort}_mk"));
            let level: usize = sort
                .strip_prefix('D')
                .expect("original sort")
                .parse()
                .unwrap();
            assert!((1..=k).contains(&level));
            assert_eq!(
                node.fields().len(),
                2,
                "both read AND unread fields survive"
            );
            for child in node.fields() {
                assert!(child.index() < id.index(), "well-founded sharing");
                let value = snapshot.node(child).expect("every field is present");
                if level == 1 {
                    assert_eq!(value.bitvector().expect("complete scalar leaf").1, 32);
                } else {
                    assert_eq!(
                        value.datatype().expect("complete product child").0,
                        format!("D{}", level - 1)
                    );
                }
            }
        } else {
            assert_eq!(node.bitvector().expect("original BV32 leaf").1, 32);
        }
    }
    let mut value = snapshot
        .step(2)
        .expect("original query antecedent")
        .binding("bb1_v0")
        .expect("original variable, not a projected scalar");
    for _ in 0..k {
        value = snapshot
            .node(value)
            .expect("selector root")
            .fields()
            .next()
            .expect("original a field");
    }
    let selected = snapshot.node(value).expect("selected original leaf");
    let (value, width) = selected.bitvector().expect("selected bitvector");
    assert_eq!(width, 32);
    assert_eq!(value.to_string(), "5", "the ORIGINAL guard holds");
}
