// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

const ORIGINAL: &str =
    include_str!("../../../../tests/fixtures/model_checker_consumer_struct_dag_datatype_k10.smt2");

fn source(k: usize) -> String {
    let mut lines = vec!["(set-logic HORN)".to_owned()];
    for level in 1..=k {
        let inner = if level == 1 {
            "(_ BitVec 32)".to_owned()
        } else {
            format!("D{}", level - 1)
        };
        lines.push(format!(
            "(declare-datatype D{level} ((D{level}_mk (D{level}_a {inner}) (D{level}_b {inner}))))"
        ));
    }
    let mut read = "bb1_v0".to_owned();
    for level in (1..=k).rev() {
        read = format!("(D{level}_a {read})");
    }
    lines.extend([
        format!("(declare-var bb0_v0 D{k})"),
        format!("(declare-var bb1_v0 D{k})"),
        "(declare-rel error ())".to_owned(),
        format!("(declare-rel bb0 (D{k}))"),
        format!("(declare-rel bb1 (D{k}))"),
        "(rule (=> true (bb0 bb0_v0)))".to_owned(),
        "(rule (=> (bb0 bb0_v0) (bb1 bb0_v0)))".to_owned(),
        format!("(rule (=> (and (bb1 bb1_v0) (= {read} #x00000005)) error))"),
        "(query error)".to_owned(),
    ]);
    lines.join("\n") + "\n"
}

#[test]
fn original_k10_and_four_step_k32_transport_keep_one_owner_without_tree_expansion() {
    assert_eq!(source(10), ORIGINAL);
    for k in [10, 32] {
        let problem = ChcParser::parse(&source(k)).expect("original-shaped source");
        assert_eq!(problem.clauses().len(), 4);
        let mut owner = Owner::capture().expect("one producer owner");
        let mut arena = Arena::new();
        let mut root = arena
            .intern(
                &ValueNode::BitVec {
                    value: BigUint::from(5u8),
                    width: 32,
                },
                &mut owner,
            )
            .expect("original leaf");
        for level in 1..=k {
            root = arena
                .intern(
                    &ValueNode::Datatype {
                        sort: format!("D{level}"),
                        constructor: format!("D{level}_mk"),
                        fields: vec![root, root],
                    },
                    &mut owner,
                )
                .expect("complete shared product");
        }
        let mut steps = Vec::new();
        for (clause_index, name) in [Some("bb0_v0"), Some("bb0_v0"), Some("bb1_v0"), None]
            .into_iter()
            .enumerate()
        {
            steps.push(CompactStep {
                clause_index,
                env: name
                    .into_iter()
                    .map(|name| (name.to_owned(), root))
                    .collect(),
                premises: if clause_index == 0 {
                    vec![]
                } else {
                    vec![clause_index - 1]
                },
            });
        }
        let derivation = CompactDerivation {
            arena,
            steps,
            query_step: 3,
        };
        let artifact = encode_with_owner(&problem, &derivation, &mut owner)
            .expect("whole original-owner transport, not an identity-only check");
        owner.poll().expect("original owner still healthy");
        let bytes = artifact.into_bytes();
        assert!(bytes.len() < 16 * 1024);
        let snapshot = validate_chc_compact_ground_derivation_artifact(&problem, &bytes)
            .expect("fresh reader replays original clauses");
        assert_eq!(snapshot.node_count(), k + 1);
        assert_eq!(snapshot.step_count(), 4);
        assert_eq!(snapshot.step(3).expect("original query").premises(), &[2]);
    }
}

#[test]
fn original_k32_identity_pricing_tracks_streamed_selector_spine() {
    use ay_core::resource::{ChildSpec, Guard, NodeLabel};

    let measured = [16, 32].map(|k| {
        let problem = ChcParser::parse(&source(k)).expect("unchanged original shape");
        let guard = Guard::root_child(ChildSpec::new(NodeLabel::Check));
        let _scope = guard.enter();
        let mut owner = Owner::capture().expect("one identity owner");
        super::super::source::admit_identity(&problem, &mut owner)
            .expect("price the complete source, including unread datatype fields");
        owner.poll().expect("same owner after pricing cleanup");
        guard.ledger_ticks()
    });
    let [small, large] = measured;
    assert!(
        small > 0 && large > small,
        "all added source still costs work"
    );
    // Before unary-spine streaming, ancestor suffix copies exceeded this
    // ratio. Declaration sorting and all original source checks still count;
    // this is a scaling regression, not a whole-solve O(k) work claim.
    assert!(
        large * 4 <= small * 9,
        "selector prefixes must not pay for suffix copies no longer performed: {measured:?}"
    );
}
