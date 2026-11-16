// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::{ChcParser, ChcProblem};

mod guards;
mod memory;
mod ownership;
mod progress;
mod scalar;

fn script(depth: usize, guard: u32) -> String {
    let mut text = String::from("(set-logic HORN)\n");
    for level in 1..=depth {
        let child = if level == 1 {
            "(_ BitVec 32)".to_owned()
        } else {
            format!("D{}", level - 1)
        };
        text.push_str(&format!("(declare-datatype D{level} ((D{level}_mk (D{level}_a {child}) (D{level}_b {child}))))\n"));
    }
    text.push_str(&format!("(declare-var bb0_v0 D{depth})\n(declare-var bb1_v0 D{depth})\n(declare-rel error ())\n(declare-rel bb0 (D{depth}))\n(declare-rel bb1 (D{depth}))\n(rule (=> true (bb0 bb0_v0)))\n(rule (=> (bb0 bb0_v0) (bb1 bb0_v0)))\n"));
    let mut path = "bb1_v0".to_owned();
    for level in (1..=depth).rev() {
        path = format!("(D{level}_a {path})");
    }
    text.push_str(&format!(
        "(rule (=> (and (bb1 bb1_v0) (= {path} (_ bv{guard} 32))) error))\n(query error)\n"
    ));
    text
}

fn evidence(depth: usize) -> (ChcProblem, CompactDerivation) {
    let problem = ChcParser::parse(&script(depth, 5)).expect("original source");
    let mut owner = Owner::capture().expect("original owner");
    let mut arena = Arena::new();
    let mut default = arena
        .intern(
            &ValueNode::BitVec {
                value: 0u32.into(),
                width: 32,
            },
            &mut owner,
        )
        .expect("zero");
    let mut spine = arena
        .intern(
            &ValueNode::BitVec {
                value: 5u32.into(),
                width: 32,
            },
            &mut owner,
        )
        .expect("five");
    for level in 1..=depth {
        let sort = format!("D{level}");
        let constructor = format!("D{level}_mk");
        let next_default = arena
            .intern(
                &ValueNode::Datatype {
                    sort: sort.clone(),
                    constructor: constructor.clone(),
                    fields: vec![default, default],
                },
                &mut owner,
            )
            .expect("full default");
        spine = arena
            .intern(
                &ValueNode::Datatype {
                    sort,
                    constructor,
                    fields: vec![spine, default],
                },
                &mut owner,
            )
            .expect("full spine");
        default = next_default;
    }
    let mut source = source::Source::new(&problem, &mut owner).expect("declarations");
    let steps = problem
        .clauses()
        .iter()
        .enumerate()
        .map(|(index, clause)| {
            let env = source
                .clause(clause, &mut owner)
                .expect("clause")
                .vars
                .keys()
                .map(|name| ((*name).to_owned(), spine))
                .collect();
            CompactStep {
                clause_index: index,
                env,
                premises: if index == 0 { vec![] } else { vec![index - 1] },
            }
        })
        .collect();
    drop(source);
    (
        problem,
        CompactDerivation {
            arena,
            steps,
            query_step: 3,
        },
    )
}

fn check(problem: &ChcProblem, derivation: &CompactDerivation) -> Result<()> {
    validate(problem, derivation, &mut Owner::<'_>::capture()?)
}

#[test]
fn original_k10_k16_k32_replay_stays_linear_and_complete() {
    for depth in [10, 16, 32] {
        let (problem, derivation) = evidence(depth);
        assert_eq!(derivation.steps.len(), 4);
        assert_eq!(derivation.arena.nodes().len(), 2 * depth + 2);
        assert_eq!(check(&problem, &derivation), Ok(()), "depth={depth}");
    }
}

#[test]
fn unread_sibling_corruption_breaks_original_relation_equality() {
    let (problem, mut derivation) = evidence(10);
    let root = *derivation.steps[1].env.values().next().expect("binding");
    let ValueNode::Datatype {
        sort,
        constructor,
        fields,
    } = derivation.arena.get(root).expect("root").clone()
    else {
        panic!("datatype");
    };
    assert_ne!(fields[0], fields[1]);
    let corrupt = derivation
        .arena
        .intern(
            &ValueNode::Datatype {
                sort,
                constructor,
                fields: vec![fields[0], fields[0]],
            },
            &mut Owner::<'_>::capture().expect("owner"),
        )
        .expect("typed but different complete value");
    *derivation.steps[1]
        .env
        .values_mut()
        .next()
        .expect("binding") = corrupt;
    assert_eq!(check(&problem, &derivation), Err(Error::InvalidDerivation));
}

#[test]
fn source_guard_is_replayed_not_trusted_from_candidate() {
    let (_, derivation) = evidence(10);
    let changed = ChcParser::parse(&script(10, 6)).expect("changed original");
    assert_eq!(check(&changed, &derivation), Err(Error::InvalidDerivation));
}

#[test]
fn forward_wrong_missing_and_unrooted_premises_are_rejected() {
    for bad in [0, 2, usize::MAX] {
        let (problem, mut derivation) = evidence(2);
        derivation.steps[2].premises[0] = bad;
        assert_eq!(check(&problem, &derivation), Err(Error::InvalidDerivation));
    }
    let (problem, mut derivation) = evidence(2);
    derivation.steps[1].premises.clear();
    assert_eq!(check(&problem, &derivation), Err(Error::InvalidDerivation));
    let (problem, mut derivation) = evidence(2);
    derivation.query_step = 2;
    assert_eq!(check(&problem, &derivation), Err(Error::InvalidDerivation));
}

#[test]
fn missing_extra_and_mistyped_bindings_do_not_get_defaults() {
    let (problem, mut derivation) = evidence(2);
    let name = derivation.steps[0].env.keys().next().expect("name").clone();
    derivation.steps[0].env.remove(&name);
    assert_eq!(check(&problem, &derivation), Err(Error::InvalidDerivation));
    let (problem, mut derivation) = evidence(2);
    derivation.steps[0]
        .env
        .insert("extra".to_owned(), ValueId(0));
    assert_eq!(check(&problem, &derivation), Err(Error::InvalidDerivation));
    let (problem, mut derivation) = evidence(2);
    *derivation.steps[0]
        .env
        .values_mut()
        .next()
        .expect("binding") = ValueId(0);
    assert_eq!(check(&problem, &derivation), Err(Error::InvalidValue));
}

#[test]
fn unknown_constructor_arity_and_child_sort_are_rejected() {
    for mode in 0..3 {
        let (problem, mut derivation) = evidence(1);
        let mut node = ValueNode::Datatype {
            sort: "D1".to_owned(),
            constructor: "D1_mk".to_owned(),
            fields: vec![ValueId(1), ValueId(0)],
        };
        if let ValueNode::Datatype {
            constructor,
            fields,
            ..
        } = &mut node
        {
            match mode {
                0 => *constructor = "wrong".to_owned(),
                1 => {
                    fields.pop();
                }
                _ => fields[0] = ValueId(2),
            }
        }
        let id = derivation
            .arena
            .intern(&node, &mut Owner::<'_>::capture().expect("owner"))
            .expect("structural node");
        *derivation.steps[0]
            .env
            .values_mut()
            .next()
            .expect("binding") = id;
        assert_eq!(check(&problem, &derivation), Err(Error::InvalidValue));
    }
}

#[test]
fn arena_hash_consing_is_exact_and_only_backward_edges_exist() {
    let mut owner = Owner::capture().expect("owner");
    let mut arena = Arena::new();
    let zero = ValueNode::BitVec {
        value: 0u32.into(),
        width: 32,
    };
    let id = arena.intern(&zero, &mut owner).expect("zero");
    assert_eq!(arena.intern(&zero, &mut owner), Ok(id));
    let forward = ValueNode::Datatype {
        sort: "D".to_owned(),
        constructor: "mk".to_owned(),
        fields: vec![ValueId(1)],
    };
    assert_eq!(arena.intern(&forward, &mut owner), Err(Error::InvalidValue));
    for width in [0, crate::MAX_BITVECTOR_WIDTH + 1] {
        assert_eq!(
            arena.intern(
                &ValueNode::BitVec {
                    value: 0u32.into(),
                    width
                },
                &mut owner
            ),
            Err(Error::InvalidValue)
        );
    }
    assert_eq!(
        arena.intern(
            &ValueNode::BitVec {
                value: 256u32.into(),
                width: 8
            },
            &mut owner
        ),
        Err(Error::InvalidValue)
    );
}

#[test]
fn conflicting_original_datatype_definition_and_stripped_forall_refuse() {
    let (mut problem, derivation) = evidence(2);
    problem.add_datatype_def(
        "D1".to_owned(),
        vec![(
            "D1_mk".to_owned(),
            vec![
                ("D1_a".to_owned(), crate::ChcSort::Bool),
                ("D1_b".to_owned(), crate::ChcSort::Bool),
            ],
        )],
    );
    assert_eq!(check(&problem, &derivation), Err(Error::InvalidSource));
    let (mut problem, derivation) = evidence(2);
    problem.mark_stripped_body_forall();
    assert_eq!(check(&problem, &derivation), Err(Error::InvalidSource));
}

#[test]
fn malformed_predicate_names_and_action_ids_are_not_authenticated() {
    for name in ["bb0", "bad\0name"] {
        let (mut problem, derivation) = evidence(2);
        problem.declare_predicate(name, vec![]);
        assert_eq!(check(&problem, &derivation), Err(Error::InvalidSource));
    }
    let (mut problem, derivation) = evidence(2);
    let clause = problem.clauses()[0].clone();
    problem.add_clause_with_action(clause, crate::clause::ActionId::new(u32::MAX));
    assert_eq!(check(&problem, &derivation), Err(Error::InvalidSource));
}
