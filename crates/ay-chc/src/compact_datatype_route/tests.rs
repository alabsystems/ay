// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::ground_derivation::compact::{validate, ValueNode};
use crate::{ChcExpr, ChcParser, ChcSort, ClauseHead};
use ay_core::resource::{enter_check_stop, ChildSpec, Guard, NodeLabel};
use ay_core::time::Instant;
use sha2::{Digest, Sha256};
use std::sync::{
    atomic::{AtomicBool, Ordering},
    Arc,
};
use std::time::Duration;

const ORIGINAL: &str =
    include_str!("../../tests/fixtures/model_checker_consumer_struct_dag_datatype_k10.smt2");

fn product_source(k: usize) -> String {
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

fn bounded_case(source: &str, expected: bool) -> Option<CompactDerivation> {
    // A test-only diagnostic owner, not a budget attributed to the consumer.
    let _deadline = crate::smt::deadline::ScopedSmtDeadline::install_until(
        Instant::now() + Duration::from_secs(20),
    );
    let mut owner = Owner::capture().expect("original owner");
    let problem = ChcParser::parse(source).expect("test source parses");
    let witness = derive(&problem, &mut owner).expect("supported producer");
    assert_eq!(
        witness.is_some(),
        expected,
        "Unknown or no witness does not satisfy an Unsafe test"
    );
    if let Some(witness) = &witness {
        validate(&problem, witness, &mut owner).expect("independent original replay");
    }
    owner.poll().expect("same original owner after replay");
    witness
}

#[test]
fn original_k10_and_generated_k16_k32_solve_with_complete_linear_values() {
    assert_eq!(ORIGINAL.len(), 896);
    assert_eq!(
        format!("{:x}", Sha256::digest(ORIGINAL.as_bytes())),
        "555712d96a47f700d3621b3a8fbe725904fb3e71bfc4362d8f5dd4018bf1cc24"
    );
    assert_eq!(product_source(10), ORIGINAL);
    for k in [10, 16, 32] {
        let source = product_source(k);
        let witness = bounded_case(&source, true).expect("actual original-clause witness");
        assert_eq!(witness.steps.len(), 4);
        assert!(
            witness.arena.nodes().len() <= 3 * k + 4,
            "no eager leaf materialization"
        );
        for (index, node) in witness.arena.nodes().iter().enumerate() {
            if let ValueNode::Datatype { fields, .. } = node {
                assert_eq!(
                    fields.len(),
                    2,
                    "both observed and unread fields are concrete"
                );
                assert!(fields.iter().all(|field| (field.0 as usize) < index));
            }
        }
    }
}

fn pair(guards: &str) -> String {
    format!(
        "(set-logic HORN)
      (declare-datatype Packet ((assemble (flag Bool) (payload (_ BitVec 8)))))
      (declare-var left Packet) (declare-var right Packet)
      (declare-rel start (Packet)) (declare-rel finish (Packet))
      (rule (start left))
      (rule (=> (start left) (finish left)))
      (rule (=> (and (finish right) {guards}) false))"
    )
}

#[test]
fn renamed_boolean_and_bitvector_fields_use_actual_model_not_fixed_leaf() {
    let source = pair("(flag right) (= (bvadd (payload right) #x03) #x2c)");
    let witness = bounded_case(&source, true).expect("renamed product witness");
    assert!(witness
        .arena
        .nodes()
        .iter()
        .any(|node| matches!(node, ValueNode::Bool(true))));
    assert!(witness.arena.nodes().iter().any(|node| matches!(node, ValueNode::BitVec { value, width: 8 } if *value == num_bigint::BigUint::from(41u8))));
}

#[test]
fn conflicting_reads_of_same_path_are_not_independent_havocs() {
    bounded_case(
        &pair("(= (payload right) #x03) (= (payload right) #x04)"),
        false,
    );
}

#[test]
fn original_fact_and_transition_guards_are_preserved() {
    let source = pair("(= (payload right) #x04)").replace(
        "(rule (start left))",
        "(rule (=> (= (payload left) #x03) (start left)))",
    );
    bounded_case(&source, false);
    let source = pair("(= (payload right) #x04)").replace(
        "(rule (=> (start left) (finish left)))",
        "(rule (=> (and (start left) (= (payload left) #x03)) (finish left)))",
    );
    bounded_case(&source, false);
}

#[test]
fn repeated_predicate_positions_unify_complete_products() {
    let prefix = "(set-logic HORN)
      (declare-datatype Pair ((pack (read (_ BitVec 8)) (unread Bool))))
      (declare-var a Pair) (declare-var b Pair) (declare-var c Pair)
      (declare-rel stage (Pair Pair)) (rule (stage a a))";
    bounded_case(
        &format!(
            "{prefix} (rule (=> (and (stage b c) (= (read b) #x12) (= (read c) #x12)) false))"
        ),
        true,
    );
    bounded_case(
        &format!(
            "{prefix} (rule (=> (and (stage b c) (= (read b) #x12) (= (read c) #x13)) false))"
        ),
        false,
    );
}

#[test]
fn reordered_columns_preserve_positional_aliases() {
    let prefix = "(set-logic HORN)
      (declare-datatype Boxed ((box (value (_ BitVec 8)) (spare Bool))))
      (declare-var a Boxed) (declare-var b Boxed)
      (declare-var x Boxed) (declare-var y Boxed)
      (declare-var m Boxed) (declare-var n Boxed)
      (declare-rel before (Boxed Boxed)) (declare-rel after (Boxed Boxed))
      (rule (=> (and (= (value a) #x01) (= (value b) #x02)) (before a b)))
      (rule (=> (before x y) (after y x)))";
    bounded_case(
        &format!(
            "{prefix} (rule (=> (and (after m n) (= (value m) #x02) (= (value n) #x01)) false))"
        ),
        true,
    );
    bounded_case(
        &format!(
            "{prefix} (rule (=> (and (after m n) (= (value m) #x02) (= (value n) #x02)) false))"
        ),
        false,
    );
}

#[test]
fn clause_local_scalar_names_are_not_global_aliases() {
    let source = pair("(flag right)")
        .replace(
            "(declare-var left Packet)",
            "(declare-var scratch (_ BitVec 8)) (declare-var left Packet)",
        )
        .replace(
            "(rule (start left))",
            "(rule (=> (= scratch #x01) (start left)))",
        )
        .replace(
            "(rule (=> (start left) (finish left)))",
            "(rule (=> (and (start left) (= scratch #x02)) (finish left)))",
        );
    bounded_case(&source, true);
}

#[test]
fn alternative_predecessors_do_not_lose_a_valid_path() {
    let source = pair("(= (payload right) #x29)").replace("(rule (start left))", "(rule (=> (= (payload left) #x01) (start left)))\n(rule (=> (= (payload left) #x29) (start left)))");
    bounded_case(&source, true);
}

#[test]
fn completed_candidate_rejects_bad_premise_and_unread_field_change() {
    let source = pair("(= (payload right) #x29)");
    let problem = ChcParser::parse(&source).expect("source");
    let mut witness = bounded_case(&source, true).expect("witness");
    let mut owner = Owner::capture().expect("owner");
    witness.steps[1].premises[0] = 1;
    assert!(validate(&problem, &witness, &mut owner).is_err());
    witness.steps[1].premises[0] = 0;
    let root = witness.steps[1].env["left"];
    let Some(ValueNode::Datatype {
        sort,
        constructor,
        fields,
    }) = witness.arena.get(root)
    else {
        panic!("complete product");
    };
    let (sort, constructor, mut fields) = (sort.clone(), constructor.clone(), fields.clone());
    let mut owner = Owner::capture().expect("fresh independent negative check");
    fields[0] = witness
        .arena
        .intern(&ValueNode::Bool(true), &mut owner)
        .expect("changed unread field");
    let changed = witness
        .arena
        .intern(
            &ValueNode::Datatype {
                sort,
                constructor,
                fields,
            },
            &mut owner,
        )
        .expect("complete changed node");
    witness.steps[1].env.insert("left".to_owned(), changed);
    assert!(
        validate(&problem, &witness, &mut owner).is_err(),
        "whole predicate tuple, including unread fields, must match"
    );
}

#[test]
fn wrong_selector_sort_and_same_name_different_variable_sort_are_rejected() {
    let mut problem = ChcParser::parse(&pair("(= (payload right) #x29)")).expect("source");
    let query = problem
        .clauses_mut()
        .iter_mut()
        .find(|clause| clause.is_query())
        .expect("query");
    query.body.constraint = Some(ChcExpr::FuncApp(
        "payload".into(),
        ChcSort::Bool,
        vec![Arc::new(ChcExpr::Var(crate::ChcVar::new(
            "right",
            ChcSort::Bool,
        )))],
    ));
    let mut owner = Owner::capture().expect("owner");
    assert!(derive(&problem, &mut owner).is_err());
}

#[test]
fn source_quantifier_polarity_and_resource_refusal_are_not_witnesses() {
    let mut problem = ChcParser::parse(&pair("(flag right)")).expect("source");
    problem.mark_stripped_body_forall();
    let mut owner = Owner::capture().expect("owner");
    assert!(matches!(
        derive(&problem, &mut owner),
        Err(Error::Unsupported)
    ));
    let problem = ChcParser::parse(&pair("(flag right)")).expect("source");
    let guard = Guard::root_child(ChildSpec::new(NodeLabel::Check).with_rlimit(Some(1)));
    let _scope = guard.enter();
    let mut owner = Owner::capture().expect("owner before work");
    assert!(derive(&problem, &mut owner).is_err());
    assert!(owner.poll().is_err());
}

#[test]
fn original_callback_is_retained_and_refusal_is_sticky() {
    let problem = ChcParser::parse(&pair("(flag right)")).expect("source");
    let stopped = Arc::new(AtomicBool::new(false));
    let captured = Arc::clone(&stopped);
    let original = enter_check_stop(Arc::new(move || captured.load(Ordering::Relaxed)));
    let mut owner = Owner::capture().expect("original owner");
    drop(original);
    let _replacement = enter_check_stop(Arc::new(|| false));
    stopped.store(true, Ordering::Relaxed);
    assert!(derive(&problem, &mut owner).is_err());
    stopped.store(false, Ordering::Relaxed);
    assert!(derive(&problem, &mut owner).is_err());
}

#[test]
fn unsupported_constructor_columns_do_not_become_false_unsafe() {
    let mut problem = ChcParser::parse(&pair("(flag right)")).expect("source");
    let fact = problem
        .clauses_mut()
        .iter_mut()
        .find(|clause| clause.is_fact())
        .expect("fact");
    let ClauseHead::Predicate(_, args) = &mut fact.head else {
        panic!("fact predicate");
    };
    let sort = args[0].sort();
    args[0] = ChcExpr::FuncApp(
        "assemble".into(),
        sort,
        vec![
            Arc::new(ChcExpr::Bool(false)),
            Arc::new(ChcExpr::BitVec(0, 8)),
        ],
    );
    let mut owner = Owner::capture().expect("owner");
    assert!(derive(&problem, &mut owner)
        .expect("unsupported path falls through")
        .is_none());
}
