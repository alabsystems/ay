// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

#[test]
fn duplicate_names_distinct_ids_unknown_ids_and_duplicate_applications_match() {
    let problem = fixture();
    let original = quiet_owner();
    consume(&original, &problem).unwrap();
    let actual = input::build(&problem, &mut Legacy).unwrap();
    assert!(actual.contains("predicate p0 name=") && actual.contains("predicate p1 name="));
    assert!(actual.contains("pred-expr:p?31:") && actual.contains("head=p?63("));
    assert_eq!(actual.matches("p0(int:").count(), 2);
}

#[test]
fn clause_body_and_action_permutations_preserve_canonical_rows() {
    let first = fixture();
    let mut second = first.clone();
    second.clauses_mut().reverse();
    second.clauses_mut()[1].body.predicates.reverse();
    let original = quiet_owner();
    consume(&original, &first).unwrap();
    consume(&original, &second).unwrap();
    assert_eq!(
        input::build(&first, &mut Legacy),
        input::build(&second, &mut Legacy)
    );
    let mut actions_a = ChcProblem::new();
    let mut actions_b = ChcProblem::new();
    actions_a.declare_action("z");
    actions_a.declare_action("a");
    actions_b.declare_action("a");
    actions_b.declare_action("z");
    assert_eq!(
        input::build(&actions_a, &mut Legacy),
        input::build(&actions_b, &mut Legacy)
    );
}

#[test]
fn commutative_children_sort_but_noncommutative_order_remains_visible() {
    let original = quiet_owner();
    for op in [
        ChcOp::And,
        ChcOp::Add,
        ChcOp::Eq,
        ChcOp::BvXnor,
        ChcOp::Sub,
        ChcOp::Ite,
    ] {
        let mut first = ChcProblem::new();
        raw(
            &mut first,
            HornClause::query(ClauseBody::constraint(ChcExpr::Op(
                op,
                vec![Arc::new(ChcExpr::Int(1)), Arc::new(ChcExpr::Int(2))],
            ))),
        );
        let mut second = first.clone();
        let Some(ChcExpr::Op(_, args)) = &mut second.clauses_mut()[0].body.constraint else {
            panic!("fixture op");
        };
        args.reverse();
        consume(&original, &first).unwrap();
        consume(&original, &second).unwrap();
        assert_eq!(
            input::build(&first, &mut Legacy) == input::build(&second, &mut Legacy),
            super::super::super::payload::is_commutative_op(op)
        );
    }
}

#[test]
fn mergesort_is_stable_and_prices_long_common_prefix_comparisons() {
    let mut keys = [
        vec![b'a'; 257],
        vec![b'a'; 257],
        vec![b'a'; 257],
        vec![b'a'; 257],
    ];
    keys[0].push(b'b');
    keys[1].push(b'a');
    keys[2].push(b'b');
    keys[3].push(b'a');
    let mut count = 0usize;
    {
        let mut sink = |work: usize, _: usize| {
            count += work;
            Ok(())
        };
        let mut work = WorkBudget::with_admission(1_000_000, &mut sink);
        let indices = order::indices(keys.len(), &mut Borrowed(&mut work), |a, b, control| {
            order::compare(&keys[a], &keys[b], control)
        })
        .unwrap();
        assert_eq!(indices, vec![1, 3, 0, 2]);
    }
    assert!(count >= 4 * 257);
}
