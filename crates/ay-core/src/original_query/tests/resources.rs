// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

#[test]
fn cancellation_stays_failed_after_callback_becomes_permissive() {
    let a = checked(base());
    let b = checked(base());
    let mut first = true;
    let mut poll = || {
        if first {
            first = false;
            ControlFlow::Break(StopReason::Cancelled)
        } else {
            ControlFlow::Continue(())
        }
    };
    let mut work = WorkBudget::new(1_000, &mut poll);
    assert_eq!(
        a.structurally_matches(&b, &mut work),
        Err(QueryError::Interrupted(StopReason::Cancelled))
    );
    assert_eq!(
        a.structurally_matches(&b, &mut work),
        Err(QueryError::Interrupted(StopReason::Cancelled))
    );
}

#[test]
fn exhausted_work_is_sticky_in_subsequent_operations() {
    let a = checked(base());
    let b = checked(base());
    let mut poll = || ControlFlow::Continue(());
    let mut work = WorkBudget::new(0, &mut poll);
    assert_eq!(
        a.structurally_matches(&b, &mut work),
        Err(QueryError::Exhausted)
    );
    assert_eq!(
        a.structurally_matches(&b, &mut work),
        Err(QueryError::Exhausted)
    );
}

#[test]
fn deadline_interrupts_a_single_large_string_scan() {
    let mut draft = base();
    draft.data.push(DataNode::Literal(Literal {
        kind: LiteralKind::String,
        text: "x".repeat(16_384),
    }));
    draft.typing.push(Attribute {
        keyword: "host".into(),
        value: Some(DataId(0)),
    });
    let a = checked(draft.clone());
    let b = checked(draft);
    let mut calls = 0;
    let mut poll = || {
        calls += 1;
        if calls > 20 {
            ControlFlow::Break(StopReason::Deadline)
        } else {
            ControlFlow::Continue(())
        }
    };
    assert_eq!(
        a.structurally_matches(&b, &mut WorkBudget::new(1_000_000, &mut poll)),
        Err(QueryError::Interrupted(StopReason::Deadline))
    );
}

#[test]
fn number_digit_scanning_cannot_hide_behind_one_node() {
    let mut draft = base();
    let root = node(
        &mut draft,
        1,
        NodeKind::Literal(Literal {
            kind: LiteralKind::Numeral,
            text: "1".repeat(16_384),
        }),
    );
    draft.commands.push(QueryCommand::Request {
        head: token("get-value"),
        payload: vec![],
        terms: vec![root],
    });
    let a = checked(draft.clone());
    let b = checked(draft);
    let mut poll = || ControlFlow::Continue(());
    assert_eq!(
        a.structurally_matches(&b, &mut WorkBudget::new(1_024, &mut poll)),
        Err(QueryError::Exhausted)
    );
}

#[test]
fn duplicate_occurrence_fanout_costs_work_even_when_node_is_memoized() {
    let mut draft = base();
    let root = boolean(&mut draft, true);
    draft.commands.push(QueryCommand::Check {
        kind: CheckKind::Assuming,
        assumptions: vec![root; 8_192],
    });
    let a = checked(draft.clone());
    let b = checked(draft);
    let mut poll = || ControlFlow::Continue(());
    assert_eq!(
        a.structurally_matches(&b, &mut WorkBudget::new(100, &mut poll)),
        Err(QueryError::Exhausted)
    );
}

#[test]
fn cyclic_arena_is_rejected_before_occurrence_walk() {
    let mut draft = base();
    node(
        &mut draft,
        0,
        NodeKind::Annotated {
            body: NodeId(0),
            attributes: vec![],
        },
    );
    assert_root(&mut draft, NodeId(0));
    assert!(matches!(
        refused(draft),
        QueryError::Invalid("non-topological arena edge")
    ));
}

#[test]
fn zero_credit_refusal_retains_unmodified_owned_draft_without_authored_value() {
    let mut draft = base();
    draft.initial_lifetime = DeclarationLifetime::Global;
    draft.reset_lifetime = ResetLifetimePolicy::PreserveCurrent;
    let marker = "caller-owned-secret-source".repeat(1_024);
    draft.data.push(DataNode::Literal(Literal {
        kind: LiteralKind::String,
        text: marker.clone(),
    }));
    let mut poll = || ControlFlow::Continue(());
    let mut work = WorkBudget::new(0, &mut poll);
    let failure = AuthoredQuery::validate(draft, &mut work)
        .expect_err("zero credit cannot construct authored query");
    assert_eq!(failure.error(), QueryError::Exhausted);
    assert!(!format!("{failure:?}").contains("caller-owned-secret-source"));
    let retained = failure.into_draft();
    assert_eq!(retained.initial_lifetime, DeclarationLifetime::Global);
    assert_eq!(
        retained.reset_lifetime,
        ResetLifetimePolicy::PreserveCurrent
    );
    assert!(
        matches!(&retained.data[0], DataNode::Literal(Literal { text, .. }) if text == &marker)
    );
    let again = AuthoredQuery::validate(retained, &mut work)
        .expect_err("the same exhausted ledger cannot mint a value");
    assert_eq!(again.error(), QueryError::Exhausted);
}

#[test]
fn equivalent_persistent_binding_extensions_share_environment_identity() {
    use super::super::environments::{Environment, Environments};
    let mut rows = Environments::default();
    let left = binder(0, "left", 0);
    let right = binder(19, "right", 0);
    let mut poll = || ControlFlow::Continue(());
    let mut work = WorkBudget::new(10_000, &mut poll);
    let a = rows
        .term(Environment::default(), &left, &right, &mut work)
        .expect("first extension");
    let b = rows
        .term(Environment::default(), &left, &right, &mut work)
        .expect("same extension");
    assert_eq!(a, b);
    assert!(rows
        .terms_match(a, left.id, right.id, &mut work)
        .expect("paired lookup"));
}
