// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

fn history(steps: &[(ScopeKind, u32)]) -> QueryDraft {
    let mut draft = base();
    for &(kind, levels) in steps {
        draft.commands.push(QueryCommand::Scope {
            kind,
            levels,
            numeral: Some(levels.to_string()),
        });
    }
    draft
}

#[test]
fn scope_level_mismatch_is_a_recognized_control_mismatch() {
    let one = history(&[(ScopeKind::Push, 1), (ScopeKind::Pop, 1)]);
    let two = history(&[(ScopeKind::Push, 2), (ScopeKind::Pop, 2)]);
    assert!(!matches(one.clone(), two.clone()));
    assert!(!matches(two, one));
}

#[test]
fn scope_kind_mismatch_is_not_a_noncontrol_fallback() {
    let nested = history(&[
        (ScopeKind::Push, 1),
        (ScopeKind::Push, 1),
        (ScopeKind::Pop, 1),
        (ScopeKind::Pop, 1),
    ]);
    let sequential = history(&[
        (ScopeKind::Push, 1),
        (ScopeKind::Pop, 1),
        (ScopeKind::Push, 1),
        (ScopeKind::Pop, 1),
    ]);
    assert!(!matches(nested.clone(), sequential.clone()));
    assert!(!matches(sequential, nested));
}

#[test]
fn identical_scope_histories_match() {
    let draft = history(&[(ScopeKind::Push, 2), (ScopeKind::Pop, 2)]);
    assert!(matches(draft.clone(), draft));
}
