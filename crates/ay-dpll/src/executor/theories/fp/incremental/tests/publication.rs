// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use ay_core::TermId;

use super::*;

fn command(executor: &mut Executor, text: &str) -> Vec<String> {
    executor.execute_all(&parse(text).unwrap()).unwrap()
}

fn pending_after_pop(named: bool) -> (Executor, TermId) {
    let mut executor = Executor::new();
    let assertion = if named {
        "(set-option :produce-unsat-cores true) (assert (! b :named named_b))"
    } else {
        "(assert b)"
    };
    command(
        &mut executor,
        &format!("(declare-const b Bool) {assertion}"),
    );
    let root = executor.ctx.assertions[0];
    assert_eq!(command(&mut executor, "(check-sat)"), ["sat"]);
    assert!(executor.last_model.is_some());
    command(
        &mut executor,
        "(push 1) (declare-const x (_ FloatingPoint 5 11)) (assert (fp.isZero x))",
    );
    // Manufacture only the unavailable numeric frontier; the real command
    // performs the checked push and records its deferred failure, without a
    // huge SAT allocation. Pop then removes every FP root before the check.
    executor.incr_fp_state.as_mut().unwrap().fp_cache.next_var = u32::MAX;
    command(&mut executor, "(push 1) (pop 2)");
    assert_eq!(executor.ctx.assertions, [root]);
    let state = executor.incr_fp_state.as_ref().unwrap();
    assert_eq!(state.scope_depth, 0);
    assert!(state.persistent_sat.is_none());
    assert!(!state.disabled);
    (executor, root)
}

#[test]
fn text_boolean_check_delivers_pending_fp_refusal_once_even_when_reuse_is_disabled() {
    for disabled in [false, true] {
        let (mut executor, root) = pending_after_pop(false);
        if disabled {
            executor
                .incr_fp_state
                .as_mut()
                .unwrap()
                .disable_and_teardown();
        }
        assert_eq!(command(&mut executor, "(check-sat)"), ["unknown"]);
        revoked(&executor, UnknownOrigin::DeterministicResourceBudget);
        assert_eq!(executor.ctx.assertions, [root]);
        assert_eq!(executor.incr_fp_state.as_ref().unwrap().disabled, disabled);
        assert_eq!(command(&mut executor, "(check-sat)"), ["sat"]);
        assert!(executor.last_model.is_some());
        assert_eq!(executor.ctx.assertions, [root]);
        assert!(executor.unknown_origin().is_none());
    }
}

#[test]
fn text_named_assumptions_cannot_rescue_the_pending_resource_refusal() {
    let (mut executor, root) = pending_after_pop(true);
    assert_eq!(executor.ctx.named_terms_iter().count(), 1);
    assert_eq!(
        command(&mut executor, "(check-sat-assuming (b))"),
        ["unknown"]
    );
    revoked(&executor, UnknownOrigin::DeterministicResourceBudget);
    assert_eq!(executor.ctx.assertions, [root]);
    assert_eq!(command(&mut executor, "(check-sat-assuming (b))"), ["sat"]);
    assert_eq!(executor.ctx.assertions, [root]);
    assert!(executor.last_model.is_some());
}

#[derive(Clone, Copy, Debug)]
enum DirectEntry {
    Plain,
    Assuming,
    NamedAssuming,
}

fn direct(executor: &mut Executor, root: TermId, entry: DirectEntry) -> SolveResult {
    match entry {
        DirectEntry::Plain => executor.check_sat(),
        DirectEntry::Assuming => executor.check_sat_assuming(&[root]),
        DirectEntry::NamedAssuming => executor.check_sat_assuming_with_named_cores(&[root]),
    }
    .unwrap()
}

#[test]
fn direct_executor_entries_revoke_before_named_redirect_or_non_fp_routing() {
    for entry in [
        DirectEntry::Plain,
        DirectEntry::Assuming,
        DirectEntry::NamedAssuming,
    ] {
        let (mut executor, root) = pending_after_pop(true);
        // Direct crate entrypoints do not run the text begin-query wrapper.
        // Seed the stale guard fields that their canonical refusal must clear.
        executor.last_model_validated = true;
        executor.last_assumption_core = Some(vec![root]);
        assert!(matches!(
            direct(&mut executor, root, entry),
            SolveResult::Unknown
        ));
        revoked(&executor, UnknownOrigin::DeterministicResourceBudget);
        assert_eq!(executor.ctx.assertions, [root], "{entry:?}");
        assert!(matches!(
            direct(&mut executor, root, entry),
            SolveResult::Sat
        ));
        assert_eq!(executor.ctx.assertions, [root], "{entry:?}");
    }
}
