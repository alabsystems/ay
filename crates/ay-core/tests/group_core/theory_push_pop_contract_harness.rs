// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Shared push/pop contract harness for `TheorySolver` implementations.
//!
//! Contract under test:
//! after `push(); <scoped mutations>; pop();`, solver-observable semantics must
//! match the pre-push state for scope-local effects.
//!
//! Part of #3664.

use ay_core::{TermId, TheoryPropagation, TheoryResult, TheorySolver};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum ContractOutcome {
    Sat,
    Unsat,
    Unknown,
    Other,
}

fn classify_result(result: &TheoryResult) -> ContractOutcome {
    match result {
        TheoryResult::Sat => ContractOutcome::Sat,
        TheoryResult::Unsat(_) | TheoryResult::UnsatWithFarkas(_) => ContractOutcome::Unsat,
        TheoryResult::Unknown => ContractOutcome::Unknown,
        _ => ContractOutcome::Other,
    }
}

fn assert_scope_restoration_contract<T: TheorySolver>(solver: &mut T) -> Result<(), String> {
    // Symbolic term IDs for harness assertions.
    let base = TermId::new(1);
    let scoped_conflict = TermId::new(2);

    solver.assert_literal(base, true);
    let base_result = solver.check();
    let base_outcome = classify_result(&base_result);
    if base_outcome != ContractOutcome::Sat {
        return Err(format!(
            "pre-push baseline must be SAT for this harness, got {base_result:?}"
        ));
    }

    solver.push();
    solver.assert_literal(scoped_conflict, true);
    let scoped_result = solver.check();
    if classify_result(&scoped_result) != ContractOutcome::Unsat {
        return Err(format!(
            "scoped mutation must trigger UNSAT in this harness, got {scoped_result:?}"
        ));
    }

    solver.pop();
    let post_result = solver.check();
    let post_outcome = classify_result(&post_result);
    if post_outcome != base_outcome {
        return Err(format!(
            "post-pop outcome {post_result:?} does not match pre-push outcome {base_result:?}"
        ));
    }

    Ok(())
}

/// Minimal theory used to validate the harness itself.
///
/// `buggy_pop = true` simulates the pre-fix stale-scope bug class where
/// scoped assertions are not removed on pop.
struct MockScopeTheory {
    asserted: Vec<TermId>,
    scopes: Vec<usize>,
    buggy_pop: bool,
}

impl MockScopeTheory {
    fn new(buggy_pop: bool) -> Self {
        Self {
            asserted: Vec::new(),
            scopes: Vec::new(),
            buggy_pop,
        }
    }
}

impl TheorySolver for MockScopeTheory {
    fn assert_literal(&mut self, literal: TermId, value: bool) {
        if value {
            self.asserted.push(literal);
        }
    }

    fn check(&mut self) -> TheoryResult {
        // Base assertion is SAT; adding scoped_conflict in same assignment is UNSAT.
        let has_base = self.asserted.contains(&TermId::new(1));
        let has_scoped_conflict = self.asserted.contains(&TermId::new(2));
        if has_base && has_scoped_conflict {
            TheoryResult::Unsat(Vec::new())
        } else {
            TheoryResult::Sat
        }
    }

    fn propagate(&mut self) -> Vec<TheoryPropagation> {
        Vec::new()
    }

    fn push(&mut self) {
        self.scopes.push(self.asserted.len());
    }

    fn pop(&mut self) {
        if let Some(prev_len) = self.scopes.pop() {
            if !self.buggy_pop {
                self.asserted.truncate(prev_len);
            }
        }
    }

    fn reset(&mut self) {
        self.asserted.clear();
        self.scopes.clear();
    }
}

#[test]
fn contract_harness_accepts_restoring_solver() {
    let mut solver = MockScopeTheory::new(false);
    assert!(
        assert_scope_restoration_contract(&mut solver).is_ok(),
        "restoring implementation should satisfy push/pop contract"
    );
}

#[test]
fn contract_harness_rejects_non_restoring_solver() {
    let mut solver = MockScopeTheory::new(true);
    let err = assert_scope_restoration_contract(&mut solver)
        .expect_err("non-restoring implementation must fail the contract harness");
    assert!(
        err.contains("post-pop outcome"),
        "harness must report post-pop semantic mismatch, got: {err}"
    );
}
