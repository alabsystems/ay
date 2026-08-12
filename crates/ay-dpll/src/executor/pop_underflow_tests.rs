// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use std::panic::{catch_unwind, AssertUnwindSafe};

fn assert_scope_underflow(result: Result<Option<String>>) {
    assert!(
        matches!(
            result,
            Err(ExecutorError::Elaborate(
                ay_frontend::ElaborateError::ScopeUnderflow
            ))
        ),
        "expected scope underflow, got {result:?}"
    );
}

#[test]
fn executor_pop_without_push_returns_error_without_unwind() {
    let mut exec = Executor::new();

    let unwind = catch_unwind(AssertUnwindSafe(|| exec.execute(&Command::Pop(1))));

    assert!(unwind.is_ok(), "empty pop must not panic");
    assert_scope_underflow(unwind.expect("checked above"));

    exec.execute(&Command::Push(1))
        .expect("push after failed pop should succeed");
    exec.execute(&Command::Pop(1))
        .expect("balanced pop after failed pop should succeed");
}

#[test]
fn executor_pop_too_many_returns_error_without_unwind() {
    let mut exec = Executor::new();
    exec.execute(&Command::Push(1))
        .expect("push should succeed");

    let unwind = catch_unwind(AssertUnwindSafe(|| exec.execute(&Command::Pop(2))));

    assert!(unwind.is_ok(), "oversized pop must not panic");
    assert_scope_underflow(unwind.expect("checked above"));

    exec.execute(&Command::Pop(1))
        .expect("failed oversized pop should leave the scope available");
}

#[test]
fn executor_misaligned_subsystem_pop_returns_error_without_unwind() {
    let mut exec = Executor::new();
    exec.execute(&Command::Push(1))
        .expect("push should succeed");

    IncrementalSubsystem::reset(&mut exec.proof_tracker);

    let unwind = catch_unwind(AssertUnwindSafe(|| exec.execute(&Command::Pop(1))));

    assert!(
        unwind.is_ok(),
        "misaligned proof tracker pop must not panic"
    );
    assert_scope_underflow(unwind.expect("checked above"));
}
