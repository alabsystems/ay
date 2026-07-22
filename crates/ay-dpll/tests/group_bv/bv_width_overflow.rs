// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(deprecated)]
#![allow(clippy::panic)]

use ay_dpll::api::{Logic, Solver, SolverError, Sort};
use ntest::timeout;

fn assert_invalid_argument(
    err: SolverError,
    expected_operation: &'static str,
    expected_message: &str,
) {
    match err {
        SolverError::InvalidArgument { operation, message } => {
            assert_eq!(operation, expected_operation);
            assert_eq!(message, expected_message);
        }
        other => panic!("expected InvalidArgument, got {other:?}"),
    }
}

fn assert_panics_containing_all<F: FnOnce() + std::panic::UnwindSafe>(f: F, needles: &[&str]) {
    let payload = std::panic::catch_unwind(f).expect_err("expected panic");
    let msg = if let Some(s) = payload.downcast_ref::<String>() {
        s.as_str()
    } else if let Some(s) = payload.downcast_ref::<&'static str>() {
        s
    } else {
        "<non-string panic payload>"
    };
    for needle in needles {
        assert!(
            msg.contains(needle),
            "expected panic message to contain {needle:?}, got {msg:?}"
        );
    }
}

#[test]
#[timeout(5000)]
fn test_try_bvconcat_rejects_width_overflow() {
    let mut solver = Solver::new(Logic::QfBv);
    let w = u32::MAX;
    let a = solver.declare_const("a", Sort::bitvec(w));
    let b = solver.declare_const("b", Sort::bitvec(1));

    let err = solver.try_bvconcat(a, b).unwrap_err();
    assert_invalid_argument(
        err,
        "bvconcat",
        &format!("resulting bitvector width overflows u32: {} + {}", w, 1),
    );
}

#[test]
#[timeout(5000)]
fn test_try_bvzeroext_rejects_width_overflow() {
    let mut solver = Solver::new(Logic::QfBv);
    let w = u32::MAX;
    let a = solver.declare_const("a", Sort::bitvec(w));

    let err = solver.try_bvzeroext(a, 1).unwrap_err();
    assert_invalid_argument(
        err,
        "bvzeroext",
        &format!("resulting bitvector width overflows u32: {} + {}", w, 1),
    );
}

#[test]
#[timeout(5000)]
fn test_try_bvsignext_rejects_width_overflow() {
    let mut solver = Solver::new(Logic::QfBv);
    let w = u32::MAX;
    let a = solver.declare_const("a", Sort::bitvec(w));

    let err = solver.try_bvsignext(a, 1).unwrap_err();
    assert_invalid_argument(
        err,
        "bvsignext",
        &format!("resulting bitvector width overflows u32: {} + {}", w, 1),
    );
}

#[test]
#[timeout(5000)]
fn test_try_bvrepeat_rejects_width_overflow() {
    let mut solver = Solver::new(Logic::QfBv);
    let w = u32::MAX;
    let a = solver.declare_const("a", Sort::bitvec(w));

    let err = solver.try_bvrepeat(a, 2).unwrap_err();
    assert_invalid_argument(
        err,
        "bvrepeat",
        &format!("resulting bitvector width overflows u32: {} * {}", w, 2),
    );
}

#[test]
#[timeout(5000)]
fn test_try_bvrepeat_rejects_zero_repeat_count() {
    let mut solver = Solver::new(Logic::QfBv);
    let a = solver.declare_const("a", Sort::bitvec(1));

    let err = solver.try_bvrepeat(a, 0).unwrap_err();
    assert_invalid_argument(err, "bvrepeat", "repeat count (0) must be > 0");
}

#[test]
#[timeout(5000)]
fn test_try_bvconcat_allows_u32_max_width() {
    let mut solver = Solver::new(Logic::QfBv);
    let a = solver.declare_const("a", Sort::bitvec(u32::MAX - 1));
    let b = solver.declare_const("b", Sort::bitvec(1));

    let ab = solver.try_bvconcat(a, b).unwrap();
    let c = solver.declare_const("c", Sort::bitvec(1));
    let err = solver.try_bvconcat(ab, c).unwrap_err();
    assert_invalid_argument(
        err,
        "bvconcat",
        &format!(
            "resulting bitvector width overflows u32: {} + {}",
            u32::MAX,
            1
        ),
    );
}

#[test]
#[timeout(5000)]
fn test_try_bvzeroext_allows_u32_max_width() {
    let mut solver = Solver::new(Logic::QfBv);
    let a = solver.declare_const("a", Sort::bitvec(u32::MAX - 1));

    let a_max = solver.try_bvzeroext(a, 1).unwrap();
    let err = solver.try_bvzeroext(a_max, 1).unwrap_err();
    assert_invalid_argument(
        err,
        "bvzeroext",
        &format!(
            "resulting bitvector width overflows u32: {} + {}",
            u32::MAX,
            1
        ),
    );
}

#[test]
#[timeout(5000)]
fn test_try_bvsignext_allows_u32_max_width() {
    let mut solver = Solver::new(Logic::QfBv);
    let a = solver.declare_const("a", Sort::bitvec(u32::MAX - 1));

    let a_max = solver.try_bvsignext(a, 1).unwrap();
    let err = solver.try_bvsignext(a_max, 1).unwrap_err();
    assert_invalid_argument(
        err,
        "bvsignext",
        &format!(
            "resulting bitvector width overflows u32: {} + {}",
            u32::MAX,
            1
        ),
    );
}

#[test]
#[timeout(5000)]
fn test_try_bvrepeat_allows_u32_max_width() {
    let mut solver = Solver::new(Logic::QfBv);
    let a = solver.declare_const("a", Sort::bitvec(u32::MAX));

    let a_max = solver.try_bvrepeat(a, 1).unwrap();
    let err = solver.try_bvrepeat(a_max, 2).unwrap_err();
    assert_invalid_argument(
        err,
        "bvrepeat",
        &format!(
            "resulting bitvector width overflows u32: {} * {}",
            u32::MAX,
            2
        ),
    );
}

#[test]
#[timeout(5000)]
fn test_bvconcat_panics_on_width_overflow() {
    assert_panics_containing_all(
        || {
            let mut solver = Solver::new(Logic::QfBv);
            let a = solver.declare_const("a", Sort::bitvec(u32::MAX));
            let b = solver.declare_const("b", Sort::bitvec(1));
            let _ = solver.bvconcat(a, b);
        },
        &["invalid argument to bvconcat", "overflows u32"],
    );
}

#[test]
#[timeout(5000)]
fn test_bvzeroext_panics_on_width_overflow() {
    assert_panics_containing_all(
        || {
            let mut solver = Solver::new(Logic::QfBv);
            let a = solver.declare_const("a", Sort::bitvec(u32::MAX));
            let _ = solver.bvzeroext(a, 1);
        },
        &["invalid argument to bvzeroext", "overflows u32"],
    );
}

#[test]
#[timeout(5000)]
fn test_bvsignext_panics_on_width_overflow() {
    assert_panics_containing_all(
        || {
            let mut solver = Solver::new(Logic::QfBv);
            let a = solver.declare_const("a", Sort::bitvec(u32::MAX));
            let _ = solver.bvsignext(a, 1);
        },
        &["invalid argument to bvsignext", "overflows u32"],
    );
}

#[test]
#[timeout(5000)]
fn test_bvrepeat_panics_on_width_overflow() {
    assert_panics_containing_all(
        || {
            let mut solver = Solver::new(Logic::QfBv);
            let a = solver.declare_const("a", Sort::bitvec(u32::MAX));
            let _ = solver.bvrepeat(a, 2);
        },
        &["invalid argument to bvrepeat", "overflows u32"],
    );
}

#[test]
#[timeout(5000)]
fn test_try_bvadd_no_overflow_unsigned_builds_at_max_width() {
    // The unsigned bvadd-no-overflow encoding stays at the OPERAND width
    // (`bvuge(bvadd(a, b), a)`) instead of zero-extending by one bit, so it
    // introduces no wider intermediate and therefore has NO u32 width-overflow
    // failure mode — it builds even at w = u32::MAX. (The old +1-extension
    // encoding overflowed here, but it also made u64/usize add-overflow checks
    // silently return `unknown`; see api/bitvectors/overflow.rs. Width growth
    // that genuinely overflows u32 only affects bvmul/concat/repeat, which keep
    // their own rejection tests below.)
    let mut solver = Solver::new(Logic::QfBv);
    let w = u32::MAX;
    let a = solver.declare_const("a", Sort::bitvec(w));
    let b = solver.declare_const("b", Sort::bitvec(w));

    assert!(
        solver.try_bvadd_no_overflow(a, b, false).is_ok(),
        "same-width unsigned bvadd_no_overflow must build at u32::MAX width"
    );
}

#[test]
#[timeout(5000)]
fn test_try_bvmul_no_overflow_rejects_width_overflow() {
    let mut solver = Solver::new(Logic::QfBv);
    let w = (u32::MAX / 2) + 1;
    let a = solver.declare_const("a", Sort::bitvec(w));
    let b = solver.declare_const("b", Sort::bitvec(w));

    let err = solver.try_bvmul_no_overflow(a, b, true).unwrap_err();
    assert_invalid_argument(
        err,
        "bvmul_no_overflow",
        &format!("resulting bitvector width overflows u32: {w} * 2"),
    );
}

#[test]
#[timeout(5000)]
fn test_try_bvneg_no_overflow_rejects_zero_width() {
    let mut solver = Solver::new(Logic::QfBv);
    let a = solver.declare_const("a", Sort::bitvec(0));

    let err = solver.try_bvneg_no_overflow(a).unwrap_err();
    assert_invalid_argument(err, "bvneg_no_overflow", "bitvector width (0) must be > 0");
}

#[test]
#[timeout(5000)]
fn test_try_bvsub_no_overflow_rejects_zero_width() {
    let mut solver = Solver::new(Logic::QfBv);
    let a = solver.declare_const("a", Sort::bitvec(0));
    let b = solver.declare_const("b", Sort::bitvec(0));

    let err = solver.try_bvsub_no_overflow(a, b).unwrap_err();
    assert_invalid_argument(err, "bvsub_no_overflow", "bitvector width (0) must be > 0");
}

#[test]
#[timeout(5000)]
fn test_try_bvsdiv_no_overflow_rejects_zero_width() {
    let mut solver = Solver::new(Logic::QfBv);
    let a = solver.declare_const("a", Sort::bitvec(0));
    let b = solver.declare_const("b", Sort::bitvec(0));

    let err = solver.try_bvsdiv_no_overflow(a, b).unwrap_err();
    assert_invalid_argument(err, "bvsdiv_no_overflow", "bitvector width (0) must be > 0");
}

#[test]
#[timeout(5000)]
fn test_try_bvmul_no_underflow_rejects_width_overflow() {
    let mut solver = Solver::new(Logic::QfBv);
    let w = (u32::MAX / 2) + 1;
    let a = solver.declare_const("a", Sort::bitvec(w));
    let b = solver.declare_const("b", Sort::bitvec(w));

    let err = solver.try_bvmul_no_underflow(a, b).unwrap_err();
    assert_invalid_argument(
        err,
        "bvmul_no_underflow",
        &format!("resulting bitvector width overflows u32: {w} * 2"),
    );
}
