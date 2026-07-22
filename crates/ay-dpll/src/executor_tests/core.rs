// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Core executor tests - basic SAT/UNSAT, push/pop, multiple check-sat

use std::time::Duration;

use crate::{Executor, UnknownReason};
use ay_frontend::parse;
use ay_frontend::sexp::parse_sexp;

#[test]
fn test_executor_simple_sat() {
    let input = r#"
        (set-logic QF_UF)
        (declare-const a Bool)
        (declare-const b Bool)
        (assert (or a b))
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs, vec!["sat"]);
}

#[test]
fn test_executor_set_timeout_allows_fast_sat() {
    let input = r#"
        (set-logic QF_UF)
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let timeout = Duration::from_secs(1);
    exec.set_timeout(Some(timeout));

    assert_eq!(exec.timeout(), Some(timeout));
    assert_eq!(exec.execute_all(&commands).unwrap(), vec!["sat"]);
    assert_eq!(exec.unknown_reason(), None);
}

#[test]
fn test_executor_timeout_returns_unknown_with_reason() {
    let input = r#"
        (set-logic QF_UF)
        (check-sat)
        (get-info :reason-unknown)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    exec.set_timeout(Some(Duration::ZERO));

    let outputs = exec.execute_all(&commands).unwrap();
    assert_eq!(outputs, vec!["unknown", "(:reason-unknown timeout)"]);
    assert_eq!(exec.unknown_reason(), Some(UnknownReason::Timeout));
}

#[test]
fn test_executor_timeout_can_be_cleared_for_later_solves() {
    let commands = parse("(check-sat)").unwrap();
    let mut exec = Executor::new();
    exec.set_timeout(Some(Duration::ZERO));

    assert_eq!(exec.execute_all(&commands).unwrap(), vec!["unknown"]);
    assert_eq!(exec.unknown_reason(), Some(UnknownReason::Timeout));

    exec.set_timeout(None);
    assert_eq!(exec.timeout(), None);
    assert_eq!(exec.execute_all(&commands).unwrap(), vec!["sat"]);
    assert_eq!(exec.unknown_reason(), None);
}

#[test]
fn test_executor_timeout_applies_to_check_sat_assuming() {
    let input = r#"
        (set-logic QF_UF)
        (declare-const p Bool)
        (check-sat-assuming (p))
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    exec.set_timeout(Some(Duration::ZERO));

    assert_eq!(exec.execute_all(&commands).unwrap(), vec!["unknown"]);
    assert_eq!(exec.unknown_reason(), Some(UnknownReason::Timeout));
}

#[test]
fn test_executor_set_option_timeout_installs_wall_clock_bound() {
    // Regression: the SetOption handler used to process only :random-seed and
    // silently drop :timeout, so `(set-option :timeout ms)` never reached
    // set_timeout. Callers that configure a timeout purely through SMT-LIB —
    // notably ay-chc's PdrExecutorBackend on the PDR path — then got no
    // deadline, and a diverging nonlinear-integer split loop (solve_nia -> SAT)
    // ran forever ignoring the wall-clock bound. The option must install a
    // bound exactly like the Rust-level set_timeout API.
    let mut exec = Executor::new();
    assert_eq!(exec.timeout(), None);

    exec.execute_all(&parse("(set-option :timeout 1500)").unwrap())
        .unwrap();
    assert_eq!(exec.timeout(), Some(Duration::from_millis(1500)));

    // 0 means "no timeout" (Z3 convention) — it clears any installed bound.
    exec.execute_all(&parse("(set-option :timeout 0)").unwrap())
        .unwrap();
    assert_eq!(exec.timeout(), None);
}

#[test]
fn test_executor_set_option_timeout_zero_forces_unknown_path_disabled() {
    // A positive `:timeout` followed by a 0 clears the bound, so a trivially
    // satisfiable query solves normally rather than tripping a stale deadline.
    let mut exec = Executor::new();
    exec.execute_all(&parse("(set-option :timeout 5000)").unwrap())
        .unwrap();
    exec.execute_all(&parse("(set-option :timeout 0)").unwrap())
        .unwrap();
    assert_eq!(exec.timeout(), None);
    assert_eq!(
        exec.execute_all(&parse("(set-logic QF_UF)\n(check-sat)").unwrap())
            .unwrap(),
        vec!["sat"]
    );
    assert_eq!(exec.unknown_reason(), None);
}

#[test]
fn test_executor_set_option_rlimit_installs_conflict_budget() {
    // Regression (#8749): the SetOption handler used to drop `:rlimit`
    // silently, exactly like `:timeout` before it was wired. `:rlimit`
    // installs a *deterministic* (conflict-count) budget — machine-independent,
    // so a verification run stops at the same point on every host. The option
    // must reach set_resource_limit, and `0` must clear it (Z3 convention).
    let mut exec = Executor::new();
    assert_eq!(exec.resource_limit(), None);

    exec.execute_all(&parse("(set-option :rlimit 5000)").unwrap())
        .unwrap();
    assert_eq!(exec.resource_limit(), Some(5000));

    exec.execute_all(&parse("(set-option :rlimit 0)").unwrap())
        .unwrap();
    assert_eq!(exec.resource_limit(), None);
}

#[test]
fn test_executor_set_option_max_memory_installs_rss_ceiling() {
    // Regression (#8749): `:max-memory` was parsed and silently dropped, the
    // same bug class as `:timeout`/`:rlimit`. The value is megabytes (Z3
    // convention) and must reach set_memory_limit as a byte ceiling; `0` must
    // clear it.
    let mut exec = Executor::new();
    assert_eq!(exec.memory_limit(), None);

    exec.execute_all(&parse("(set-option :max-memory 512)").unwrap())
        .unwrap();
    assert_eq!(exec.memory_limit(), Some(512 * 1024 * 1024));

    exec.execute_all(&parse("(set-option :max-memory 0)").unwrap())
        .unwrap();
    assert_eq!(exec.memory_limit(), None);
}

#[test]
fn test_executor_max_memory_forces_unknown_with_memout() {
    // A 1 MB RSS ceiling is below any live process, so the bound is already
    // crossed when check-sat runs. The central abort check
    // (should_abort_theory_loop, hit before logic dispatch) must surface this
    // as a MemoryLimit unknown — the same boundary that enforces `:timeout`.
    let input = "(set-logic QF_UF)\n(set-option :max-memory 1)\n\
                 (check-sat)\n(get-info :reason-unknown)\n";
    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs, vec!["unknown", "(:reason-unknown memout)"]);
    assert_eq!(exec.unknown_reason(), Some(UnknownReason::MemoryLimit));
}

#[test]
fn test_executor_rlimit_forces_deterministic_resource_limit() {
    // A pigeonhole instance (8 pigeons, 7 holes) is UNSAT and exponentially
    // hard for resolution — preprocessing can't refute it, so the CDCL core
    // must perform real search and accrue conflicts. A tiny `:rlimit` conflict
    // budget must therefore halt the solve with a ResourceLimit unknown
    // *before* it proves UNSAT, and must do so deterministically (same outcome
    // regardless of wall-clock speed). This is the machine-independent
    // companion to the `:timeout` deadline. A smaller hole (4/3) gets refuted
    // by preprocessing with zero search conflicts and never trips the budget.
    const PIGEONS: u32 = 8;
    const HOLES: u32 = 7;
    let mut smt = String::from("(set-logic QF_UF)\n(set-option :rlimit 1)\n");
    for i in 1..=PIGEONS {
        for j in 1..=HOLES {
            smt.push_str(&format!("(declare-const p_{i}_{j} Bool)\n"));
        }
    }
    // Each pigeon occupies at least one hole.
    for i in 1..=PIGEONS {
        let lits: Vec<String> = (1..=HOLES).map(|j| format!("p_{i}_{j}")).collect();
        smt.push_str(&format!("(assert (or {}))\n", lits.join(" ")));
    }
    // No two pigeons share a hole.
    for j in 1..=HOLES {
        for i in 1..=PIGEONS {
            for k in (i + 1)..=PIGEONS {
                smt.push_str(&format!("(assert (or (not p_{i}_{j}) (not p_{k}_{j})))\n"));
            }
        }
    }
    smt.push_str("(check-sat)\n(get-info :reason-unknown)\n");

    let commands = parse(&smt).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs, vec!["unknown", "(:reason-unknown resourceout)"]);
    assert_eq!(exec.unknown_reason(), Some(UnknownReason::ResourceLimit));
}

/// Pigeonhole SMT text (n pigeons, m holes): UNSAT for n > m, exponentially
/// hard for resolution, immune to cheap preprocessing — forces real CDCL
/// search. Shared by the deterministic-budget tests below.
fn pigeonhole_smt(pigeons: u32, holes: u32, options: &str) -> String {
    let mut smt = format!("(set-logic QF_UF)\n{options}");
    for i in 1..=pigeons {
        for j in 1..=holes {
            smt.push_str(&format!("(declare-const p_{i}_{j} Bool)\n"));
        }
    }
    for i in 1..=pigeons {
        let lits: Vec<String> = (1..=holes).map(|j| format!("p_{i}_{j}")).collect();
        smt.push_str(&format!("(assert (or {}))\n", lits.join(" ")));
    }
    for j in 1..=holes {
        for i in 1..=pigeons {
            for k in (i + 1)..=pigeons {
                smt.push_str(&format!("(assert (or (not p_{i}_{j}) (not p_{k}_{j})))\n"));
            }
        }
    }
    smt.push_str("(check-sat)\n(get-info :reason-unknown)\n");
    smt
}

#[test]
fn test_default_ground_budget_active_and_overridable() {
    // #ground-determinism: a fresh executor arms every pipeline SAT solve
    // with the DEFAULT deterministic ground allowances (conflicts +
    // decisions); an explicit `:rlimit`/decision limit overrides the
    // corresponding axis; disabling the ground budget clears the defaults.
    let mut exec = Executor::new();
    assert_eq!(
        exec.effective_conflict_allowance(),
        Some(Executor::DEFAULT_GROUND_CONFLICT_ALLOWANCE)
    );
    assert_eq!(
        exec.effective_decision_allowance(),
        Some(Executor::DEFAULT_GROUND_DECISION_ALLOWANCE)
    );

    exec.set_resource_limit(Some(7));
    exec.set_decision_limit(Some(9));
    assert_eq!(exec.effective_conflict_allowance(), Some(7));
    assert_eq!(exec.effective_decision_allowance(), Some(9));

    exec.set_resource_limit(None);
    exec.set_decision_limit(None);
    exec.set_ground_budget_enabled(false);
    assert_eq!(exec.effective_conflict_allowance(), None);
    assert_eq!(exec.effective_decision_allowance(), None);
}

#[test]
fn test_executor_set_option_rlimit_zero_disables_default_ground_budget() {
    // `(set-option :rlimit 0)` must remain a TRUE opt-out to unbounded
    // solving: since the default ground budget landed, "no limit" also
    // means "no default budget".
    let mut exec = Executor::new();
    assert!(exec.ground_budget_enabled());

    exec.execute_all(&parse("(set-option :rlimit 0)").unwrap())
        .unwrap();
    assert!(!exec.ground_budget_enabled());
    assert_eq!(exec.effective_conflict_allowance(), None);
    assert_eq!(exec.effective_decision_allowance(), None);

    // A later nonzero `:rlimit` installs its explicit conflict budget (the
    // decision default stays off — the caller opted out of defaults).
    exec.execute_all(&parse("(set-option :rlimit 5000)").unwrap())
        .unwrap();
    assert_eq!(exec.effective_conflict_allowance(), Some(5000));
}

#[test]
fn test_executor_decision_limit_forces_deterministic_resource_limit() {
    // Decision-budget companion of
    // test_executor_rlimit_forces_deterministic_resource_limit: pigeonhole
    // search makes thousands of decisions, so a tiny DECISION budget must
    // halt the solve with a ResourceLimit unknown before it proves UNSAT —
    // the axis that bounds decision-heavy/conflict-light churn a conflict
    // budget cannot see (#ground-determinism).
    let smt = pigeonhole_smt(8, 7, "");
    let commands = parse(&smt).unwrap();
    let mut exec = Executor::new();
    exec.set_decision_limit(Some(50));
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs, vec!["unknown", "(:reason-unknown resourceout)"]);
    assert_eq!(exec.unknown_reason(), Some(UnknownReason::ResourceLimit));
}

#[test]
fn test_ground_budget_stop_point_is_deterministic() {
    // Identical inputs must do identical work: two fresh executors given the
    // same formula and the same tiny budget must stop at the SAME conflict
    // and decision counts (#ground-determinism constraint (a)).
    let smt = pigeonhole_smt(8, 7, "(set-option :rlimit 3)\n");
    let run = || {
        let commands = parse(&smt).unwrap();
        let mut exec = Executor::new();
        let outputs = exec.execute_all(&commands).unwrap();
        assert_eq!(outputs, vec!["unknown", "(:reason-unknown resourceout)"]);
        (exec.statistics().conflicts, exec.statistics().decisions)
    };
    let (c1, d1) = run();
    let (c2, d2) = run();
    assert_eq!(c1, c2, "conflict count at stop must be machine-independent");
    assert_eq!(d1, d2, "decision count at stop must be machine-independent");
    assert!(c1 >= 3, "the budget must have been the stopping cause");
}

#[test]
fn test_executor_simple_unsat() {
    let input = r#"
        (set-logic QF_UF)
        (declare-const a Bool)
        (assert a)
        (assert (not a))
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs, vec!["unsat"]);
}

#[test]
fn test_executor_optimize_maximize_qf_lia() {
    let input = r#"
        (set-logic QF_LIA)
        (declare-const x Int)
        (declare-const y Int)
        (assert (>= x 0))
        (assert (>= y 0))
        (assert (<= (+ x y) 10))
        (maximize (+ (* 2 x) y))
        (check-sat)
        (get-objectives)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs.first().map(String::as_str), Some("sat"));

    let sexp = parse_sexp(&outputs[1]).unwrap();
    let items = sexp.as_list().unwrap();
    assert_eq!(items[0].as_symbol(), Some("objectives"));
    assert_eq!(items.len(), 2);

    let pair = items[1].as_list().unwrap();
    assert_eq!(pair.len(), 2);
    assert_eq!(pair[1].as_numeral(), Some("20"));
}

#[test]
fn test_executor_optimize_maximize_qf_lra() {
    // Maximize x subject to 0 <= x <= 10.5. Optimal: x = 10.5 = 21/2.
    let input = r#"
        (set-logic QF_LRA)
        (declare-const x Real)
        (assert (>= x 0.0))
        (assert (<= x (/ 21 2)))
        (maximize x)
        (check-sat)
        (get-objectives)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs.first().map(String::as_str), Some("sat"));

    let sexp = parse_sexp(&outputs[1]).unwrap();
    let items = sexp.as_list().unwrap();
    assert_eq!(items[0].as_symbol(), Some("objectives"));
    assert_eq!(items.len(), 2);

    let pair = items[1].as_list().unwrap();
    assert_eq!(pair.len(), 2);
    // Optimal value is 21/2 = 10.5
    let val_str = format!("{}", pair[1]);
    assert!(
        val_str.contains("21") && val_str.contains("2"),
        "expected 21/2 (10.5), got: {val_str}"
    );
}

#[test]
fn test_executor_optimize_minimize_qf_lra() {
    // Minimize x subject to x >= 3.5. Optimal: x = 3.5 = 7/2.
    let input = r#"
        (set-logic QF_LRA)
        (declare-const x Real)
        (assert (>= x (/ 7 2)))
        (assert (<= x 100.0))
        (minimize x)
        (check-sat)
        (get-objectives)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs.first().map(String::as_str), Some("sat"));

    let sexp = parse_sexp(&outputs[1]).unwrap();
    let items = sexp.as_list().unwrap();
    assert_eq!(items[0].as_symbol(), Some("objectives"));
    assert_eq!(items.len(), 2);

    let pair = items[1].as_list().unwrap();
    assert_eq!(pair.len(), 2);
    // Optimal value is 7/2 = 3.5
    let val_str = format!("{}", pair[1]);
    assert!(
        val_str.contains("7") && val_str.contains("2"),
        "expected 7/2 (3.5), got: {val_str}"
    );
}

#[test]
fn test_executor_optimize_real_linear_combination() {
    // Maximize (+ (* (/ 3 1) x) (* (/ 2 1) y)) subject to x + y <= 10, x >= 0, y >= 0.
    // Optimal at vertex (10, 0): objective = 30.
    // Uses exact rational coefficients to avoid decimal-to-float precision loss.
    let input = r#"
        (set-logic QF_LRA)
        (declare-const x Real)
        (declare-const y Real)
        (assert (>= x (/ 0 1)))
        (assert (>= y (/ 0 1)))
        (assert (<= (+ x y) (/ 10 1)))
        (maximize (+ (* (/ 3 1) x) (* (/ 2 1) y)))
        (check-sat)
        (get-objectives)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs.first().map(String::as_str), Some("sat"));

    let sexp = parse_sexp(&outputs[1]).unwrap();
    let items = sexp.as_list().unwrap();
    assert_eq!(items[0].as_symbol(), Some("objectives"));
    assert_eq!(items.len(), 2);

    let pair = items[1].as_list().unwrap();
    assert_eq!(pair.len(), 2);
    // Optimal value is 30 (at x=10, y=0)
    let val_str = format!("{}", pair[1]);
    assert!(
        val_str == "30" || val_str.contains("30"),
        "expected 30, got: {val_str}"
    );
}

#[test]
fn test_executor_optimize_real_unsat() {
    // Infeasible constraints: x >= 5 and x <= 3.
    let input = r#"
        (set-logic QF_LRA)
        (declare-const x Real)
        (assert (>= x 5.0))
        (assert (<= x 3.0))
        (maximize x)
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs.first().map(String::as_str), Some("unsat"));
}

#[test]
fn test_executor_qf_nira_with_real_terms_returns_unknown() {
    let input = r#"
        (set-logic QF_NIRA)
        (declare-const x Real)
        (declare-const y Int)
        (assert (= (* x x) (to_real y)))
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs, vec!["unknown"]);
}

#[test]
fn test_executor_qf_nira_with_int_only_can_be_unsat() {
    let input = r#"
        (set-logic QF_NIRA)
        (declare-const x Int)
        (assert (> x 0))
        (assert (<= x 0))
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs, vec!["unsat"]);
}

#[test]
fn test_executor_euf_unsat() {
    let input = r#"
        (set-logic QF_UF)
        (declare-sort U 0)
        (declare-const a U)
        (declare-const b U)
        (declare-fun p (U) Bool)
        (assert (= a b))
        (assert (p a))
        (assert (not (p b)))
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs, vec!["unsat"]);
}

#[test]
fn test_executor_euf_sat() {
    let input = r#"
        (set-logic QF_UF)
        (declare-sort U 0)
        (declare-const a U)
        (declare-const b U)
        (declare-fun p (U) Bool)
        (assert (p a))
        (assert (not (p b)))
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs, vec!["sat"]);
}

// test_executor_eq_diamond20_unsat moved to integration test with watchdog (#1535)

#[test]
fn test_executor_euf_congruence() {
    let input = r#"
        (set-logic QF_UF)
        (declare-sort U 0)
        (declare-const a U)
        (declare-const b U)
        (declare-const c U)
        (assert (= a b))
        (assert (= b c))
        (assert (not (= a c)))
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs, vec!["unsat"]);
}

#[test]
fn test_executor_distinct() {
    let input = r#"
        (set-logic QF_UF)
        (declare-sort U 0)
        (declare-const a U)
        (declare-const b U)
        (assert (= a b))
        (assert (distinct a b))
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs, vec!["unsat"]);
}

#[test]
fn test_executor_multiple_check_sat() {
    let input = r#"
        (set-logic QF_UF)
        (declare-const a Bool)
        (assert a)
        (check-sat)
        (assert (not a))
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs, vec!["sat", "unsat"]);
}

#[test]
fn test_executor_push_pop() {
    let input = r#"
        (set-logic QF_UF)
        (declare-const a Bool)
        (assert a)
        (push 1)
        (assert (not a))
        (check-sat)
        (pop 1)
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    // After push + assert (not a), should be unsat
    // After pop, only a is asserted, should be sat
    assert_eq!(outputs, vec!["unsat", "sat"]);
}

#[test]
fn test_executor_no_logic() {
    // Should work with default logic (treated as QF_UF)
    let input = r#"
        (declare-const a Bool)
        (assert a)
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs, vec!["sat"]);
}

#[test]
fn executor_new_does_not_arm_process_global_memory_limit_under_test() {
    // Root-cause guard for the full-suite mass-failure: `Executor::new()` arms
    // the PROCESS-GLOBAL memory ceiling (`ay_sys::set_process_memory_limit`,
    // embedded default ~phys/8) for production embedders. In the unit-test
    // harness — one long-lived process running thousands of solver tests —
    // that global ceiling is tripped by the harness's AGGREGATE footprint, not
    // by the current solve: once the suite's cumulative allocator-retained
    // footprint crossed 95% of the 3 GiB embedded default (24 GiB host), every
    // subsequent solve in the process degraded to Unknown(MemoryLimit)
    // (~1200+ load-dependent failures that all pass in isolation). The arm is
    // therefore compiled out under cfg(test); tests that exercise memory-exit
    // paths use the thread-local `force_process_memory_exceeded_for_testing`
    // hook instead, which works with no limit armed.
    //
    // No ay-dpll lib test sets a process-wide limit, so this global read is
    // race-free within the suite.
    let _exec = Executor::new();
    assert_eq!(
        ay_sys::get_process_memory_limit(),
        0,
        "cfg(test) builds must not arm the process-global memory ceiling: \
         a shared ceiling couples every test through total-harness footprint \
         and mass-degrades solves to Unknown(MemoryLimit) under load"
    );
    assert!(
        !ay_sys::process_memory_exceeded(),
        "with no process limit armed, the process-wide memory gate must be inert in tests"
    );
}
