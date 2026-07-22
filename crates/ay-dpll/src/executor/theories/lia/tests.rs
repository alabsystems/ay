// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use crate::Executor;
use ay_frontend::parse;

fn run_script(input: &str) -> Vec<String> {
    let commands = parse(input).expect("SMT-LIB script should parse");
    let mut exec = Executor::new();
    exec.execute_all(&commands)
        .expect("SMT-LIB script should execute")
}

// --- Core check-sat path tests ---

#[test]
fn lia_sat_simple_bound() {
    let input = r#"
        (set-logic QF_LIA)
        (declare-const x Int)
        (assert (>= x 0))
        (assert (<= x 10))
        (check-sat)
    "#;
    assert_eq!(run_script(input), vec!["sat"]);
}

#[test]
fn lia_unsat_contradictory_bounds() {
    let input = r#"
        (set-logic QF_LIA)
        (declare-const x Int)
        (assert (> x 5))
        (assert (< x 5))
        (check-sat)
    "#;
    assert_eq!(run_script(input), vec!["unsat"]);
}

#[test]
fn lia_sat_equality() {
    let input = r#"
        (set-logic QF_LIA)
        (declare-const x Int)
        (assert (= x 42))
        (check-sat)
    "#;
    assert_eq!(run_script(input), vec!["sat"]);
}

#[test]
fn lia_unsat_equality_with_disequality() {
    let input = r#"
        (set-logic QF_LIA)
        (declare-const x Int)
        (assert (= x 5))
        (assert (distinct x 5))
        (check-sat)
    "#;
    assert_eq!(run_script(input), vec!["unsat"]);
}

#[test]
fn lia_empty_assertions_sat() {
    let input = r#"
        (set-logic QF_LIA)
        (declare-const x Int)
        (check-sat)
    "#;
    assert_eq!(run_script(input), vec!["sat"]);
}

#[test]
fn lia_sat_branch_and_bound() {
    // Requires branch-and-bound: fractional relaxation exists but integer solution needed
    let input = r#"
        (set-logic QF_LIA)
        (declare-const x Int)
        (declare-const y Int)
        (assert (>= (+ x y) 3))
        (assert (<= x 2))
        (assert (<= y 2))
        (assert (>= x 0))
        (assert (>= y 0))
        (check-sat)
    "#;
    assert_eq!(run_script(input), vec!["sat"]);
}

#[test]
fn lia_unsat_no_integer_in_range() {
    // x > 0 and x < 1 has no integer solutions
    let input = r#"
        (set-logic QF_LIA)
        (declare-const x Int)
        (assert (> x 0))
        (assert (< x 1))
        (check-sat)
    "#;
    // LIA: strictly between 0 and 1 has no integer, should be unsat
    assert_eq!(run_script(input), vec!["unsat"]);
}

// --- Incremental / push-pop tests ---

#[test]
fn incremental_lia_push_pop_roundtrip() {
    let input = r#"
        (set-logic QF_LIA)
        (declare-const x Int)
        (assert (= x 0))
        (push 1)
        (assert (> x 0))
        (check-sat)
        (pop 1)
        (check-sat)
    "#;

    assert_eq!(run_script(input), vec!["unsat", "sat"]);
}

/// Regression test for #2822: same activation-scope bug as LRA affects all
/// theory solvers sharing IncrementalTheoryState. After pop+push, scoped
/// activation clauses for global assertions were not re-added.
#[test]
fn incremental_lia_contradiction_after_push_pop_cycle() {
    let input = r#"
        (set-logic QF_LIA)
        (declare-const x Int)
        (assert (>= x 0))
        (assert (<= x 5))
        (push 1)
        (assert (> x 3))
        (check-sat)
        (pop 1)
        (push 1)
        (assert (> x 5))
        (check-sat)
        (pop 1)
    "#;
    let result = run_script(input);
    assert_eq!(
        result,
        vec!["sat", "unsat"],
        "x<=5 and x>5 should be UNSAT after push/pop cycle, got {result:?}"
    );
}

#[test]
fn incremental_lia_nested_push_pop() {
    let input = r#"
        (set-logic QF_LIA)
        (declare-const x Int)
        (assert (>= x 0))
        (push 1)
        (assert (<= x 10))
        (push 1)
        (assert (> x 10))
        (check-sat)
        (pop 1)
        (check-sat)
        (pop 1)
        (check-sat)
    "#;
    assert_eq!(run_script(input), vec!["unsat", "sat", "sat"]);
}

#[test]
fn incremental_lia_multiple_check_sats_same_scope() {
    let input = r#"
        (set-logic QF_LIA)
        (declare-const x Int)
        (assert (>= x 0))
        (push 1)
        (check-sat)
        (assert (< x 0))
        (check-sat)
        (pop 1)
        (check-sat)
    "#;
    assert_eq!(run_script(input), vec!["sat", "unsat", "sat"]);
}

#[test]
fn incremental_lia_empty_assertions_are_sat() {
    let input = r#"
        (set-logic QF_LIA)
        (declare-const x Int)
        (push 1)
        (check-sat)
        (pop 1)
        (check-sat)
    "#;

    assert_eq!(run_script(input), vec!["sat", "sat"]);
}

#[test]
fn incremental_qf_auflia_pure_bool_push_routes_propositional() {
    let input = r#"
        (set-logic QF_AUFLIA)
        (declare-const b_current Bool)
        (declare-const b_final Bool)
        (declare-const old_b_current Bool)
        (declare-const b_current_final Bool)
        (declare-const unused_int Int)
        (assert (= b_final (not b_current)))
        (assert (= old_b_current b_current))
        (assert (= b_current_final (not b_current)))
        (push 1)
        (assert (not (= b_final old_b_current)))
        (check-sat)
        (pop 1)
    "#;

    assert_eq!(run_script(input), vec!["sat"]);
}

#[test]
fn incremental_qf_auflia_unused_declarations_pure_lia_push_routes_lia() {
    let input = r#"
        (set-logic QF_AUFLIA)
        (declare-datatype Env ((mk-env (slot Int))))
        (declare-const c Env)
        (declare-fun closure_postcondition_mut (Env Env Int) Bool)
        (declare-const x Int)
        (declare-const x_final Int)
        (assert (= x_final (+ x 1)))
        (push 1)
        (check-sat)
        (pop 1)
    "#;

    assert_eq!(run_script(input), vec!["sat"]);
}

/// #6661: mod by constant now handled by incremental path
#[test]
fn lia_mod_by_constant_sat() {
    let input = r#"
        (set-logic QF_LIA)
        (declare-const x Int)
        (assert (= (mod x 3) 0))
        (assert (>= x 1))
        (assert (<= x 10))
        (check-sat)
    "#;
    assert_eq!(run_script(input), vec!["sat"]);
}

/// #6661: div by constant now handled by incremental path
#[test]
fn lia_div_by_constant_unsat() {
    let input = r#"
        (set-logic QF_LIA)
        (declare-const x Int)
        (assert (= (div x 2) 3))
        (assert (< x 6))
        (assert (> x 7))
        (check-sat)
    "#;
    assert_eq!(run_script(input), vec!["unsat"]);
}

/// #6661: equality substitution now handled by incremental path
#[test]
fn lia_int_equality_substitution_sat() {
    let input = r#"
        (set-logic QF_LIA)
        (declare-const x Int)
        (declare-const y Int)
        (assert (= y (+ x 1)))
        (assert (>= y 5))
        (assert (<= x 10))
        (check-sat)
    "#;
    assert_eq!(run_script(input), vec!["sat"]);
}

/// #6661: push/pop LIA still solves mod/div formulas correctly.
#[test]
fn incremental_lia_mod_div_push_pop() {
    let input = r#"
        (set-logic QF_LIA)
        (declare-const x Int)
        (assert (>= x 0))
        (assert (<= x 20))
        (push 1)
        (assert (= (mod x 5) 0))
        (assert (= (div x 5) 3))
        (check-sat)
        (pop 1)
        (push 1)
        (assert (= (mod x 7) 0))
        (assert (<= x 7))
        (check-sat)
        (pop 1)
    "#;
    assert_eq!(run_script(input), vec!["sat", "sat"]);
}

/// #6661: push/pop LIA still solves equality-substitution formulas correctly.
#[test]
fn incremental_lia_equality_subst_push_pop() {
    let input = r#"
        (set-logic QF_LIA)
        (declare-const x Int)
        (declare-const y Int)
        (assert (>= x 0))
        (push 1)
        (assert (= y (+ x 1)))
        (assert (= y 5))
        (check-sat)
        (pop 1)
        (push 1)
        (assert (= y (* x 2)))
        (assert (= y 8))
        (check-sat)
        (pop 1)
    "#;
    assert_eq!(run_script(input), vec!["sat", "sat"]);
}

#[test]
fn incremental_lia_mod_div_uses_persistent_solver_state() {
    let input = r#"
        (set-logic QF_LIA)
        (declare-const x Int)
        (push 1)
        (assert (= (mod x 5) 0))
        (assert (= (div x 5) 3))
        (check-sat)
    "#;

    let commands = parse(input).expect("SMT-LIB script should parse");
    let mut exec = Executor::new();
    // White-box probe of the LAZY incremental arm's persistent SAT state;
    // pin lazy routing (Fix B1 routes incremental sessions eager by default,
    // solving on a discarded temporary state).
    exec.lia_incremental_eager_override = Some(false);
    assert_eq!(
        exec.execute_all(&commands)
            .expect("SMT-LIB script should execute"),
        vec!["sat"]
    );

    let state = exec
        .incr_theory_state
        .as_ref()
        .expect("incremental LIA solve should initialize theory state");
    assert!(
        state.lia_persistent_sat.is_some(),
        "native incremental LIA path must retain a persistent SAT solver for mod/div formulas"
    );
    assert!(
        !state.lia_derived_assertions.is_empty(),
        "mod/div preprocessing should register derived assertion metadata"
    );
}

#[test]
fn incremental_lia_equality_subst_uses_persistent_solver_state() {
    let input = r#"
        (set-logic QF_LIA)
        (declare-const x Int)
        (declare-const y Int)
        (push 1)
        (assert (= y (+ x 1)))
        (assert (= y 5))
        (check-sat)
    "#;

    let commands = parse(input).expect("SMT-LIB script should parse");
    let mut exec = Executor::new();
    // White-box probe of the LAZY incremental arm's persistent SAT state;
    // pin lazy routing (Fix B1 routes incremental sessions eager by default,
    // solving on a discarded temporary state).
    exec.lia_incremental_eager_override = Some(false);
    assert_eq!(
        exec.execute_all(&commands)
            .expect("SMT-LIB script should execute"),
        vec!["sat"]
    );

    let state = exec
        .incr_theory_state
        .as_ref()
        .expect("incremental LIA solve should initialize theory state");
    assert!(
        state.lia_persistent_sat.is_some(),
        "native incremental LIA path must retain a persistent SAT solver for equality substitution"
    );
    assert!(
        !state.lia_derived_assertions.is_empty(),
        "equality substitution should register derived assertion metadata"
    );
}

// --- Fix B1: eager routing for incremental (push/pop) sessions ---

/// Default routing sends incremental QF_LIA check-sats through the eager
/// BCP-interleaved arm on a TEMPORARY isolated state (Fix B1): the session's
/// persistent `lia_persistent_sat` stays unpopulated because the temp state
/// is discarded after each solve.
#[test]
fn incremental_lia_eager_routing_solves_on_discarded_temp_state() {
    let input = r#"
        (set-logic QF_LIA)
        (declare-const x Int)
        (declare-const y Int)
        (assert (>= x 0))
        (push 1)
        (assert (= y (+ x 1)))
        (assert (< y 0))
        (check-sat)
        (pop 1)
        (push 1)
        (assert (= y (+ x 1)))
        (assert (= y 5))
        (check-sat)
    "#;

    let commands = parse(input).expect("SMT-LIB script should parse");
    let mut exec = Executor::new();
    assert_eq!(
        exec.execute_all(&commands)
            .expect("SMT-LIB script should execute"),
        vec!["unsat", "sat"]
    );

    let state = exec
        .incr_theory_state
        .as_ref()
        .expect("incremental LIA solve should initialize theory state");
    assert!(
        state.lia_persistent_sat.is_none(),
        "eager-routed incremental LIA must solve on a discarded temporary \
         state, leaving the session's lazy-arm SAT solver unpopulated"
    );
}

/// Push/pop retraction correctness under default (eager) incremental routing:
/// constraints asserted inside a popped scope must not leak into later
/// check-sats, and scope-depth bookkeeping on the session state must survive
/// the temp-state swap.
#[test]
fn incremental_lia_eager_routing_push_pop_retraction() {
    let input = r#"
        (set-logic QF_LIA)
        (declare-const x Int)
        (assert (>= x 0))
        (check-sat)
        (push 1)
        (assert (< x 0))
        (check-sat)
        (pop 1)
        (check-sat)
        (push 1)
        (assert (<= x 3))
        (assert (>= x 3))
        (check-sat)
        (pop 1)
    "#;
    assert_eq!(run_script(input), vec!["sat", "unsat", "sat", "sat"]);
}

/// Proof-producing sessions must stay on the lazy arm (eager-incremental
/// proof artifacts are not validated yet): the lazy arm populates the
/// session's persistent `lia_persistent_sat`.
#[test]
fn incremental_lia_proof_sessions_stay_on_lazy_arm() {
    let input = r#"
        (set-logic QF_LIA)
        (set-option :produce-proofs true)
        (declare-const x Int)
        (push 1)
        (assert (>= x 0))
        (assert (< x 0))
        (check-sat)
    "#;

    let commands = parse(input).expect("SMT-LIB script should parse");
    let mut exec = Executor::new();
    assert_eq!(
        exec.execute_all(&commands)
            .expect("SMT-LIB script should execute"),
        vec!["unsat"]
    );

    let state = exec
        .incr_theory_state
        .as_ref()
        .expect("incremental LIA solve should initialize theory state");
    assert!(
        state.lia_persistent_sat.is_some(),
        "proof-producing incremental sessions must keep the lazy arm \
         (which retains the session's persistent SAT solver)"
    );
}

// --- check-sat-assuming with Boolean-structured LIA assumptions ---

#[test]
fn lia_check_sat_assuming_implication_sat() {
    let input = r#"
        (set-logic QF_LIA)
        (declare-const act Bool)
        (declare-const x Int)
        (assert (=> act (< x 0)))
        (assert (=> act (> x (- 10))))
        (check-sat-assuming (act))
    "#;
    let result = run_script(input);
    assert_eq!(
        result,
        vec!["sat"],
        "implication assumption should be SAT, got {result:?}"
    );
}

#[test]
fn lia_check_sat_assuming_negated_activation_sat() {
    let input = r#"
        (set-logic QF_LIA)
        (declare-const act Bool)
        (declare-const x Int)
        (assert (=> act (< x 0)))
        (assert (=> act (> x (- 10))))
        (check-sat-assuming ((not act)))
    "#;
    let result = run_script(input);
    assert_eq!(
        result,
        vec!["sat"],
        "negated activation should be SAT, got {result:?}"
    );
}

#[test]
fn lia_check_sat_assuming_conjunction_assumption_sat() {
    let input = r#"
        (set-logic QF_LIA)
        (declare-const act Bool)
        (declare-const x Int)
        (assert (< x 100))
        (assert (=> act (and (< x 0) (> x (- 10)))))
        (check-sat-assuming (act))
    "#;
    let result = run_script(input);
    assert_eq!(
        result,
        vec!["sat"],
        "conjunction under implication should be SAT, got {result:?}"
    );
}

#[test]
fn lia_check_sat_assuming_implication_unsat() {
    let input = r#"
        (set-logic QF_LIA)
        (declare-const act Bool)
        (declare-const x Int)
        (assert (> x 5))
        (assert (=> act (< x 0)))
        (check-sat-assuming (act))
    "#;
    let result = run_script(input);
    assert_eq!(
        result,
        vec!["unsat"],
        "contradictory implication should be UNSAT, got {result:?}"
    );
}

#[test]
fn lia_check_sat_assuming_bare_atom_sat() {
    let input = r#"
        (set-logic QF_LIA)
        (declare-const x Int)
        (assert (> x 0))
        (assert (< x 10))
        (check-sat-assuming ((> x 3)))
    "#;
    let result = run_script(input);
    assert_eq!(
        result,
        vec!["sat"],
        "bare atom assumption should be SAT, got {result:?}"
    );
}

#[test]
fn lia_check_sat_assuming_bmc_style_activation_sat() {
    let input = r#"
        (set-logic QF_LIA)
        (declare-const act0 Bool)
        (declare-const act1 Bool)
        (declare-const x0 Int)
        (declare-const x1 Int)
        (assert (=> act0 (and (>= x0 0) (<= x0 10))))
        (assert (=> act1 (and (= x1 (+ x0 1)) (>= x1 0))))
        (check-sat-assuming (act0 act1))
    "#;
    let result = run_script(input);
    assert_eq!(
        result,
        vec!["sat"],
        "BMC-style activation pattern should be SAT, got {result:?}"
    );
}

#[test]
fn lia_check_sat_assuming_bmc_style_activation_unsat() {
    let input = r#"
        (set-logic QF_LIA)
        (declare-const act0 Bool)
        (declare-const act1 Bool)
        (declare-const x0 Int)
        (declare-const x1 Int)
        (assert (=> act0 (> x0 100)))
        (assert (=> act1 (and (= x1 (+ x0 1)) (< x1 50))))
        (check-sat-assuming (act0 act1))
    "#;
    let result = run_script(input);
    assert_eq!(
        result,
        vec!["unsat"],
        "contradictory BMC activation should be UNSAT, got {result:?}"
    );
}

#[test]
fn lia_check_sat_assuming_or_in_assumption() {
    let input = r#"
        (set-logic QF_LIA)
        (declare-const x Int)
        (assert (>= x 0))
        (assert (<= x 100))
        (check-sat-assuming ((or (< x 5) (> x 95))))
    "#;
    let result = run_script(input);
    assert_eq!(
        result,
        vec!["sat"],
        "OR in assumption should be SAT, got {result:?}"
    );
}

#[test]
fn lia_check_sat_assuming_nested_boolean_structure() {
    // Deeply nested Boolean structure with LIA atoms
    let input = r#"
        (set-logic QF_LIA)
        (declare-const x Int)
        (declare-const y Int)
        (declare-const z Int)
        (assert (>= x 0))
        (assert (>= y 0))
        (assert (>= z 0))
        (check-sat-assuming ((and (or (< x 5) (< y 5)) (> (+ x y z) 2))))
    "#;
    let result = run_script(input);
    assert_eq!(
        result,
        vec!["sat"],
        "nested Boolean structure in assumption should be SAT, got {result:?}"
    );
}

#[test]
fn lia_check_sat_assuming_nested_boolean_structure_debug() {
    let input = r#"
        (set-logic QF_LIA)
        (declare-const x Int)
        (declare-const y Int)
        (declare-const z Int)
        (assert (>= x 0))
        (assert (>= y 0))
        (assert (>= z 0))
        (check-sat-assuming ((and (or (< x 5) (< y 5)) (> (+ x y z) 2))))
    "#;
    let commands = parse(input).expect("parse");
    let mut exec = Executor::new();
    let result = exec.execute_all(&commands).expect("execute");
    eprintln!("result: {result:?}");
    eprintln!("last_unknown_reason: {:?}", exec.get_reason_unknown());
    eprintln!("last_model: {:?}", exec.last_model);
    eprintln!("last_model_validated: {:?}", exec.last_model_validated);
    assert_eq!(result, vec!["sat"], "got {result:?}");
}

#[test]
fn lia_check_sat_assuming_multiple_check_with_activation() {
    let input = r#"
        (set-logic QF_LIA)
        (declare-const act Bool)
        (declare-const x Int)
        (assert (=> act (< x 0)))
        (assert (> x 5))
        (check-sat-assuming (act))
        (check-sat-assuming ((not act)))
    "#;
    let result = run_script(input);
    assert_eq!(
        result,
        vec!["unsat", "sat"],
        "first query should be UNSAT, second should be SAT, got {result:?}"
    );
}
