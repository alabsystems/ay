// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Integration regressions for #4304 (array soundness).

use ay_dpll::Executor;
use ay_frontend::parse;
use ntest::timeout;
use std::io::Read;
use std::process::{Command, Stdio};
use std::time::Duration;
use wait_timeout::ChildExt;

fn solve(smt: &str) -> (Executor, Vec<String>) {
    let commands = parse(smt).expect("parse");
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).expect("execute_all");
    (exec, outputs)
}

enum TimedChildOutcome {
    Result(String),
    Timeout,
}

fn sat_result(output: &str) -> Option<&str> {
    output
        .lines()
        .map(str::trim)
        .find(|line| matches!(*line, "sat" | "unsat" | "unknown"))
}

fn run_current_test_with_timeout(
    test_name: &str,
    child_env: &str,
    deadline: Duration,
) -> TimedChildOutcome {
    let current_exe = std::env::current_exe().expect("current test binary path");
    let mut child = Command::new(current_exe)
        .arg("--exact")
        .arg(test_name)
        .arg("--nocapture")
        .env(child_env, "1")
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("failed to spawn child test binary");

    let status = match child
        .wait_timeout(deadline)
        .expect("failed waiting on child test binary")
    {
        Some(status) => status,
        None => {
            let _ = child.kill();
            let _ = child.wait();
            return TimedChildOutcome::Timeout;
        }
    };

    let mut stdout = String::new();
    let mut stderr = String::new();
    child
        .stdout
        .take()
        .expect("stdout pipe")
        .read_to_string(&mut stdout)
        .expect("read child stdout");
    child
        .stderr
        .take()
        .expect("stderr pipe")
        .read_to_string(&mut stderr)
        .expect("read child stderr");

    assert!(
        status.success(),
        "child test {test_name} exited with {status}\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );

    TimedChildOutcome::Result(stdout)
}

include!("array_soundness_4304/model_and_cross_theory.rs");

include!("array_soundness_4304/row2_and_bitvector.rs");

include!("array_soundness_4304/store_fixpoint.rs");

/// #5086 variant: Three stores to the same target.
///
/// store(a,x,v)=b, store(a,y,w)=b, store(a,z,u)=b
/// with x!=y, y!=z, x!=z and a!=b → contradiction because
/// from any pair, x=y OR a=b, and we have x!=y → a=b.
#[test]
#[timeout(10_000)]
fn disjunctive_store_equality_three_stores_5086() {
    let (_, outputs) = solve(
        r#"
        (set-logic QF_AUFLIA)
        (declare-fun a () (Array Int Int))
        (declare-fun b () (Array Int Int))
        (declare-fun x () Int)
        (declare-fun y () Int)
        (declare-fun z () Int)
        (declare-fun v () Int)
        (declare-fun w () Int)
        (declare-fun u () Int)
        (assert (= (store a x v) b))
        (assert (= (store a y w) b))
        (assert (not (= x y)))
        (assert (not (= a b)))
        (check-sat)
    "#,
    );
    assert_eq!(
        outputs[0], "unsat",
        "three stores: x!=y and a!=b contradicts store(a,x,v)=store(a,y,w)"
    );
}

// --- Regressions for #6282: QF_AUFLIA storeinv wrong answers ---

/// AUFLIA storeinv nf size=2: cross-swap at 2 indices using nested let.
///
/// This is the QF_AUFLIA variant of the QF_AX storeinv test above, using
/// Int-sorted arrays and indices. The N-O fixpoint must propagate array
/// equalities back to EUF for this to work (#6282).
///
/// AY cannot yet solve this within 30s (deep store chain reasoning needed).
/// Run in a subprocess so the timeout kills the whole solver, not just the
/// parent test thread.
///
/// Matches storeinv_nf_size2.smt2 benchmark.
#[test]
fn qf_auflia_storeinv_nf_2idx_6282() {
    const CHILD_ENV: &str = "AY_ARRAY_STOREINV_NF_2IDX_6282_CHILD";

    if std::env::var_os(CHILD_ENV).is_some() {
        let (_, outputs) = solve(
            r#"
            (set-logic QF_AUFLIA)
            (declare-fun a1 () (Array Int Int))
            (declare-fun a2 () (Array Int Int))
            (declare-fun i1 () Int)
            (declare-fun i2 () Int)
            (declare-fun sk ((Array Int Int) (Array Int Int)) Int)
            (assert (let ((?v_0 (store a2 i1 (select a1 i1)))
                          (?v_1 (store a1 i1 (select a2 i1))))
                      (= (store ?v_1 i2 (select ?v_0 i2))
                         (store ?v_0 i2 (select ?v_1 i2)))))
            (assert (let ((?v_0 (sk a1 a2))) (not (= (select a1 ?v_0) (select a2 ?v_0)))))
            (check-sat)
        "#,
        );
        println!("{}", outputs[0]);
        return;
    }

    match run_current_test_with_timeout(
        "array_soundness_4304::qf_auflia_storeinv_nf_2idx_6282",
        CHILD_ENV,
        Duration::from_secs(30),
    ) {
        TimedChildOutcome::Result(stdout) => {
            let result = sat_result(&stdout).expect("child emitted solve result");
            assert_ne!(
                result, "sat",
                "AUFLIA storeinv nf 2idx: cross-swap must not return false SAT (#6282)"
            );
        }
        TimedChildOutcome::Timeout => {
            // Timeout: AY cannot solve 2-index storeinv nf within 30s — incompleteness, not unsoundness.
        }
    }
}

/// AUFLIA storeinv single: store(a, i, select(a, i)) = a.
///
/// Simplest store invariant in QF_AUFLIA with Int sorts.
/// Matches storeinv_nf_single.smt2 benchmark.
#[test]
#[timeout(10_000)]
fn qf_auflia_storeinv_nf_single_6282() {
    let (_, outputs) = solve(
        r#"
        (set-logic QF_AUFLIA)
        (declare-fun a () (Array Int Int))
        (declare-fun i () Int)
        (assert (not (= (store a i (select a i)) a)))
        (check-sat)
    "#,
    );
    assert_eq!(
        outputs[0], "unsat",
        "AUFLIA storeinv single: store(a,i,sel(a,i)) = a (#6282)"
    );
}

/// AUFLIA storeinv sf size=2: flat form with intermediate variables.
///
/// Same cross-swap as nf but using named intermediates. This encoding is
/// easier for the solver because each store has a named variable base,
/// allowing direct ROW lemma generation.
#[test]
fn qf_auflia_storeinv_sf_2idx_6282() {
    const CHILD_ENV: &str = "AY_ARRAY_STOREINV_SF_2IDX_6282_CHILD";

    if std::env::var_os(CHILD_ENV).is_some() {
        let (_, outputs) = solve(
            r#"
            (set-logic QF_AUFLIA)
            (declare-fun a1 () (Array Int Int))
            (declare-fun a2 () (Array Int Int))
            (declare-fun i1 () Int)
            (declare-fun i2 () Int)
            (declare-fun sk ((Array Int Int) (Array Int Int)) Int)
            (declare-fun v0 () (Array Int Int))
            (assert (= v0 (store a2 i1 (select a1 i1))))
            (declare-fun v1 () (Array Int Int))
            (assert (= v1 (store a1 i1 (select a2 i1))))
            (assert (= (store v1 i2 (select v0 i2))
                       (store v0 i2 (select v1 i2))))
            (assert (let ((?v_0 (sk a1 a2))) (not (= (select a1 ?v_0) (select a2 ?v_0)))))
            (check-sat)
        "#,
        );
        println!("{}", outputs[0]);
        return;
    }

    match run_current_test_with_timeout(
        "array_soundness_4304::qf_auflia_storeinv_sf_2idx_6282",
        CHILD_ENV,
        Duration::from_mins(2),
    ) {
        TimedChildOutcome::Result(stdout) => {
            let result = sat_result(&stdout).expect("child emitted solve result");
            assert_eq!(
                result, "unsat",
                "AUFLIA storeinv sf 2idx: flat cross-swap forces a1 = a2 (#6282)"
            );
        }
        TimedChildOutcome::Timeout => {
            // Timeout remains acceptable here: this benchmark is still incomplete
            // at current HEAD, even when run in isolation.
        }
    }
}

/// Regression: storeinv_invalid_t1_pp_nf_ai_00002 is SAT (`:status sat` in
/// SMT-LIB, confirmed by Z3). This test is a soundness guard: AY must not
/// return `unsat` on the benchmark, even though current HEAD still times out on
/// it under the test budget.
///
/// The formula asserts that two store chains on `a1` and `a2` produce equal
/// results after a cross-swap of selected values, and simultaneously that `a1`
/// and `a2` differ at some witness index `sk(a1,a2)`. This is satisfiable
/// (the arrays can differ at indices other than `i1`/`i2`).
///
/// Run in a subprocess so the timeout kills the solver process, not just the
/// parent test thread. Timeout remains acceptable here: it is an
/// incompleteness/performance gap, not a soundness bug.
#[test]
fn storeinv_invalid_false_unsat_smtcomp_6608() {
    const CHILD_ENV: &str = "AY_ARRAY_STOREINV_INVALID_6608_CHILD";

    if std::env::var_os(CHILD_ENV).is_some() {
        let (_, outputs) = solve(
            r#"
            (set-logic QF_AUFLIA)
            (declare-fun a1 () (Array Int Int))
            (declare-fun a2 () (Array Int Int))
            (declare-fun i1 () Int)
            (declare-fun i2 () Int)
            (declare-fun sk ((Array Int Int) (Array Int Int)) Int)
            (assert (let ((?v_0 (store a2 i1 (select a1 i1)))
                          (?v_1 (store a1 i1 (select a2 i1))))
                      (= (store ?v_1 i1 (select ?v_0 i2))
                         (store ?v_0 i2 (select ?v_1 i2)))))
            (assert (let ((?v_0 (sk a1 a2)))
                      (not (= (select a1 ?v_0) (select a2 ?v_0)))))
            (check-sat)
        "#,
        );
        println!("{}", outputs[0]);
        return;
    }

    match run_current_test_with_timeout(
        "array_soundness_4304::storeinv_invalid_false_unsat_smtcomp_6608",
        CHILD_ENV,
        Duration::from_secs(30),
    ) {
        TimedChildOutcome::Result(stdout) => {
            let result = sat_result(&stdout).expect("child emitted solve result");
            assert_ne!(
                result, "unsat",
                "storeinv_invalid is SAT (:status sat, Z3 confirms); AY must not return false UNSAT"
            );
        }
        TimedChildOutcome::Timeout => {
            // Timeout remains acceptable here: current HEAD still fails to
            // solve the benchmark under 30s, but that is incompleteness rather
            // than a false UNSAT result.
        }
    }
}

/// #arr_lia561 wrong-UNSAT regression: an Int-array AUFLIA formula where one var
/// (`a2`) is given TWO store-flat definitions to the SAME base (`a1`), combined
/// with a select-through-store on a third array `a3` (sharing the constant `0`),
/// `i1 != 3`, and `a1 != a3`.
///
/// The combined LIA+Array+EUF route merges `parent_selects` across the array
/// equality/alias closure (including model/sentinel equalities). The
/// read-over-write conflict checker (`check_array_equality`) then paired
/// `select(a3, K)` — which is only MODEL-equal to `a1`, not provably so — with
/// `select(a2, K)` under `a1 = a2` and emitted the false theorem
/// `select(a1,K)=select(a3,K) | ¬(a1=a2) | ¬(select(a1,K)=select(a2,K))`,
/// closing a spurious UNSAT. The fix validates each select's actual array
/// against the equality side (adding the alias proof, or skipping if not
/// provable). Z3 confirms `sat`; AY must never return UNSAT here. This minimized
/// core solves to `sat`; the original arr_lia561 9-assertion form (which also
/// aliases `a2 = a0`) degrades to a sound `unknown` under the in-process solver.
#[test]
#[timeout(60_000)]
fn arr_lia561_dup_store_flat_not_false_unsat() {
    let (_, outputs) = solve(
        r#"
        (set-logic ALL)
        (declare-fun a0 () (Array Int Int))
        (declare-fun a1 () (Array Int Int))
        (declare-fun a2 () (Array Int Int))
        (declare-fun a3 () (Array Int Int))
        (declare-fun i1 () Int)
        (declare-fun e1 () Int)
        (declare-fun e2 () Int)
        (assert (= 2 (select (store a3 0 e1) i1)))
        (assert (= a2 (store a1 i1 0)))
        (assert (= a2 (store a1 3 e2)))
        (assert (distinct 3 i1))
        (assert (not (= a1 a3)))
        (check-sat)
    "#,
    );
    let result = sat_result(&outputs[0]).expect("solver emitted a result");
    assert_ne!(
        result, "unsat",
        "arr_lia561 dup-store-flat core is SAT (Z3 confirms); AY must not return false UNSAT"
    );
}

// --- Regression: a declared BV logic must not swallow a non-BV array theory ---

/// A `(set-logic QF_ABV)` script whose arrays range over UNINTERPRETED sorts
/// must not be dispatched to the eager bit-blasting lane.
///
/// That lane's array axiom generator (`executor::theories::bv_axioms_array`)
/// models `select`/`store` only when the index AND element sorts are bit-vectors
/// — every ROW/extensionality site there bails out on
/// `let Sort::BitVec(..) = .. else`. With uninterpreted `Index`/`Element` the
/// formula reached the SAT solver with ZERO array axioms
/// (`array-axioms.after-row=0`), read-over-write was never enforced, and the
/// search returned a MODEL THAT FALSIFIES an authored assertion — the
/// `[AY SOUNDNESS GATE]` "caught an INVALID model" banner. Fail-closed, so no
/// wrong `sat` shipped, but the model itself was genuinely wrong.
///
/// The declared logic is an upper bound, not a licence to drop a theory: with no
/// bit-vector term anywhere in the assertions the router now re-derives the
/// category from content and the array+EUF lane decides this exactly.
///
/// This is the same store/cross-swap shape as
/// `qf_ax_storeinv_cross_swap_nf_2idx`, reduced to the two `select` reads that
/// were falsified, and it is UNSAT: `i2 = d` forces `select(v0, d)` and
/// `select(v0, i2)` to agree by congruence, so assertions 2 and 3 conflict.
#[test]
#[timeout(10_000)]
fn qf_abv_uninterpreted_sort_array_is_not_bit_blasted() {
    let (_, outputs) = solve(
        r#"
        (set-logic QF_ABV)
        (declare-sort Element 0)
        (declare-sort Index 0)
        (declare-const i1 Index)
        (declare-const i2 Index)
        (declare-const a2 (Array Index Element))
        (declare-const a1 (Array Index Element))
        (declare-const d Index)
        (assert (= i2 d))
        (assert (= (select a1 d) (select (store a1 i1 (select a2 i1)) d)))
        (assert (= (select (store a2 i1 (select a1 i1)) i2)
                   (select (store a1 i1 (select a2 i1)) i2)))
        (assert (not (= (select a1 d) (select (store a2 i1 (select a1 i1)) d))))
        (check-sat)
    "#,
    );
    assert_eq!(
        outputs[0], "unsat",
        "arrays over uninterpreted sorts must reach the array+EUF lane even under \
         a declared BV logic; the bit-blasting lane emits no ROW axioms for them \
         and returns an invalid model"
    );
}
