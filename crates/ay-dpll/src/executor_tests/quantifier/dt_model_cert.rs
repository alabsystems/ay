// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! DT-MBQI-Sat certificate tests (`try_dt_model_sat_certificate`).
//!
//! The positive tests pin the certificate's GRANTS (F4 cell-invariant
//! datatype-binder foralls that MUST certify SAT under `AY_DT_CERT=on`). The
//! adversarial / decline tests pin its REFUSALS: every way the certificate
//! could be fooled (a tester read as a free UF, an unclaimed non-F4 forall, a
//! distinct-collapse, a negative table leaf) must NEVER report `sat`.
//!
//! `AY_DT_CERT` and `AY_DT_LAZY` are process-global env vars. Flagged solves run
//! in an isolated child copy of this test binary so parallel solver tests can
//! never observe a transient gate value. A mutex still serializes these heavy
//! child solves to avoid turning CPU contention into spurious timeouts.

use super::*;
use std::io::{Read, Write};
use std::process::{Command, Stdio};
use std::sync::Mutex;

static ENV_LOCK: Mutex<()> = Mutex::new(());
const SUBPROCESS_WORKER_ENV: &str = "AY_INTERNAL_DT_CERT_TEST_WORKER";
const SKIP_RESEQUENCE_ENV: &str = "AY_INTERNAL_DT_CERT_SKIP_RESEQUENCE";
const SUBPROCESS_RESULT_PREFIX: &str = "AY_INTERNAL_DT_CERT_TEST_RESULT=";
const SUBPROCESS_WORKER_TEST: &str =
    "executor_tests::quantifier::dt_model_cert::dt_cert_subprocess_worker";

/// Run one solver input in an isolated child test process.
///
/// `cert` always overrides (or removes) `AY_DT_CERT`. `lazy_override` is
/// `None` to inherit the caller's `AY_DT_LAZY`, `Some(Some(value))` to set it,
/// and `Some(None)` to remove it. The parent process environment is untouched.
fn solve_in_subprocess(
    cert: Option<&str>,
    lazy_override: Option<Option<&str>>,
    skip_resequence: bool,
    input: &str,
) -> String {
    let mut command = Command::new(std::env::current_exe().expect("locate ay-dpll test binary"));
    command
        .arg(SUBPROCESS_WORKER_TEST)
        .arg("--exact")
        .arg("--nocapture")
        .arg("--test-threads=1")
        .env(SUBPROCESS_WORKER_ENV, "1")
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped());
    match cert {
        Some(value) => {
            command.env("AY_DT_CERT", value);
        }
        None => {
            command.env_remove("AY_DT_CERT");
        }
    }
    if let Some(lazy) = lazy_override {
        match lazy {
            Some(value) => {
                command.env("AY_DT_LAZY", value);
            }
            None => {
                command.env_remove("AY_DT_LAZY");
            }
        }
    }
    if skip_resequence {
        command.env(SKIP_RESEQUENCE_ENV, "1");
    } else {
        command.env_remove(SKIP_RESEQUENCE_ENV);
    }

    let mut child = command.spawn().expect("spawn isolated DT-gate test worker");
    child
        .stdin
        .take()
        .expect("DT-gate worker stdin")
        .write_all(input.as_bytes())
        .expect("write solver input to DT-gate worker");
    let output = child
        .wait_with_output()
        .expect("wait for DT-gate test worker");
    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        output.status.success(),
        "isolated DT-gate worker failed (status={}):\nstdout:\n{}\nstderr:\n{}",
        output.status,
        stdout,
        stderr
    );
    stdout
        .lines()
        .find_map(|line| {
            line.split_once(SUBPROCESS_RESULT_PREFIX)
                .map(|(_, result)| result)
        })
        .map(str::to_owned)
        .unwrap_or_else(|| {
            panic!(
                "isolated DT-gate worker emitted no result marker:\nstdout:\n{}\nstderr:\n{}",
                stdout, stderr
            )
        })
}

/// Solve `input` with `AY_DT_CERT` set to `mode` for the duration.
fn solve_with_mode(mode: Option<&str>, input: &str) -> String {
    let _guard = ENV_LOCK.lock().unwrap_or_else(|e| e.into_inner());
    solve_in_subprocess(mode, None, false, input)
}

/// Force the post-solve certificate arm, bypassing only the test binary's
/// bounded re-sequencing probe.  This pins parity between both grant sites.
fn solve_with_postsolve_certificate(mode: Option<&str>, input: &str) -> String {
    let _guard = ENV_LOCK.lock().unwrap_or_else(|e| e.into_inner());
    solve_in_subprocess(mode, None, true, input)
}

/// Solve `input` with `AY_DT_CERT`=`cert` AND `AY_DT_LAZY`=`lazy` for the
/// duration in a child process. The same `ENV_LOCK` serializes these expensive
/// child solves without exposing either override in the parent process. Used by
/// the `AY_DT_LAZY × AY_DT_CERT` composition pin.
fn solve_with_flags(cert: Option<&str>, lazy: Option<&str>, input: &str) -> String {
    let _guard = ENV_LOCK.lock().unwrap_or_else(|e| e.into_inner());
    solve_in_subprocess(cert, Some(lazy), false, input)
}

/// Child-process entry point selected exactly by [`solve_in_subprocess`].
/// A normal parent test run executes this once as a no-op.
#[test]
fn dt_cert_subprocess_worker() {
    if std::env::var_os(SUBPROCESS_WORKER_ENV).is_none() {
        return;
    }
    let mut input = String::new();
    std::io::stdin()
        .read_to_string(&mut input)
        .expect("read isolated DT-gate solver input");
    let commands = parse(&input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();
    println!(
        "{}{}",
        SUBPROCESS_RESULT_PREFIX,
        outputs.last().cloned().unwrap_or_default()
    );
}

#[test]
fn flagged_solve_isolated_from_parallel_parent_reader() {
    let cert_before = std::env::var_os("AY_DT_CERT");
    let lazy_before = std::env::var_os("AY_DT_LAZY");
    let observer_cert = cert_before.clone();
    let observer_lazy = lazy_before.clone();
    let barrier = std::sync::Arc::new(std::sync::Barrier::new(2));
    let observer_barrier = std::sync::Arc::clone(&barrier);
    let (stop_tx, stop_rx) = std::sync::mpsc::channel::<()>();
    let observer = std::thread::spawn(move || {
        observer_barrier.wait();
        let mut observations = 0usize;
        while matches!(
            stop_rx.try_recv(),
            Err(std::sync::mpsc::TryRecvError::Empty)
        ) {
            assert_eq!(std::env::var_os("AY_DT_CERT"), observer_cert);
            assert_eq!(std::env::var_os("AY_DT_LAZY"), observer_lazy);
            observations += 1;
            std::thread::yield_now();
        }
        observations
    });

    barrier.wait();
    let verdict = solve_with_flags(
        Some("child-only-cert"),
        Some("child-only-lazy"),
        "(set-logic QF_UF)\n(check-sat)\n",
    );
    drop(stop_tx);
    let observations = observer
        .join()
        .expect("parallel parent environment observer");

    assert_eq!(verdict, "sat");
    assert!(observations > 0, "parent environment observer never ran");
    assert_eq!(std::env::var_os("AY_DT_CERT"), cert_before);
    assert_eq!(std::env::var_os("AY_DT_LAZY"), lazy_before);
}

/// The min1 RED shape: `forall x:List. 0 <= logic_sum(x)` + the ground
/// unfolder + discriminant chain forcing `is-Cons self`.
const MIN1: &str = r#"
    (set-logic ALL)
    (declare-datatypes ((List 0)) (((Cons (enum_payload_get_0_1_u4c697374 Int) (enum_payload_get_1_1_u4c697374 List)) (Nil))))
    (declare-const self List)
    (declare-fun logic_sum (List) Int)
    (declare-fun list_cons_1 (List) List)
    (declare-fun list_cons_0__ret_496e74 (List) Int)
    (declare-fun method_discriminant_1_d4c697374 (List) Int)
    (declare-const __uf_int_aux_1 Int)
    (assert (! (forall ((spec_param_self_2_13 List)) (<= 0 (logic_sum spec_param_self_2_13))) :named dn4))
    (assert (! (ite (is-Cons self) (= (logic_sum self) (+ (list_cons_0__ret_496e74 self) (logic_sum (list_cons_1 self)))) (= 0 (logic_sum self))) :named dn80))
    (assert (! (or (and (<= 0 (list_cons_0__ret_496e74 self)) (<= (list_cons_0__ret_496e74 self) 4294967295)) (not (is-Cons self))) :named dn2))
    (assert (! (= (method_discriminant_1_d4c697374 self) __uf_int_aux_1) :named dn54))
    (assert (! (or (not (is-Cons self)) (= 0 __uf_int_aux_1)) :named dn55))
    (assert (! (or (= 1 __uf_int_aux_1) (not (is-Nil self))) :named dn56))
    (assert (! (= 0 __uf_int_aux_1) :named dn60))
    (check-sat)
"#;

// ---------------------------------------------------------------------------
// Grants (only under AY_DT_CERT=on).
// ---------------------------------------------------------------------------

#[test]
fn dt_cert_grants_min1_under_on() {
    assert_eq!(solve_with_mode(Some("on"), MIN1), "sat");
}

#[test]
fn dt_cert_min1_byte_identical_when_unset() {
    // The RED stays a fail-closed quantifier Unknown when the gate is off.
    assert_eq!(solve_with_mode(None, MIN1), "unknown");
}

#[test]
fn dt_cert_min1_shadow_never_flips() {
    // Shadow runs the certificate (and would log) but never grants.
    assert_eq!(solve_with_mode(Some("shadow"), MIN1), "unknown");
}

#[test]
fn dt_cert_grants_min0_nonneg_lemma() {
    // Smallest F4 shape: nonneg lemma + one ground pin, no unfolder.
    let verdict = solve_with_mode(
        Some("on"),
        r#"
        (set-logic ALL)
        (declare-datatypes ((List 0)) (((Cons (hd Int) (tl List)) (Nil))))
        (declare-const self List)
        (declare-fun logic_sum (List) Int)
        (assert (forall ((x List)) (<= 0 (logic_sum x))))
        (assert (= (logic_sum self) 5))
        (check-sat)
    "#,
    );
    assert_eq!(verdict, "sat");
}

#[test]
fn dt_cert_grants_free_uf_no_observation() {
    // `forall x:List. 0 <= f(x)` with f entirely free: default cell 0 >= 0.
    let verdict = solve_with_mode(
        Some("on"),
        r#"
        (set-logic ALL)
        (declare-datatypes ((List 0)) (((Cons (hd Int) (tl List)) (Nil))))
        (declare-fun f (List) Int)
        (declare-const c List)
        (assert (forall ((x List)) (<= 0 (f x))))
        (assert (is-Cons c))
        (check-sat)
    "#,
    );
    assert_eq!(verdict, "sat");
}

// ---------------------------------------------------------------------------
// The Int-binder control is UNTOUCHED (finite-table cert path, gate-agnostic).
// ---------------------------------------------------------------------------

#[test]
fn dt_cert_int_control_unchanged() {
    let prog = r#"
        (set-logic ALL)
        (declare-fun f (Int) Int)
        (declare-const x Int)
        (assert (forall ((i Int)) (<= 0 (f i))))
        (assert (= (f x) 5))
        (check-sat)
    "#;
    // Sat via the finite-table cert regardless of AY_DT_CERT.
    assert_eq!(solve_with_mode(Some("on"), prog), "sat");
    assert_eq!(solve_with_mode(None, prog), "sat");
}

// ---------------------------------------------------------------------------
// Refusals — must NEVER be `sat`, even under AY_DT_CERT=on.
// ---------------------------------------------------------------------------

#[test]
fn dt_cert_refuses_tester_on_binder() {
    // `forall x:List. is-Cons x` is UNSAT (Nil). The tester must never be
    // treated as a free finite-piecewise UF.
    let verdict = solve_with_mode(
        Some("on"),
        r#"
        (set-logic ALL)
        (declare-datatypes ((List 0)) (((Cons (hd Int) (tl List)) (Nil))))
        (declare-const self List)
        (assert (forall ((x List)) (is-Cons x)))
        (assert (is-Cons self))
        (check-sat)
    "#,
    );
    assert_ne!(verdict, "sat");
}

#[test]
fn dt_cert_refuses_selector_on_binder() {
    // The binder read through a selector is out of the cell-invariant class.
    let verdict = solve_with_mode(
        Some("on"),
        r#"
        (set-logic ALL)
        (declare-datatypes ((List 0)) (((Cons (hd Int) (tl List)) (Nil))))
        (declare-const self List)
        (assert (forall ((x List)) (<= 0 (hd x))))
        (assert (is-Cons self))
        (check-sat)
    "#,
    );
    assert_ne!(verdict, "sat");
}

#[test]
fn dt_cert_refuses_all_or_nothing_unroutable() {
    // A grantable F4 forall plus a forall that matches NO route (a bridge UF read
    // at a NESTED selector argument `(tl y)` — not F2/F3/G/F4): all-or-nothing
    // means the cert must decline the whole snapshot. (M4: the pure-bridge shape
    // `(= (list_cons_1 y) (tl y)) ∨ ¬is-Cons y` is now the sanctioned F3 route —
    // see `dt_cert_grants_f3_bridge_default` — so the discipline is exercised here
    // with a genuinely unroutable forall instead.)
    let verdict = solve_with_mode(
        Some("on"),
        r#"
        (set-logic ALL)
        (declare-datatypes ((List 0)) (((Cons (hd Int) (tl List)) (Nil))))
        (declare-const self List)
        (declare-fun logic_sum (List) Int)
        (declare-fun list_cons_1 (List) List)
        (assert (forall ((x List)) (<= 0 (logic_sum x))))
        (assert (forall ((y List)) (= (list_cons_1 y) (list_cons_1 (tl y)))))
        (assert (is-Cons self))
        (assert (= (logic_sum self) 3))
        (check-sat)
    "#,
    );
    assert_ne!(verdict, "sat");
}

// ---------------------------------------------------------------------------
// M4 routes: G (ground-reduction), F2 (selector tautology), F3 (bridge
// symbolic default) — GRANTS (only under AY_DT_CERT=on, via the ground-core
// re-sequencing probe).
// ---------------------------------------------------------------------------

#[test]
fn dt_cert_grants_f2_selector_tautology() {
    // F2: `sel_i(C(a,b)) = a` is a datatype theory tautology. Combined with a
    // grantable F4 nonneg lemma + a satisfiable ground core.
    let verdict = solve_with_mode(
        Some("on"),
        r#"
        (set-logic ALL)
        (declare-datatypes ((List 0)) (((Cons (hd Int) (tl List)) (Nil))))
        (declare-const self List)
        (declare-fun logic_sum (List) Int)
        (assert (forall ((x List)) (<= 0 (logic_sum x))))
        (assert (forall ((a Int) (b List)) (= a (hd (Cons a b)))))
        (assert (forall ((a Int) (b List)) (= b (tl (Cons a b)))))
        (assert (is-Cons self))
        (assert (= (logic_sum self) 4))
        (check-sat)
    "#,
    );
    assert_eq!(verdict, "sat");
}

#[test]
fn dt_cert_grants_f3_bridge_default() {
    // F3: `is-Cons x => list_cons_1(x) = tl(x)` closes via the SYMBOLIC selector
    // default (list_cons_1 ≡ tl). The ground core forces the exception rows to
    // agree with the selector; the default is the selector by construction.
    let verdict = solve_with_mode(
        Some("on"),
        r#"
        (set-logic ALL)
        (declare-datatypes ((List 0)) (((Cons (hd Int) (tl List)) (Nil))))
        (declare-const self List)
        (declare-fun logic_sum (List) Int)
        (declare-fun list_cons_1 (List) List)
        (assert (forall ((x List)) (<= 0 (logic_sum x))))
        (assert (forall ((y List)) (or (= (list_cons_1 y) (tl y)) (not (is-Cons y)))))
        (assert (is-Cons self))
        (assert (= (tl self) Nil))
        (assert (= (list_cons_1 self) (tl self)))
        (assert (= (logic_sum self) 2))
        (check-sat)
    "#,
    );
    assert_eq!(verdict, "sat");
}

#[test]
fn dt_cert_grants_g_ground_reduction() {
    // G: `self = Cons(a,b) => tl(self) = b` — DT injectivity pins b = tl(self),
    // making the consequent reflexive at the single relevant point.
    let verdict = solve_with_mode(
        Some("on"),
        r#"
        (set-logic ALL)
        (declare-datatypes ((List 0)) (((Cons (hd Int) (tl List)) (Nil))))
        (declare-const self List)
        (declare-fun logic_sum (List) Int)
        (assert (forall ((x List)) (<= 0 (logic_sum x))))
        (assert (forall ((a Int) (b List))
            (or (= (tl self) b) (not (= self (Cons a b))))))
        (assert (forall ((a Int) (b List))
            (or (= (hd self) a) (not (= self (Cons a b))))))
        (assert (is-Cons self))
        (assert (= (hd self) 7))
        (assert (= (tl self) Nil))
        (assert (= (logic_sum self) 3))
        (check-sat)
    "#,
    );
    assert_eq!(verdict, "sat");
}

#[test]
fn dt_cert_grants_g_vacuous_when_not_cons() {
    // G over a term that is NOT a Cons under M' (it is Nil): the guard is false
    // for all binders, so the universal is vacuously true — certified.
    let verdict = solve_with_mode(
        Some("on"),
        r#"
        (set-logic ALL)
        (declare-datatypes ((List 0)) (((Cons (hd Int) (tl List)) (Nil))))
        (declare-const l List)
        (declare-fun logic_sum (List) Int)
        (assert (forall ((x List)) (<= 0 (logic_sum x))))
        (assert (forall ((a Int) (b List))
            (or (= (hd l) 999) (not (= l (Cons a b))))))
        (assert (is-Nil l))
        (assert (= (logic_sum l) 0))
        (check-sat)
    "#,
    );
    assert_eq!(verdict, "sat");
}

// The fullsort shape in miniature: F4 + F2 + F3 + two G foralls (one reading
// the bridge, exercising the M' rewrite) over one Cons constant.
const MIXED_ALL_ROUTES_INPUT: &str = r#"
        (set-logic ALL)
        (declare-datatypes ((List 0)) (((Cons (hd Int) (tl List)) (Nil))))
        (declare-const self List)
        (declare-fun logic_sum (List) Int)
        (declare-fun list_cons_1 (List) List)
        (assert (forall ((x List)) (<= 0 (logic_sum x))))
        (assert (forall ((a Int) (b List)) (= b (tl (Cons a b)))))
        (assert (forall ((y List)) (or (= (list_cons_1 y) (tl y)) (not (is-Cons y)))))
        (assert (forall ((a Int) (b List))
            (or (= (tl self) b) (not (= self (Cons a b))))))
        (assert (forall ((a Int) (b List))
            (or (= (tl self) (list_cons_1 self)) (not (= self (Cons a b))))))
        (assert (is-Cons self))
        (assert (= (hd self) 3))
        (assert (= (tl self) Nil))
        (assert (= (list_cons_1 self) (tl self)))
        (assert (= (logic_sum self) 5))
        (check-sat)
    "#;

#[test]
fn dt_cert_grants_mixed_all_routes() {
    let verdict = solve_with_mode(Some("on"), MIXED_ALL_ROUTES_INPUT);
    assert_eq!(verdict, "sat");
}

#[test]
fn dt_cert_postsolve_grant_survives_emission_gates() {
    let verdict = solve_with_postsolve_certificate(Some("on"), MIXED_ALL_ROUTES_INPUT);
    assert_eq!(verdict, "sat");
}

#[test]
fn dt_cert_mixed_all_routes_without_grant_fails_closed() {
    let verdict = solve_with_mode(None, MIXED_ALL_ROUTES_INPUT);
    assert_eq!(verdict, "unknown");
}

// ---------------------------------------------------------------------------
// M4 adversarial mutants — must NEVER be `sat` under AY_DT_CERT=on.
// ---------------------------------------------------------------------------

#[test]
fn dt_cert_refuses_g_nonunique_pin() {
    // 5a: the guard's `t` side is NOT ground (mentions a binder), so the
    // equation does not pin the binders uniquely — G must decline.
    let verdict = solve_with_mode(
        Some("on"),
        r#"
        (set-logic ALL)
        (declare-datatypes ((List 0)) (((Cons (hd Int) (tl List)) (Nil))))
        (declare-const self List)
        (declare-fun logic_sum (List) Int)
        (declare-fun f (List) List)
        (assert (forall ((x List)) (<= 0 (logic_sum x))))
        (assert (forall ((a Int) (b List))
            (or (= (hd self) 999) (not (= (f b) (Cons a b))))))
        (assert (is-Cons self))
        (assert (= (hd self) 3))
        (assert (= (logic_sum self) 3))
        (check-sat)
    "#,
    );
    assert_ne!(verdict, "sat");
}

#[test]
fn dt_cert_refuses_g_false_at_pin() {
    // 5b: the consequent is FALSE at the injectivity-pinned point
    // (`hd self = 999` but `hd self = 3` is asserted) — UNSAT, never sat.
    let verdict = solve_with_mode(
        Some("on"),
        r#"
        (set-logic ALL)
        (declare-datatypes ((List 0)) (((Cons (hd Int) (tl List)) (Nil))))
        (declare-const self List)
        (declare-fun logic_sum (List) Int)
        (assert (forall ((x List)) (<= 0 (logic_sum x))))
        (assert (forall ((a Int) (b List))
            (or (= (hd self) 999) (not (= self (Cons a b))))))
        (assert (is-Cons self))
        (assert (= (hd self) 3))
        (assert (= (tl self) Nil))
        (assert (= (logic_sum self) 3))
        (check-sat)
    "#,
    );
    assert_ne!(verdict, "sat");
}

#[test]
fn dt_cert_refuses_f3_selector_disagreement() {
    // 5c: an F3 bridge whose ground exception row DISAGREES with the selector
    // (`list_cons_1 self = Cons 9 Nil` but `tl self = Nil`) — after the uf ≡ sel
    // rewrite the ground re-verification refutes it. UNSAT, never sat.
    let verdict = solve_with_mode(
        Some("on"),
        r#"
        (set-logic ALL)
        (declare-datatypes ((List 0)) (((Cons (hd Int) (tl List)) (Nil))))
        (declare-const self List)
        (declare-fun logic_sum (List) Int)
        (declare-fun list_cons_1 (List) List)
        (assert (forall ((x List)) (<= 0 (logic_sum x))))
        (assert (forall ((y List)) (or (= (list_cons_1 y) (tl y)) (not (is-Cons y)))))
        (assert (is-Cons self))
        (assert (= (tl self) Nil))
        (assert (= (list_cons_1 self) (Cons 9 Nil)))
        (assert (= (logic_sum self) 1))
        (check-sat)
    "#,
    );
    assert_ne!(verdict, "sat");
}

#[test]
fn dt_cert_refuses_adv3_g_false_after_rewrite() {
    // 5d (the adv3 composition): a G claim TRUE under the raw candidate M becomes
    // FALSE under the completed M' (list_cons_1 ≡ tl). The SINGLE-AUTHORITY
    // post-M' re-verification of the G claim must catch it. UNSAT, never sat.
    let verdict = solve_with_mode(
        Some("on"),
        r#"
        (set-logic ALL)
        (declare-datatypes ((List 0)) (((Cons (hd Int) (tl List)) (Nil))))
        (declare-const self List)
        (declare-fun logic_sum (List) Int)
        (declare-fun list_cons_1 (List) List)
        (assert (forall ((x List)) (<= 0 (logic_sum x))))
        (assert (forall ((y List)) (or (= (list_cons_1 y) (tl y)) (not (is-Cons y)))))
        (assert (forall ((a Int) (b List))
            (or (= (list_cons_1 self) (Cons 7 Nil)) (not (= self (Cons a b))))))
        (assert (is-Cons self))
        (assert (= (hd self) 5))
        (assert (= (tl self) Nil))
        (assert (= (logic_sum self) 3))
        (check-sat)
    "#,
    );
    assert_ne!(verdict, "sat");
}

#[test]
fn dt_cert_refuses_unsat_ground_core() {
    // 5e (mini-fullsort): a mutated ground assertion makes the GROUND CORE
    // itself UNSAT (`hd self` = 5 and = 7). No candidate ⇒ the re-sequence
    // declines; the normal solve concludes UNSAT. Never sat.
    let verdict = solve_with_mode(
        Some("on"),
        r#"
        (set-logic ALL)
        (declare-datatypes ((List 0)) (((Cons (hd Int) (tl List)) (Nil))))
        (declare-const self List)
        (declare-fun logic_sum (List) Int)
        (assert (forall ((x List)) (<= 0 (logic_sum x))))
        (assert (is-Cons self))
        (assert (= (hd self) 5))
        (assert (= (hd self) 7))
        (check-sat)
    "#,
    );
    assert_ne!(verdict, "sat");
}

#[test]
fn dt_cert_refuses_int_binder_forall_in_snapshot() {
    // A mixed snapshot with an Int-binder forall is not all-DT-F4: the DT cert
    // declines (the Int one is the finite-table cert's job, not this one).
    let verdict = solve_with_mode(
        Some("on"),
        r#"
        (set-logic ALL)
        (declare-datatypes ((List 0)) (((Cons (hd Int) (tl List)) (Nil))))
        (declare-const self List)
        (declare-fun logic_sum (List) Int)
        (declare-fun g (Int) Int)
        (assert (forall ((x List)) (<= 0 (logic_sum x))))
        (assert (forall ((i Int)) (< (g i) 0)))
        (assert (= (g 0) 5))
        (check-sat)
    "#,
    );
    // g(0)=5 contradicts (< (g 0) 0): UNSAT, never sat.
    assert_ne!(verdict, "sat");
}

#[test]
fn dt_cert_never_sat_distinct_collapse_twin() {
    // Two EUF-distinct classes materialize to Cons(0,Nil): injectivity ⇒ a=b,
    // but `distinct a b` is asserted. UNSAT; never sat.
    let verdict = solve_with_mode(
        Some("on"),
        r#"
        (set-logic ALL)
        (declare-datatypes ((List 0)) (((Cons (hd Int) (tl List)) (Nil))))
        (declare-fun logic_sum (List) Int)
        (declare-const a List)
        (declare-const b List)
        (assert (forall ((x List)) (<= 0 (logic_sum x))))
        (assert (is-Cons a))
        (assert (= (hd a) 0))
        (assert (= (tl a) Nil))
        (assert (is-Cons b))
        (assert (= (hd b) 0))
        (assert (= (tl b) Nil))
        (assert (distinct a b))
        (assert (= (logic_sum a) 5))
        (assert (= (logic_sum b) 7))
        (check-sat)
    "#,
    );
    assert_ne!(verdict, "sat");
}

#[test]
fn dt_cert_never_sat_negative_leaf_sibling() {
    // A negative table entry logic_sum(neg) = -1 violates the nonneg atom.
    // UNSAT; never sat.
    let verdict = solve_with_mode(
        Some("on"),
        r#"
        (set-logic ALL)
        (declare-datatypes ((List 0)) (((Cons (hd Int) (tl List)) (Nil))))
        (declare-fun logic_sum (List) Int)
        (declare-const neg List)
        (assert (forall ((x List)) (<= 0 (logic_sum x))))
        (assert (= (logic_sum neg) (- 1)))
        (check-sat)
    "#,
    );
    assert_ne!(verdict, "sat");
}

// ---------------------------------------------------------------------------
// AY_DT_LAZY × AY_DT_CERT composition pin (#dt-cert-lazy-compose).
//
// The lazy DT lane (`AY_DT_LAZY`, on by default; kill switch `=0`) and the
// DT-MBQI-Sat certificate (`AY_DT_CERT=on`) MUST compose: enabling the lazy
// lane may never suppress a cert grant. On the MIN1 DT-cert RED the lazy lane
// is content-INELIGIBLE — `dt_lazy_content_eligible` requires every term sort
// to be Bool / Uninterpreted / Datatype, but MIN1 carries Int-sorted terms
// (the `Cons` payload, `logic_sum`, the discriminant auxiliaries), so the lane
// early-returns `Ok(None)` and never fires. The grant comes from the M4
// re-sequence probe (`dt_cert_resequence_probe`), which runs its own scoped,
// budget-capped ground-core solve BEFORE `process_quantifiers` and is entirely
// independent of the lazy lane. Both-flags-on is therefore byte-behaviour-
// identical to cert-alone (verified: 0 `dt-lazy` phase-trace lines, cert grant
// via `re-sequence ... grant=true`, deterministic `sat` in ~5s).
//
// These pins lock the composition so a FUTURE lazy-lane change that becomes
// eligible on a DT-cert shape (and could then starve the cert via the R1
// half-budget time split) cannot land without tripping a test.
// ---------------------------------------------------------------------------

#[test]
fn dt_cert_grants_min1_under_on_and_lazy() {
    // THE interaction pin: BOTH flags on → sat, identical to cert-alone.
    assert_eq!(solve_with_flags(Some("on"), Some("1"), MIN1), "sat");
}

#[test]
fn dt_cert_min1_lazy_alone_stays_unknown() {
    // Lazy lane alone (no cert) leaves the RED a fail-closed quantifier
    // Unknown: the lane grants nothing on this shape, and without the cert
    // there is no grant authority. Locks the lazy-alone verdict.
    assert_eq!(solve_with_flags(None, Some("1"), MIN1), "unknown");
}

#[test]
fn dt_cert_min1_grant_independent_of_lazy_kill_switch() {
    // Explicitly disabling the lazy lane (kill switch `=0`) with the cert on
    // still grants: the cert is independent of the lane in either direction.
    assert_eq!(solve_with_flags(Some("on"), Some("0"), MIN1), "sat");
}
