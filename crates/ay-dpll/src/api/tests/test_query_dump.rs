// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! `AY_DUMP_QUERY_DIR` query-dump self-containment (#dump-self-contained).
//!
//! A dumped script must be usable as a standalone repro/oracle input: every
//! uninterpreted sort referenced by the query must be declared, and the script
//! must round-trip through ay's own front end. If a `z3` binary is on PATH the
//! script is additionally checked to be z3-parseable (soft check: skipped when
//! z3 is absent, never a hard dependency).

use crate::api::*;
use std::io::Write as _;

const QUERY_DUMP_CHILD_DIR: &str = "AY_TEST_QUERY_DUMP_CHILD_DIR";
const QUERY_DUMP_TEST_NAME: &str =
    "api::tests::test_query_dump::query_dump_env_writes_self_contained_file";

/// Run a dumped script through ay's own parser + executor in a fresh process
/// state and return the final command output (the `(check-sat)` verdict).
fn replay_through_own_frontend(script: &str) -> String {
    let mut exec = Executor::new();
    let cmds = ay_frontend::parse(script)
        .unwrap_or_else(|e| panic!("dumped script does not re-parse: {e:?}\n{script}"));
    let mut last = String::new();
    for cmd in &cmds {
        if let Some(s) = exec
            .execute(cmd)
            .unwrap_or_else(|e| panic!("dumped script does not re-execute: {e:?}\n{script}"))
        {
            last = s;
        }
    }
    last
}

/// Soft z3 parse/solve check: only runs when a `z3` binary is available.
/// Asserts the script produces a clean verdict (no parse errors) when z3 is
/// present; silently skips otherwise.
fn soft_check_z3_parseable(script: &str, expected: &[&str]) {
    // A real unique tempfile avoids collisions between equal-length scripts in
    // concurrent tests (PID + length was not a unique name).
    let mut file = tempfile::Builder::new()
        .prefix("ay-test-query-dump-")
        .suffix(".smt2")
        .tempfile()
        .expect("create z3 query-dump tempfile");
    file.write_all(script.as_bytes())
        .expect("write z3 query-dump tempfile");
    file.flush().expect("flush z3 query-dump tempfile");
    let output = std::process::Command::new("z3")
        .arg("-smt2")
        .arg(file.path())
        .output();
    let Ok(output) = output else {
        return; // z3 not installed: soft check skipped
    };
    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        output.status.success() && !stdout.contains("error") && !stderr.contains("error"),
        "z3 rejected the dumped script (status {}):\nstdout: {stdout}\nstderr: {stderr}\n{script}",
        output.status
    );
    let verdict = stdout
        .lines()
        .last()
        .map(str::trim)
        .unwrap_or("")
        .to_string();
    assert!(
        expected.contains(&verdict.as_str()),
        "unexpected z3 verdict {verdict:?} (expected one of {expected:?}):\n{script}"
    );
}

/// A verification-consumer-shaped query: constants and a function over uninterpreted sorts
/// whose names require pipe-quoting (`__verification_consumer_mutref::int`) plus a plain
/// one (`Unit`). The dump must declare both sorts and round-trip.
#[test]
fn query_dump_declares_uninterpreted_sorts_and_roundtrips() {
    let mut solver = Solver::new(Logic::All);
    let mutref = Sort::Uninterpreted("__verification_consumer_mutref::int".to_string());
    let unit = Sort::Uninterpreted("Unit".to_string());

    let m = solver.declare_const("m", mutref.clone());
    let n = solver.declare_const("n", mutref.clone());
    let u = solver.declare_const("u", unit);
    let cur = solver.declare_fun("cur", &[mutref], Sort::Int);
    let cm = solver.apply(&cur, &[m]);
    let cn = solver.apply(&cur, &[n]);
    let five = solver.int_const(5);
    let a1 = solver.eq(cm, five);
    solver.assert_term(a1);
    let a2 = solver.neq(cm, cn);
    solver.assert_term(a2);
    let a3 = solver.eq(u, u);
    solver.assert_term(a3);

    let script = solver.query_dump_script(&[]);
    assert!(
        script.contains("(declare-sort |__verification_consumer_mutref::int| 0)"),
        "{script}"
    );
    assert!(script.contains("(declare-sort Unit 0)"), "{script}");

    // The dump must round-trip through ay's own front end with the same
    // verdict the native query has.
    assert_eq!(solver.check_sat(), SolveResult::Sat);
    assert_eq!(replay_through_own_frontend(&script), "sat", "{script}");

    // Soft oracle check: z3 (if present) must parse the script cleanly.
    soft_check_z3_parseable(&script, &["sat"]);
}

/// Native theory constructors are represented by named application nodes in
/// the core DAG, but they are not user functions.  The dump walker must not
/// fabricate declarations for them: the frontend deliberately rejects such a
/// declaration because it would conflate a user symbol with builtin semantics.
#[test]
fn query_dump_native_const_array_uses_builtin_syntax_and_roundtrips() {
    let mut solver = Solver::new(Logic::QfAuflia);
    let zero = solver.int_const(0);
    let array = solver.const_array(Sort::Int, zero);
    let named_array = solver.declare_const("array", Sort::array(Sort::Int, Sort::Int));
    let definition = solver.eq(named_array, array);
    solver.assert_term(definition);
    let index = solver.declare_const("index", Sort::Int);
    let read = solver.select(named_array, index);
    let assertion = solver.eq(read, zero);
    solver.assert_term(assertion);

    let script = solver.query_dump_script(&[]);
    assert!(
        !script.contains("(declare-fun const-array")
            && !script.contains("(declare-const const-array"),
        "builtin const-array was fabricated as a user declaration:\n{script}"
    );
    assert!(
        script.contains("((as const (Array Int Int)) 0)"),
        "constant array was not rendered with standard SMT-LIB syntax:\n{script}"
    );

    assert_eq!(solver.check_sat(), SolveResult::Sat);
    assert_eq!(replay_through_own_frontend(&script), "sat", "{script}");
    soft_check_z3_parseable(&script, &["sat"]);

    let sexpr = solver.assertions_sexpr(&solver.assertions());
    assert!(
        !sexpr.contains("(declare-fun const-array"),
        "Z3-shape assertion dump fabricated a builtin declaration:\n{sexpr}"
    );
    assert!(
        sexpr.contains("((as const (Array Int Int)) 0)"),
        "Z3-shape assertion dump used a nonstandard constant array:\n{sexpr}"
    );
}

/// `fresh_var` normally supplies quantifier/let binders, but programmatic
/// clients may also use one as a free constant. A standalone dump must declare
/// that free occurrence while keeping lexically bound occurrences local.
#[test]
fn query_dump_declares_free_fresh_vars_but_not_quantifier_binders() {
    let mut solver = Solver::new(Logic::All);
    let free = solver.fresh_var("dump_free", Sort::Int);
    let free_name = solver.format_term(free);
    let zero = solver.int_const(0);
    let free_nonnegative = solver.ge(free, zero);
    solver.assert_term(free_nonnegative);

    let bound = solver.fresh_var("dump_bound", Sort::Int);
    let bound_name = solver.format_term(bound);
    let tautology = solver.eq(bound, bound);
    let quantified = solver.forall(&[bound], tautology);
    solver.assert_term(quantified);

    let script = solver.query_dump_script(&[]);
    assert!(
        script.contains(&format!("(declare-const {free_name} Int)")),
        "free fresh variable was omitted from the standalone dump:\n{script}"
    );
    assert!(
        !script.contains(&format!("(declare-const {bound_name} ")),
        "quantifier binder leaked into the global declaration set:\n{script}"
    );
    assert!(
        script.contains(&format!("(forall (({bound_name} Int))")),
        "quantifier binder was not retained in lexical scope:\n{script}"
    );

    assert_eq!(solver.check_sat(), SolveResult::Sat);
    assert_eq!(replay_through_own_frontend(&script), "sat", "{script}");
    soft_check_z3_parseable(&script, &["sat"]);
}

/// Assumptions passed to `check_sat_assuming` are part of the dumped script;
/// a sort referenced only by an assumption term must still be declared.
#[test]
fn query_dump_includes_assumption_only_sorts() {
    let mut solver = Solver::new(Logic::All);
    let elem = Sort::Uninterpreted("Elem".to_string());
    let x = solver.declare_const("x", Sort::Int);
    let zero = solver.int_const(0);
    let base = solver.ge(x, zero);
    solver.assert_term(base);

    // The Elem-sorted symbols enter the query only through the assumption.
    let e1 = solver.declare_const("e1", elem.clone());
    let e2 = solver.declare_const("e2", elem);
    let assumption = solver.neq(e1, e2);

    let script = solver.query_dump_script(&[assumption]);
    assert!(script.contains("(declare-sort Elem 0)"), "{script}");
    assert!(script.contains("e1"), "{script}");

    assert_eq!(solver.check_sat_assuming(&[assumption]), SolveResult::Sat);
    assert_eq!(replay_through_own_frontend(&script), "sat", "{script}");
    soft_check_z3_parseable(&script, &["sat"]);
}

/// Native datatype dumps deliberately weaken constructor/selector/tester
/// semantics to UF. That weakening must be explicit in the file, and the
/// resulting constructor-, selector-, and tester-using script must still be a
/// genuine standalone input for AY and z3. Its SAT result remains inconclusive
/// by design; this test checks transportability, not oracle equivalence.
#[test]
fn query_dump_datatype_weakening_is_standalone_and_fail_visible() {
    let source = r#"
        (set-logic ALL)
        (declare-datatypes ((Pair 0))
            (((mk-pair (first Int) (second Int)))))
        (declare-const p Pair)
        (assert (= p (mk-pair 1 2)))
        (assert (= (first p) 1))
        (assert ((_ is mk-pair) p))
    "#;
    let commands = ay_frontend::parse(source).expect("parse datatype source");
    let mut exec = Executor::new();
    for command in &commands {
        exec.execute(command)
            .expect("execute datatype source before dumping");
    }

    let script = exec.to_smtlib2();
    assert!(
        script.contains("; WARNING: NOT oracle-equivalent"),
        "{script}"
    );
    assert!(script.contains("(declare-sort Pair 0)"), "{script}");
    assert!(script.contains("mk-pair"), "{script}");
    assert!(script.contains("first"), "{script}");
    assert!(script.contains("is-mk-pair"), "{script}");
    assert_eq!(replay_through_own_frontend(&script), "sat", "{script}");
    soft_check_z3_parseable(&script, &["sat"]);
}

/// End-to-end env-gated path: `AY_DUMP_QUERY_DIR` writes the self-contained
/// script from an isolated child test process. The parent never mutates its
/// process-global environment and validates the child's captured file.
#[test]
fn query_dump_env_writes_self_contained_file() {
    // Environment mutation in one test thread is visible to every other test
    // thread, including readers that do not participate in the cooperative env
    // mutex. Exercise the actual env-gated path in a dedicated child test
    // process instead. The parent sets the child environment on `Command`
    // without mutating its own process.
    if let Some(dir) = std::env::var_os(QUERY_DUMP_CHILD_DIR) {
        assert_eq!(
            std::env::var_os("AY_DUMP_QUERY_DIR").as_deref(),
            Some(dir.as_os_str()),
            "child sentinel and production dump directory diverged"
        );

        let mut solver = Solver::new(Logic::All);
        let carrier = Sort::Uninterpreted("qdump_env_test::sort".to_string());
        let c1 = solver.declare_const("qdump_env_test_c1", carrier.clone());
        let c2 = solver.declare_const("qdump_env_test_c2", carrier);
        let a = solver.neq(c1, c2);
        solver.assert_term(a);
        assert_eq!(solver.check_sat(), SolveResult::Sat);
        return;
    }

    let dir = tempfile::tempdir().expect("create query-dump child directory");
    let output = std::process::Command::new(
        std::env::current_exe().expect("resolve current ay-dpll test executable"),
    )
    .arg("--exact")
    .arg(QUERY_DUMP_TEST_NAME)
    .arg("--nocapture")
    .arg("--test-threads=1")
    .env(QUERY_DUMP_CHILD_DIR, dir.path())
    .env("AY_DUMP_QUERY_DIR", dir.path())
    .output()
    .expect("run isolated query-dump child test");
    assert!(
        output.status.success(),
        "isolated query-dump child failed (status {}):\nstdout:\n{}\nstderr:\n{}",
        output.status,
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );

    let mut matched = None;
    for entry in std::fs::read_dir(dir.path()).expect("dump dir was not created") {
        let path = entry.unwrap().path();
        let Ok(content) = std::fs::read_to_string(&path) else {
            continue;
        };
        if content.contains("qdump_env_test_c1") {
            matched = Some(content);
            break;
        }
    }
    let script = matched.expect("no dump file contained the test query");
    assert!(
        script.contains("(declare-sort |qdump_env_test::sort| 0)"),
        "{script}"
    );
    assert_eq!(replay_through_own_frontend(&script), "sat", "{script}");
}

/// Verdict preservation on the unsat side: a verification-consumer-shaped VC (mutable
/// borrow carrier sort, `fin(self) = cur(self) + 1`, negated postcondition)
/// must dump to a script that ay and z3 (if present) both refute.
#[test]
fn query_dump_roundtrips_unsat_verification_consumer_shaped_vc() {
    let mut solver = Solver::new(Logic::All);
    let mutref = Sort::Uninterpreted("__verification_consumer_mutref::int".to_string());
    let self_t = solver.declare_const("self", mutref.clone());
    let cur = solver.declare_fun("cur", std::slice::from_ref(&mutref), Sort::Int);
    let fin = solver.declare_fun("fin", &[mutref], Sort::Int);
    let cur_self = solver.apply(&cur, &[self_t]);
    let fin_self = solver.apply(&fin, &[self_t]);
    let one = solver.int_const(1);
    let cur_plus_1 = solver.add(cur_self, one);
    let step = solver.eq(fin_self, cur_plus_1);
    solver.assert_term(step);
    let post = solver.ge(fin_self, cur_self);
    let neg_post = solver.not(post);
    solver.assert_term(neg_post);

    let script = solver.query_dump_script(&[]);
    assert!(
        script.contains("(declare-sort |__verification_consumer_mutref::int| 0)"),
        "{script}"
    );

    assert!(solver.check_sat().is_unsat());
    assert_eq!(replay_through_own_frontend(&script), "unsat", "{script}");
    soft_check_z3_parseable(&script, &["unsat"]);
}
