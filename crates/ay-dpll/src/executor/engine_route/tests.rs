// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::super::Executor;
use ay_frontend::parse;

fn run(exec: &mut Executor, script: &str) -> Vec<String> {
    let commands = parse(script).expect("script parses");
    exec.execute_all(&commands).expect("script executes")
}

fn shed() -> Executor {
    let mut exec = Executor::new();
    exec.set_competition_mode(true);
    exec
}

/// Both postures: the `--z3-mode` one and the default one.
fn postures() -> [Executor; 2] {
    [shed(), Executor::new()]
}

fn verdicts(out: &[String]) -> Vec<&str> {
    out.iter()
        .map(String::as_str)
        .filter(|l| matches!(*l, "sat" | "unsat" | "unknown"))
        .collect()
}

fn kernel(exec: &Executor) -> Option<&str> {
    exec.last_statistics.get_string("engine.kernel")
}

fn fallback(exec: &Executor) -> Option<&str> {
    exec.last_statistics.get_string("engine.fallback")
}

/// Needs a search: a disjunction over bounds, one side refuted by a sum.
const SAT_SCRIPT: &str = "(set-logic QF_LRA)\n\
    (declare-const x Real) (declare-const y Real) (declare-const p Bool)\n\
    (assert (or (and p (< x 0.0)) (and (not p) (> x 3.0))))\n\
    (assert (>= (+ x y) 2.0)) (assert (<= y 1.5)) (assert (distinct x 4.0))\n\
    (check-sat)\n";

const UNSAT_SCRIPT: &str = "(set-logic QF_LRA)\n\
    (declare-const x Real) (declare-const y Real) (declare-const z Real)\n\
    (assert (or (< x y) (< y z)))\n\
    (assert (or (>= x y) (< z x)))\n\
    (assert (>= x z)) (assert (or (>= y z) (>= z (+ x 1.0))))\n\
    (assert (or (< y x) (> y (+ z 2.0))))\n\
    (assert (<= (- y z) 1.0)) (assert (>= y x))\n\
    (check-sat)\n";

/// QF_UF that needs congruence, a Boolean argument and a predicate.
const UF_SAT: &str = "(set-logic QF_UF)\n\
    (declare-sort U 0)\n\
    (declare-fun a () U) (declare-fun b () U) (declare-fun q () Bool)\n\
    (declare-fun f (U) U) (declare-fun p (U Bool) Bool)\n\
    (assert (not (= (f a) a))) (assert (= (f (f a)) b))\n\
    (assert (p a q)) (assert (not (p (f a) q)))\n\
    (check-sat)\n";

/// Congruence refutes it: `a = b` forces `f a = f b`.
const UF_UNSAT: &str = "(set-logic QF_UF)\n\
    (declare-sort U 0)\n\
    (declare-fun a () U) (declare-fun b () U) (declare-fun c () U)\n\
    (declare-fun f (U) U)\n\
    (assert (or (= a b) (= a c))) (assert (= b c))\n\
    (assert (not (= (f a) (f c))))\n\
    (check-sat)\n";

#[test]
fn the_kernel_answers_qf_lra_in_the_shed_posture() {
    let mut exec = shed();
    let out = run(&mut exec, SAT_SCRIPT);
    assert_eq!(out.last().map(String::as_str), Some("sat"));
    let st = &exec.last_statistics;
    assert_eq!(kernel(&exec), Some("sat"), "{st:?}");
    assert_eq!(st.get_int("engine.solve_calls"), Some(1));
    assert_eq!(fallback(&exec), None);
    // The model the gates accepted is the kernel's, and it is printable.
    let values = run(&mut exec, "(get-value (x y p))\n");
    assert_eq!(values.len(), 1, "{values:?}");
    assert!(
        values[0].contains('x') && values[0].contains('p'),
        "{values:?}"
    );

    let mut exec = shed();
    let out = run(&mut exec, UNSAT_SCRIPT);
    assert_eq!(out.last().map(String::as_str), Some("unsat"));
    let st = &exec.last_statistics;
    assert_eq!(kernel(&exec), Some("unsat"), "{st:?}");
    assert_eq!(st.get_int("engine.solve_calls"), Some(1));
}

/// The default posture certifies every QF_LRA `unsat` from the proof the
/// lane records; the kernel does not produce that certificate yet.
#[test]
fn the_default_posture_keeps_the_qf_lra_lane() {
    for script in [SAT_SCRIPT, UNSAT_SCRIPT] {
        let mut exec = Executor::new();
        let out = run(&mut exec, script);
        assert!(matches!(
            out.last().map(String::as_str),
            Some("sat" | "unsat")
        ));
        assert_eq!(kernel(&exec), None);
    }
}

/// A proof demand in the shed posture also keeps the QF_LRA lane.
#[test]
fn a_proof_demand_keeps_the_qf_lra_lane() {
    let mut exec = shed();
    let out = run(
        &mut exec,
        &format!("(set-option :produce-proofs true)\n{UNSAT_SCRIPT}"),
    );
    assert_eq!(out.last().map(String::as_str), Some("unsat"));
    assert_eq!(kernel(&exec), None);
}

/// QF_LRA push/pop sessions keep the persistent lane.
#[test]
fn a_qf_lra_incremental_session_keeps_the_lane() {
    let mut exec = shed();
    let script = SAT_SCRIPT.replace("(check-sat)", "(push 1) (check-sat)");
    let out = run(&mut exec, &script);
    assert_eq!(out.last().map(String::as_str), Some("sat"));
    assert_eq!(kernel(&exec), None);
}

/// Several check-sats without push/pop are each the kernel's, and each is
/// one search.
#[test]
fn every_top_level_check_is_one_search() {
    let mut exec = shed();
    let script = format!(
        "{}(assert (> y 1.0)) (check-sat)\n(assert (< x 0.0)) (check-sat)\n",
        SAT_SCRIPT
    );
    let out = run(&mut exec, &script);
    assert_eq!(verdicts(&out), ["sat", "sat", "unsat"], "{out:?}");
    let st = &exec.last_statistics;
    assert_eq!(kernel(&exec), Some("unsat"), "{st:?}");
    assert_eq!(st.get_int("engine.solve_calls"), Some(1));
}

/// QF_UF `sat` is the kernel's in both postures, and `get-value` and
/// `get-model` read the kernel's model.
#[test]
fn the_kernel_answers_qf_uf_sat_in_both_postures() {
    for mut exec in postures() {
        let out = run(&mut exec, UF_SAT);
        assert_eq!(verdicts(&out), ["sat"], "{out:?}");
        assert_eq!(kernel(&exec), Some("sat"), "{:?}", exec.last_statistics);
        assert_eq!(fallback(&exec), None);
        assert_eq!(exec.last_statistics.get_int("engine.solve_calls"), Some(1));
        let values = run(
            &mut exec,
            "(get-value ((f a) a (f (f a)) b (p a q) (p (f a) q)))\n",
        );
        assert_eq!(values.len(), 1, "{values:?}");
        let text = &values[0];
        assert!(!text.contains("error"), "{text}");
        assert!(text.contains("((p a q) true)"), "{text}");
        assert!(text.contains("((p (f a) q) false)"), "{text}");
        let model = run(&mut exec, "(get-model)\n");
        assert!(
            model[0].contains("define-fun f") && model[0].contains("define-fun p"),
            "{model:?}"
        );
        assert!(!model[0].contains("error"), "{model:?}");
    }
}

/// A QF_UF `unsat` is published by the kernel in the `--z3-mode` posture;
/// the default posture asks for a checked certificate, so the lane decides
/// again and certifies it.
#[test]
fn a_qf_uf_unsat_needs_the_lane_in_the_default_posture() {
    let mut exec = shed();
    let out = run(&mut exec, UF_UNSAT);
    assert_eq!(verdicts(&out), ["unsat"], "{out:?}");
    assert_eq!(kernel(&exec), Some("unsat"));
    assert_eq!(fallback(&exec), None);

    let mut exec = Executor::new();
    let out = run(&mut exec, UF_UNSAT);
    assert_eq!(verdicts(&out), ["unsat"], "{out:?}");
    assert_eq!(
        fallback(&exec),
        Some("unsat needs the lane's certificate"),
        "{:?}",
        exec.last_statistics
    );
    assert_eq!(exec.last_statistics.get_int("engine.disagree"), None);
}

/// The lane's model for this file breaks congruence (x = y with f x != f y)
/// and its gate withholds it; the kernel's passes.
#[test]
fn the_kernel_answers_a_qf_uflra_disequality_between_applications() {
    let script = "(set-logic QF_UFLRA)\n\
        (declare-fun x () Real) (declare-fun y () Real) (declare-fun f (Real) Real)\n\
        (assert (distinct (f x) (f y)))\n\
        (check-sat)\n(get-value (x y (f x) (f y)))\n";
    for mut exec in postures() {
        let out = run(&mut exec, script);
        assert_eq!(verdicts(&out), ["sat"], "{out:?}");
        assert_eq!(kernel(&exec), Some("sat"));
        assert!(!out[1].contains("error"), "{out:?}");
    }
}

/// An application over a term-level `ite` is read back through the named
/// window: the kernel valued `(f k)` for the name `k` of the `ite`.
#[test]
fn an_application_over_an_ite_reads_the_kernels_table() {
    let script = "(set-logic QF_UF)\n\
        (declare-sort U 0)\n\
        (declare-fun a () U) (declare-fun b () U) (declare-fun c () U)\n\
        (declare-fun p () Bool) (declare-fun f (U) U)\n\
        (assert (= (f (ite p a b)) c)) (assert (not (= (f a) c)))\n\
        (check-sat)\n(get-value (p (f b) c))\n";
    for mut exec in postures() {
        let out = run(&mut exec, script);
        assert_eq!(verdicts(&out), ["sat"], "{out:?}");
        assert_eq!(kernel(&exec), Some("sat"), "{:?}", exec.last_statistics);
        assert_eq!(fallback(&exec), None);
        assert!(out[1].contains("(p false)"), "{out:?}");
    }
}

/// Push/pop and repeated check-sats: each check is one kernel search over
/// the current stack, and every model is served from the check it answered.
#[test]
fn incremental_qf_uf_sessions_are_the_kernels() {
    let script = "(set-logic QF_UF)\n\
        (declare-sort U 0)\n\
        (declare-fun a () U) (declare-fun b () U) (declare-fun f (U) U)\n\
        (assert (not (= (f a) (f b))))\n\
        (check-sat)\n(get-value ((= a b)))\n\
        (push 1) (assert (= a b)) (check-sat) (pop 1)\n\
        (check-sat)\n(get-value ((f a) (f b)))\n\
        (push 1) (declare-fun c () U) (assert (= (f c) (f a))) (check-sat)\n\
        (get-value ((= (f c) (f b))))\n(pop 1)\n";
    for mut exec in postures() {
        let out = run(&mut exec, script);
        assert_eq!(verdicts(&out), ["sat", "unsat", "sat", "sat"], "{out:?}");
        assert!(out.iter().all(|line| !line.contains("error")), "{out:?}");
        assert!(out[1].contains("false"), "{out:?}");
        assert!(out.last().is_some_and(|l| l.contains("false")), "{out:?}");
        assert_eq!(kernel(&exec), Some("sat"));
    }
}

/// A check the kernel gives up on goes to the lane, whose verdict stands;
/// the session continues with the kernel. No plug-in owns `mod` by zero.
#[test]
fn a_kernel_give_up_hands_the_check_to_the_lane() {
    let first = "(set-logic QF_UFLIA)\n\
        (declare-fun x () Int) (declare-fun f (Int) Int)\n\
        (push 1) (assert (= (f (mod x 0)) 3)) (assert (> x 2)) (check-sat)\n";
    let then = "(pop 1)\n(assert (> (f x) x)) (check-sat)\n";
    for mut exec in postures() {
        let out = run(&mut exec, first);
        assert_eq!(verdicts(&out), ["sat"], "{out:?}");
        assert_eq!(kernel(&exec), Some("unknown"), "{:?}", exec.last_statistics);
        assert!(
            fallback(&exec).is_some_and(|why| why.contains("no plug-in owns `mod`")),
            "{:?}",
            exec.last_statistics
        );
        let out = run(&mut exec, then);
        assert_eq!(verdicts(&out), ["sat"], "{out:?}");
        assert_eq!(kernel(&exec), Some("sat"), "{:?}", exec.last_statistics);
        assert_eq!(fallback(&exec), None);
    }
}

/// A user declaration the term layer stores under its private identity
/// (`__ay_overload_N`: a builtin's name such as `abs`, or a name declared
/// again after a pop) is uninterpreted to the kernel and to the route's
/// model read-back alike, so the kernel's `sat` publishes and `get-value` /
/// `get-model` read its table.
#[test]
fn a_user_declaration_under_a_private_identity_is_the_kernels() {
    let builtin_name = "(set-logic QF_UF)\n\
        (declare-sort U 0)\n\
        (declare-fun a () U) (declare-fun b () U) (declare-fun abs (U) U)\n\
        (assert (not (= (abs a) (abs b))))\n\
        (check-sat)\n(get-value ((abs a) (abs b)))\n(get-model)\n";
    let redeclared = "(set-logic QF_UF)\n\
        (declare-sort U 0)\n\
        (declare-fun a () U) (declare-fun b () U)\n\
        (push 1) (declare-fun f (U) U) (assert (not (= (f a) (f b)))) (check-sat) (pop 1)\n\
        (declare-fun f (U U) Bool)\n\
        (assert (f a b)) (assert (not (f b a))) (check-sat)\n\
        (get-value ((f a b) (f b a)))\n(get-model)\n";
    for (script, verdicts_wanted, symbol) in [
        (builtin_name, &["sat"][..], "abs"),
        (redeclared, &["sat", "sat"][..], "f"),
    ] {
        for mut exec in postures() {
            let out = run(&mut exec, script);
            assert_eq!(verdicts(&out), verdicts_wanted, "{out:?}");
            assert_eq!(kernel(&exec), Some("sat"), "{:?}", exec.last_statistics);
            assert_eq!(fallback(&exec), None, "{:?}", exec.last_statistics);
            let n = verdicts_wanted.len();
            assert!(!out[n].contains("error"), "{out:?}");
            assert!(
                out[n + 1].contains(&format!("define-fun {symbol} ")),
                "{out:?}"
            );
            assert!(!out[n + 1].contains("__ay_overload"), "{out:?}");
        }
    }
}

/// `check-sat-assuming` keeps the lane: failed-assumption cores are its.
#[test]
fn check_sat_assuming_keeps_the_lane() {
    let script = "(set-logic QF_UF)\n\
        (declare-sort U 0)\n\
        (declare-fun a () U) (declare-fun b () U) (declare-fun s () Bool)\n\
        (declare-fun f (U) U)\n\
        (assert (=> s (= a b))) (assert (not (= (f a) (f b))))\n\
        (check-sat-assuming (s))\n";
    for mut exec in postures() {
        let out = run(&mut exec, script);
        assert_eq!(verdicts(&out), ["unsat"], "{out:?}");
        assert_eq!(kernel(&exec), None);
    }
}

/// QF_UFLIA is the kernel's in both postures.
#[test]
fn qf_uflia_is_the_kernels_in_both_postures() {
    let script = "(set-logic QF_UFLIA)\n\
        (declare-fun x () Int) (declare-fun f (Int) Int)\n\
        (assert (> (f x) x)) (assert (= (f (+ x 1)) (- (f x) 2))) (check-sat)\n\
        (get-value ((f x) (f (+ x 1))))\n";
    for mut exec in postures() {
        let out = run(&mut exec, script);
        assert_eq!(verdicts(&out), ["sat"], "{out:?}");
        assert_eq!(kernel(&exec), Some("sat"), "{:?}", exec.last_statistics);
        assert_eq!(fallback(&exec), None);
        assert!(!out[1].contains("error"), "{out:?}");
    }
}

/// QF_UFIDL is the kernel's in the `--z3-mode` posture; the default posture
/// keeps its lane.
#[test]
fn qf_ufidl_is_the_kernels_in_the_shed_posture_only() {
    let script = "(set-logic QF_UFIDL)\n\
        (declare-fun x () Int) (declare-fun y () Int) (declare-fun f (Int) Int)\n\
        (assert (< (- x y) 3)) (assert (distinct (f x) (f y))) (check-sat)\n";
    let mut exec = shed();
    let out = run(&mut exec, script);
    assert_eq!(verdicts(&out), ["sat"], "{out:?}");
    assert_eq!(kernel(&exec), Some("sat"), "{:?}", exec.last_statistics);

    let mut exec = Executor::new();
    let out = run(&mut exec, script);
    assert_eq!(verdicts(&out), ["sat"], "{out:?}");
    assert_eq!(kernel(&exec), None);
}

/// A QF_UFLRA script whose content is the arithmetic alone stays in its
/// division's family: the kernel answers its push/pop check (the QF_LRA lane
/// ran this one to its timeout).
#[test]
fn a_qf_uflra_script_without_functions_is_the_kernels_under_push() {
    let script = "(set-logic QF_UFLRA)\n(declare-fun x0 () Real)\n\
        (assert (<= x0 6.0)) (assert (> x0 6.0))\n(push 1)\n(check-sat)\n";
    let mut exec = shed();
    let out = run(&mut exec, script);
    assert_eq!(verdicts(&out), ["unsat"], "{out:?}");
    assert_eq!(kernel(&exec), Some("unsat"));
}

/// The kernel's model is published as it was checked: the counterexample
/// minimizer moved `k17` under the row the table read for the named `ite`,
/// and `get-model` printed a `t16` that was not a function.
#[test]
fn a_kernel_model_prints_its_tables_as_functions() {
    let script = "(set-logic QF_UFLRA)\n(set-option :produce-models true)\n\
        (declare-fun b2 () Bool) (declare-fun t16 (Real) Bool) (declare-fun k17 () Real)\n\
        (assert (not (= (t16 (ite b2 k17 (+ k17 1.0))) (t16 k17))))\n\
        (check-sat)\n(get-model)\n";
    for mut exec in postures() {
        let out = run(&mut exec, script);
        assert_eq!(verdicts(&out), ["sat"], "{out:?}");
        assert_eq!(kernel(&exec), Some("sat"), "{:?}", exec.last_statistics);
        assert!(out[1].contains("define-fun t16"), "{out:?}");
        assert!(!out[1].contains("error"), "{out:?}");
    }
}

/// A resource limit keeps the lane, which arms the count; the kernel cannot
/// read ay-sat's search ticks yet (DR-36). That holds for every family the
/// kernel owns, in both postures. `:rlimit 0` is no limit, so that check
/// stays the kernel's.
#[test]
fn a_resource_limit_keeps_the_lane() {
    for (script, verdict) in [(SAT_SCRIPT, "sat"), (UNSAT_SCRIPT, "unsat")] {
        let mut exec = shed();
        let out = run(
            &mut exec,
            &format!("(set-option :rlimit 1000000)\n{script}"),
        );
        assert_eq!(verdicts(&out), [verdict], "{out:?}");
        assert_eq!(kernel(&exec), None, "{:?}", exec.last_statistics);
        assert_eq!(fallback(&exec), None, "{:?}", exec.last_statistics);
    }
    for script in [UF_SAT, UF_UNSAT] {
        for mut exec in postures() {
            let out = run(
                &mut exec,
                &format!("(set-option :rlimit 1000000)\n{script}"),
            );
            assert_eq!(verdicts(&out).len(), 1, "{out:?}");
            assert_eq!(kernel(&exec), None, "{:?}", exec.last_statistics);
            assert_eq!(fallback(&exec), None, "{:?}", exec.last_statistics);
        }
    }

    let mut exec = shed();
    exec.set_resource_limit(Some(1_000_000));
    let out = run(&mut exec, UF_SAT);
    assert_eq!(verdicts(&out), ["sat"], "{out:?}");
    assert_eq!(kernel(&exec), None);

    let mut exec = shed();
    let out = run(&mut exec, &format!("(set-option :rlimit 0)\n{SAT_SCRIPT}"));
    assert_eq!(verdicts(&out), ["sat"], "{out:?}");
    assert_eq!(kernel(&exec), Some("sat"), "{:?}", exec.last_statistics);
}
