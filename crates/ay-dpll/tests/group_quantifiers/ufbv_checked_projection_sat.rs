// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! End-to-end checks for the independently certified UFBV projection lane.

const DIRECT_PROJECTION_QUERY: &str = r#"
(set-logic UFBV)
(set-option :produce-models true)
(declare-fun plain_projection ((_ BitVec 8) (_ BitVec 8)) (_ BitVec 8))
(assert
  (forall ((x (_ BitVec 8)) (y (_ BitVec 8)))
    (=> (= x y) (= (plain_projection y x) y))))
(check-sat)
"#;

#[test]
fn authored_plain_query_emits_checked_sat() {
    assert_eq!(
        crate::common::solve_authored_vec(DIRECT_PROJECTION_QUERY),
        ["sat"],
        "the checked total projection f(a,b)=a is a constructive model"
    );
}

#[test]
fn checked_projection_sat_survives_self_check() {
    assert_eq!(
        crate::common::solve_authored_selfcheck_vec(DIRECT_PROJECTION_QUERY),
        ["sat"],
        "self-check must recognize the same independently checked evidence"
    );
}

#[test]
fn generic_and_assumption_origins_cannot_acquire_projection_authority() {
    assert_ne!(
        crate::common::solve_vec(DIRECT_PROJECTION_QUERY),
        ["sat"],
        "the generic executor adapter is not an authored-query boundary"
    );

    let assuming = DIRECT_PROJECTION_QUERY.replace("(check-sat)", "(check-sat-assuming ())");
    assert_ne!(
        crate::common::solve_authored_vec(&assuming),
        ["sat"],
        "even empty check-sat-assuming has a distinct, ineligible authority origin"
    );
}

#[test]
fn checked_model_prints_and_evaluates_the_total_projection() {
    let script = DIRECT_PROJECTION_QUERY.replace(
        "(check-sat)",
        "(check-sat)\n(get-value ((plain_projection #x12 #x34)))\n(get-model)",
    );
    let output = crate::common::solve_authored_vec(&script);
    assert_eq!(output.first().map(String::as_str), Some("sat"));
    assert!(
        output
            .iter()
            .any(|line| line.contains("((plain_projection #x12 #x34) #x12)")),
        "get-value must follow the checked projection at a fresh argument tuple: {output:?}"
    );
    let model = output
        .iter()
        .find(|line| line.starts_with("(model"))
        .expect("get-model response");
    assert!(model.contains("define-fun plain_projection"), "{model}");
    assert!(model.contains("__ay_projection_arg_0"), "{model}");
    assert!(
        !model.contains("ite"),
        "the total projection must not degrade to a finite table: {model}"
    );
}

#[test]
fn later_projection_query_cannot_reuse_popped_solver_state() {
    let script = r#"
(set-logic UFBV)
(set-option :produce-models true)
(declare-fun seed () (_ BitVec 8))
(push 1)
(assert (= seed #x5a))
(check-sat)
(pop 1)
(declare-fun scoped_projection ((_ BitVec 8) (_ BitVec 8)) (_ BitVec 8))
(assert
  (forall ((x (_ BitVec 8)) (y (_ BitVec 8)))
    (=> (= x y) (= (scoped_projection y x) y))))
(check-sat)
(get-value ((scoped_projection #x12 #x34) seed))
"#;

    let output = crate::common::solve_authored_vec(script);
    assert_eq!(
        output.iter().filter(|line| line.as_str() == "sat").count(),
        2,
        "both the ordinary scoped query and the later checked query must solve: {output:?}"
    );
    assert!(
        output.iter().any(|line| {
            line.contains("(scoped_projection #x12 #x34) #x12")
                && line.contains("seed #x00")
        }),
        "the later witness must use the checked projection and a fresh canonical value, not the popped #x5a assignment: {output:?}"
    );
}

#[test]
fn scoped_declaration_identity_cannot_cross_pop_and_identical_redeclaration() {
    let script = r#"
(set-logic UFBV)
(set-option :produce-models true)
(push 1)
(declare-fun same_name ((_ BitVec 8) (_ BitVec 8)) (_ BitVec 8))
(assert
  (forall ((x (_ BitVec 8)) (y (_ BitVec 8)))
    (=> (= x y) (= (same_name y x) y))))
(check-sat)
(get-value ((same_name #x12 #x34)))
(pop 1)
(declare-fun same_name ((_ BitVec 8) (_ BitVec 8)) (_ BitVec 8))
(assert
  (forall ((x (_ BitVec 8)) (y (_ BitVec 8)))
    (=> (= x y) (= (same_name x y) y))))
(check-sat)
(get-value ((same_name #x12 #x34)))
"#;

    let output = crate::common::solve_authored_vec(script);
    assert_eq!(
        output.iter().filter(|line| line.as_str() == "sat").count(),
        2,
        "both independently checked declaration lifetimes must solve: {output:?}"
    );
    assert!(
        output
            .iter()
            .any(|line| line.contains("((same_name #x12 #x34) #x12)")),
        "the scoped declaration must use its own argument-0 projection: {output:?}"
    );
    assert!(
        output
            .iter()
            .any(|line| line.contains("((same_name #x12 #x34) #x34)")),
        "the identical redeclaration must use its fresh argument-1 projection: {output:?}"
    );
}

#[test]
fn multiple_checked_functions_share_one_exact_model_across_consumers() {
    let script = r#"
(set-logic UFBV)
(set-option :produce-models true)
(declare-fun project_left ((_ BitVec 8) (_ BitVec 8)) (_ BitVec 8))
(declare-fun project_right ((_ BitVec 8) (_ BitVec 8)) (_ BitVec 8))
(assert
  (forall ((x (_ BitVec 8)) (y (_ BitVec 8)))
    (=> (= x y)
        (and (= (project_left y x) y)
             (= (project_right x y) y)))))
(check-sat)
(get-value ((project_left #x12 #x34) (project_right #x12 #x34)))
(get-model)
"#;

    let output = crate::common::solve_authored_vec(script);
    assert_eq!(
        output.first().map(String::as_str),
        Some("sat"),
        "{output:?}"
    );
    assert!(
        output.iter().any(|line| {
            line.contains("(project_left #x12 #x34) #x12")
                && line.contains("(project_right #x12 #x34) #x34")
        }),
        "get-value must evaluate both checked total functions: {output:?}"
    );
    let model = output
        .iter()
        .find(|line| line.starts_with("(model"))
        .expect("get-model response");
    assert!(model.contains("define-fun project_left"), "{model}");
    assert!(model.contains("define-fun project_right"), "{model}");
}

#[test]
fn later_contradiction_revokes_projection_authority_and_model() {
    let script = r#"
(set-logic UFBV)
(declare-fun f ((_ BitVec 8) (_ BitVec 8)) (_ BitVec 8))
(assert
  (forall ((x (_ BitVec 8)) (y (_ BitVec 8)))
    (=> (= x y) (= (f y x) y))))
(check-sat)
(assert (not (= (f #x00 #x00) #x00)))
(check-sat)
"#;

    assert_eq!(
        crate::common::solve_authored_vec(script),
        ["sat", "unsat"],
        "a later assertion must retire the checked shortcut, its certificate, and its model"
    );
}

#[test]
fn mutable_context_escape_revokes_checked_sat_and_model_consumers() {
    use ay_dpll::Executor;
    use ay_frontend::parse;

    let mut executor = Executor::new();
    let commands = parse(DIRECT_PROJECTION_QUERY).expect("valid checked-projection query");
    let mut output = Vec::new();
    for command in &commands {
        if let Some(line) = executor
            .execute_authored(command)
            .expect("checked-projection query executes")
        {
            output.push(line);
        }
    }
    assert_eq!(output, ["sat"]);
    assert!(executor.last_result_is_sat());

    let mutation = parse("(assert false)").expect("valid context mutation");
    let _ = executor
        .context_mut()
        .process_command(&mutation[0])
        .expect("direct context mutation executes");

    assert!(
        !executor.last_result_is_sat(),
        "a mutable Context escape must revoke the preceding checked SAT"
    );
    for consumer in ["(get-model)", "(get-value ((plain_projection #x12 #x34)))"] {
        let command = parse(consumer).expect("valid model consumer");
        let response = executor
            .execute(&command[0])
            .expect("revoked model consumer executes")
            .expect("model consumer returns an error response");
        assert!(
            response.contains("model is not available"),
            "direct context mutation must not expose the stale projection model: {response}"
        );
    }
}

/// The `model_check_gate.result` value written when the ordinary
/// model-validation funnel's independent gate confirms a witness.
const CONFIRMED_SAT_INDEPENDENT_GATE: &str = "confirmed-sat";

/// The `model_check_gate.result` value written by the constructive projection
/// lane. It shares the `confirmed-sat` prefix so one census counts every
/// confirmed SAT, and carries a distinct suffix so the two authorities stay
/// tellable apart.
const CONFIRMED_SAT_CHECKED_PROJECTION: &str = "confirmed-sat-checked-projection";

/// A published `sat` must always name the authority that confirmed it.
///
/// This is the exact shape of the two UFBV corpus files
/// `wintersteiger/fmsd13/fixpoint/{small-swap2-fixpoint-6, itc-b13-fixpoint-7}`,
/// which reached `sat` through this lane while writing NO
/// `model_check_gate.result` at all — indistinguishable, to an evidence census,
/// from a `sat` nothing had confirmed. The lane's confirmation is real (an
/// `ay_model_check` proof kernel that depends on no solver code) but it was
/// reported only under `model_validation.checked_projection_certificate`, so
/// the signal every other SAT carries was simply missing.
#[test]
fn checked_projection_sat_names_its_confirming_authority() {
    let (output, gate) =
        crate::common::solve_authored_vec_with_gate_result(DIRECT_PROJECTION_QUERY);
    assert_eq!(output, ["sat"]);
    assert_eq!(
        gate.as_deref(),
        Some(CONFIRMED_SAT_CHECKED_PROJECTION),
        "the checked-projection lane must publish its own confirming authority"
    );
}

/// The lane names a DIFFERENT authority than the compositional gate.
///
/// The projection kernel proves a universal implication; the ordinary gate
/// evaluates a witness compositionally and reports `CannotConfirm` on any
/// quantifier. Collapsing both onto the bare `confirmed-sat` string would claim
/// an evaluation that never happened, so the values must stay distinguishable
/// while still sharing the prefix a census matches on.
#[test]
fn checked_projection_authority_is_distinguishable_from_the_compositional_gate() {
    let (_, gate) = crate::common::solve_authored_vec_with_gate_result(DIRECT_PROJECTION_QUERY);
    let gate = gate.expect("the checked-projection lane publishes a SAT-evidence signal");
    assert_ne!(
        gate, CONFIRMED_SAT_INDEPENDENT_GATE,
        "the projection lane must not be reported as the compositional gate's verdict"
    );
    assert!(
        gate.starts_with(CONFIRMED_SAT_INDEPENDENT_GATE),
        "a confirmed-SAT authority value must carry the shared census prefix: {gate}"
    );
}

/// An ordinary ground SAT keeps reporting exactly `confirmed-sat`.
///
/// The evidence value existing runs already publish must not shift under this
/// change: the constructive lanes add values, they do not rename the gate's.
#[test]
fn ordinary_ground_sat_still_reports_the_bare_independent_gate_value() {
    let (output, gate) = crate::common::solve_authored_vec_with_gate_result(
        "(set-logic QF_BV)\n\
         (declare-fun a () (_ BitVec 8))\n\
         (assert (= a #x2a))\n\
         (check-sat)\n",
    );
    assert_eq!(output, ["sat"]);
    assert_eq!(
        gate.as_deref(),
        Some(CONFIRMED_SAT_INDEPENDENT_GATE),
        "the ordinary funnel's published evidence value is unchanged"
    );
}

/// A query the lane cannot certify never acquires its authority value.
///
/// `check-sat-assuming` is a different, ineligible authority origin, so the
/// constructive lane declines and the verdict is not `sat`. Nothing may print
/// the lane's green signal for it — a confirmation value with no confirmation
/// behind it is the defect this signal exists to expose.
#[test]
fn ineligible_origin_gets_no_checked_projection_authority() {
    let assuming = DIRECT_PROJECTION_QUERY.replace("(check-sat)", "(check-sat-assuming ())");
    let (output, gate) = crate::common::solve_authored_vec_with_gate_result(&assuming);
    assert_ne!(
        output.first().map(String::as_str),
        Some("sat"),
        "an ineligible authority origin must not publish sat: {output:?}"
    );
    assert_ne!(
        gate.as_deref(),
        Some(CONFIRMED_SAT_CHECKED_PROJECTION),
        "an unconfirmed query must never carry the lane's confirmation value"
    );
}

/// A later checked query reports its own authority, not the previous solve's.
///
/// The scoped ordinary `check-sat` here is confirmed by the compositional gate;
/// the second is decided by the projection lane. Statistics are reset per
/// `check-sat`, so the published signal must describe the LAST verdict — a
/// stale `confirmed-sat` carried forward would attribute the quantified answer
/// to an evaluator that never saw it.
#[test]
fn later_checked_query_reports_its_own_authority_not_the_previous_solves() {
    let script = r#"
(set-logic UFBV)
(set-option :produce-models true)
(declare-fun seed () (_ BitVec 8))
(push 1)
(assert (= seed #x5a))
(check-sat)
(pop 1)
(declare-fun scoped_projection ((_ BitVec 8) (_ BitVec 8)) (_ BitVec 8))
(assert
  (forall ((x (_ BitVec 8)) (y (_ BitVec 8)))
    (=> (= x y) (= (scoped_projection y x) y))))
(check-sat)
"#;
    let (output, gate) = crate::common::solve_authored_vec_with_gate_result(script);
    assert_eq!(
        output.iter().filter(|line| line.as_str() == "sat").count(),
        2,
        "both queries must solve: {output:?}"
    );
    assert_eq!(
        gate.as_deref(),
        Some(CONFIRMED_SAT_CHECKED_PROJECTION),
        "the published signal must name the authority for the last verdict"
    );
}

/// The two named UFBV corpus files themselves carry the signal.
///
/// The hermetic tests above pin the shape; this pins the literal files the
/// evidence census counts. The corpus is gitignored, so this skips-and-passes
/// when it is absent — set `AY_REQUIRE_CORPUS=1` to make that a failure.
#[test]
fn wintersteiger_fixpoint_corpus_files_carry_the_sat_evidence_signal() {
    for name in [
        "non-incremental__UFBV__wintersteiger__fmsd13__fixpoint__small-swap2-fixpoint-6.smt2",
        "non-incremental__UFBV__wintersteiger__fmsd13__fixpoint__itc-b13-fixpoint-7.smt2",
    ] {
        let path = crate::common::workspace_path(format!("benchmarks/smtlib-all/UFBV/{name}"));
        if !path.exists() {
            assert!(crate::common::corpus_skip_allowed(&path));
            continue;
        }
        let smt = std::fs::read_to_string(&path).expect("readable corpus file");
        let (output, gate) = crate::common::solve_authored_vec_with_gate_result(&smt);
        assert_eq!(
            output.first().map(String::as_str),
            Some("sat"),
            "{name} must still solve sat"
        );
        assert_eq!(
            gate.as_deref(),
            Some(CONFIRMED_SAT_CHECKED_PROJECTION),
            "{name} must publish the checked-projection confirmation authority"
        );
    }
}
