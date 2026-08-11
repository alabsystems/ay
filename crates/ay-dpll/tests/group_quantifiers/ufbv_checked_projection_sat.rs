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
