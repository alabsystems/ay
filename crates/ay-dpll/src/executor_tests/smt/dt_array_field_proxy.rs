// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Captured model-checker-consumer datatype-array field-proxy regression. The sibling fixture
//! retains every declaration, constant and query command of the 22-assertion
//! reduction. The original failure returned unknown after the array oracle
//! rejected a selected constructor against an independently defaulted field.

use super::*;
use std::time::Duration;

const REDUCED: &str = include_str!("dt_array_field_proxy.smt2");

fn with_assertions(assertions: &str) -> String {
    const CHECK: &str = "(check-sat)";
    assert_eq!(REDUCED.matches(CHECK).count(), 1);
    REDUCED.replacen(CHECK, &format!("{assertions}\n{CHECK}"), 1)
}

fn assert_verdict(input: &str, expected: &str) {
    let commands = parse(input).expect("captured fixture must parse");
    let mut exec = Executor::new();
    exec.set_timeout(Some(Duration::from_secs(27)));
    let outputs = exec
        .execute_all(&commands)
        .expect("fixture commands must execute");
    assert_eq!(
        outputs.len(),
        2,
        "retain check-sat and the original get-value: {outputs:?}"
    );
    assert_eq!(outputs[0], expected, "{outputs:?}");
    if expected == "sat" {
        assert!(
            outputs[1].starts_with("((") && outputs[1].ends_with("))"),
            "SAT must retain a readable get-value result: {outputs:?}"
        );
    } else {
        assert_eq!(outputs[1], "(error \"model is not available\")");
    }
}

#[test]
fn reduced_datatype_array_field_proxy_is_sat() {
    assert_verdict(REDUCED, "sat");
}

#[test]
fn equal_datatype_array_field_proxy_cannot_be_distinct() {
    // REDUCED already asserts equality of exactly these two terms. Keep that
    // equality and add its contradiction before the unchanged query commands.
    let input = with_assertions(
        "(assert (distinct mem_symbolic_9 \
         (select |dual_ra_inbounds::dual_ra_inbounds::local_47_0| #x0000000000000000)))",
    );
    assert_verdict(&input, "unsat");
}

#[test]
fn selected_nonzero_constructor_is_shared_by_both_array_cells() {
    // The original conditional fixes the second cell's function pointer to
    // #x0f5444d98f1b15fb and its Boolean field to true when local_36_0 is 1.
    // Sharing the two cells prevents an all-default, guard-false witness from
    // concealing inconsistent reconstruction of the fresh datatype fields.
    let input = with_assertions(
        "(assert (= |dual_ra_inbounds::dual_ra_inbounds::local_36_0| #x0000000000000001))\n\
         (assert (= mem_symbolic_9 mem_symbolic_11))",
    );
    assert_verdict(&input, "sat");
}

#[test]
fn datatype_array_field_proxy_get_value_preserves_shared_nonzero_constructor() {
    use ay_frontend::sexp::{parse_sexp, SExpr};

    let forced = with_assertions(
        "(assert (= |dual_ra_inbounds::dual_ra_inbounds::local_36_0| #x0000000000000001))\n\
         (assert (= mem_symbolic_9 mem_symbolic_11))",
    );
    let terms = "(mem_symbolic_9 mem_symbolic_11 \
        (select |dual_ra_inbounds::dual_ra_inbounds::local_47_0| #x0000000000000000) \
        (select |dual_ra_inbounds::dual_ra_inbounds::local_47_0| #x0000000000000001))";
    let input = format!("{forced}\n(get-value {terms})");
    let commands = parse(&input).expect("captured fixture and value query must parse");
    let mut exec = Executor::new();
    exec.set_timeout(Some(Duration::from_secs(27)));
    let outputs = exec
        .execute_all(&commands)
        .expect("fixture commands must execute");
    assert_eq!(
        outputs.len(),
        3,
        "retain both original query outputs: {outputs:?}"
    );
    assert_eq!(outputs[0], "sat", "{outputs:?}");
    assert!(
        outputs[1].starts_with("((") && outputs[1].ends_with("))"),
        "original get-value must remain readable: {outputs:?}"
    );

    let printed = parse_sexp(&outputs[2]).expect("datatype values must be SMT-LIB");
    let pairs = printed.as_list().expect("get-value must return a list");
    let expected_query = parse_sexp(terms).expect("value query terms must parse");
    let keys = expected_query
        .as_list()
        .expect("query terms must be a list");
    assert_eq!(pairs.len(), 4, "{printed:?}");
    let values: Vec<&SExpr> = pairs
        .iter()
        .enumerate()
        .map(|(index, pair)| {
            let pair = pair.as_list().expect("get-value entry must be a pair");
            assert_eq!(pair.len(), 2, "{pair:?}");
            assert_eq!(pair[0], keys[index], "query identity must be preserved");
            &pair[1]
        })
        .collect();
    for value in &values[1..] {
        assert_eq!(
            values[0], *value,
            "equal proxies and cells must print equally"
        );
    }
    let outer = values[0]
        .as_list()
        .expect("outer value must be a constructor");
    assert_eq!(outer.len(), 2, "{outer:?}");
    assert!(outer[0].is_symbol("core_fmt_rt_Argument_lt_mk"));
    let inner = outer[1]
        .as_list()
        .expect("field value must be a constructor");
    assert_eq!(inner.len(), 4, "{inner:?}");
    assert!(inner[0].is_symbol("Placeholder_core_fmt_rt_ArgumentType_lt"));
    let function_pointer = parse_sexp("#x0f5444d98f1b15fb").expect("valid BV64 literal");
    assert_eq!(
        inner[2], function_pointer,
        "preserve the selected nonzero field"
    );
    assert_eq!(inner[3], SExpr::True, "preserve the selected Boolean field");
}

#[test]
fn reduced_datatype_array_field_proxy_is_sat_with_cli_authored_proof_policy() {
    use ay_frontend::{Command, CommandStream, CommandStreamItem};

    let mut exec = Executor::new();
    // Match a plain `ay FILE.smt2 -t 27000`: standard rigor, demanded model,
    // and the budgeted synthesized-default file proof policy in run.rs.
    exec.context_mut().set_strict_logic_compliance(false);
    exec.set_strict_grant_evidence_required(false);
    exec.set_model_output_shedding(false);
    exec.set_best_effort_produce_proofs(1_000_000);
    exec.set_deadline(Some(
        ay_core::time::Instant::now() + Duration::from_secs(27),
    ));
    let mut stream = CommandStream::new(REDUCED);
    let mut outputs = Vec::new();
    loop {
        let start = stream.position();
        let Some(item) = stream.next_command() else {
            break;
        };
        let command = match item {
            CommandStreamItem::Command(command) => *command,
            CommandStreamItem::Error(error) => panic!("captured CLI input must parse: {error}"),
        };
        if matches!(command, Command::CheckSat | Command::CheckSatAssuming(_)) {
            exec.observe_authored_commands_ahead(&REDUCED[start..]);
        }
        exec.observe_authored_command_source(&REDUCED[start..stream.position()]);
        if let Some(output) = exec
            .execute_authored(&command)
            .expect("CLI command must execute")
        {
            outputs.push(output);
        }
        if matches!(command, Command::CheckSat) {
            assert!(
                exec.last_check_saw_authored_query_authority(),
                "the regression must exercise the authored CLI boundary"
            );
        }
    }
    assert_eq!(
        outputs.len(),
        2,
        "preserve the original query outputs: {outputs:?}"
    );
    assert_eq!(
        outputs[0], "sat",
        "CLI-policy witness must confirm: {outputs:?}"
    );
    assert!(
        outputs[1].starts_with("((") && outputs[1].ends_with("))"),
        "preserve the original readable get-value response: {outputs:?}"
    );
}
