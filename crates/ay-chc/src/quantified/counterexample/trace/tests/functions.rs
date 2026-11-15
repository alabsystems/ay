// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

mod native;

#[test]
fn local_pins_still_refuse_a_missing_total_function_inventory() {
    let original = scalar_source();
    // An unused function still belongs to the complete authenticated source.
    let input = original.source_smtlib().replace(
        "(set-logic HORN)",
        "(set-logic HORN)\n(declare-fun unused ((_ BitVec 2)) (_ BitVec 2))",
    );
    let source = QuantifiedChcProblem::parse_smtlib(&input).unwrap();
    let token = CancellationToken::new();
    // Test-only metadata, not a claimed solver result. The refusal precedes
    // replay even when source/topology/script bindings match.
    let base = unchecked_base(&source, &token);
    assert!(bound_render(&base, &source, &control(&token)).is_some());
    assert!(base
        .concrete_trace(&source, Duration::ZERO, &token)
        .is_none());
    let forged = QuantifiedChcTrace {
        pinned_obligation: base.obligation.clone(),
        base,
        bindings: vec![],
        functions: vec![],
    };
    assert!(!forged.recheck(&source, Duration::from_secs(30), &token));
}

#[test]
fn scalar_function_signature_authentication_is_exact_not_nominal_or_width_truncated() {
    use crate::quantified::QuantifiedChcFunction;
    use ay_core::Sort;
    let declaration = QuantifiedChcFunction::new(
        "uf wide".into(),
        vec![ChcSort::Bool, ChcSort::BitVec(136)],
        ChcSort::BitVec(136),
    );
    let token = CancellationToken::new();
    let accepted = control(&token);
    let arguments = [Sort::Bool, Sort::bitvec(136)];
    let result = Sort::bitvec(136);
    assert!(
        authenticate_function(&declaration, "uf wide", &arguments, &result, &accepted).is_some()
    );
    for (name, args, result) in [
        ("other", arguments.to_vec(), result.clone()),
        (
            "uf wide",
            vec![Sort::bitvec(136), Sort::Bool],
            result.clone(),
        ),
        ("uf wide", vec![Sort::Bool], result.clone()),
        (
            "uf wide",
            vec![Sort::Bool, Sort::bitvec(128)],
            result.clone(),
        ),
        ("uf wide", arguments.to_vec(), Sort::bitvec(128)),
        ("uf wide", arguments.to_vec(), Sort::Bool),
        ("uf wide", vec![Sort::Bool, Sort::Int], result.clone()),
    ] {
        assert!(
            authenticate_function(&declaration, name, &args, &result, &control(&token)).is_none()
        );
    }
    assert!(!same_scalar_sort(&ChcSort::BitVec(0), &Sort::bitvec(0)));
    assert!(!same_scalar_sort(
        &ChcSort::BitVec(crate::MAX_BITVECTOR_WIDTH + 1),
        &Sort::bitvec(crate::MAX_BITVECTOR_WIDTH + 1),
    ));
    assert!(same_scalar_sort(
        &ChcSort::BitVec(crate::MAX_BITVECTOR_WIDTH),
        &Sort::bitvec(crate::MAX_BITVECTOR_WIDTH),
    ));
}

#[test]
fn function_signature_work_refusal_is_sticky_and_fresh_retry_is_independent() {
    use crate::quantified::QuantifiedChcFunction;
    let declaration = QuantifiedChcFunction::new("f".into(), vec![], ChcSort::BitVec(1));
    let token = CancellationToken::new();
    let exhausted = control(&token);
    exhausted.bytes(64 * 1024 * 1024).unwrap();
    assert!(authenticate_function(
        &declaration,
        "f",
        &[],
        &ay_core::Sort::bitvec(1),
        &exhausted
    )
    .is_none());
    assert!(exhausted.poll().is_none());
    let fresh = control(&token);
    assert!(
        authenticate_function(&declaration, "f", &[], &ay_core::Sort::bitvec(1), &fresh).is_some()
    );
    token.cancel();
    assert!(
        authenticate_function(&declaration, "f", &[], &ay_core::Sort::bitvec(1), &fresh).is_none()
    );
    token.reset();
    assert!(
        authenticate_function(&declaration, "f", &[], &ay_core::Sort::bitvec(1), &fresh).is_none()
    );
}

#[test]
fn combined_native_snapshot_allowances_are_earmarked_before_any_solver_exists() {
    let token = CancellationToken::new();
    let deadline = Instant::now() + Duration::from_secs(30);
    for function_names in [vec![], vec!["unused"]] {
        let allowance = if function_names.is_empty() { 24 } else { 48 } * 1024 * 1024;
        let exact = control(&token);
        exact.bytes(64 * 1024 * 1024 - allowance).unwrap();
        // Invalid header declines before Solver::try_new. A live final control
        // proves both complete response allowances were admitted exactly.
        assert!(replay::extract(
            "invalid",
            &[],
            &function_names,
            deadline,
            None,
            &token,
            &exact
        )
        .is_none());
        assert!(exact.bytes(0).is_some());
        assert!(exact.bytes(1).is_none());
        let short = control(&token);
        short.bytes(64 * 1024 * 1024 - allowance + 1).unwrap();
        assert!(replay::extract(
            "invalid",
            &[],
            &function_names,
            deadline,
            None,
            &token,
            &short
        )
        .is_none());
        assert!(short.poll().is_none());
        assert!(replay::extract(
            "invalid",
            &[],
            &function_names,
            deadline,
            None,
            &token,
            &short
        )
        .is_none());
        let fresh = control(&token);
        assert!(replay::extract(
            "invalid",
            &[],
            &function_names,
            deadline,
            None,
            &token,
            &fresh
        )
        .is_none());
        assert!(fresh.poll().is_some());
    }
}
