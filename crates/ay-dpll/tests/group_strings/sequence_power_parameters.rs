// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

#[test]
fn sequence_power_parameters_global_option_changes_simplification_not_models() {
    let output =
        crate::common::solve_vec(include_str!("../fixtures/sequence_power_parameters.smt2"));
    assert_eq!(output.len(), 11, "{output:?}");
    assert!(output[0].contains("power"), "{output:?}");
    assert!(
        output[1].contains("str.++") && !output[1].contains("power"),
        "{output:?}"
    );
    assert!(output[2].contains("power"), "{output:?}");
    assert_eq!(output[3], "\"ababab\"");
    assert!(output[4].contains("power"), "{output:?}");
    assert!(
        output[5].contains("seq.++") && !output[5].contains("power"),
        "{output:?}"
    );
    assert_eq!(output[6], "\"\"");
    assert_eq!(output[7], "s");
    assert_eq!(&output[8..10], ["unsat", "sat"]);
    assert!(output[10].contains("\"ababab\""), "{output:?}");
}

#[test]
fn sequence_power_parameters_macro_modes_do_not_leak_into_normal_solving() {
    let input = include_str!("../fixtures/sequence_power_macro_modes.smt2");
    let output = crate::common::solve_vec(input);
    assert_eq!(
        output.last().map(String::as_str),
        Some("unsat"),
        "{output:?}"
    );
    assert!(
        output.iter().all(|value| !value.starts_with("(error")),
        "{output:?}"
    );
}

#[test]
fn sequence_power_parameters_normalized_alias_replaces_prior_setting() {
    let output = crate::common::solve_vec(include_str!(
        "../fixtures/sequence_power_normalized_option.smt2"
    ));
    assert_eq!(output.len(), 2, "{output:?}");
    assert!(output[0].contains("power"), "{output:?}");
    assert_eq!(output[1], "\"ababab\"");
}
