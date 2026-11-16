// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![cfg(test)]

use super::*;

pub(super) fn check_transport(
    version: Version,
    source: &str,
    problem: &ChcProblem,
    bytes: &[u8],
    expected: &BigUint,
) {
    let text = std::str::from_utf8(bytes).expect("canonical artifact JSON");
    // Preserve field order, binding sets, sorts and every node/edge count.
    // With all concrete Boolean cells false, the output cannot equal the
    // original store(..., 41, true), regardless of the chosen input array.
    let true_cell = r#""kind":"bool","value":true"#;
    assert!(text.contains(true_cell));
    let false_arrays = text.replace(true_cell, r#""kind":"bool","value":false"#);
    assert_eq!(
        version
            .replay(problem, false_arrays.as_bytes())
            .unwrap_err()
            .reason,
        Reason::DerivationRejected,
    );
    if expected != &BigUint::from(1_u8) {
        let word = format!(r#""width":256,"value_hex":"{}""#, expected.to_str_radix(16));
        assert_eq!(text.matches(&word).count(), 1);
        let truncated = text.replace(&word, r#""width":256,"value_hex":"1""#);
        assert_eq!(
            version
                .replay(problem, truncated.as_bytes())
                .unwrap_err()
                .reason,
            Reason::DerivationRejected,
        );
    }
    let old_store = "(store obj_valid #x00000029 true)";
    assert_eq!(source.matches(old_store).count(), 1);
    let changed =
        ChcParser::parse(&source.replace(old_store, "(store obj_valid #x00000029 false)"))
            .expect("well-typed different source");
    changed
        .validate()
        .expect("source mutation remains well typed");
    assert_eq!(
        version.replay(&changed, bytes).unwrap_err().reason,
        Reason::ProblemHashMismatch,
    );
    // Identity rejection is not claimed as semantic replay of the new source.
    let checked = version
        .replay(problem, bytes)
        .expect("negative attempts cannot mutate original evidence");
    assert_original_values(&checked, expected);
}

fn reject_native_binding(problem: &ChcProblem, cex: &Counterexample, name: &str, value: SmtValue) {
    let mut derivation = cex.ground_derivation.clone().expect("actual BMC evidence");
    let step_index = derivation
        .steps
        .iter()
        .position(|step| step.env.contains_key(name))
        .expect("original named binding");
    assert!(derivation.steps[step_index]
        .env
        .insert(name.to_owned(), value)
        .is_some());
    assert_eq!(
        validate_ground_derivation(problem, &derivation),
        Err(GroundDerivationError::ConstraintFalse { step: step_index }),
    );
    let changed = cex.clone().with_ground_derivation(derivation);
    for version in [Version::V1, Version::V2] {
        assert_eq!(
            version.encode(problem, &changed).unwrap_err().reason,
            Reason::DerivationRejected
        );
    }
}

pub(super) fn check_native(problem: &ChcProblem, cex: &Counterexample, expected: &BigUint) {
    let output = cex
        .ground_derivation
        .as_ref()
        .unwrap()
        .steps
        .iter()
        .find_map(|step| step.env.get("obj_valid__out"))
        .expect("original output array");
    // Preserve the original default and all existing stores. A distinct
    // default alone need not establish array disequality to the evaluator.
    let (default, mut entries) = match output {
        SmtValue::ConstArray(default) => (default.clone(), Vec::new()),
        SmtValue::ArrayMap { default, entries } => (default.clone(), entries.clone()),
        _ => panic!("validated original array must be concrete"),
    };
    entries.push((SmtValue::BitVec(41, 32), SmtValue::Bool(false)));
    reject_native_binding(
        problem,
        cex,
        "obj_valid__out",
        SmtValue::ArrayMap { default, entries },
    );
    if expected != &BigUint::from(1_u8) {
        // Keep the correct width and canonical representation: only the high
        // half's numeric payload is lost, not the declared type.
        reject_native_binding(
            problem,
            cex,
            WORD,
            SmtValue::try_bitvec_from_u128(1, 256).expect("canonical BV256 low half"),
        );
    }
    validate_ground_derivation(problem, cex.ground_derivation.as_ref().unwrap())
        .expect("mutating clones cannot mutate original evidence");
}
