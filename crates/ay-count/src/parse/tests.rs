// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// Textually included by `parse::tests` to preserve the existing test FQNs.

use proptest::prelude::*;

#[cfg(test)]
fn rat(s: &str) -> BigRational {
    parse_rational(s).unwrap()
}

#[cfg(test)]
fn real(value: i64) -> RawWeight {
    RawWeight::Rat(BigRational::from_integer(value.into()))
}

#[test]
fn rational_forms() {
    assert_eq!(rat("0.4"), BigRational::new(2.into(), 5.into()));
    assert_eq!(rat("3/10"), BigRational::new(3.into(), 10.into()));
    assert_eq!(rat("-0.5"), BigRational::new((-1).into(), 2.into()));
    assert_eq!(rat("1.23e+4"), BigRational::from_integer(12300.into()));
    assert_eq!(rat("1e-2"), BigRational::new(1.into(), 100.into()));
    assert_eq!(rat("7"), BigRational::from_integer(7.into()));
    assert!(parse_rational("1/0").is_err());
    assert!(parse_rational("abc").is_err());
}

#[test]
fn rational_exponent_does_not_wrap_or_amplify_without_bound() {
    assert!(parse_rational("1e4294967296").is_err());
    assert!(parse_rational("1e-9223372036854775808").is_err());
    assert!(parse_rational("1e1000001").is_err());
}

#[test]
fn zero_at_exponent_bound_is_canonical_without_power_expansion() {
    assert!(parse_rational("0e1000000").unwrap().is_zero());
    assert!(parse_rational("-0e-1000000").unwrap().is_zero());
}

#[test]
fn parser_rejects_compact_expanded_weight() {
    let error = parse_instance("c t wmc\np cnf 1 0\nc p weight 1 1e10000 0\n")
        .expect_err("expanded weight must remain proportional to its token");
    assert!(error.0.contains("expanded weight requires"));
    assert!(error.0.contains("limit for its 7-byte token"));
}

#[test]
fn aggregate_weight_budget_checks_limit_and_overflow_without_allocation() {
    assert_eq!(
        checked_total_weight_bits(MAX_TOTAL_WEIGHT_BITS - 1, 1).unwrap(),
        MAX_TOTAL_WEIGHT_BITS
    );
    assert!(checked_total_weight_bits(MAX_TOTAL_WEIGHT_BITS, 1)
        .unwrap_err()
        .0
        .contains("exceeding the supported maximum"));
    assert!(checked_total_weight_bits(u64::MAX, 1)
        .unwrap_err()
        .0
        .contains("bit count overflows"));
}

#[test]
fn parser_rejects_variable_count_above_dense_allocation_cap() {
    let text = format!("p cnf {} 0\n", MAX_COUNT_VARS + 1);
    let error = parse_instance(&text).expect_err("overlarge header must fail closed");
    assert!(error.to_string().contains("maximum supported"));
}

#[test]
fn complex_weight_forms() {
    match parse_weight("0.4+0.2i").unwrap() {
        RawWeight::Complex(re, im) => {
            assert_eq!(re, rat("0.4"));
            assert_eq!(im, rat("0.2"));
        }
        RawWeight::Rat(_) => panic!("expected complex"),
    }
    match parse_weight("0.6-0.6i").unwrap() {
        RawWeight::Complex(re, im) => {
            assert_eq!(re, rat("0.6"));
            assert_eq!(im, rat("-0.6"));
        }
        RawWeight::Rat(_) => panic!("expected complex"),
    }
    match parse_weight("1/2+3/10i").unwrap() {
        RawWeight::Complex(re, im) => {
            assert_eq!(re, rat("1/2"));
            assert_eq!(im, rat("3/10"));
        }
        RawWeight::Rat(_) => panic!("expected complex"),
    }
    match parse_weight("1.2e+3+0.5i").unwrap() {
        RawWeight::Complex(re, im) => {
            assert_eq!(re, rat("1200"));
            assert_eq!(im, rat("0.5"));
        }
        RawWeight::Rat(_) => panic!("expected complex"),
    }
}

#[test]
fn parses_spec_example_1() {
    let text = "c c comment\np cnf 6 4\nc t mc\n-1 -2\n0\n2 3 -4 0\n4 5 0\n4 6 0\n";
    let inst = parse_instance(text).unwrap();
    assert_eq!(inst.num_vars, 6);
    assert_eq!(inst.clauses.len(), 4);
    assert_eq!(inst.ptype, ProblemType::Mc);
    assert_eq!(inst.clauses[0], vec![-1, -2]);
}

#[test]
fn parses_spec_example_4_pmc() {
    let text = "p cnf 6 4 2\nc t pmc\nc p show 1 2 0\n-1 -2 0\n2 3 -4 0\n4 5 0\n4 6 0\n";
    let inst = parse_instance(text).unwrap();
    assert_eq!(inst.ptype, ProblemType::Pmc);
    assert_eq!(inst.show, Some(vec![1, 2]));
}

#[test]
fn rejects_excess_clauses() {
    let text = "p cnf 2 1\n1 0\n2 0\n";
    assert!(parse_instance(text).is_err());
}

#[test]
fn rejects_unterminated_excess_clause() {
    let text = "p cnf 1 0\n1";
    let error = parse_instance(text).expect_err("unterminated clause still counts");
    assert!(error.to_string().contains("more clauses than the 0"));
}

#[test]
fn infers_wmc_from_weight_lines() {
    let text = "p cnf 2 1\nc p weight 1 0.4 0\nc p weight -1 0.6 0\n1 2 0\n";
    let inst = parse_instance(text).unwrap();
    assert_eq!(inst.ptype, ProblemType::Wmc);
}

#[test]
fn weight_complement_defaulting() {
    let raw = vec![(1i32, RawWeight::Rat(rat("0.4")))];
    let resolved = resolve_real_weights(1, &raw, None).unwrap();
    assert_eq!(resolved.weights[0], rat("0.4"));
    assert_eq!(resolved.weights[1], rat("0.6"));
    assert_eq!(resolved.warnings.len(), 1);
}

#[test]
fn nonpositive_weight_without_complement_is_error() {
    let raw = vec![(1i32, RawWeight::Rat(rat("-0.5")))];
    assert!(resolve_real_weights(1, &raw, None).is_err());
}

#[test]
fn negative_weight_with_complement_ok() {
    let raw = vec![
        (1i32, RawWeight::Rat(rat("-0.5"))),
        (-1i32, RawWeight::Rat(rat("1.5"))),
    ];
    let resolved = resolve_real_weights(1, &raw, None).unwrap();
    assert_eq!(resolved.weights[0], rat("-0.5"));
    assert_eq!(resolved.weights[1], rat("1.5"));
}

#[test]
fn missing_terminator_on_show_is_error() {
    let text = "p cnf 2 1\nc p show 1 2\n1 0\n";
    assert!(parse_instance(text).is_err());
}

#[test]
fn show_rejects_tokens_after_terminator() {
    let error = parse_instance("p cnf 2 0\nc p show 1 0 2\n")
        .expect_err("projection terminator must end its record");
    assert!(error.to_string().contains("trailing token `2`"));
}

#[test]
fn weight_accepts_compatible_terminators_only() {
    for line in ["c p weight 1 1/2", "c p weight 1 1/2 0"] {
        let text = format!("p cnf 1 0\n{line}\n");
        assert!(parse_instance(&text).is_ok(), "line should parse: {line}");
    }
    for line in ["c p weight 1 1/2 junk", "c p weight 1 1/2 0 junk"] {
        let text = format!("p cnf 1 0\n{line}\n");
        assert!(parse_instance(&text).is_err(), "line must fail: {line}");
    }
}

#[test]
fn instance_validation_rejects_invalid_public_field_values() {
    let mut instance = parse_instance("p cnf 2 0\nc p show 1 0\n").unwrap();
    instance.clauses.push(vec![0]);
    assert!(instance
        .validate()
        .unwrap_err()
        .0
        .contains("clause literal 0"));

    instance.clauses.clear();
    instance.show = Some(vec![3]);
    assert!(instance
        .validate()
        .unwrap_err()
        .0
        .contains("projection variable 3"));

    instance.show = Some(vec![1]);
    instance.ptype = ProblemType::Pwmc;
    instance.weights.push((0, real(1)));
    assert!(instance
        .validate()
        .unwrap_err()
        .0
        .contains("weight literal 0"));
}

#[test]
fn instance_validation_treats_projection_as_a_set() {
    let mut instance = parse_instance("p cnf 2 0\n").unwrap();
    instance.ptype = ProblemType::Pmc;
    instance.show = Some(vec![2, 1]);
    instance
        .validate()
        .expect("projection order is a semantic no-op");

    instance.show = Some(vec![1, 1]);
    assert!(instance
        .validate()
        .unwrap_err()
        .0
        .contains("projection variable 1 is listed more than once"));
}

#[test]
fn instance_validation_rejects_track_fields_the_solver_would_ignore() {
    let mut mc = parse_instance("p cnf 2 0\n").unwrap();
    mc.weights.push((1, real(1)));
    assert!(mc
        .validate()
        .unwrap_err()
        .0
        .contains("mc instances cannot contain weights"));

    let mut pmc = mc;
    pmc.ptype = ProblemType::Pmc;
    assert!(pmc
        .validate()
        .unwrap_err()
        .0
        .contains("pmc instances cannot contain weights"));
}

#[test]
fn instance_validation_requires_projected_track_state() {
    for problem_type in [ProblemType::Pmc, ProblemType::Pwmc] {
        let mut instance = parse_instance("p cnf 1 0\n").unwrap();
        instance.ptype = problem_type;
        let error = instance
            .validate()
            .expect_err("projected track must carry its projection set");
        assert!(error.0.contains("require a projection set"));
    }
}

#[test]
fn parser_canonicalizes_fields_ignored_by_explicit_tracks() {
    let mc = parse_instance("c t mc\np cnf 1 0\nc p show 1 0\nc p weight 1 1 0\n").unwrap();
    assert_eq!(mc.show, None);
    assert!(mc.weights.is_empty());
    mc.validate().unwrap();

    let wmc = parse_instance("c t wmc\np cnf 1 0\nc p show 1 0\n").unwrap();
    assert_eq!(wmc.show, None);
    wmc.validate().unwrap();
}

#[test]
fn projected_tracks_without_show_records_use_empty_projection() {
    for problem_type in ["pmc", "pwmc"] {
        let instance = parse_instance(&format!("c t {problem_type}\np cnf 2 0\n")).unwrap();
        assert_eq!(instance.show, Some(Vec::new()), "{problem_type}");
        instance.validate().unwrap();
    }
}

#[test]
fn parser_rejects_projection_for_complex_track() {
    let error = parse_instance("c t amc-complex\np cnf 1 0\nc p show 1 0\n")
        .expect_err("projected AMC is not a supported track");
    assert!(error
        .0
        .contains("amc-complex does not support projection records"));
}

#[test]
fn resolvers_reject_invalid_dimensions_literals_and_masks() {
    for lit in [0, 2, -2, i32::MIN] {
        let raw = vec![(lit, real(1))];
        assert!(resolve_real_weights(1, &raw, None).is_err(), "real {lit}");
        assert!(resolve_complex_weights(1, &raw).is_err(), "complex {lit}");
    }
    let raw = vec![(1, real(1)), (-1, real(1))];
    assert!(resolve_real_weights(1, &raw, Some(&[])).is_err());
    assert!(resolve_real_weights(1, &raw, Some(&[true, false])).is_err());
    assert!(resolve_real_weights(0, &[(1, real(1))], None).is_err());
    assert!(resolve_complex_weights(0, &[(1, real(1))]).is_err());
    assert!(resolve_real_weights(MAX_COUNT_VARS + 1, &[], None).is_err());
    assert!(resolve_complex_weights(MAX_COUNT_VARS + 1, &[]).is_err());
}

#[test]
fn identical_duplicate_real_and_complex_weights_are_harmless() {
    let real_raw = vec![(1, real(1)), (1, real(1)), (-1, real(1))];
    assert!(resolve_real_weights(1, &real_raw, None).is_ok());

    let value = RawWeight::Complex(rat("1/2"), rat("1/3"));
    let complex_raw = vec![(1, value.clone()), (1, value), (-1, real(1))];
    assert!(resolve_complex_weights(1, &complex_raw).is_ok());
}

#[test]
fn conflicting_duplicate_weights_are_errors() {
    let real_raw = vec![(1, real(1)), (1, real(2)), (-1, real(1))];
    let error = resolve_real_weights(1, &real_raw, None).unwrap_err();
    assert!(error
        .0
        .contains("conflicting duplicate weight for literal 1"));

    let complex_raw = vec![
        (1, RawWeight::Complex(rat("1"), rat("0"))),
        (1, RawWeight::Complex(rat("1"), rat("1"))),
        (-1, real(1)),
    ];
    let error = resolve_complex_weights(1, &complex_raw).unwrap_err();
    assert!(error
        .0
        .contains("conflicting duplicate weight for literal 1"));
}

#[test]
fn duplicate_conflict_is_checked_before_projection_filtering() {
    let raw = vec![(1, real(1)), (1, real(2))];
    let error = resolve_real_weights(1, &raw, Some(&[false])).unwrap_err();
    assert!(error
        .0
        .contains("conflicting duplicate weight for literal 1"));
    assert!(!error.0.contains("non-projection"));
}

proptest! {
    #[test]
    fn arbitrary_text_never_panics(input in any::<String>()) {
        let _ = parse_instance(&input);
    }

    #[test]
    fn arbitrary_resolver_inputs_never_panic(
        num_vars in 0usize..8,
        literal in any::<i32>(),
        mask in prop::collection::vec(any::<bool>(), 0..10),
        value in any::<i32>(),
    ) {
        let raw = vec![(
            literal,
            RawWeight::Rat(BigRational::from_integer(value.into())),
        )];
        let _ = resolve_real_weights(num_vars, &raw, Some(&mask));
        let _ = resolve_complex_weights(num_vars, &raw);
    }
}
