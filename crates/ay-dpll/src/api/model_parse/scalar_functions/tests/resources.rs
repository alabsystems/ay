// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

#[test]
fn actual_shared_work_copy_and_output_boundaries_are_atomic_and_sticky() {
    let output = "(model (define-fun unused () (_ BitVec 136) (_ bv1 136)) (define-fun f ((x (_ BitVec 8))) (_ BitVec 8) (ite (= x #x00) #x01 x)))";
    let args = [bv(8)];
    let small = bv(8);
    let wide = bv(136);
    let expected = [("f", args.as_slice(), &small), ("unused", &[][..], &wide)];
    let initial = Budget::new();
    let mut measured = Budget::new();
    let baseline = parse_with_budget(output, &expected, &mut measured).unwrap();
    let work = initial.work - measured.work;
    let bytes = initial.bytes - measured.bytes;
    let text = initial.output - measured.output;
    assert!(bytes > output.len() && work > output.len() && text > 0);
    let mut exact = Budget {
        work,
        bytes,
        output: text,
        ..Budget::new()
    };
    assert_eq!(
        parse_with_budget(output, &expected, &mut exact).unwrap(),
        baseline
    );
    for mut short in [
        Budget {
            work: work - 1,
            ..Budget::new()
        },
        Budget {
            bytes: bytes - 1,
            ..Budget::new()
        },
        Budget {
            output: text - 1,
            ..Budget::new()
        },
    ] {
        assert!(parse_with_budget(output, &expected, &mut short).is_none());
        assert!(short.stopped);
        assert!(short.charge(0, 0).is_none());
        assert!(parse_with_budget("(model)", &[], &mut short).is_none());
    }
    assert_eq!(
        parse_with_budget(output, &expected, &mut Budget::new()).unwrap(),
        baseline
    );
}

#[test]
fn whole_batch_cumulative_limits_include_unused_definitions_and_large_literals() {
    let tiny = "(model (define-fun f () (_ BitVec 8) #x00))";
    let expected = [("f", &[][..], &bv(8))];
    let mut measured = Budget::new();
    parse_with_budget(tiny, &expected, &mut measured).unwrap();
    let used = Budget::new().bytes - measured.bytes;
    let larger = format!("(model (define-fun f () (_ BitVec 8) #x00) (define-fun unused ((very_long_unused_parameter_name Bool)) (_ BitVec 136) #x{}))", "0".repeat(34));
    let mut short = Budget {
        bytes: used,
        ..Budget::new()
    };
    assert!(parse_with_budget(&larger, &expected, &mut short).is_none());
    assert!(parse_scalar_function_models(&larger, &expected).is_some());
    let digits = "9".repeat(20_000);
    assert!(one(&format!("(_ bv{digits} 1048576)"), "", &[], 1048576).is_none());
    assert!(one("(_ bv1 136)", "", &[], 136).is_some());
}

#[test]
fn text_depth_name_and_inventory_admission_happen_before_recursive_consumers() {
    let body = format!("{}#x00{}", "(ite true #x00 ".repeat(130), ")".repeat(130));
    assert!(one(&body, "", &[], 8).is_none());
    let body = format!("{}#x00{}", "(ite true #x00 ".repeat(65), ")".repeat(65));
    assert!(one(&body, "", &[], 8).is_none());
    let name = "n".repeat(16_385);
    let text = format!("(model (define-fun {name} () (_ BitVec 8) #x00))");
    assert!(parse_scalar_function_models(&text, &[(&name, &[], &bv(8))]).is_none());
    let sort = bv(8);
    let expected = vec![("f", &[][..], &sort); MAX_FUNCTIONS + 1];
    assert!(parse_scalar_function_models("(model)", &expected).is_none());
    let text = format!("(model);{}", "x".repeat(admission::MAX_BYTES));
    assert!(parse_scalar_function_models(&text, &[]).is_none());
}
