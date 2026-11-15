// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Adapt the diagnostic capture to the model parser's SMT-LIB surface.
//! Raw captured expressions remain byte-bound; quoting preserves whole names.

use super::*;

pub(super) fn model_definitions(input: &str) -> String {
    let mut output = String::new();
    for line in input.lines() {
        if line.starts_with("(declare-rel ") || line.trim_start().starts_with(';') {
            continue;
        }
        // These exact captures contain plain diagnostic symbols, not strings,
        // quoted symbols or inline comments. Refuse other fixture surfaces.
        assert!(!line.contains(['|', '"', ';']));
        let delimiter = |c: char| c.is_whitespace() || matches!(c, '(' | ')');
        for segment in line.split_inclusive(delimiter) {
            let token = segment.trim_end_matches(delimiter);
            if token.contains(':') {
                output.push_str(&ay_core::quote_symbol(token));
            } else {
                output.push_str(token);
            }
            output.push_str(&segment[token.len()..]);
        }
        output.push('\n');
    }
    output
}

// The model parser uses `and_all`, which removes identical conjuncts. Restore
// only byte-identical repetitions in their original positions, retaining the
// parsed children. Any other top-level erasure/flattening is a fixture error,
// not permission to reduce an original obligation's expected conjunct count.
pub(super) fn restore_conjunct_occurrences(input: &str, name: &str, parsed: &ChcExpr) -> ChcExpr {
    let source = captured_conjuncts(input, name);
    let mut unique = Vec::new();
    let mut positions = Vec::new();
    for conjunct in source {
        assert!(
            !matches!(conjunct, "true" | "false") && !conjunct.starts_with("(and "),
            "capture restoration admits only duplicate removal, not Boolean simplification"
        );
        let position = unique.iter().position(|previous| *previous == conjunct);
        positions.push(position.unwrap_or_else(|| {
            unique.push(conjunct);
            unique.len() - 1
        }));
    }
    let ChcExpr::Op(ChcOp::And, args) = parsed else {
        panic!("capture parser erased the original conjunction");
    };
    assert_eq!(
        unique.len(),
        args.len(),
        "capture parser changed more than byte-identical conjunct repetitions"
    );
    ChcExpr::Op(
        ChcOp::And,
        positions
            .into_iter()
            .map(|i| Arc::clone(&args[i]))
            .collect(),
    )
}

fn captured_conjuncts<'a>(input: &'a str, name: &str) -> Vec<&'a str> {
    let offset = input.find(&format!("(define-fun {name}")).unwrap();
    let expression = input[offset..]
        .lines()
        .find(|line| line.starts_with("(and "))
        .unwrap();
    assert!(!expression.contains(['|', '"', ';']));
    let mut remaining = expression.strip_prefix("(and ").unwrap();
    remaining = remaining.strip_suffix(')').unwrap();
    let mut result = Vec::new();
    while !remaining.trim().is_empty() {
        remaining = remaining.trim_start();
        let mut depth = 0_usize;
        let mut end = remaining.len();
        for (i, byte) in remaining.bytes().enumerate() {
            match byte {
                b'(' => depth += 1,
                b')' => depth = depth.checked_sub(1).expect("balanced captured expression"),
                _ => {}
            }
            if depth == 0 && (byte == b')' || byte.is_ascii_whitespace()) {
                end = i + usize::from(byte == b')');
                break;
            }
        }
        assert_eq!(depth, 0, "balanced captured expression");
        assert!(end > 0);
        result.push(&remaining[..end]);
        remaining = &remaining[end..];
    }
    result
}

#[test]
fn whole_rust_symbols_are_quoted_without_renaming_or_prefix_replacement() {
    let text = "; provenance: not a model\n(declare-rel p ((_ BitVec 8)))\n\
        (define-fun p ((a::x (_ BitVec 8))) Bool (= a::x a::xy))\n";
    assert_eq!(
        model_definitions(text),
        "(define-fun p ((|a::x| (_ BitVec 8))) Bool (= |a::x| |a::xy|))\n"
    );
}

#[test]
fn exact_capture_duplicate_positions_and_restored_implications_are_preserved() {
    for (input, count, first, repeated, spelling) in [
        (
            include_str!("clause12.smt2"),
            66,
            6,
            65,
            "(= _testcrate_0::chc_std_alloc_realloc_grow_full_3 (_ bv283467841536 64))",
        ),
        (
            include_str!("clause22.smt2"),
            72,
            19,
            63,
            "(= _testcrate_0::chc_std_alloc_realloc_grow_full_9_fld1 (_ bv147573952589676412932 128))",
        ),
    ] {
        let source = captured_conjuncts(input, "captured_head");
        assert_eq!(source.len(), count);
        assert_eq!(source[first], spelling);
        assert_eq!(source[repeated], spelling);
        assert_eq!(source.iter().filter(|text| **text == spelling).count(), 2);
        let unique: std::collections::BTreeSet<_> = source.iter().collect();
        assert_eq!(unique.len(), count - 1);
        let (_, restored) = original::parse(input);
        let ChcExpr::Op(ChcOp::And, args) = &restored else {
            panic!("restored conjunction");
        };
        assert_eq!(args.len(), count);
        assert_eq!(args[first], args[repeated]);
        let normalized = ChcExpr::and_all(args.iter().map(|arg| arg.as_ref().clone()));
        let ChcExpr::Op(ChcOp::And, unique_args) = &normalized else {
            panic!("normalized conjunction");
        };
        assert_eq!(unique_args.len(), count - 1);
        assert_eq!(prove(&restored, &normalized), Ok(true));
        assert_eq!(prove(&normalized, &restored), Ok(true));
    }
}

#[test]
fn duplicate_restoration_does_not_authorize_other_conjunct_erasure() {
    let a = variable("a", ChcSort::Bool);
    let b = variable("b", ChcSort::Bool);
    let parsed = op(ChcOp::And, vec![a, b]);
    for original in ["(and a true b)", "(and (and a b) a)", "(and a b c)"] {
        let input = format!("(define-fun captured_head () Bool\n{original}\n)");
        assert!(std::panic::catch_unwind(|| {
            restore_conjunct_occurrences(&input, "captured_head", &parsed)
        })
        .is_err());
    }
}

#[test]
fn restored_boolean_duplicates_match_every_assignment_and_retain_bad_types() {
    use crate::smt::SmtValue;
    use ay_core::kani_compat::DetHashMap;
    let capture = |head: &str| {
        format!(
            "(declare-rel captured_body (Bool Bool))\n\
             (declare-rel captured_head (Bool Bool))\n\
             (define-fun captured_body ((a Bool) (b Bool)) Bool\n(and a b)\n)\n\
             (define-fun captured_head ((a Bool) (b Bool)) Bool\n{head}\n)\n"
        )
    };
    let (normalized, restored) = original::parse(&capture("(and a b a)"));
    let ChcExpr::Op(ChcOp::And, args) = &restored else {
        panic!("restored conjunction");
    };
    assert_eq!(args.len(), 3);
    assert_eq!(args[0], args[2]);
    for a in [false, true] {
        for b in [false, true] {
            let environment: DetHashMap<_, _> = [
                ("a".into(), SmtValue::Bool(a)),
                ("b".into(), SmtValue::Bool(b)),
            ]
            .into_iter()
            .collect();
            assert_eq!(
                crate::expr::evaluate_expr(&restored, &environment).unwrap(),
                SmtValue::Bool(a && b)
            );
            assert_eq!(
                crate::expr::evaluate_expr(&normalized, &environment).unwrap(),
                SmtValue::Bool(a && b)
            );
        }
    }
    let (_, malformed) = original::parse(&capture("(and (= a (_ bv0 2)) b (= a (_ bv0 2)))"));
    let ChcExpr::Op(ChcOp::And, args) = &malformed else {
        panic!("malformed conjunction retained");
    };
    assert_eq!(args.len(), 3);
    assert_eq!(args[0], args[2]);
    assert_eq!(prove(&malformed, &malformed), Ok(false));
}
