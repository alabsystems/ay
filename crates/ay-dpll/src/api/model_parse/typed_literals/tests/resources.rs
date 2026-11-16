// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

const WORK: usize = 1_048_576;
const COPY: usize = 16 * 1024 * 1024;

#[test]
fn exact_single_literal_allowance_and_one_short_refusal_use_one_shared_ledger() {
    let (parse_work, parse_bytes) = storage::allowance("true").unwrap();
    // Result Vec, borrowed-sort preflight, then existing Decoder input/sort/value.
    let work = 1 + parse_work + 1 + 3;
    let bytes = 2 * size_of::<ModelValue>() + parse_bytes + size_of::<&ay_frontend::SExpr>();
    let mut exact = Decoder::new();
    exact
        .reserve_literal_resources(WORK - work, COPY - bytes)
        .unwrap();
    assert_eq!(
        decode_with(&[("true", &Sort::Bool)], &mut exact),
        Some(vec![ModelValue::Bool(true)])
    );
    assert_eq!(exact.reserve_literal_resources(0, 0), Some(()));
    assert_eq!(exact.reserve_literal_resources(1, 0), None);
    for (work_left, bytes_left) in [(work - 1, bytes), (work, bytes - 1)] {
        let mut short = Decoder::new();
        short
            .reserve_literal_resources(WORK - work_left, COPY - bytes_left)
            .unwrap();
        assert!(decode_with(&[("true", &Sort::Bool)], &mut short).is_none());
        assert!(decode_with(&[], &mut short).is_none());
    }
    assert_eq!(
        ModelValue::decode_typed_literals(&[("true", &Sort::Bool)]).unwrap(),
        vec![ModelValue::Bool(true)]
    );
}

#[test]
fn actual_batch_reuses_value_work_and_never_returns_a_successful_prefix() {
    let text = format!("\"{}\"", "a".repeat(100_000));
    assert!(ModelValue::decode_typed_literals(&[(&text, &Sort::String)]).is_ok());
    // Each entry fits alone. Three complete text/preflight/value traversals
    // exceed one shared work budget, despite remaining below 8 MiB of text.
    let mut decoder = Decoder::new();
    assert!(decode_with(
        &[
            (&text, &Sort::String),
            (&text, &Sort::String),
            (&text, &Sort::String)
        ],
        &mut decoder
    )
    .is_none());
    assert!(decode_with(&[("true", &Sort::Bool)], &mut decoder).is_none());
    assert!(ModelValue::decode_typed_literals(&[(&text, &Sort::String)]).is_ok());
    assert!(
        ModelValue::decode_typed_literals(&[("true", &Sort::Bool), ("unknown", &Sort::Bool)])
            .is_err()
    );
}

#[test]
fn all_expected_metadata_is_checked_before_any_literal_ast() {
    let malformed = record_sort(
        "R",
        "mkR",
        vec![("field", Sort::Bool), ("field", Sort::Bool)],
    );
    let mut decoder = Decoder::new();
    // The first text is lexically admissible but not one value. Metadata
    // preflight remains independent and rejects the later duplicate field.
    assert!(preflight(
        &[
            ("true false", &Sort::Bool),
            ("(mkR true false)", &malformed)
        ],
        &mut decoder
    )
    .is_none());
    assert!(decoder.reserve_literal_resources(0, 0).is_none());
    let fields = (0..128)
        .map(|i| (format!("field{i}"), Sort::Bool))
        .collect::<Vec<_>>();
    let record = Sort::Datatype(DatatypeSort::new(
        "Wide",
        vec![DatatypeConstructor::new(
            "mkWide",
            fields
                .into_iter()
                .map(|(name, sort)| DatatypeField::new(name, sort))
                .collect(),
        )],
    ));
    assert!(preflight(&[("mkWide", &record)], &mut Decoder::new()).is_some());
    // Unused schemas are charged on every requested occurrence, not once per
    // shared Sort allocation, before parsing/cloning any hypothetical values.
    assert!(preflight(&vec![("mkWide", &record); 256], &mut Decoder::new()).is_none());
}

#[test]
fn request_lexical_and_recursive_sort_caps_have_nonvacuous_boundaries() {
    let boolean = Sort::Bool;
    let bools = vec![("true", &boolean); MAX_LITERALS];
    assert_eq!(
        ModelValue::decode_typed_literals(&bools).unwrap().len(),
        MAX_LITERALS
    );
    assert!(
        ModelValue::decode_typed_literals(&vec![("true", &Sort::Bool); MAX_LITERALS + 1]).is_err()
    );
    let large = " ".repeat(admission::MAX_BYTES + 1);
    assert!(ModelValue::decode_typed_literals(&[(&large, &Sort::Bool)]).is_err());
    let deep = format!(
        "{}true{}",
        "(".repeat(admission::MAX_DEPTH + 1),
        ")".repeat(admission::MAX_DEPTH + 1)
    );
    assert!(ModelValue::decode_typed_literals(&[(&deep, &Sort::Bool)]).is_err());
    let mut sort = Sort::Bool;
    for _ in 0..64 {
        sort = Sort::Seq(Box::new(sort));
    }
    assert!(ModelValue::decode_typed_literals(&[("seq.empty", &sort)]).is_ok());
    let too_deep = Sort::Seq(Box::new(sort));
    assert!(ModelValue::decode_typed_literals(&[("seq.empty", &too_deep)]).is_err());
}

#[test]
fn parser_storage_counts_quoted_payloads_and_error_line_tables_before_allocation() {
    let (small_work, small_bytes) = storage::allowance("\"x\"").unwrap();
    let (quoted_work, quoted_bytes) = storage::allowance("\"xxxxxxxxxx\"").unwrap();
    assert_eq!(quoted_work - small_work, 27);
    assert_eq!(quoted_bytes - small_bytes, 18);
    let (_, newline) = storage::allowance("\"\n\"").unwrap();
    assert_eq!(newline - small_bytes, 2 * size_of::<usize>());
    // Literal/comment parentheses do not create hypothetical AST nodes.
    assert_eq!(storage::allowance("|(|"), storage::allowance("|x|"));
    assert_eq!(
        storage::allowance(";(((\ntrue"),
        storage::allowance(";xxx\ntrue")
    );
    let (work, bytes) = storage::allowance("true").unwrap();
    let mut short = Decoder::new();
    short
        .reserve_literal_resources(WORK - work, COPY - bytes + 1)
        .unwrap();
    assert!(short.reserve_literal_resources(work, bytes).is_none());
}
