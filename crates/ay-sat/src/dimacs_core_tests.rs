// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

#[test]
fn test_simple_cnf() {
    let input = "c comment\np cnf 3 2\n1 -2 3 0\n-1 2 0\n";
    let (header, records) = parse_dimacs_records_str(input).unwrap();
    assert_eq!(header.num_vars, 3);
    assert_eq!(header.num_clauses, 2);
    assert_eq!(records.len(), 2);
    assert_eq!(records[0], DimacsRecord::Clause(vec![1, -2, 3]));
    assert_eq!(records[1], DimacsRecord::Clause(vec![-1, 2]));
}

#[test]
fn test_streaming_events_match_record_parser() {
    let input = "c comment\np cnf 3 3\n1 -2 0\n3 0\n0\n";
    let (expected_header, expected_records) = parse_dimacs_records_str(input).unwrap();

    let mut header = None;
    let mut records = Vec::new();
    let parsed_header = parse_dimacs_events(input.as_bytes(), |event| {
        match event {
            DimacsEvent::Header(parsed) => header = Some(parsed),
            DimacsEvent::Record(DimacsRecordRef::Clause(raw)) => {
                records.push(DimacsRecord::Clause(raw.to_vec()));
            }
            DimacsEvent::Record(DimacsRecordRef::Tagged { tag, values }) => {
                records.push(DimacsRecord::Tagged {
                    tag,
                    values: values.to_vec(),
                });
            }
        }
        Ok(())
    })
    .unwrap();

    assert_eq!(parsed_header, expected_header);
    assert_eq!(header, Some(expected_header));
    assert_eq!(records, expected_records);
}

#[test]
fn test_multiline_clause() {
    let input = "p cnf 5 1\n1 2 3\n4 5 0\n";
    let (_, records) = parse_dimacs_records_str(input).unwrap();
    assert_eq!(records.len(), 1);
    assert_eq!(records[0], DimacsRecord::Clause(vec![1, 2, 3, 4, 5]));
}

#[test]
fn test_empty_clause() {
    let input = "p cnf 3 3\n1 2 0\n0\n-1 0\n";
    let (_, records) = parse_dimacs_records_str(input).unwrap();
    assert_eq!(records.len(), 3);
    assert_eq!(records[0], DimacsRecord::Clause(vec![1, 2]));
    assert_eq!(records[1], DimacsRecord::Clause(vec![])); // empty clause
    assert_eq!(records[2], DimacsRecord::Clause(vec![-1]));
}

#[test]
fn test_percent_terminator() {
    let input = "p cnf 3 2\n1 -2 0\n-1 2 0\n%\ngarbage\n";
    let (_, records) = parse_dimacs_records_str(input).unwrap();
    assert_eq!(records.len(), 2);
}

#[test]
fn test_tagged_xor_style() {
    // XOR tag joined to first literal: x1 2 3 0
    let input = "p cnf 3 0\nx1 2 3 0\n";
    let (_, records) = parse_dimacs_records_str(input).unwrap();
    assert_eq!(records.len(), 1);
    assert_eq!(
        records[0],
        DimacsRecord::Tagged {
            tag: 'x',
            values: vec![1, 2, 3],
        }
    );
}

#[test]
fn test_tagged_qbf_style() {
    // QBF tags separated by space: e 1 2 0
    let input = "p cnf 4 1\ne 1 3 0\na 2 4 0\n1 -2 3 -4 0\n";
    let (header, records) = parse_dimacs_records_str(input).unwrap();
    assert_eq!(header.num_vars, 4);
    assert_eq!(records.len(), 3);
    assert_eq!(
        records[0],
        DimacsRecord::Tagged {
            tag: 'e',
            values: vec![1, 3],
        }
    );
    assert_eq!(
        records[1],
        DimacsRecord::Tagged {
            tag: 'a',
            values: vec![2, 4],
        }
    );
    assert_eq!(records[2], DimacsRecord::Clause(vec![1, -2, 3, -4]));
}

#[test]
fn test_tagged_xor_negative() {
    // XOR with negative literals
    let input = "p cnf 3 0\nx-1 2 0\n";
    let (_, records) = parse_dimacs_records_str(input).unwrap();
    assert_eq!(
        records[0],
        DimacsRecord::Tagged {
            tag: 'x',
            values: vec![-1, 2],
        }
    );
}

#[test]
fn test_missing_header() {
    let input = "1 2 0\n";
    assert!(matches!(
        parse_dimacs_records_str(input),
        Err(DimacsCoreError::MissingHeader)
    ));
}

#[test]
fn test_duplicate_header_is_rejected_before_second_event() {
    let input = "p cnf 1 1\n0\np cnf 1 0\n";
    let mut headers = 0;
    let mut clauses = 0;
    let result = parse_dimacs_events(input.as_bytes(), |event| {
        match event {
            DimacsEvent::Header(_) => headers += 1,
            DimacsEvent::Record(DimacsRecordRef::Clause(_)) => clauses += 1,
            DimacsEvent::Record(_) => {}
        }
        Ok(())
    });
    assert!(matches!(
        result,
        Err(DimacsCoreError::DuplicateHeader { line_number: 3 })
    ));
    assert_eq!(headers, 1);
    assert_eq!(clauses, 1);
    assert!(matches!(
        parse_dimacs_records_str(input),
        Err(DimacsCoreError::DuplicateHeader { line_number: 3 })
    ));
}

#[test]
fn test_variable_out_of_range() {
    let input = "p cnf 3 1\n1 2 4 0\n";
    assert!(matches!(
        parse_dimacs_records_str(input),
        Err(DimacsCoreError::VariableOutOfRange {
            var: 4,
            max: 3,
            line_number: 2
        })
    ));
}

#[test]
#[cfg(target_pointer_width = "64")]
fn test_overdeclared_header_above_u32_does_not_wrap_range_check() {
    let input = "p cnf 5000000000 1\n1 0\n";
    let (header, records) = parse_dimacs_records_str(input).unwrap();

    assert_eq!(header.num_vars, 5_000_000_000);
    assert_eq!(records, vec![DimacsRecord::Clause(vec![1])]);
}

#[test]
fn test_unterminated_clause() {
    // Clause not terminated by 0 — pushed at EOF
    let input = "p cnf 3 1\n1 2 3\n";
    let (_, records) = parse_dimacs_records_str(input).unwrap();
    assert_eq!(records.len(), 1);
    assert_eq!(records[0], DimacsRecord::Clause(vec![1, 2, 3]));
}

#[test]
fn test_blank_and_comment_lines() {
    let input = "\nc first comment\n\np cnf 2 1\nc another comment\n\n1 -2 0\n\n";
    let (header, records) = parse_dimacs_records_str(input).unwrap();
    assert_eq!(header.num_vars, 2);
    assert_eq!(records.len(), 1);
}

#[test]
fn test_byte_parser_spacing_crlf_and_multiple_clauses_per_line() {
    let input =
        "\t c leading whitespace comment\r\n \tp cnf +3 +3 extra\r\n+1\t-2 0  +3 0\r\n 0\r\n";
    let (header, records) = parse_dimacs_records_str(input).unwrap();
    assert_eq!(header.num_vars, 3);
    assert_eq!(header.num_clauses, 3);
    assert_eq!(records.len(), 3);
    assert_eq!(records[0], DimacsRecord::Clause(vec![1, -2]));
    assert_eq!(records[1], DimacsRecord::Clause(vec![3]));
    assert_eq!(records[2], DimacsRecord::Clause(vec![]));
}

#[test]
fn test_invalid_header_keeps_trimmed_line_content() {
    let input = "  p bad 3 1  \r\n";
    assert!(matches!(
        parse_dimacs_records_str(input),
        Err(DimacsCoreError::InvalidHeader {
            line_content,
            line_number: 1,
        }) if line_content == "p bad 3 1"
    ));
}

#[test]
fn test_invalid_literal_overflow_reports_token() {
    let input = "p cnf 1 1\n2147483648 0\n";
    assert!(matches!(
        parse_dimacs_records_str(input),
        Err(DimacsCoreError::InvalidLiteral {
            token,
            line_number: 2,
        }) if token == "2147483648"
    ));
}

#[test]
fn test_mixed_tagged_and_clauses() {
    // XOR + CNF interleaved
    let input = "p cnf 3 1\nx1 2 0\n1 -2 3 0\nx-3 0\n";
    let (_, records) = parse_dimacs_records_str(input).unwrap();
    assert_eq!(records.len(), 3);
    assert!(matches!(&records[0], DimacsRecord::Tagged { tag: 'x', .. }));
    assert!(matches!(&records[1], DimacsRecord::Clause(_)));
    assert!(matches!(&records[2], DimacsRecord::Tagged { tag: 'x', .. }));
}

#[test]
fn test_zero_vars_empty_clause() {
    let input = "p cnf 0 1\n0\n";
    let (header, records) = parse_dimacs_records_str(input).unwrap();
    assert_eq!(header.num_vars, 0);
    assert_eq!(records.len(), 1);
    assert_eq!(records[0], DimacsRecord::Clause(vec![]));
}
