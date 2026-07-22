// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use crate::literal::Variable;

#[derive(Debug)]
struct FailingWrite {
    err_kind: io::ErrorKind,
}

impl FailingWrite {
    fn broken_pipe() -> Self {
        Self {
            err_kind: io::ErrorKind::BrokenPipe,
        }
    }
}

impl Write for FailingWrite {
    fn write(&mut self, _buf: &[u8]) -> io::Result<usize> {
        Err(io::Error::new(self.err_kind, "simulated write failure"))
    }

    fn flush(&mut self) -> io::Result<()> {
        Ok(())
    }
}

#[derive(Debug, Default)]
struct CountingWrite {
    bytes: Vec<u8>,
    write_calls: usize,
}

impl Write for CountingWrite {
    fn write(&mut self, buf: &[u8]) -> io::Result<usize> {
        self.write_calls += 1;
        self.bytes.extend_from_slice(buf);
        Ok(buf.len())
    }

    fn flush(&mut self) -> io::Result<()> {
        Ok(())
    }
}

#[test]
fn test_text_add_clause() {
    let mut buf = Vec::new();
    let mut writer = DratWriter::new_text(&mut buf);

    let clause = vec![
        Literal::positive(Variable(0)),
        Literal::negative(Variable(1)),
        Literal::positive(Variable(2)),
    ];
    writer.add(&clause).unwrap();

    let output = String::from_utf8(buf).unwrap();
    assert_eq!(output, "1 -2 3 0\n");
}

#[test]
fn test_drat_text_add_clause_single_write_preserves_bytes() {
    let mut writer = DratWriter::new_text(CountingWrite::default());

    let clause = vec![
        Literal::positive(Variable(0)),
        Literal::negative(Variable(1)),
        Literal::positive(Variable(2)),
    ];
    writer.add(&clause).unwrap();

    let sink = writer.into_inner().unwrap();
    assert_eq!(sink.write_calls, 1);
    assert_eq!(String::from_utf8(sink.bytes).unwrap(), "1 -2 3 0\n");
}

#[test]
fn test_text_delete_clause() {
    let mut buf = Vec::new();
    let mut writer = DratWriter::new_text(&mut buf);

    let clause = vec![
        Literal::positive(Variable(0)),
        Literal::positive(Variable(1)),
    ];
    writer.delete(&clause).unwrap();

    let output = String::from_utf8(buf).unwrap();
    assert_eq!(output, "d 1 2 0\n");
}

#[test]
fn test_drat_text_delete_clause_single_write_preserves_bytes() {
    let mut writer = DratWriter::new_text(CountingWrite::default());

    let clause = vec![
        Literal::positive(Variable(0)),
        Literal::positive(Variable(1)),
    ];
    writer.delete(&clause).unwrap();

    let sink = writer.into_inner().unwrap();
    assert_eq!(sink.write_calls, 1);
    assert_eq!(String::from_utf8(sink.bytes).unwrap(), "d 1 2 0\n");
}

#[test]
fn test_drat_text_jumbo_add_uses_temporary_line_buffer() {
    let mut writer = DratWriter::new_text(CountingWrite::default());
    let retained_capacity_before = writer.text_line_capacity_for_tests();
    let max_retained = DratWriter::<CountingWrite>::max_retained_text_line_capacity_for_tests();
    let literal_count = max_retained / 10 + 1;
    let max_var = i32::MAX as u32 - 1;
    let clause = (0..literal_count)
        .map(|idx| Literal::positive(Variable(max_var - idx as u32)))
        .collect::<Vec<_>>();

    writer.add(&clause).unwrap();

    assert_eq!(
        writer.text_line_capacity_for_tests(),
        retained_capacity_before
    );
    assert!(writer.text_line_capacity_for_tests() <= max_retained);

    let sink = writer.into_inner().unwrap();
    assert_eq!(sink.write_calls, 1);

    let mut expected = Vec::new();
    for lit in &clause {
        expected.extend_from_slice(format!("{} ", lit.to_dimacs()).as_bytes());
    }
    expected.extend_from_slice(b"0\n");
    assert!(expected.len() > max_retained);
    assert_eq!(sink.bytes, expected);
}

#[test]
fn test_binary_add_clause() {
    let mut buf = Vec::new();
    let mut writer = DratWriter::new_binary(&mut buf);

    // Single variable clause: literal +x0 -> var 1 (1-indexed), encoded as 2*1=2
    let clause = vec![Literal::positive(Variable(0))];
    writer.add(&clause).unwrap();

    // Expected: 'a' (0x61), then 2 (the encoded literal), then 0
    assert_eq!(buf, vec![0x61, 2, 0]);
}

#[test]
fn test_binary_delete_clause() {
    let mut buf = Vec::new();
    let mut writer = DratWriter::new_binary(&mut buf);

    // Literal -x0 -> var 1 (1-indexed), encoded as 2*1+1=3
    let clause = vec![Literal::negative(Variable(0))];
    writer.delete(&clause).unwrap();

    // Expected: 'd' (0x64), then 3, then 0
    assert_eq!(buf, vec![0x64, 3, 0]);
}

#[test]
fn test_counts() {
    let mut buf = Vec::new();
    let mut writer = DratWriter::new_text(&mut buf);

    let clause1 = vec![Literal::positive(Variable(0))];
    let clause2 = vec![Literal::positive(Variable(1))];

    writer.add(&clause1).unwrap();
    writer.add(&clause2).unwrap();
    writer.delete(&clause1).unwrap();

    assert_eq!(writer.added_count(), 2);
    assert_eq!(writer.deleted_count(), 1);
}

#[test]
fn test_empty_clause() {
    let mut buf = Vec::new();
    let mut writer = DratWriter::new_text(&mut buf);

    // Empty clause (used to indicate final conflict)
    writer.add(&[]).unwrap();

    let output = String::from_utf8(buf).unwrap();
    assert_eq!(output, "0\n");
}

// LRAT tests

#[test]
fn lrat_writer_fails_closed_on_unrepresentable_original_count() {
    let mut buf = Vec::new();
    let mut writer = LratWriter::new_text(&mut buf, u64::MAX);

    assert!(writer.has_io_error());
    assert_eq!(writer.add(&[], &[]).unwrap(), 0);
    drop(writer);
    assert!(buf.is_empty());
}

#[test]
fn lrat_writer_accepts_largest_safe_original_count_without_wrapping() {
    let mut writer = LratWriter::new_text(io::sink(), MAX_LRAT_ORIGINAL_CLAUSES);

    assert!(!writer.has_io_error());
    assert_eq!(writer.next_id(), i64::MAX as u64);
    assert_eq!(writer.reserve_id(), i64::MAX as u64);
    assert!(writer.has_io_error(), "no further representable ID remains");
}

#[test]
fn test_lrat_text_add_clause() {
    let mut buf = Vec::new();
    let mut writer = LratWriter::new_text(&mut buf, 3); // 3 original clauses

    let clause = vec![
        Literal::positive(Variable(0)),
        Literal::negative(Variable(1)),
    ];
    let hints = vec![1, 2, 3]; // derived from clauses 1, 2, 3
    let id = writer.add(&clause, &hints).unwrap();

    assert_eq!(id, 4); // First learned clause gets ID 4
    let output = String::from_utf8(buf).unwrap();
    assert_eq!(output, "4 1 -2 0 1 2 3 0\n");
}

#[test]
fn lrat_reserved_addition_precedes_pending_text_deletion() {
    let mut writer = LratWriter::new_text(Vec::new(), 1);
    let reserved = writer.reserve_id();
    assert_eq!(reserved, 2);
    writer.delete(1).unwrap();
    writer
        .add_with_id_signed_hints(reserved, &[Literal::positive(Variable(0))], &[-1, 1])
        .unwrap();

    let output = String::from_utf8(writer.into_inner().unwrap()).unwrap();
    assert_eq!(output, "2 1 0 -1 1 0\n3 d 1 0\n");
}

#[test]
fn lrat_reserved_addition_precedes_pending_binary_deletion() {
    let mut writer = LratWriter::new_binary(Vec::new(), 1);
    let reserved = writer.reserve_id();
    writer.delete(1).unwrap();
    writer
        .add_with_id_signed_hints(reserved, &[Literal::positive(Variable(0))], &[1])
        .unwrap();

    let bytes = writer.into_inner().unwrap();
    let steps = ay_lrat_check::lrat_parser::parse_binary_lrat(&bytes).unwrap();
    assert!(matches!(
        &steps[..],
        [
            ay_lrat_check::lrat_parser::LratStep::Add { id: 2, .. },
            ay_lrat_check::lrat_parser::LratStep::Delete { ids }
        ] if ids == &[1]
    ));
}

#[test]
fn lrat_rejects_backfill_after_newer_text_deletion_step() {
    let mut writer = LratWriter::new_text(Vec::new(), 1);
    let reserved = writer.reserve_id();
    writer.delete(1).unwrap();
    writer.flush().unwrap();

    let error = writer
        .add_with_id(reserved, &[Literal::positive(Variable(0))], &[1])
        .unwrap_err();
    assert_eq!(error.kind(), io::ErrorKind::InvalidInput);
    assert!(writer.has_io_error());
}

#[test]
fn test_lrat_text_add_clause_single_write_preserves_bytes() {
    let mut writer = LratWriter::new_text(CountingWrite::default(), 3);

    let clause = vec![
        Literal::positive(Variable(0)),
        Literal::negative(Variable(1)),
    ];
    let id = writer.add(&clause, &[1, 2, 3]).unwrap();

    assert_eq!(id, 4);
    let sink = writer.into_inner().unwrap();
    assert_eq!(sink.write_calls, 1);
    assert_eq!(String::from_utf8(sink.bytes).unwrap(), "4 1 -2 0 1 2 3 0\n");
}

#[test]
fn test_lrat_text_multiple_adds() {
    let mut buf = Vec::new();
    let mut writer = LratWriter::new_text(&mut buf, 2); // 2 original clauses

    let clause1 = vec![Literal::positive(Variable(0))];
    let clause2 = vec![Literal::negative(Variable(1))];

    let id1 = writer.add(&clause1, &[1, 2]).unwrap();
    let id2 = writer.add(&clause2, &[1, 3]).unwrap();

    assert_eq!(id1, 3);
    assert_eq!(id2, 4);

    let output = String::from_utf8(buf).unwrap();
    assert_eq!(output, "3 1 0 1 2 0\n4 -2 0 1 3 0\n");
}

#[test]
fn test_lrat_text_delete_batch_single_write_preserves_bytes() {
    let mut writer = LratWriter::new_text(CountingWrite::default(), 2);
    let clause = vec![Literal::positive(Variable(0))];

    writer.add(&clause, &[1, 2]).unwrap();
    writer.delete(1).unwrap();
    writer.delete(2).unwrap();
    writer.flush().unwrap();

    let sink = writer.into_inner().unwrap();
    assert_eq!(sink.write_calls, 2);
    assert_eq!(
        String::from_utf8(sink.bytes).unwrap(),
        "3 1 0 1 2 0\n4 d 1 2 0\n"
    );
}

#[test]
fn test_lrat_text_jumbo_add_uses_temporary_line_buffer() {
    let mut writer = LratWriter::new_text(CountingWrite::default(), 1);
    let retained_capacity_before = writer.text_line_capacity_for_tests();
    let max_retained = LratWriter::<CountingWrite>::max_retained_text_line_capacity_for_tests();
    let jumbo_hint = i64::MAX as u64;
    let hint_count = max_retained / 20 + 1;
    let hints = vec![jumbo_hint; hint_count];
    let clause = vec![Literal::positive(Variable(0))];

    let id = writer.add(&clause, &hints).unwrap();

    assert_eq!(id, 2);
    assert_eq!(
        writer.text_line_capacity_for_tests(),
        retained_capacity_before
    );
    assert!(writer.text_line_capacity_for_tests() <= max_retained);

    let sink = writer.into_inner().unwrap();
    assert_eq!(sink.write_calls, 1);

    let mut expected = Vec::new();
    expected.extend_from_slice(b"2 1 0 ");
    for _ in 0..hint_count {
        expected.extend_from_slice(b"9223372036854775807 ");
    }
    expected.extend_from_slice(b"0\n");
    assert!(expected.len() > max_retained);
    assert_eq!(sink.bytes, expected);
}

#[test]
fn test_lrat_text_jumbo_delete_uses_temporary_line_buffer() {
    let max_retained = LratWriter::<CountingWrite>::max_retained_text_line_capacity_for_tests();
    let max_pending =
        LratWriter::<CountingWrite>::max_retained_pending_deletions_capacity_for_tests();
    let delete_count = max_retained / 5;
    let num_original = delete_count as u64 + 1;
    let del_id = num_original + 1;
    let mut writer = LratWriter::new_text(CountingWrite::default(), num_original);
    let retained_capacity_before = writer.text_line_capacity_for_tests();

    for id in 1..=delete_count as u64 {
        writer.delete(id).unwrap();
    }
    writer.flush().unwrap();

    assert_eq!(
        writer.text_line_capacity_for_tests(),
        retained_capacity_before
    );
    assert!(writer.text_line_capacity_for_tests() <= max_retained);
    assert!(
        writer.pending_deletions_capacity_for_tests() <= max_pending,
        "flush should not retain a jumbo pending-deletion batch"
    );

    let sink = writer.into_inner().unwrap();
    assert_eq!(sink.write_calls, 1);

    let mut expected = Vec::new();
    expected.extend_from_slice(format!("{del_id} d ").as_bytes());
    for id in 1..=delete_count as u64 {
        expected.extend_from_slice(format!("{id} ").as_bytes());
    }
    expected.extend_from_slice(b"0\n");
    assert!(expected.len() > max_retained);
    assert_eq!(sink.bytes, expected);
}

#[test]
fn test_lrat_text_large_decimal_fields_preserve_bytes() {
    let mut buf = Vec::new();
    let mut writer = LratWriter::new_text(&mut buf, 2);
    writer.advance_past(9_876_543_210);

    let clause = vec![
        Literal::positive(Variable(i32::MAX as u32 - 1)),
        Literal::negative(Variable(123_455)),
    ];
    let id = writer.add(&clause, &[1, 2_147_483_647]).unwrap();
    writer.delete(2_147_483_647).unwrap();
    writer.flush().unwrap();

    assert_eq!(id, 9_876_543_210);
    let output = String::from_utf8(buf).unwrap();
    assert_eq!(
        output,
        "9876543210 2147483647 -123456 0 1 2147483647 0\n9876543211 d 2147483647 0\n"
    );
}

#[test]
fn test_lrat_text_delete() {
    let mut buf = Vec::new();
    let mut writer = LratWriter::new_text(&mut buf, 2);

    // Add a clause first
    let clause = vec![Literal::positive(Variable(0))];
    writer.add(&clause, &[1, 2]).unwrap();

    // Delete clause 1
    writer.delete(1).unwrap();

    // Deletions are batched, flush on next add or flush
    let clause2 = vec![Literal::negative(Variable(0))];
    writer.add(&clause2, &[2]).unwrap();

    let output = String::from_utf8(buf).unwrap();
    // First add, then deletion batch, then second add
    // Deletion steps consume their own monotonically-increasing ID (#4398).
    // Sequence: add(ID=3), delete(ID=4), add(ID=5).
    assert_eq!(output, "3 1 0 1 2 0\n4 d 1 0\n5 -1 0 2 0\n");
}

#[test]
fn test_lrat_binary_add_clause() {
    let mut buf = Vec::new();
    let mut writer = LratWriter::new_binary(&mut buf, 2);

    // Add clause with literal +x0 (encoded as 2) and hints [1, 2]
    let clause = vec![Literal::positive(Variable(0))];
    let id = writer.add(&clause, &[1, 2]).unwrap();

    assert_eq!(id, 3);
    // Binary LRAT encodes IDs as 2*id: id=3→6, hint=1→2, hint=2→4.
    // Expected: 'a' (0x61), id=6, lit=2, 0, hint=2, hint=4, 0
    assert_eq!(buf, vec![0x61, 6, 2, 0, 2, 4, 0]);
}

#[test]
fn test_lrat_binary_delete() {
    let mut buf = Vec::new();
    let mut writer = LratWriter::new_binary(&mut buf, 2);

    // Add a clause
    let clause = vec![Literal::positive(Variable(0))];
    writer.add(&clause, &[1]).unwrap();

    // Delete clauses 1 and 2
    writer.delete(1).unwrap();
    writer.delete(2).unwrap();

    // Flush to write deletions
    writer.flush().unwrap();

    // Binary LRAT encodes IDs as 2*id: id=3→6, hint=1→2, del_id=1→2, del_id=2→4.
    // Expected: 'a'=0x61, id=6, lit=2, 0, hint=2, 0
    //           'd'=0x64, id=2, id=4, 0
    assert_eq!(buf, vec![0x61, 6, 2, 0, 2, 0, 0x64, 2, 4, 0]);
}

#[test]
fn test_lrat_empty_clause_with_hint() {
    let mut buf = Vec::new();
    let mut writer = LratWriter::new_text(&mut buf, 1);

    // Empty clause (final conflict) with hint referencing original clause 1.
    // LRAT requires non-empty hints for all additions (#4490).
    let id = writer.add(&[], &[1]).unwrap();

    assert_eq!(id, 2);
    let output = String::from_utf8(buf).unwrap();
    assert_eq!(output, "2 0 1 0\n");
}

#[test]
fn test_lrat_add_multi_lit_empty_hints_allowed() {
    let mut buf = Vec::new();
    let mut writer = LratWriter::new_text(&mut buf, 1);

    // LratWriter::add() allows empty hints for multi-literal clauses (#7108).
    // TrustedTransform clauses (inprocessing binaries/ternaries) are written
    // as axioms without hint chains. The ProofManager validates Derived hints
    // at a higher level (#4490).
    let clause = vec![
        Literal::positive(Variable(0)),
        Literal::negative(Variable(1)),
    ];
    let id = writer
        .add(&clause, &[])
        .expect("empty hints should be accepted");
    assert_eq!(id, 2); // next_id starts at num_original + 1 = 2
}

#[test]
fn test_lrat_add_unit_empty_hints_allowed() {
    let mut buf = Vec::new();
    let mut writer = LratWriter::new_text(&mut buf, 1);

    // Unit and empty clauses are allowed with empty hints (#4490).
    let unit = vec![Literal::positive(Variable(0))];
    let id = writer.add(&unit, &[]).unwrap();
    assert_eq!(id, 2);

    let id2 = writer.add(&[], &[]).unwrap();
    assert_eq!(id2, 3);
}

#[test]
fn test_lrat_counts() {
    let mut buf = Vec::new();
    let mut writer = LratWriter::new_text(&mut buf, 5);

    let clause = vec![Literal::positive(Variable(0))];
    writer.add(&clause, &[1]).unwrap();
    writer.add(&clause, &[2]).unwrap();
    writer.delete(1).unwrap();
    writer.delete(2).unwrap();

    assert_eq!(writer.added_count(), 2);
    assert_eq!(writer.deleted_count(), 2);
    assert_eq!(writer.next_id(), 8); // 5 original + 2 added = next is 8
}

#[test]
fn test_lrat_num_original_clauses_stable_after_deletions() {
    // Regression test for #4498: num_original_clauses() must return
    // the construction-time value regardless of adds and deletions.
    let mut buf = Vec::new();
    let mut writer = LratWriter::new_text(&mut buf, 5);

    assert_eq!(writer.num_original_clauses(), 5);

    // Add 2 clauses
    let clause = vec![Literal::positive(Variable(0))];
    writer.add(&clause, &[1]).unwrap();
    writer.add(&clause, &[2]).unwrap();
    assert_eq!(writer.num_original_clauses(), 5);

    // Queue and flush deletions
    writer.delete(1).unwrap();
    writer.delete(2).unwrap();
    writer.flush().unwrap();
    assert_eq!(writer.num_original_clauses(), 5);

    // Add another clause after deletion flush
    writer.add(&clause, &[3]).unwrap();
    assert_eq!(writer.num_original_clauses(), 5);
}

#[test]
fn test_proof_output_into_inner_propagates_lrat_io_error() {
    let mut output = ProofOutput::lrat_text(FailingWrite::broken_pipe(), 2);

    // Queue deletion without writing yet; into_inner() flushes the batch.
    output.delete(&[], 1).unwrap();

    let err = output.into_inner().expect_err("expected LRAT flush error");
    assert_eq!(err.kind(), io::ErrorKind::BrokenPipe);
}

// I/O error tracking tests (CaDiCaL-style)

#[test]
fn test_drat_io_error_sets_flag_and_skips_counter() {
    let mut writer = DratWriter::new_text(FailingWrite::broken_pipe());
    let clause = vec![Literal::positive(Variable(0))];

    // First write fails — error returned, flag set, counter not incremented
    assert!(writer.add(&clause).is_err());
    assert!(writer.has_io_error());
    assert_eq!(writer.added_count(), 0);
    assert_eq!(writer.deleted_count(), 0);
}

#[test]
fn test_drat_subsequent_writes_are_noop_after_failure() {
    let mut writer = DratWriter::new_text(FailingWrite::broken_pipe());
    let clause = vec![Literal::positive(Variable(0))];

    // First write fails
    let _ = writer.add(&clause);
    assert!(writer.has_io_error());

    // Subsequent writes are silent no-ops (return Ok, don't increment)
    assert!(writer.add(&clause).is_ok());
    assert!(writer.delete(&clause).is_ok());
    assert!(writer.flush().is_ok());
    assert_eq!(writer.added_count(), 0);
    assert_eq!(writer.deleted_count(), 0);
}

#[test]
fn test_drat_into_inner_fails_after_io_error() {
    let mut writer = DratWriter::new_text(FailingWrite::broken_pipe());
    let _ = writer.add(&[]);

    let err = writer
        .into_inner()
        .expect_err("expected error from into_inner");
    assert_eq!(err.kind(), io::ErrorKind::Other);
}

#[test]
fn test_drat_no_io_error_by_default() {
    let mut buf = Vec::new();
    let writer = DratWriter::new_text(&mut buf);
    assert!(!writer.has_io_error());
}

#[test]
fn test_lrat_io_error_sets_flag_and_skips_counter() {
    let mut writer = LratWriter::new_text(FailingWrite::broken_pipe(), 2);
    let clause = vec![Literal::positive(Variable(0))];

    // First write fails — error returned, flag set, counter not incremented
    assert!(writer.add(&clause, &[1]).is_err());
    assert!(writer.has_io_error());
    assert_eq!(writer.added_count(), 0);
}

#[test]
fn test_lrat_subsequent_writes_are_noop_after_failure() {
    let mut writer = LratWriter::new_text(FailingWrite::broken_pipe(), 2);
    let clause = vec![Literal::positive(Variable(0))];

    // First write fails
    let _ = writer.add(&clause, &[1]);
    assert!(writer.has_io_error());

    // Subsequent writes are silent no-ops
    let result = writer.add(&clause, &[2]);
    assert!(result.is_ok());
    assert_eq!(result.unwrap(), 0); // Returns 0 for no-op'd LRAT add
    assert_eq!(writer.added_count(), 0);

    // Delete is also no-op'd
    assert!(writer.delete(1).is_ok());
    assert_eq!(writer.deleted_count(), 0);
}

#[test]
fn test_lrat_into_inner_fails_after_io_error() {
    let mut writer = LratWriter::new_text(FailingWrite::broken_pipe(), 2);
    let _ = writer.add(&[], &[1]);

    let err = writer
        .into_inner()
        .expect_err("expected error from into_inner");
    assert_eq!(err.kind(), io::ErrorKind::Other);
}

#[test]
fn test_proof_output_has_io_error_drat() {
    let mut output = ProofOutput::drat_text(FailingWrite::broken_pipe());
    assert!(!output.has_io_error());

    let _ = output.add(&[], &[]);
    assert!(output.has_io_error());
}

#[test]
fn test_proof_output_has_io_error_lrat() {
    let mut output = ProofOutput::lrat_text(FailingWrite::broken_pipe(), 2);
    assert!(!output.has_io_error());

    let _ = output.add(&[], &[1]);
    assert!(output.has_io_error());
}

#[test]
fn test_proof_output_into_inner_fails_drat_after_io_error() {
    let mut output = ProofOutput::drat_text(FailingWrite::broken_pipe());
    let _ = output.add(&[], &[]);

    let err = output.into_inner().expect_err("expected DRAT io error");
    assert_eq!(err.kind(), io::ErrorKind::Other);
}

// -- Overflow boundary tests (#4474) --

#[test]
fn test_drat_binary_max_safe_variable() {
    // Variable(i32::MAX as u32 - 1) is the largest variable that can
    // encode safely in both DIMACS text and binary proof formats.
    let mut buf = Vec::new();
    {
        let mut writer = DratWriter::new_binary(&mut buf);
        let var = Variable(i32::MAX as u32 - 1);
        let clause = vec![Literal::positive(var)];
        writer.add(&clause).unwrap();
        assert!(!writer.has_io_error());
    }
    // Should succeed without panic; verify marker present
    assert_eq!(buf[0], b'a');
}

#[test]
fn test_drat_text_max_safe_variable() {
    let mut buf = Vec::new();
    {
        let mut writer = DratWriter::new_text(&mut buf);
        let var = Variable(i32::MAX as u32 - 1);
        let clause = vec![Literal::positive(var)];
        writer.add(&clause).unwrap();
    }
    let output = String::from_utf8(buf).unwrap();
    // DIMACS variable = (i32::MAX - 1) + 1 = i32::MAX = 2147483647
    assert!(output.starts_with("2147483647 0"));
}

#[test]
fn test_lrat_binary_max_safe_variable() {
    let mut buf = Vec::new();
    {
        let mut writer = LratWriter::new_binary(&mut buf, 1);
        let var = Variable(i32::MAX as u32 - 1);
        let clause = vec![Literal::positive(var)];
        let id = writer.add(&clause, &[1]).unwrap();
        assert_eq!(id, 2);
        assert!(!writer.has_io_error());
    }
    assert_eq!(buf[0], b'a');
}

// ── Contract tests (#4442) ───────────────────────────────────

#[test]
#[cfg(debug_assertions)]
fn test_lrat_delete_zero_id_panics() {
    let result = std::panic::catch_unwind(|| {
        let mut buf = Vec::new();
        let mut writer = LratWriter::new_text(&mut buf, 3);
        let _ = writer.delete(0);
    });
    assert!(result.is_err(), "deleting clause ID 0 must panic");
}

#[test]
#[cfg(debug_assertions)]
fn test_lrat_delete_future_id_panics() {
    let result = std::panic::catch_unwind(|| {
        let mut buf = Vec::new();
        let mut writer = LratWriter::new_text(&mut buf, 3);
        // next_id is 4 (3 original + 1), so deleting ID 10 is invalid
        let _ = writer.delete(10);
    });
    assert!(result.is_err(), "deleting future clause ID must panic");
}

#[test]
#[cfg(debug_assertions)]
fn test_lrat_add_hint_zero_panics() {
    let result = std::panic::catch_unwind(|| {
        let mut buf = Vec::new();
        let mut writer = LratWriter::new_text(&mut buf, 3);
        let clause = vec![Literal::positive(Variable(0))];
        let _ = writer.add(&clause, &[0]);
    });
    assert!(result.is_err(), "hint ID 0 must panic");
}

// Note: hint range validation (future IDs) is tested in proof_manager tests
// via ProofManager::validate_lrat_hints, which has access to the full set of
// registered clause IDs. The LratWriter doesn't track externally registered IDs.

#[test]
fn test_lrat_delete_valid_id_succeeds() {
    let mut buf = Vec::new();
    let mut writer = LratWriter::new_text(&mut buf, 3);
    // IDs 1, 2, 3 are original clauses; delete ID 2
    writer.delete(2).unwrap();
    assert_eq!(writer.deleted_count(), 1);
}

#[test]
fn test_lrat_add_valid_hints_succeeds() {
    let mut buf = Vec::new();
    let mut writer = LratWriter::new_text(&mut buf, 3);
    let clause = vec![Literal::positive(Variable(0))];
    // Hints reference original clause IDs 1 and 2
    let id = writer.add(&clause, &[1, 2]).unwrap();
    assert_eq!(id, 4); // next after 3 originals
}

#[test]
fn test_lrat_text_max_safe_variable() {
    let mut buf = Vec::new();
    {
        let mut writer = LratWriter::new_text(&mut buf, 1);
        let var = Variable(i32::MAX as u32 - 1);
        let clause = vec![Literal::positive(var)];
        writer.add(&clause, &[1]).unwrap();
    }
    let output = String::from_utf8(buf).unwrap();
    // LRAT text: "id lit 0 hint 0\n"
    // DIMACS variable = (i32::MAX - 1) + 1 = i32::MAX = 2147483647
    assert!(
        output.contains("2147483647"),
        "LRAT text should contain max-safe DIMACS variable: {output}"
    );
}

// -- Binary encoding overflow tests via boundary variable (#4474) --
//
// Variable(i32::MAX as u32) passes the Literal constructor (encoding
// 2 * i32::MAX fits in u32), but the binary proof format encodes
// 2 * (var + 1) which overflows: 2 * (i32::MAX + 1) = 2^32 > u32::MAX.

#[test]
#[should_panic(expected = "literal encoding overflow")]
fn test_drat_binary_panics_on_boundary_variable() {
    let mut buf = Vec::new();
    let mut writer = DratWriter::new_binary(&mut buf);
    let var = Variable(i32::MAX as u32);
    let clause = vec![Literal::positive(var)];
    let _ = writer.add(&clause);
}

#[test]
#[should_panic(expected = "literal encoding overflow")]
fn test_lrat_binary_panics_on_boundary_variable() {
    let mut buf = Vec::new();
    let mut writer = LratWriter::new_binary(&mut buf, 1);
    let var = Variable(i32::MAX as u32);
    let clause = vec![Literal::positive(var)];
    let _ = writer.add(&clause, &[1]);
}

// -- from_index() bypass tests (#4474) --
//
// Literal::from_index() skips the constructor assert!, so write_binary_lit
// is the last defense against overlarge variable indices.

#[test]
#[should_panic(expected = "overflow")]
fn test_drat_binary_panics_on_from_index_bypass() {
    let mut buf = Vec::new();
    let mut writer = DratWriter::new_binary(&mut buf);
    // Literal(u32::MAX) -> variable = u32::MAX >> 1 = i32::MAX
    // In write_binary_lit: (i32::MAX).checked_add(1) = 2^31,
    // then 2^31.checked_mul(2) overflows u32.
    let lit = Literal::from_index(u32::MAX as usize);
    let _ = writer.add(&[lit]);
}

#[test]
#[should_panic(expected = "overflow")]
fn test_lrat_binary_panics_on_from_index_bypass() {
    let mut buf = Vec::new();
    let mut writer = LratWriter::new_binary(&mut buf, 1);
    let lit = Literal::from_index(u32::MAX as usize);
    let _ = writer.add(&[lit], &[1]);
}

// -- Text encoding overflow via from_index() bypass (#4474) --

#[test]
#[should_panic(expected = "DIMACS i32 encoding range")]
fn test_drat_text_panics_on_from_index_bypass() {
    let mut buf = Vec::new();
    let mut writer = DratWriter::new_text(&mut buf);
    // Literal(u32::MAX) -> variable = i32::MAX, to_dimacs() tries
    // i32::try_from(i32::MAX).checked_add(1) which overflows i32.
    let lit = Literal::from_index(u32::MAX as usize);
    let _ = writer.add(&[lit]);
}

#[test]
#[should_panic(expected = "DIMACS i32 encoding range")]
fn test_lrat_text_panics_on_from_index_bypass() {
    let mut buf = Vec::new();
    let mut writer = LratWriter::new_text(&mut buf, 1);
    let lit = Literal::from_index(u32::MAX as usize);
    let _ = writer.add(&[lit], &[1]);
}
