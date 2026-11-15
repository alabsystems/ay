//! Regression tests for how a DIMACS literal names a variable.
//!
//! Two independent defects, both in the front ends that read variable indices
//! out of untrusted text:
//!
//! * the WCNF parser built the variable name by *string concatenation* on the
//!   literal's raw slice (`"x" + lex.slice()`), so `1`, `01`, `001` and `+1`
//!   -- all accepted by the `[+-]?[0-9]+` token and all denoting variable 1 --
//!   interned four different variables. Splitting one variable into several
//!   always *relaxes* the formula, so the reachable error is a false
//!   `VERIFIED`, not a false rejection.
//! * the CNF parser cast the parsed literal straight to a variable index.
//!   `Lit` packs `(var_idx << 1) ^ is_negated` into one `usize`, so an index
//!   above `Lit::MAX_VAR_IDX` either collides with the reserved
//!   `Lit::new_undef()` sentinel (which the clause normalizer read as "no
//!   previous literal" and dropped) or aliases a different variable outright.

use std::io::Write;
use std::path::PathBuf;

use veripb_formula::prelude::*;
use veripb_parser::{
    cnf_parser::{CnfParserOptions, parse_cnf_from_file_with_options},
    error::ParserError,
    wcnf_parser::parse_wcnf_from_file,
};

/// Write `contents` to a fresh file inside a temporary directory and return
/// both (the directory keeps the file alive for the duration of the test).
fn write_temp(name: &str, contents: &str) -> (tempfile::TempDir, PathBuf) {
    let dir = tempfile::tempdir().expect("failed to create temporary directory");
    let path = dir.path().join(name);
    let mut file = std::fs::File::create(&path).expect("failed to create temporary file");
    file.write_all(contents.as_bytes())
        .expect("failed to write test input");
    file.flush().expect("failed to flush test input");
    (dir, path)
}

// --------------------------------------------------------------------------
// WCNF: variable identity comes from the literal's value, not its spelling
// --------------------------------------------------------------------------

/// Parse `contents` as WCNF and return the constraints and the interned names.
fn parse_wcnf(contents: &str) -> (Vec<PBConstraintEnum>, Vec<String>) {
    let (_dir, path) = write_temp("t.wcnf", contents);
    let (formula, var_names) = parse_wcnf_from_file(&path).expect("WCNF must parse");
    let names = (0..var_names.len())
        .map(|idx| var_names.get_name(idx).to_string())
        .collect();
    (formula.constraints, names)
}

#[test]
fn wcnf_literal_spellings_denote_the_same_variable() {
    let canonical = parse_wcnf("h 1 0\nh -1 0\n");
    assert_eq!(canonical.1, vec!["x1".to_string()]);

    for spelling in ["h 1 0\nh -01 0\n", "h +1 0\nh -1 0\n", "h 001 0\nh -1 0\n"] {
        let parsed = parse_wcnf(spelling);
        assert_eq!(
            parsed.1, canonical.1,
            "{spelling:?} must intern exactly the variable x1"
        );
        assert_eq!(
            parsed.0, canonical.0,
            "{spelling:?} must yield the same clauses as the canonical spelling"
        );
    }
}

#[test]
fn wcnf_most_negative_literal_does_not_wrap() {
    // `-integer` wraps back to `i64::MIN` for `integer == i64::MIN`, and the
    // release profile had no overflow checks then, so the naive negation produced
    // the name `x-9223372036854775808`. `unsigned_abs()` is the exact step.
    let (_, names) = parse_wcnf("h -9223372036854775808 0\n");
    assert_eq!(names, vec!["x9223372036854775808".to_string()]);
}

#[test]
fn wcnf_positive_and_negative_spellings_share_one_variable() {
    // A single clause naming the same variable twice with different spellings
    // and opposite signs is `x v ~x`, i.e. trivially true -- not a two-literal
    // clause over two unrelated variables.
    let (constraints, names) = parse_wcnf("h 1 -01 0\n");
    assert_eq!(names, vec!["x1".to_string()]);
    assert_eq!(constraints.len(), 1);
    assert!(constraints[0].is_trivial());
}

// --------------------------------------------------------------------------
// CNF: a variable index `Lit` cannot represent must be rejected, and rejected
// *unconditionally* -- the header-count check is a truncation heuristic and
// must not double as the guard for a sentinel collision.
// --------------------------------------------------------------------------

fn parse_cnf(contents: &str, options: CnfParserOptions) -> Result<(Formula, usize), ParserError> {
    let (_dir, path) = write_temp("t.cnf", contents);
    parse_cnf_from_file_with_options(&path, options)
}

fn assert_index_rejected(contents: &str, what: &str) {
    for (label, options) in [
        ("lenient", CnfParserOptions::lenient()),
        ("strict", CnfParserOptions::strict()),
    ] {
        match parse_cnf(contents, options) {
            Err(ParserError::VariableIndexOutOfRange { index, max, .. }) => {
                assert!(index > max, "{what} ({label}): {index} must exceed {max}");
            }
            other => panic!(
                "{what} ({label}): expected VariableIndexOutOfRange, got {:?}",
                other.map(|(formula, num_vars)| (formula.len(), num_vars))
            ),
        }
    }
}

#[test]
fn cnf_rejects_the_literal_that_packs_as_the_undef_sentinel() {
    // Variable 2^63 - 1 negated packs to `usize::MAX`, the `Lit::new_undef()`
    // value: the clause normalizer read it as a duplicate of "no previous
    // literal" and dropped it, so this unit clause became the empty clause and
    // the checker verified UNSAT for a satisfiable formula.
    assert_index_rejected(
        "p cnf 1 1\n-9223372036854775807 0\n",
        "negated sentinel literal",
    );
    // The positive sibling packs to `usize::MAX - 1` and drove the dedup
    // loop's `new_idx -= 1` through an unsigned underflow.
    assert_index_rejected(
        "p cnf 1 1\n9223372036854775807 0\n",
        "positive sibling of the sentinel",
    );
}

#[test]
fn cnf_rejects_the_most_negative_literal_without_wrapping() {
    // `-integer` for `i64::MIN` wraps to `i64::MIN`, which `as usize` reads as
    // 2^63; `unsigned_abs()` reports the true index instead.
    let (_dir, path) = write_temp("t.cnf", "p cnf 1 1\n-9223372036854775808 0\n");
    match parse_cnf_from_file_with_options(&path, CnfParserOptions::lenient()) {
        Err(ParserError::VariableIndexOutOfRange { index, .. }) => {
            assert_eq!(index, 9223372036854775808);
        }
        other => panic!("expected VariableIndexOutOfRange, got {}", other.is_ok()),
    }
}

#[test]
fn cnf_rejects_a_declared_variable_count_outside_the_representable_range() {
    // Declaring the count is the only other route to an unrepresentable index:
    // callers size a variable-name table from it, and a large enough count
    // would let an out-of-range literal satisfy the header check.
    assert_index_rejected(
        "p cnf 9223372036854775807 1\n1 0\n",
        "declared variable count",
    );
}

#[test]
fn cnf_accepts_the_largest_dense_variable_index() {
    // The positive control: the boundary index itself is representable in both
    // polarities and small enough for the checker's dense per-variable tables,
    // so it must not be rejected.
    let contents = format!(
        "p cnf {max} 2\n{max} 0\n-{max} 0\n",
        max = MAX_DENSE_VAR_IDX
    );
    let (formula, num_vars) =
        parse_cnf(&contents, CnfParserOptions::strict()).expect("the boundary index is legal");
    assert_eq!(num_vars, MAX_DENSE_VAR_IDX);
    assert_eq!(formula.len(), 2);
    for constraint in &formula.constraints {
        assert_eq!(constraint.len(), 1, "each unit clause must survive");
        assert_eq!(constraint.get_lit(0).unwrap().get_var(), MAX_DENSE_VAR_IDX);
    }
}

// --------------------------------------------------------------------------
// CNF: the returned variable count is the size of the variable space the file
// USES, and a space too large for the checker's dense tables is refused.
// --------------------------------------------------------------------------

fn assert_space_rejected(contents: &str, what: &str) {
    for (label, options) in [
        ("lenient", CnfParserOptions::lenient()),
        ("strict", CnfParserOptions::strict()),
    ] {
        match parse_cnf(contents, options) {
            Err(ParserError::VariableSpaceTooLarge { index, max, .. }) => {
                assert!(index > max, "{what} ({label}): {index} must exceed {max}");
                assert_eq!(max, MAX_DENSE_VAR_IDX);
            }
            other => panic!(
                "{what} ({label}): expected VariableSpaceTooLarge, got {:?}",
                other.map(|(formula, num_vars)| (formula.len(), num_vars))
            ),
        }
    }
}

#[test]
fn cnf_rejects_a_variable_index_too_large_for_a_dense_variable_space() {
    // Representable, and still refused: the checker is densely indexed by
    // variable, so this 24-byte file would cost ~90 bytes of tables for every
    // index up to 2^27 -- ≈12 GB and ≈35 s, measured at the bound, see
    // `MAX_DENSE_VAR_IDX` -- before a single proof line. Unconditional, like the
    // representability check above it -- `--lenient-header-counts` relaxes a
    // truncation heuristic and nothing else.
    let above = MAX_DENSE_VAR_IDX + 1;
    assert!(above < Lit::MAX_VAR_IDX, "the index must be representable");
    assert_space_rejected(
        &format!("p cnf 1 1\n{above} 0\n"),
        "literal above the dense bound",
    );
    assert_space_rejected(
        &format!("p cnf 1 1\n-{above} 0\n"),
        "negated literal above the dense bound",
    );
    // The declared count reaches the same tables on its own -- `src/lib.rs`
    // builds `x1..xN` from it -- so it needs the same bound, and this file's
    // header is otherwise consistent with its contents, i.e. reachable with
    // the strict header check that is the default.
    assert_space_rejected(
        &format!("p cnf {above} 1\n1 0\n"),
        "declared count above the dense bound",
    );
}

#[test]
fn cnf_returns_the_variable_space_the_file_uses_not_the_one_it_declares() {
    // The defect: this returned 1, the declared count. `src/lib.rs` then built
    // a two-entry variable-name table, the checker sized its `Assignment` from
    // that, and `Assignment::{get,set}_lit_value_unchecked` indexed variable 5
    // in it with `get_unchecked` -- an out-of-bounds read on the accept/reject
    // path, which in one spelling printed `s VERIFIED SATISFIABLE` for a
    // solution that falsifies the formula.
    let (formula, num_vars) = parse_cnf("p cnf 1 2\n5 0\n-5 0\n", CnfParserOptions::lenient())
        .expect("a header-count mismatch is only a warning in lenient mode");
    assert_eq!(formula.len(), 2);
    assert_eq!(
        num_vars, 5,
        "the returned count must cover every literal in the file, not just the declared ones"
    );
}

#[test]
fn cnf_keeps_an_over_declared_variable_count() {
    // The other direction is normal DIMACS and must be left alone: declaring
    // more variables than are used means those variables exist and are
    // unconstrained, and the proof may name them.
    let (_, num_vars) = parse_cnf("p cnf 10 1\n1 0\n", CnfParserOptions::strict())
        .expect("declaring unused variables is legal");
    assert_eq!(num_vars, 10);
}

#[test]
fn cnf_survives_a_declared_clause_count_no_allocator_could_meet() {
    // `reserve_exact(999999999999999)` asked for 96 PB of constraint storage
    // and took the process down with `memory allocation of ... bytes failed`
    // before a single clause had been read. The reservation is an
    // optimisation, so a request the allocator refuses is now dropped.
    let (formula, num_vars) = parse_cnf(
        "p cnf 1 999999999999999\n1 0\n",
        CnfParserOptions::lenient(),
    )
    .expect("an absurd clause count is a header mismatch, not a crash");
    assert_eq!(formula.len(), 1);
    assert_eq!(num_vars, 1);
}
