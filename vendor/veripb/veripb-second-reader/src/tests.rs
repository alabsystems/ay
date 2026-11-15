//! Unit tests for the second reader, one per format subtlety.
//!
//! These are hand-written files rather than corpus instances on purpose: the
//! point of the crate is to read the *format*, and the corpus exercises a
//! small and rather regular slice of it. The corpus-level check that the
//! reader agrees with the checker on every shipped instance lives in
//! `tests/kernel_verify.rs`, which runs the whole thing under
//! `--kernel-verify`.

use super::*;

fn big(n: i64) -> BigInt {
    BigInt::from(n)
}

/// `coeff name negated` triples of a constraint, for compact assertions.
fn terms(c: &Constraint) -> Vec<(i64, &str, bool)> {
    c.terms
        .iter()
        .map(|t| {
            (
                i64::try_from(t.coeff.clone()).expect("test coefficients fit i64"),
                t.var.as_str(),
                t.negated,
            )
        })
        .collect()
}

fn read_ok(text: &str, format: Format) -> Formula {
    read(text.as_bytes(), format).unwrap_or_else(|e| panic!("reader refused: {e}"))
}

// ---------------------------------------------------------------------------
// OPB
// ---------------------------------------------------------------------------

/// A second item after the first `;` on a line is refused, on this reader's own
/// terms.
///
/// This crate exists to be an *independent* reading of the formula, catching
/// "the formula stored is not the formula on disk" — the class defects 16 and
/// 17 lived in. It did not catch this one, because it was written to the same
/// shape as the primary reader and inherited the same lenience: both parsed one
/// item per line and ignored the rest, so
/// `1 x1 >= 1 ; 1 ~x1 >= 1 ;` on one line was read as just `1 x1 >= 1 ;`. That
/// file is unsatisfiable and verified as `s VERIFIED SATISFIABLE` at exit 0,
/// with `--kernel-verify` reporting the cross-check as passing.
///
/// A cross-check that shares the blind spot it is checking for is not a
/// cross-check, so this is tested here rather than only through the checker.
/// The `p cnf` header owns its line, on this reader's own terms.
///
/// Clause data is a stream and may share and span lines; the header is not
/// clause data. The primary reader returned after the two counts and dropped
/// the rest of the header line, so `p cnf 1 2 1 0` silently lost the clause
/// `1 0`, the truncated formula was satisfiable where the file is not, and
/// this reader -- written to the same shape -- reported the cross-check as
/// passing. Same class as the OPB one-item-per-line hole below.
#[test]
fn cnf_refuses_content_after_the_header_counts() {
    assert!(
        read(b"p cnf 1 2 1 0\n-1 0\n-1 0\n", Format::Cnf).is_err(),
        "the second reader accepted a clause on the header line, which is how \
         the formula cross-check went blind"
    );
    // Two clauses sharing a non-header line are legal stream DIMACS.
    let f = read_ok("p cnf 1 2\n1 0 -1 0\n", Format::Cnf);
    assert_eq!(f.constraints.len(), 2);
}

#[test]
fn opb_refuses_a_second_item_after_the_semicolon() {
    for text in [
        "1 x1 >= 1 ; 1 ~x1 >= 1 ;\n",
        "min: 1 x1 ; 1 x1 >= 1 ;\n",
        "preserved: x1 ; 1 x1 >= 1 ;\n",
        "@a 1 x1 >= 1 ; 1 ~x1 >= 1 ;\n",
    ] {
        assert!(
            read(text.as_bytes(), Format::Opb).is_err(),
            "the second reader accepted two items on one line, which is how the \
             formula cross-check went blind: {text:?}"
        );
    }
    // The same content, one item per line, still reads.
    let f = read_ok("1 x1 >= 1 ;\n1 ~x1 >= 1 ;\n", Format::Opb);
    assert_eq!(f.constraints.len(), 2);
}

/// The XPB grammar allows at most one objective, before every constraint
/// (the development design notes §XPB: `xpb ::= {skip}, [objective], {skip | constraint}`).
/// The reader used to assign on `min:`/`max:` wherever it stood, so a second
/// objective silently replaced the first and an objective after the
/// constraints read as if it led the file — the same dropped-data shape as
/// the one-item-per-line hole above. Refused on this reader's own terms.
#[test]
fn opb_refuses_a_misplaced_or_repeated_objective() {
    for text in [
        // A second objective would silently replace the first.
        "min: 1 x1 ;\nmin: 2 x2 ;\n1 x1 >= 1 ;\n",
        "min: 1 x1 ;\nmax: 2 x2 ;\n1 x1 >= 1 ;\n",
        // An objective after a constraint did not lead the file.
        "1 x1 >= 1 ;\nmin: 1 x1 ;\n",
        // Repeated *and* misplaced.
        "min: 1 x1 ;\n1 x1 >= 1 ;\nmin: 2 x2 ;\n",
    ] {
        assert!(
            read(text.as_bytes(), Format::Opb).is_err(),
            "the second reader accepted an objective the XPB grammar rules out, \
             and would have silently dropped data: {text:?}"
        );
    }
    // The grammar's own shape still reads: one objective, then constraints.
    let f = read_ok("min: 1 x1 ;\n1 x1 >= 1 ;\n", Format::Opb);
    assert_eq!(f.constraints.len(), 1);
    assert!(f.objective.is_some());
}

/// `preserved:` is not in the XPB grammar at all — it is an extension the
/// checker reads — so its *placement* is free and stays free; but a second
/// list would silently replace the first in the primary reader, and both
/// readers refuse it.
#[test]
fn opb_refuses_a_second_preserved_list_but_not_a_late_one() {
    assert!(
        read(
            b"preserved: x1 ;\npreserved: x2 ;\n1 x1 >= 1 ;\n",
            Format::Opb
        )
        .is_err(),
        "the second reader accepted a second `preserved:` list, whose data the \
         primary reader would silently drop"
    );
    // Placement stays free: a `preserved:` list after the constraints reads.
    let f = read_ok("1 x1 >= 1 ;\npreserved: x1 ;\n", Format::Opb);
    assert_eq!(f.constraints.len(), 1);
}

#[test]
fn opb_reads_a_plain_constraint_with_signs_and_negated_literals() {
    let f = read_ok("* a comment\n+2 x1 -3 ~x2 1 y3 >= -4 ;\n", Format::Opb);
    assert_eq!(f.constraints.len(), 1);
    assert_eq!(
        terms(&f.constraints[0]),
        [(2, "x1", false), (-3, "x2", true), (1, "y3", false)]
    );
    assert_eq!(f.constraints[0].degree, big(-4));
    assert_eq!(f.constraints[0].line, 2);
    assert_eq!(f.objective, None);
}

/// Comments and blank lines carry no constraint, and a `*` comment may
/// follow a constraint on its own line only — the OPB lexer's comment token
/// runs to the end of the line.
#[test]
fn opb_skips_comments_and_blank_lines() {
    let f = read_ok(
        "* #variable= 1 #constraint= 1\n\n   \n1 x1 >= 1 ;\n* trailing\n",
        Format::Opb,
    );
    assert_eq!(f.constraints.len(), 1);
    assert_eq!(f.constraints[0].line, 4);
}

/// `<=` is stored as its negation, and the negation is exact. `i64::MIN` is
/// the value defect 6 wrapped: negating it in the constraint's own width
/// turned an infeasible row into a trivially true one.
#[test]
fn opb_less_equal_negates_every_coefficient_and_the_degree_exactly() {
    let f = read_ok("1 x1 <= -9223372036854775808 ;\n", Format::Opb);
    assert_eq!(f.constraints.len(), 1);
    assert_eq!(terms(&f.constraints[0]), [(-1, "x1", false)]);
    // 2^63, which is exactly the value that does not fit an i64.
    assert_eq!(
        f.constraints[0].degree,
        BigInt::from_str("9223372036854775808").unwrap()
    );
}

/// `=` becomes two inequalities, the `>=` half first — the order the checker
/// files them at consecutive database ids.
#[test]
fn opb_equality_becomes_two_inequalities_in_filing_order() {
    let f = read_ok("2 x1 +1 x2 = 2 ;\n", Format::Opb);
    assert_eq!(f.constraints.len(), 2);
    assert_eq!(
        terms(&f.constraints[0]),
        [(2, "x1", false), (1, "x2", false)]
    );
    assert_eq!(f.constraints[0].degree, big(2));
    assert_eq!(
        terms(&f.constraints[1]),
        [(-2, "x1", false), (-1, "x2", false)]
    );
    assert_eq!(f.constraints[1].degree, big(-2));
}

/// Duplicate and opposite literals in one OPB constraint are left exactly as
/// written: merging them is `normC`'s job on the comparison side, and this
/// reader having its own opinion about it would be a second place to get the
/// cancellation arithmetic wrong (defect 7).
#[test]
fn opb_leaves_duplicate_and_opposite_literals_alone() {
    let f = read_ok("1 x1 1 x1 1 ~x1 >= 1 ;\n", Format::Opb);
    assert_eq!(
        terms(&f.constraints[0]),
        [(1, "x1", false), (1, "x1", false), (1, "x1", true)]
    );
}

/// A constraint with no terms at all, with and without a label.
#[test]
fn opb_reads_constraints_with_no_terms() {
    let f = read_ok(">= 0 ;\n@C1 <= 0;\n", Format::Opb);
    assert_eq!(f.constraints.len(), 2);
    assert!(f.constraints[0].terms.is_empty());
    assert_eq!(f.constraints[0].degree, big(0));
    assert!(f.constraints[1].terms.is_empty());
    assert_eq!(f.constraints[1].degree, big(0));
}

/// A label names a database id; it changes nothing about the constraint.
#[test]
fn opb_label_does_not_change_the_constraint() {
    let labelled = read_ok("@first^_-{[1]} 2 x1 +1 x2 >= 2 ;\n", Format::Opb);
    let plain = read_ok("2 x1 +1 x2 >= 2 ;\n", Format::Opb);
    assert_eq!(
        terms(&labelled.constraints[0]),
        terms(&plain.constraints[0])
    );
    assert_eq!(labelled.constraints[0].degree, plain.constraints[0].degree);
}

/// `min:` — a run of `coefficient literal` pairs, optionally closed by a bare
/// coefficient which is the additive constant
/// (the development design notes: `objective ::= sum, [skip, coefficient] | coefficient`).
#[test]
fn opb_objective_reads_terms_and_a_trailing_constant() {
    let f = read_ok("min: 1 ~x1 -2 x2 +3 ;\n", Format::Opb);
    let o = f.objective.expect("objective");
    assert_eq!(o.terms.len(), 2);
    assert_eq!(o.terms[0].coeff, big(1));
    assert!(o.terms[0].negated);
    assert_eq!(o.terms[1].coeff, big(-2));
    assert_eq!(o.constant, big(3));
}

#[test]
fn opb_objective_without_a_constant_has_constant_zero() {
    let o = read_ok("min: 1 ~x1 1 ~x2 ;\n", Format::Opb)
        .objective
        .expect("objective");
    assert_eq!(o.terms.len(), 2);
    assert_eq!(o.constant, big(0));
}

#[test]
fn opb_empty_and_constant_only_objectives() {
    assert_eq!(
        read_ok("min: ;\n", Format::Opb).objective,
        Some(Objective {
            terms: vec![],
            constant: big(0)
        })
    );
    assert_eq!(
        read_ok("min: 3 ;\n", Format::Opb).objective,
        Some(Objective {
            terms: vec![],
            constant: big(3)
        })
    );
}

/// `max:` is negated on the way in, because the checker only minimizes.
#[test]
fn opb_maximization_objective_is_negated() {
    let o = read_ok("max: 2 x1 2 x2 5 ;\n", Format::Opb)
        .objective
        .expect("objective");
    assert_eq!(o.terms[0].coeff, big(-2));
    assert_eq!(o.terms[1].coeff, big(-2));
    assert_eq!(o.constant, big(-5));
}

/// `preserved:` adds neither a constraint nor an objective term.
#[test]
fn opb_preserved_line_contributes_nothing() {
    let f = read_ok("preserved: x1 x2 ;\n1 x1 >= 1 ;\n", Format::Opb);
    assert_eq!(f.constraints.len(), 1);
    assert_eq!(f.objective, None);
}

/// the development design notes: a variable name is at least two symbols, and `-` is
/// one of the symbols that may continue it.
#[test]
fn opb_variable_names_follow_the_grammar() {
    let f = read_ok("1 a[0]^1_2 1 _var 1 V-A-R >= 1 ;\n", Format::Opb);
    assert_eq!(
        terms(&f.constraints[0]),
        [
            (1, "a[0]^1_2", false),
            (1, "_var", false),
            (1, "V-A-R", false)
        ]
    );
    // One character is not a variable.
    assert!(read("1 x >= 1 ;\n".as_bytes(), Format::Opb).is_err());
}

#[test]
fn opb_refuses_a_constraint_without_its_semicolon() {
    assert!(read("1 x1 >= 1\n".as_bytes(), Format::Opb).is_err());
}

// ---------------------------------------------------------------------------
// DIMACS CNF
// ---------------------------------------------------------------------------

#[test]
fn cnf_reads_clauses_as_unit_coefficient_constraints() {
    let f = read_ok("c a comment\np cnf 2 2\n1 -2 0\n2 0\n", Format::Cnf);
    assert_eq!(f.constraints.len(), 2);
    assert_eq!(
        terms(&f.constraints[0]),
        [(1, "x1", false), (1, "x2", true)]
    );
    assert_eq!(f.constraints[0].degree, big(1));
    assert_eq!(terms(&f.constraints[1]), [(1, "x2", false)]);
    assert_eq!(f.objective, None);
}

/// DIMACS clauses are sets: `1 -2 1 0` is `1 x1 1 ~x2 >= 1`, with
/// coefficient one for the repeated literal rather than two
/// (`proof_format_overview.md` §Clauses).
#[test]
fn cnf_duplicate_literals_collapse() {
    let f = read_ok("p cnf 2 1\n1 -2 1 0\n", Format::Cnf);
    assert_eq!(
        terms(&f.constraints[0]),
        [(1, "x1", false), (1, "x2", true)]
    );
}

/// The same rule at a length where the dedup's *index* matters rather than
/// its inner loop: every literal occurs three times, spread across the whole
/// clause, and each must survive exactly once, in first-occurrence order.
/// This is the pin for replacing the quadratic `Vec::contains` scan with a
/// `HashSet` — a set keyed on the wrong thing (the name without the sign, an
/// owned copy that never matches, an insertion that reports the wrong
/// novelty) changes this answer, and nothing smaller than a repeat at
/// distance would notice.
#[test]
fn cnf_duplicate_literals_collapse_at_length() {
    const N: usize = 500;
    let mut text = format!("p cnf {N} 1\n");
    for _ in 0..3 {
        for v in 1..=N {
            // Alternate the sign by variable, so half the clause is negative
            // and the dedup key has to be the (name, sign) pair.
            let sign = if v % 2 == 0 { "-" } else { "" };
            text.push_str(&format!("{sign}{v} "));
        }
        text.push('\n');
    }
    text.push_str("0\n");
    let f = read_ok(&text, Format::Cnf);
    assert_eq!(f.constraints.len(), 1);
    let got = terms(&f.constraints[0]);
    let want: Vec<(i64, String, bool)> = (1..=N)
        .map(|v| (1i64, format!("x{v}"), v % 2 == 0))
        .collect();
    let want: Vec<(i64, &str, bool)> = want.iter().map(|(c, n, s)| (*c, n.as_str(), *s)).collect();
    assert_eq!(got, want);
}

/// Opposite literals are deliberately left in place for `normC` to cancel:
/// `1 1 2 -2 -1 3 0` must end up as `1 x3 >= -1`, which is what the kernel's
/// normalization does to the deduplicated clause.
#[test]
fn cnf_opposite_literals_are_left_for_the_kernel_to_cancel() {
    let f = read_ok("p cnf 3 1\n1 1 2 -2 -1 3 0\n", Format::Cnf);
    assert_eq!(
        terms(&f.constraints[0]),
        [
            (1, "x1", false),
            (1, "x2", false),
            (1, "x2", true),
            (1, "x1", true),
            (1, "x3", false),
        ]
    );
    assert_eq!(f.constraints[0].degree, big(1));
}

/// A clause may span lines, and a comment may sit inside the clause stream.
#[test]
fn cnf_clauses_may_span_lines() {
    let f = read_ok("p cnf 3 1\n1 2\nc mid-clause comment\n3 0\n", Format::Cnf);
    assert_eq!(f.constraints.len(), 1);
    assert_eq!(f.constraints[0].terms.len(), 3);
}

/// Variable identity is the literal's *value*: `1`, `01`, `001` and `+1` are
/// one variable. This is defect 16's rule, stated for the format the CNF
/// parser already got right.
#[test]
fn cnf_variable_identity_comes_from_the_value_not_the_spelling() {
    let f = read_ok("p cnf 1 4\n1 0\n01 0\n001 0\n+1 0\n", Format::Cnf);
    for c in &f.constraints {
        assert_eq!(terms(c), [(1, "x1", false)]);
    }
}

/// An index far outside `i64` still names a variable rather than overflowing
/// into a different one. `-9223372036854775807` is defect 17's literal.
#[test]
fn cnf_reads_huge_variable_indices_as_names() {
    let f = read_ok(
        "p cnf 1 2\n1 0\n-9223372036854775807 0\n-99999999999999999999999999 0\n",
        Format::Cnf,
    );
    assert_eq!(
        terms(&f.constraints[1]),
        [(1, "x9223372036854775807", true)]
    );
    assert_eq!(
        terms(&f.constraints[2]),
        [(1, "x99999999999999999999999999", true)]
    );
}

/// `0`, `-0` and `+0` all end a clause.
#[test]
fn cnf_every_spelling_of_zero_ends_the_clause() {
    let f = read_ok("p cnf 1 3\n1 0\n1 -0\n1 +0\n", Format::Cnf);
    assert_eq!(f.constraints.len(), 3);
}

#[test]
fn cnf_refuses_a_file_with_no_header() {
    assert!(read("1 2 0\n".as_bytes(), Format::Cnf).is_err());
}

/// The file ends mid-clause. Reading the partial clause as whole would invent
/// a constraint and dropping it is defect 2, so the reader refuses and the
/// caller counts a skip.
#[test]
fn cnf_refuses_an_unterminated_final_clause() {
    assert!(read("p cnf 2 2\n1 0\n1 2\n".as_bytes(), Format::Cnf).is_err());
}

/// The header counts are read for shape but deliberately not enforced:
/// whether a mismatch is fatal is the checker's policy
/// (`--lenient-header-counts`), not a fact about the formula.
#[test]
fn cnf_does_not_enforce_the_header_counts() {
    let f = read_ok("p cnf 1 7\n1 0\n2 0\n", Format::Cnf);
    assert_eq!(f.constraints.len(), 2);
}

// ---------------------------------------------------------------------------
// WCNF
// ---------------------------------------------------------------------------

/// Hard clauses are constraints; soft clauses are not.
#[test]
fn wcnf_hard_clauses_become_constraints() {
    let f = read_ok("h 1 2 0\nh -1 0\n", Format::Wcnf);
    assert_eq!(f.constraints.len(), 2);
    assert_eq!(
        terms(&f.constraints[0]),
        [(1, "x1", false), (1, "x2", false)]
    );
    assert_eq!(terms(&f.constraints[1]), [(1, "x1", true)]);
    assert_eq!(f.objective, Some(Objective::default()));
}

/// A unit soft clause never becomes a constraint: its *negated* literal joins
/// the objective with the clause's weight.
#[test]
fn wcnf_unit_soft_clause_goes_straight_to_the_objective() {
    let f = read_ok("3 -1 0\n", Format::Wcnf);
    assert!(f.constraints.is_empty());
    let o = f.objective.expect("objective");
    assert_eq!(o.terms.len(), 1);
    assert_eq!(o.terms[0].coeff, big(3));
    assert_eq!(o.terms[0].var, "x1");
    assert!(!o.terms[0].negated);
}

/// An empty soft clause is pure cost: its weight is added to the constant.
#[test]
fn wcnf_empty_soft_clause_raises_the_constant() {
    let o = read_ok("5 0\n7 0\n", Format::Wcnf)
        .objective
        .expect("objective");
    assert!(o.terms.is_empty());
    assert_eq!(o.constant, big(12));
}

/// A soft clause of two or more literals gets a blocking variable `_b<i>`,
/// where `i` counts **every** clause of the file, hard ones included. The
/// numbering here is the worked example from `proof_format_overview.md`
/// §MaxSAT, which produces `_b3` and `_b5`.
#[test]
fn wcnf_blocking_variables_are_named_by_file_clause_index() {
    let f = read_ok("1 1 0\nh 1 2 3 0\n1 2 3 0\n2 2 0\n2 1 2 0\n", Format::Wcnf);
    assert_eq!(f.constraints.len(), 3);
    assert_eq!(
        terms(&f.constraints[0]),
        [(1, "x1", false), (1, "x2", false), (1, "x3", false)]
    );
    assert_eq!(
        terms(&f.constraints[1]),
        [(1, "x2", false), (1, "x3", false), (1, "_b3", true)]
    );
    assert_eq!(
        terms(&f.constraints[2]),
        [(1, "x1", false), (1, "x2", false), (1, "_b5", true)]
    );
    let o = f.objective.expect("objective");
    let objective: Vec<(i64, &str, bool)> = o
        .terms
        .iter()
        .map(|t| {
            (
                i64::try_from(t.coeff.clone()).unwrap(),
                t.var.as_str(),
                t.negated,
            )
        })
        .collect();
    assert_eq!(
        objective,
        [
            (1, "x1", true),
            (1, "_b3", true),
            (2, "x2", true),
            (2, "_b5", true),
        ]
    );
    assert_eq!(o.constant, big(0));
}

/// The defect-16 rule, for the format that had it wrong: `1`, `01`, `001`
/// and `+1` are one variable.
#[test]
fn wcnf_variable_identity_comes_from_the_value_not_the_spelling() {
    let f = read_ok("h 1 0\nh -01 0\nh 001 0\nh +1 0\n", Format::Wcnf);
    for (i, c) in f.constraints.iter().enumerate() {
        assert_eq!(c.terms.len(), 1);
        assert_eq!(c.terms[0].var, "x1", "constraint {i}");
    }
    assert!(f.constraints[1].terms[0].negated);
    assert!(!f.constraints[3].terms[0].negated);
}

/// Weights may be spelled with a `+` or with leading zeros, exactly as the
/// lexer's `[+-]?[0-9]+` allows.
#[test]
fn wcnf_weights_accept_every_integer_spelling() {
    let o = read_ok("+007 -1 0\n", Format::Wcnf)
        .objective
        .expect("objective");
    assert_eq!(o.terms[0].coeff, big(7));
}

#[test]
fn wcnf_comments_are_skipped() {
    let f = read_ok("c a comment\nh 1 0\nc another\n", Format::Wcnf);
    assert_eq!(f.constraints.len(), 1);
}

#[test]
fn wcnf_refuses_an_unterminated_final_clause() {
    assert!(read("h 1 0\nh 1 2\n".as_bytes(), Format::Wcnf).is_err());
    // A bare weight with no clause after it is unterminated too.
    assert!(read("h 1 0\n5\n".as_bytes(), Format::Wcnf).is_err());
}

// ---------------------------------------------------------------------------
// Cross-cutting
// ---------------------------------------------------------------------------

#[test]
fn a_line_that_is_not_utf8_is_refused_rather_than_skipped() {
    let mut bytes = b"p cnf 1 2\n1 0\n".to_vec();
    bytes.extend_from_slice(&[0xff, b'\n']);
    bytes.extend_from_slice(b"1 0\n");
    assert!(read(&bytes, Format::Cnf).is_err());
}

#[test]
fn a_file_without_a_trailing_newline_reads_the_same() {
    let with = read_ok("p cnf 1 1\n1 0\n", Format::Cnf);
    let without = read_ok("p cnf 1 1\n1 0", Format::Cnf);
    assert_eq!(with.constraints, without.constraints);
}

#[test]
fn crlf_line_endings_read_the_same_as_lf() {
    let lf = read_ok("* c\n1 x1 >= 1 ;\n", Format::Opb);
    let crlf = read_ok("* c\r\n1 x1 >= 1 ;\r\n", Format::Opb);
    assert_eq!(lf.constraints, crlf.constraints);
}

/// Every integer spelling the lexers admit reads as its value.
#[test]
fn integer_spellings() {
    assert_eq!(int_value("42"), big(42));
    assert_eq!(int_value("+42"), big(42));
    assert_eq!(int_value("-42"), big(-42));
    assert_eq!(int_value("0042"), big(42));
    assert_eq!(int_value("+0042"), big(42));
    assert_eq!(int_value("-0042"), big(-42));
    assert_eq!(int_value("000"), big(0));
    assert!(int_is_zero("0"));
    assert!(int_is_zero("-0"));
    assert!(int_is_zero("+000"));
    assert!(!int_is_zero("-01"));
    assert!(int_is_negative("-1"));
    assert!(!int_is_negative("-0"));
    assert_eq!(dimacs_var_name("-001"), "x1");
    assert_eq!(dimacs_var_name("+1"), "x1");
}
