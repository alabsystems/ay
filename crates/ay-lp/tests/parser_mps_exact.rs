// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! The exact MPS reading (AY-N11, AY-N6 reviews): every number as written,
//! every construct as the MIPLIB solution checker reads it, a refusal where
//! readers disagree.

use ay_lp::exact::decimal::parse_decimal;
use ay_lp::{parse_mps, parse_mps_exact, ExactProblem, LpError, Sense, VarKind};
use num_rational::BigRational;

fn q(text: &str) -> BigRational {
    parse_decimal(text).expect("number")
}

fn exact(text: &str) -> ExactProblem {
    parse_mps_exact(text).expect("parse")
}

fn refused_at(text: &str) -> usize {
    match parse_mps_exact(text) {
        Err(LpError::Parse { line, .. } | LpError::InvalidNumber { line, .. }) => line,
        other => panic!("expected a refusal, got {other:?}"),
    }
}

fn bounds(p: &ExactProblem, j: usize) -> (Option<BigRational>, Option<BigRational>) {
    (p.columns[j].lower.clone(), p.columns[j].upper.clone())
}

/// The numbers of the six reviewers' files that an `f64` cannot hold are
/// kept: a bound, a coefficient written in exponent form, a right-hand side,
/// the sum of two entries, a range side.
#[test]
fn numbers_an_f64_cannot_hold_are_read_as_written() {
    let p = exact(
        "NAME EXACT\nROWS\n N  OBJ\n G  MATCH\nCOLUMNS\n    X         OBJ       0         MATCH     \
         9.007199254740993e15\n    X         MATCH     1\n    Y         MATCH     -9007199254740992\n\
         RHS\n    RHS1      MATCH     9007199254740993\nRANGES\n    RNG       MATCH     1\nBOUNDS\n \
         FX BND1      X         9007199254740993\n FX BND1      Y         0.1\nENDATA\n",
    );
    assert_eq!(p.rows[0].coeffs[0].1, q("9007199254740994"));
    assert_eq!(p.rows[0].coeffs[1].1, q("-9007199254740992"));
    assert_eq!(p.rows[0].lower, Some(q("9007199254740993")));
    assert_eq!(p.rows[0].upper, Some(q("9007199254740994")));
    assert_eq!(
        bounds(&p, 0),
        (Some(q("9007199254740993")), Some(q("9007199254740993")))
    );
    assert_eq!(bounds(&p, 1).0, Some(q("0.1")));
}

/// RANGES by row type and sign, as the checker computes them.
#[test]
fn ranges_follow_row_type_and_sign() {
    let p = exact(
        "NAME RNG\nROWS\n N OBJ\n G RG\n L RL\n E RE\n E RF\n E RZ\nCOLUMNS\n    X OBJ 1 RG 1\n    \
         X RL 1 RE 1\n    X RF 1 RZ 1\nRHS\n    RHS RG 2 RL 2\n    RHS RE 2 RF 2\n    RHS RZ 2\n\
         RANGES\n    RNG RG -3 RL -3\n    RNG RE 3 RF -3\n    RNG RZ 0\nENDATA\n",
    );
    let sides: Vec<(String, String)> = p
        .rows
        .iter()
        .map(|r| {
            (
                r.lower.as_ref().map_or("-".into(), ToString::to_string),
                r.upper.as_ref().map_or("-".into(), ToString::to_string),
            )
        })
        .collect();
    let want = [("2", "5"), ("-1", "2"), ("2", "5"), ("-1", "2"), ("2", "2")];
    for (got, want) in sides.iter().zip(want) {
        assert_eq!((got.0.as_str(), got.1.as_str()), want);
    }
}

/// The objective row's right-hand side is the negated objective constant;
/// later `N` rows are free rows; a constraint row that shares its name with
/// any other row is refused (the reviewed reader silently dropped it).
#[test]
fn objective_offset_free_rows_and_duplicate_row_names() {
    let p = exact(
        "NAME OFF\nROWS\n N OBJ\n N SPARE\n L C1\nCOLUMNS\n    X OBJ 2 C1 1\n    X SPARE 7\n\
         RHS\n    RHS OBJ 1.5 C1 4\nENDATA\n",
    );
    assert_eq!(p.offset, q("-1.5"));
    assert_eq!(p.rows.len(), 1);
    assert_eq!(
        refused_at(
            "NAME D\nROWS\n N OBJ\n N SPARE\n L SPARE\nCOLUMNS\n    X OBJ 1 SPARE 1\nENDATA\n"
        ),
        5
    );
    // RHS of a free row (the checker dereferences a missing row there).
    assert_eq!(
        refused_at(
            "NAME D\nROWS\n N OBJ\n N SPARE\n L C1\nCOLUMNS\n    X OBJ 1 C1 1\nRHS\n    \
             RHS SPARE 3\nENDATA\n"
        ),
        9
    );
}

/// `OBJSENSE MAX` on the header line is a maximisation (the reviewed reader
/// ignored it and minimised); both spellings and `OBJNAME` are read.
#[test]
fn objsense_in_both_spellings_and_objname() {
    for head in [
        "OBJSENSE MAX\n",
        "OBJSENSE\n    MAX\n",
        "OBJSENSE MAXIMIZE\n",
    ] {
        let p = parse_mps(&format!(
            "NAME S\n{head}ROWS\n N OBJ\n L C1\nCOLUMNS\n    X OBJ 1 C1 1\nENDATA\n"
        ))
        .expect("parse");
        assert_eq!(p.sense, Sense::Max, "{head}");
    }
    assert_eq!(
        refused_at("NAME S\nOBJSENSE max\nROWS\n N OBJ\nCOLUMNS\n    X OBJ 1 C1 1\nENDATA\n"),
        2
    );
    let p = exact(
        "NAME S\nOBJNAME\n    COST\nROWS\n N OTHER\n N COST\nCOLUMNS\n    X OTHER 5 COST 2\nENDATA\n",
    );
    assert_eq!(p.columns[0].objective, q("2"));
}

/// Marker integer columns follow the organizers' checker on every bound
/// entry: binary `[0, 1]` until an entry other than `UP 1`, which makes the
/// column a general integer with upper bound `+inf` before it applies. The
/// reviewed reader kept `UP 1` after a later `LO 2`. `BV` intersects the
/// bounds with `[0, 1]`.
#[test]
fn marker_defaults_and_bv_follow_the_checker_entry_by_entry() {
    let p = exact(
        "NAME B\nROWS\n N OBJ\n L C1\nCOLUMNS\n    M 'MARKER' 'INTORG'\n    A OBJ 1 C1 1\n    \
         B OBJ 1 C1 1\n    C OBJ 1 C1 1\n    D OBJ 1 C1 1\n    M 'MARKER' 'INTEND'\n    \
         E OBJ 1 C1 1\nBOUNDS\n UP BND B 1\n LO BND B 2\n LO BND C 0\n UP BND D 1\n \
         LO BND E -3\n UP BND E 0.5\n BV BND E\nENDATA\n",
    );
    assert_eq!(bounds(&p, 0), (Some(q("0")), Some(q("1"))));
    assert_eq!(p.columns[0].kind, VarKind::Binary);
    // UP 1 keeps it binary; the later LO 2 resets the upper bound.
    assert_eq!(bounds(&p, 1), (Some(q("2")), None));
    assert_eq!(p.columns[1].kind, VarKind::Integer);
    // In the organizers' checker even LO 0 resets it.
    assert_eq!(bounds(&p, 2), (Some(q("0")), None));
    assert_eq!(bounds(&p, 3), (Some(q("0")), Some(q("1"))));
    assert_eq!(bounds(&p, 4), (Some(q("0")), Some(q("0.5"))));
    assert_eq!(p.columns[4].kind, VarKind::Binary);
}

/// A negative `UP` is refused only where readers disagree: when the final
/// lower bound is 0.
#[test]
fn negative_up_with_lower_bound_zero_is_refused() {
    let head = "NAME N\nROWS\n N OBJ\n L C1\nCOLUMNS\n    X OBJ 1 C1 1\nBOUNDS\n";
    assert_eq!(refused_at(&format!("{head} UP BND X -1\nENDATA\n")), 8);
    assert_eq!(
        refused_at(&format!("{head} LO BND X 0\n UP BND X -1\nENDATA\n")),
        9
    );
    let p = exact(&format!("{head} UP BND X -1\n LO BND X -5\nENDATA\n"));
    assert_eq!(bounds(&p, 0), (Some(q("-5")), Some(q("-1"))));
}

/// Repeated matrix entries are summed exactly; a repeated objective entry,
/// non-contiguous records, a cut-off file and a line the checker splits into
/// other fields are refused.
#[test]
fn duplicates_and_layout() {
    let p = exact(
        "NAME D\nROWS\n N OBJ\n E R\nCOLUMNS\n    X OBJ 0 R 9007199254740992\n    X R 1\n\
         RHS\n    RHS R 1\nENDATA\n",
    );
    assert_eq!(p.rows[0].coeffs, vec![(0, q("9007199254740993"))]);
    let head = "NAME D\nROWS\n N OBJ\n L R\nCOLUMNS\n";
    assert_eq!(
        refused_at(&format!(
            "{head}    X OBJ -3 R 1\n    X OBJ 2 R 1\nENDATA\n"
        )),
        7
    );
    assert_eq!(
        refused_at(&format!("{head}    X OBJ 1 R 1\nRHS\n    RHS R 1\n")),
        8
    );
    // The checker reads this first COLUMNS line in its fixed layout as the
    // single field X_OBJ_1 (`solchecker`: "Syntax error in line 6: X_OBJ_1").
    assert_eq!(
        refused_at(&format!("{head}    X OBJ 1\n    X R 1 R 1\nENDATA\n")),
        6
    );
    // Out of order and unread sections.
    assert_eq!(
        refused_at(&format!("{head}    X OBJ 1 R 1\nBOUNDS\nRHS\nENDATA\n")),
        8
    );
    assert_eq!(
        refused_at(&format!("{head}    X OBJ 1 R 1\nSOS\nENDATA\n")),
        7
    );
    assert_eq!(
        refused_at(&format!(
            "{head}    X OBJ 1 R 1\nBOUNDS\n SC BND X 1\nENDATA\n"
        )),
        8
    );
}

/// Numbers the checker reads differently from other readers are refused.
#[test]
fn numbers_outside_the_shared_grammar_are_refused() {
    for bad in ["1/2", "inf", "1.5D3", "0x10", "1e999"] {
        let text = format!(
            "NAME N\nROWS\n N OBJ\n L R\nCOLUMNS\n    X OBJ 1 R {bad}\nRHS\n    RHS R 1\nENDATA\n"
        );
        assert_eq!(refused_at(&text), 6, "{bad}");
    }
}
