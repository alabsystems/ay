// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Ordering policy for the leading field of a text-LRAT line.
//!
//! The field means different things on the two kinds of line. On an addition
//! it is the new clause's ID and must strictly increase. On a deletion it is
//! a positional stamp naming the most recently added clause, so it may repeat
//! the current high-water mark. Applying the addition rule to deletion lines
//! made `ay-lrat-check` reject valid CaDiCaL proofs with
//! `non-monotonic step ID 25 after 25`.

use super::*;

/// A deletion line stamped with the ID of the clause just added is the
/// standard emission of both reference writers: drat-trim prints `"%i d "`
/// with `lastAdded` (`reference/drat-trim/drat-trim.c:383`) and CaDiCaL does
/// the same, e.g. `25 -10 2 3 0 1 7 0` followed by `25 d 1 5 6 7 0`. The
/// reference checker ignores the field entirely — `lrat-check.c:462`
/// dispatches deletions on `litList + 2` and never reads `litList[0]`.
#[test]
fn test_parse_text_accepts_deletion_repeating_previous_addition_id() {
    let steps = parse_text_lrat("25 -10 2 3 0 1 7 0\n25 d 1 5 6 7 0\n26 -7 6 5 0 2 8 0\n")
        .expect("deletion repeating the previous addition ID is standard LRAT");
    assert_eq!(
        steps,
        vec![
            LratStep::Add {
                id: 25,
                clause: vec![lit(-10), lit(2), lit(3)],
                hints: vec![1, 7],
            },
            LratStep::Delete {
                ids: vec![1, 5, 6, 7]
            },
            LratStep::Add {
                id: 26,
                clause: vec![lit(-7), lit(6), lit(5)],
                hints: vec![2, 8],
            },
        ]
    );
}

/// AY's own emitter burns a fresh ID for the deletion line
/// (`ay-sat/src/proof/lrat.rs:317`), so a stamp *above* the high-water mark
/// must keep working too.
#[test]
fn test_parse_text_accepts_deletion_id_above_previous_addition() {
    let steps = parse_text_lrat("4 1 0 1 0\n5 d 1 0\n6 0 4 3 0\n")
        .expect("a deletion stamp above the last addition ID is legal");
    assert_eq!(steps.len(), 3);
    assert_eq!(steps[1], LratStep::Delete { ids: vec![1] });
}

/// A deletion stamp that runs *backwards* means a truncated, reordered or
/// corrupted proof and is still rejected.
#[test]
fn test_parse_text_rejects_decreasing_deletion_step_id() {
    let err = parse_text_lrat("10 1 0 1 0\n9 d 1 0\n").unwrap_err();
    assert!(
        err.to_string().contains("decreasing deletion step ID"),
        "got: {err}"
    );
    // Also backwards relative to an earlier deletion stamp.
    assert!(parse_text_lrat("4 1 0 1 0\n7 d 1 0\n5 d 2 0\n").is_err());
}

/// The relaxation is scoped to deletions: a genuinely non-monotonic
/// *addition* must still be rejected, including one that follows a deletion
/// line carrying the same stamp.
#[test]
fn test_parse_text_still_rejects_non_monotonic_addition_after_deletion() {
    let err = parse_text_lrat("25 -10 0 1 0\n25 d 1 0\n25 -7 0 2 0\n").unwrap_err();
    assert!(
        err.to_string().contains("non-monotonic step ID"),
        "got: {err}"
    );
    assert!(parse_text_lrat("25 -10 0 1 0\n25 d 1 0\n24 -7 0 2 0\n").is_err());
}

/// End-to-end over a real CaDiCaL text proof shape: the PHP(4,3) prefix that
/// `ay-lrat-check` rejected at `b51e55824d`. Every deletion line repeats the
/// ID of the addition immediately above it.
#[test]
fn test_parse_text_cadical_php43_prefix_round_trips() {
    let proof = "\
23 -4 2 3 0 1 5 0
24 -7 2 3 0 1 6 0
25 -10 2 3 0 1 7 0
25 d 1 5 6 7 0
26 -7 6 5 0 2 8 0
27 -10 6 5 0 2 9 0
28 6 5 2 3 0 23 2 0
28 d 2 8 9 23 0
";
    let steps = parse_text_lrat(proof).expect("CaDiCaL text LRAT must parse");
    assert_eq!(steps.len(), 8);
    assert_eq!(
        steps
            .iter()
            .filter(|s| matches!(s, LratStep::Delete { .. }))
            .count(),
        2
    );
    assert_eq!(
        steps[3],
        LratStep::Delete {
            ids: vec![1, 5, 6, 7]
        }
    );
}
