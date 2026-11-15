// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// Textually included by `run` to preserve private helper paths and behavior.

/// Withhold every later verdict of the session, across `(reset)`.
///
/// A reader such as Verus pairs answers with queries in order. Once ay gives
/// a query an answer where z3 gives none, or the reverse, each later answer
/// sits one place off z3's and is read as the answer to another query, so a
/// later `sat` or `unsat` can be read against a query it does not answer. A
/// `(reset)` clears the problem but not the offset, so the verdicts stay
/// withheld after it.
fn withhold_answers_out_of_step(executor: &mut Executor, transcript: &mut SmtTranscriptState) {
    transcript.answers_out_of_step = true;
    mark_problem_incomplete(executor, transcript);
}

/// Whether text dropped for a parse error holds a query. z3 answers
/// `(check-sat-assuming (p) extra)` before it reports `extra` and gives no
/// answer for `(check-sat-assuming p)`, so whether z3 answered it is not
/// known.
fn dropped_text_holds_a_query(text: &str) -> bool {
    source_has_command_keyword(text, |keyword| {
        matches!(
            keyword,
            "check-sat" | "check-sat-assuming" | "check-sat-using"
        )
    })
}

/// How a decision query that failed to elaborate is answered.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct QueryRejection {
    /// Print `unknown` for the query.
    answered: bool,
    /// Withhold every later verdict ([`withhold_answers_out_of_step`]).
    withhold: bool,
}

/// How a decision query whose elaboration failed with `message` is
/// answered, or `None` for a failure that is not an elaboration error.
///
/// z3 reports an undefined symbol, a sort mismatch or a non-Boolean
/// assumption while it parses the query, prints the error and gives no
/// answer, so `--z3-mode` gives none either. Whether z3 rejected the query
/// too is known only for a sort error in a session that has withheld no
/// verdict, whose names and sorts are z3's. Otherwise later verdicts are
/// withheld: z3 may know a symbol ay does not (a builtin ay lacks), a
/// session that withheld a verdict may name things unlike z3 (z3 accepts
/// `(define-fun h () Bool ...)` beside `(declare-const h Int)`, which ay
/// drops, and then reads `h` as the Bool), and for any other elaboration
/// error, which is answered `unknown`, z3 may have rejected the query.
///
/// Plain mode answers every query, `unknown` here, where z3 may give none,
/// so it withholds every later verdict.
fn query_rejection(transcript: &SmtTranscriptState, message: &str) -> Option<QueryRejection> {
    let detail = message.strip_prefix("elaboration error: ")?;
    if !z3_mode_enabled() {
        return Some(QueryRejection {
            answered: true,
            withhold: true,
        });
    }
    if detail
        .strip_prefix("undefined symbol: ")
        .is_some_and(|symbol| !symbol.trim().is_empty())
    {
        return Some(QueryRejection {
            answered: false,
            withhold: true,
        });
    }
    if detail.starts_with("sort mismatch: ") {
        return Some(QueryRejection {
            answered: false,
            withhold: transcript.is_incomplete(),
        });
    }
    Some(QueryRejection {
        answered: true,
        withhold: true,
    })
}
