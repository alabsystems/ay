// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! The indeterminate-index read-over-write CASE SPLIT publishes a certified
//! UNSAT (the development design notes).
//!
//! `a2 = store(a, n, 0)` with `select(a, k) = 0` authored and
//! `not (select(a2, k) = 0)` is UNSAT although `k` vs `n` is unconstrained:
//! BOTH read-over-write branches reach `0`. The eager ground array lane used
//! to close this on a trust step, so no strict proof could exist, mandatory
//! certification vetoed the verdict, and the authority-bearing default
//! published `unknown` — the exact shape deductive-checks's ghost-pair replay
//! obligations export. The authored array-ROW rebuilder now closes it by case
//! split over the written index: one guarded
//! `TheoryLemmaKind::ArraySelectStore` lemma per branch, an `EufTransitive`
//! chain each, and a final resolution of the two guard units — every step
//! re-derived by the UNCHANGED strict checker before anything publishes.
//!
//! The quantified sibling (the same ground facts under a redundant `forall`)
//! exercises the consequence-replay lane end to end:
//! `crates/ay-chc`'s `ghost_pair_certificate_exports_unsat_replay_obligations`.

use ay_dpll::Executor;
use ay_frontend::parse;
use ntest::timeout;

const GROUND_CASE_SPLIT: &str = "\
(set-logic QF_AUFLIA)
(declare-const a (Array Int Int))
(declare-const n Int)
(declare-const a2 (Array Int Int))
(declare-const k Int)
(assert (= a2 (store a n 0)))
(assert (= (select a k) 0))
(assert (= (select a n) 0))
(assert (not (= (select a2 k) 0)))
(check-sat)
";

#[test]
#[timeout(60_000)]
fn test_indeterminate_index_row_case_split_publishes_certified_unsat() {
    let commands = parse(GROUND_CASE_SPLIT).expect("parse");
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).expect("execute_all");

    assert_eq!(
        outputs.first().map(String::as_str),
        Some("unsat"),
        "the certified lane must publish the case-split UNSAT"
    );
    assert_eq!(
        exec.unknown_reason(),
        None,
        "a certified verdict must carry no withholding reason"
    );
    // The CompetitionRaw carve-out is the only emitter of `unsat_admission`;
    // its absence pins that this UNSAT went through mandatory certification.
    assert_eq!(
        exec.statistics().get_string("unsat_admission"),
        None,
        "the certified lane must not publish through CompetitionRaw admission"
    );
}
