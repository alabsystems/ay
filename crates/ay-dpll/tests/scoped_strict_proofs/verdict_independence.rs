// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! What a certified verdict may NOT depend on: whether its Alethe document
//! renders, and how wide the authored connective the reorder bridge spans is.
//! Each pin below was a measured verdict flip before its fix.

use super::{assert_certified_unsat, fixture, row_body, verdicts};
use ntest::timeout;

/// Presentation never decides the verdict, pinned twice.
///
/// A row whose symbols are RE-DECLARED after a `pop` prints a projection
/// through the symbol's private `__ay_overload_N` identity, so its document
/// may not render (the ordinary lane prints `unsat` and then refuses
/// `(get-proof)` for such a row). Its replayed refutation is strictly checked,
/// so the row publishes `unsat` exactly as the ordinary lane does, and
/// `(get-proof)` prints a checked document or an honest refusal — never a
/// `hole` or `trust` step, and never a `sat`.
#[test]
#[timeout(600_000)]
fn a_replayed_row_whose_proof_cannot_print_keeps_its_checked_verdict() {
    let mut script = String::from("(set-option :produce-proofs true)\n(set-logic QF_LIA)\n");
    for _ in 0..2 {
        script.push_str("(push 1)\n");
        script.push_str(&row_body(&fixture(
            "deductive_checksgen_reach_encoding",
            "path_budget_async_sentinel.smt2",
        )));
        script.push_str("\n(check-sat)\n(get-proof)\n(pop 1)\n");
    }
    let (verdicts, reason, outputs) = verdicts(&script);
    assert_eq!(verdicts, vec!["unsat", "unsat"], "({reason:?}) {outputs:?}");
    for output in outputs.iter().filter(|output| output.contains("(assume ")) {
        assert!(
            !output.contains(":rule hole") && !output.contains(":rule trust"),
            "a published row printed an unchecked document:\n{output}"
        );
    }
}

/// The second pin: a checked refutation beside more live facts than the
/// presentation passes' override tables hold (8,192 entries) publishes `unsat`
/// with proofs on, as it does with proofs off. The replay lane used to screen
/// its candidate's presentation and withdraw the verdict when the screen
/// failed (measured: `unknown`, self-check-rejected, from 8,093 facts up).
#[test]
#[timeout(600_000)]
fn a_replayed_refutation_beside_more_facts_than_the_presentation_tables_publishes() {
    let row = fixture(
        "deductive_checksgen_reach_encoding",
        "coroutine_resume_saturated_unreachable.smt2",
    );
    let facts = 8_300;
    let mut script = String::from("(set-option :produce-proofs true)\n(set-logic QF_LIA)\n");
    for line in row.lines().filter(|line| line.starts_with("(declare")) {
        script.push_str(line);
        script.push('\n');
    }
    for index in 0..facts {
        script.push_str(&format!("(declare-fun z{index} () Int)\n"));
    }
    script.push_str("(assert (>= z0 0))\n");
    for index in 1..facts {
        script.push_str(&format!("(assert (<= z{index} (+ z{} 1)))\n", index - 1));
    }
    for line in row.lines().filter(|line| line.starts_with("(assert")) {
        script.push_str(line);
        script.push('\n');
    }
    script.push_str("(check-sat)\n");
    assert_certified_unsat("coroutine row beside 8,300 chain facts, proofs on", &script);
}

/// The a5 join with its authored index disjunction widened to 65 disjuncts,
/// one more than the reorder bridge's former 64-argument cap, still certifies
/// through the ordinary proof with the replay off. Measured before the cap
/// was deleted: k = 64 `unsat`, k = 65 `unknown` (self-check-rejected), i.e.
/// a wider join fell back to the replay lane.
#[test]
#[timeout(300_000)]
fn the_a5_join_certifies_past_the_former_reorder_arity_cap() {
    let row = fixture(
        "deductive_checksgen_reach_encoding",
        "a5_two_next_if_ok_sym_reach.smt2",
    );
    let index = "(or (and (>= __trust_u_i 0) (< __trust_u_i __trust_u_a__slice_len)) \
                 (and (>= __trust_u_i 1) (< __trust_u_i __trust_u_m)))";
    assert!(
        row.contains(index),
        "the fixture spells its index disjunction"
    );
    let mut widened =
        String::from("(or (and (>= __trust_u_i 0) (< __trust_u_i __trust_u_a__slice_len))");
    for lower in 1..65 {
        widened.push_str(&format!(
            " (and (>= __trust_u_i {lower}) (< __trust_u_i __trust_u_m))"
        ));
    }
    widened.push(')');
    let row = row.replace(index, &widened);
    let mut flags = ay_core::misc_cli_flags().clone();
    flags.no_consequence_replay = true;
    let _replay_off = ay_core::misc_test_override::set(flags);
    assert_certified_unsat("a5 reach row, 65 index disjuncts, replay off", &row);
}
