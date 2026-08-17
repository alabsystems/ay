// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Unit tests for the W4 per-position witness synthesizer helpers.

use super::*;
use ay_frontend::parse;

#[test]
fn w4_defaults_on() {
    // W4 went DEFAULT-ON (`--dpll-no-str-w4` is the kill switch); this test
    // previously asserted the pre-default-on contract and had gone stale.
    assert!(
        str_w4_enabled(),
        "W4 must default ON (`--dpll-no-str-w4` kills it)"
    );
}

#[test]
fn fresh_char_avoids_the_formula_alphabet() {
    let alpha: Vec<char> = "abcdefghijklmnopqrstuvwxyz".chars().collect();
    let fresh = w4_fresh_char(&alpha);
    assert!(!alpha.contains(&fresh));
}

#[test]
fn set_char_pins_appends_and_clears() {
    let cur: Vec<char> = "abc".chars().collect();
    let alpha: Vec<char> = vec!['a', 'b', 'c'];
    // Pin inside the string.
    let out = w4_set_char(&cur, 1, 'z', true, &alpha, 'q').unwrap();
    assert_eq!(out.iter().collect::<String>(), "azc");
    // Pin one past the end appends.
    let out = w4_set_char(&cur, 3, 'z', true, &alpha, 'q').unwrap();
    assert_eq!(out.iter().collect::<String>(), "abcz");
    // Clearing a character that is not there is a no-op (None).
    assert!(w4_set_char(&cur, 0, 'z', false, &alpha, 'q').is_none());
    // Clearing a character that IS there replaces it with a non-excluded one.
    let out = w4_set_char(&cur, 0, 'a', false, &alpha, 'q').unwrap();
    assert_ne!(out[0], 'a');
}

#[test]
fn overwrite_extends_when_needed() {
    let cur: Vec<char> = "ab".chars().collect();
    let lit: Vec<char> = "xyz".chars().collect();
    let out = w4_overwrite(&cur, 1, &lit).unwrap();
    assert_eq!(out.iter().collect::<String>(), "axyz");
}

#[test]
fn resize_window_grows_and_shrinks_in_place() {
    let cur: Vec<char> = "abcdef".chars().collect();
    // Window [2,5) of length 3 -> length 5: two pads inserted at the window end.
    let out = w4_resize_window(&cur, 2, 3, 5, '#').unwrap();
    assert_eq!(out.iter().collect::<String>(), "abcde##f");
    // Window [2,5) -> length 1: two characters dropped from the window tail.
    let out = w4_resize_window(&cur, 2, 3, 1, '#').unwrap();
    assert_eq!(out.iter().collect::<String>(), "abcf");
    // No-op resize is rejected (nothing to try).
    assert!(w4_resize_window(&cur, 2, 3, 3, '#').is_none());
}

#[test]
fn pick_char_prefers_fresh_then_alphabet() {
    let alpha: Vec<char> = vec!['x', 'y'];
    let mut excluded: HashSet<char> = HashSet::default();
    assert_eq!(w4_pick_char(&excluded, &alpha, 'q'), 'q');
    excluded.insert('q');
    assert_eq!(w4_pick_char(&excluded, &alpha, 'q'), 'x');
}

// ── The deterministic search budget (#w4-work-budget) ──────────────

#[test]
fn work_budget_default_and_kill_switch() {
    // Default is the calibrated cap; `--str-w4-work 0` restores the
    // pre-budget unbounded search exactly (B42: the override is CLI-owned,
    // so the default arm is unconditional here).
    assert_eq!(w4_search_work_budget(), Some(MAX_W4_SEARCH_WORK));
}

#[test]
fn work_budget_keeps_every_measured_conversion_in_range() {
    // The census these constants come from (see `MAX_W4_SEARCH_WORK`): the
    // costliest W4/W5/W6 search that ever produced a battery-accepted witness
    // on the 600-file QF_S + QF_SLIA canary cost 84.4M units, and the cheapest
    // starvation case cost 242.9M. The cap must separate them, and the wide
    // band's reduced share must still clear the 14,812 units `kaluza/sat/big/398`
    // needs — otherwise the constants have drifted away from their evidence.
    const COSTLIEST_CONVERSION: u64 = 84_379_455;
    const CHEAPEST_STARVATION: u64 = 242_988_834;
    const KALUZA_398_WIDE_SEARCH: u64 = 14_812;
    const {
        assert!(
            MAX_W4_SEARCH_WORK > COSTLIEST_CONVERSION,
            "budget must not cut a search that is known to succeed"
        );
        assert!(
            MAX_W4_SEARCH_WORK < CHEAPEST_STARVATION,
            "budget must cut the measured starvation cases"
        );
        assert!(
            MAX_W4_SEARCH_WORK / W4_WIDE_WORK_SHARE > KALUZA_398_WIDE_SEARCH,
            "the wide band's reduced share must still fit its measured conversion"
        );
        assert!(
            MAX_W4_WIDE_VARS >= 85,
            "kaluza/sat/big/398 declares 85 vars"
        );
    }
}

#[test]
fn work_clock_is_monotone() {
    let a = w4_work_clock();
    let b = w4_work_clock();
    assert!(b >= a, "the search work clock must never run backwards");
}

#[test]
fn budget_is_disarmed_outside_the_pass() {
    // A fresh executor has no deadline armed, so `w4_budget_exhausted` is
    // false — W6's and W7's own passes must never inherit W4's budget.
    let exec = Executor::new();
    assert_eq!(exec.w4_work_deadline.get(), None);
    assert!(!exec.w4_budget_exhausted());
}

#[test]
fn partial_budget_score_is_rejected_and_not_memoised() {
    let mut exec = Executor::new();
    let true_term = exec.ctx.terms.mk_bool(true);
    let false_term = exec.ctx.terms.mk_bool(false);
    let atoms = [(true_term, true), (false_term, true)];
    let assign = HashMap::default();

    exec.w4_work_deadline
        .set(Some(w4_work_clock().saturating_add(1)));
    assert_eq!(exec.w4_violations_complete(&atoms, &assign), None);
    assert_eq!(exec.w4_violations(&atoms, &assign), usize::MAX);

    exec.w4_work_deadline.set(None);
    assert_eq!(exec.w4_violations_complete(&atoms, &assign), Some(1));
}

#[test]
fn tiny_budget_full_w4_entrypoint_rejects_partial_candidate() {
    let _enabled = w4_test_enabled_override(true);
    let _budget = w4_test_work_budget_override(Some(1));
    let mut exec = Executor::new();
    let commands = parse(
        r#"
        (set-logic QF_S)
        (declare-const x String)
        (assert (= x "a"))
        (assert (str.in_re x (str.to_re "a")))
        "#,
    )
    .expect("parse tiny W4 formula");
    for command in &commands {
        exec.execute(command).expect("install tiny W4 formula");
    }

    let work_before = w4_work_clock();
    assert!(exec
        .try_per_position_witnesses()
        .expect("W4 search")
        .is_none());
    assert_eq!(w4_work_clock().saturating_sub(work_before), 1);
    assert_eq!(exec.w4_work_deadline.get(), None);
}
