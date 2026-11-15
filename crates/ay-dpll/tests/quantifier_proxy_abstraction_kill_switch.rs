// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Kill-switch coverage for the quantifier proxy abstraction
//! (#quantifier-proxy-abstraction).
//!
//! This file holds the switch test in its own binary, following
//! `ground_conflict_decomp_kill_switch.rs`: it installs a thread-local
//! `MiscCliFlags` override, which must never race a sibling test that could run
//! interleaved on the same thread.
//!
//! `--no-quantifier-proxy-abstraction` restores the pre-stage behaviour
//! byte-for-byte — `flatten_and_strip_quantifiers` deletes every assertion that
//! mentions a quantifier, nothing is minted, and `quantifier_abstraction_active`
//! is never set, so no downstream gate reads anything but its baseline value.
//! What must hold in BOTH positions is the soundness direction.

#![allow(clippy::panic)]

mod common;

/// UNSAT (`n <= 4` refutes `n > 5`, so the clause forces `forall x. p x`, which
/// contradicts `(not (p c))`), but the ABSTRACTED skeleton
/// `(or (> n 5) qproxy) ∧ n <= 4 ∧ ¬p(c)` is satisfiable with `qproxy := true`.
/// With the switch OFF the whole clause is deleted instead, which is a
/// DIFFERENT over-approximation of the same problem — also satisfiable. Neither
/// position may answer `sat`.
const ABSTRACTED_SKELETON_SAT_BUT_UNSAT: &str = r#"
(set-logic UFLIA)
(declare-fun n () Int)
(declare-fun c () Int)
(declare-fun p (Int) Bool)
(assert (<= n 4))
(assert (or (> n 5) (forall ((x Int)) (p x))))
(assert (not (p c)))
(check-sat)
"#;

/// Genuinely SATISFIABLE (`q ≡ true` is a model). Restoring the goal to the
/// ground solver must not manufacture a refutation in either position.
const GENUINELY_SAT_CONTROL: &str = r#"
(set-logic UFLIA)
(declare-fun n () Int)
(declare-fun c () Int)
(declare-fun q (Int) Bool)
(assert (<= n 4))
(assert (or (> n 5) (forall ((x Int)) (q x))))
(assert (q c))
(check-sat)
"#;

/// An entailed top-level universal: the pass DECLINES on it, so both switch
/// positions run the identical code path and must return the identical verdict.
/// This is the "switch-off is byte-identical" claim asserted where it is
/// cheapest to check — on the family the pass never touches.
const CONJUNCTIVE_ONLY_UNSAT: &str = r#"
(set-logic UFLIA)
(declare-fun c () Int)
(declare-fun p (Int) Bool)
(assert (forall ((x Int)) (p x)))
(assert (not (p c)))
(check-sat)
"#;

#[test]
fn quantifier_proxy_abstraction_is_fully_covered_by_the_kill_switch() {
    let off_guard = ay_core::misc_test_override::set(ay_core::MiscCliFlags {
        no_quantifier_proxy_abstraction: true,
        ..Default::default()
    });
    let off_trap = common::solve_vec(ABSTRACTED_SKELETON_SAT_BUT_UNSAT);
    let off_sat_control = common::solve_vec(GENUINELY_SAT_CONTROL);
    let off_conjunctive = common::solve_vec(CONJUNCTIVE_ONLY_UNSAT);
    drop(off_guard);

    let on_trap = common::solve_vec(ABSTRACTED_SKELETON_SAT_BUT_UNSAT);
    let on_sat_control = common::solve_vec(GENUINELY_SAT_CONTROL);
    let on_conjunctive = common::solve_vec(CONJUNCTIVE_ONLY_UNSAT);

    // SOUNDNESS, both positions. The abstraction's whole risk is that a model
    // of the over-approximation is mistaken for a model of the query; the
    // fail-closed arm at the head of `classify_quantifier_result` and the
    // publication sweep at the tail of `map_quantifier_result` are what stop
    // it, and neither is optional.
    assert!(
        !off_trap.iter().any(|r| r == "sat"),
        "switch OFF: the problem is unsatisfiable; got {off_trap:?}"
    );
    assert!(
        !on_trap.iter().any(|r| r == "sat"),
        "switch ON: an abstracted solve reaching `Sat` must publish `unknown` \
         — a model of the abstraction assigns the fresh proxy freely and says \
         nothing about the query; got {on_trap:?}"
    );
    assert!(
        !off_sat_control.iter().any(|r| r == "unsat"),
        "switch OFF: `q ≡ true` is a model; got {off_sat_control:?}"
    );
    assert!(
        !on_sat_control.iter().any(|r| r == "unsat"),
        "switch ON: restoring the goal must RELAX the ground problem, never \
         strengthen it; got {on_sat_control:?}"
    );

    // The declined family runs the identical code path in both positions, so
    // its verdict must be identical — not merely sound.
    assert_eq!(
        off_conjunctive, on_conjunctive,
        "the pass declines on an all-entailed assertion set, so both switch \
         positions must produce the same output"
    );
    assert!(
        on_conjunctive.iter().any(|r| r == "unsat"),
        "the entailed top-level universal must still be instantiated and \
         refuted; got {on_conjunctive:?}"
    );
}

/// No proxy may reach published output in either position. With the switch off
/// none is ever minted; with it on the fail-closed arm means an abstracted
/// solve publishes no model at all.
#[test]
fn no_proxy_reaches_published_output_in_either_position() {
    let with_get_model = format!("{}\n(get-model)\n", GENUINELY_SAT_CONTROL.trim_end());

    let off_guard = ay_core::misc_test_override::set(ay_core::MiscCliFlags {
        no_quantifier_proxy_abstraction: true,
        ..Default::default()
    });
    let off = common::solve_vec(&with_get_model);
    drop(off_guard);
    let on = common::solve_vec(&with_get_model);

    for (position, output) in [("off", &off), ("on", &on)] {
        for line in output {
            assert!(
                !line.contains("qproxy"),
                "switch {position}: an abstraction proxy escaped into \
                 published output: {line:?} (full output {output:?})"
            );
        }
    }
}
