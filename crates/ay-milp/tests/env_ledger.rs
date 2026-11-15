// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The env-var ledger's own invariants and the audit that reads it.
//!
//! `ay-milp knobs --list` and the unknown-name audit both read `knobs.rs`'s
//! ledger. These tests check the audit's behaviour and the ledger's data; the
//! repository-wide quality gate tracks which environment names exist.

use ay_test_support::env::with_env_edits;
use std::collections::BTreeSet;

#[path = "env_ledger/audit_policy.rs"]
mod audit_policy;
#[path = "env_ledger/census_history.rs"]
mod census_history;

use census_history::assert_census_matches_survey;

/// Names listed in `tests/retired_env_names.txt`: knobs this crate retired.
fn retired_in_comments() -> BTreeSet<&'static str> {
    include_str!("retired_env_names.txt")
        .lines()
        .map(str::trim)
        .filter(|l| !l.is_empty() && !l.starts_with('#'))
        .collect()
}

#[test]
fn the_census_matches_the_survey() {
    // Regression guard on the two numbers the debt triage rests on: if either
    // moves, the chronology in `env_ledger/census_history.md` needs re-reading.
    let total = ay_milp::KNOBS.len();
    let dead = ay_milp::KNOBS
        .iter()
        .filter(|k| k.bucket == ay_milp::Bucket::Dead)
        .count();
    assert_census_matches_survey(total, dead);
}

#[test]
fn kill_switches_are_never_marked_deprecated() {
    // `AY_MILP_NO_*` is the A/B mechanism every measured result in the journal
    // rests on. Collapsing it into a flag is fine; retiring the NAMES is not.
    for d in ay_milp::DEPRECATED {
        let k = ay_milp::KNOBS
            .iter()
            .find(|k| k.name == d.env)
            .expect("deprecation names a ledger entry");
        assert_ne!(
            k.bucket,
            ay_milp::Bucket::KillSwitch,
            "{} is a kill switch and must not be deprecated",
            d.env
        );
    }
}

#[test]
fn env_audit_flags_an_unknown_name() {
    // The audit is a pure function of the process environment, so this test
    // sets one through the shared, restore-on-unwind environment boundary.
    let name = "AY_MILP_LEDGER_TEST_TYPO_DO_NOT_ADD";
    let audit = with_env_edits(|env| {
        env.set(name, "1");
        ay_milp::env_audit()
    });
    assert!(
        audit.unknown.iter().any(|n| n == name),
        "a name outside the ledger must be reported: {:?}",
        audit.unknown
    );
}

/// A RETIRED KNOB MAY NEVER BE LAUNDERED THROUGH THE TOOLING INVENTORY.
///
/// `tooling_env_names.txt` lists the `AY_*` names this repository's own tooling
/// owns, and the audit stops reporting every name on it. A retired knob of this
/// crate's is a recipe that outlived its knob, and the audit must go on
/// reporting it, so none may appear there.
///
/// The inventory itself is DERIVED from the tooling, in both directions, by
/// `env_ledger_tooling.rs`. That is a separate test target because it reads the
/// development tree's tooling roots, and the public snapshot ships only part of
/// them (publish/manifest.txt excludes that target with them).
#[test]
fn tooling_inventory_never_launders_a_retired_knob() {
    let retired: Vec<&str> = ay_milp::tooling_env_names()
        .filter(|name| retired_in_comments().contains(name))
        .collect();
    assert!(
        retired.is_empty(),
        "these names are RETIRED knobs of this crate and must keep failing the audit, \
         not be excluded from it: {retired:?}"
    );
}

/// AN INHERITED TOOLING NAME MUST NOT STOP THE RUN.
///
/// The negative half of `env_audit_flags_an_unknown_name`: the guard keeps
/// firing on a name nothing owns, and stops firing on one the repository does.
/// The name is taken FROM the inventory rather than spelled here, so this test
/// cannot drift from it and no `AY_*` literal is added to the crate.
#[test]
fn a_name_this_repository_owns_elsewhere_does_not_stop_the_run() {
    let name = ay_milp::tooling_env_names()
        .next()
        .expect("the tooling inventory is not empty");
    let audit = with_env_edits(|env| {
        env.set(name, "1");
        ay_milp::env_audit()
    });
    assert!(
        !audit.unknown.iter().any(|n| n == name),
        "{name} is owned by this repository's tooling and must not be reported as a name \
         nothing reads: {:?}",
        audit.unknown
    );
    assert!(
        !audit.dead.iter().any(|n| n == name),
        "{name} is not a dead knob of this crate: {:?}",
        audit.dead
    );
}

/// Every `AY_*` in `knobs::ZERO_IGNORED` must be a real ledger entry.
#[test]
fn zero_ignored_names_are_in_the_ledger() {
    for z in ay_milp::ZERO_IGNORED {
        assert!(
            ay_milp::KNOBS.iter().any(|k| k.name == z.env),
            "{} is in ZERO_IGNORED but not in the ledger",
            z.env
        );
        assert!(
            !z.zero_would_mean.is_empty(),
            "{} needs a note saying what an operator would expect 0 to mean",
            z.env
        );
    }
}
