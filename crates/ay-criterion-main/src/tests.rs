// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::{normalize_libtest_args, NormalizedArgs};
use std::ffi::OsString;

fn os(args: &[&str]) -> Vec<OsString> {
    args.iter().map(OsString::from).collect()
}

fn normalize(args: &[&str]) -> NormalizedArgs {
    normalize_libtest_args(os(args))
}

fn assert_forwarded(given: &[&str], forwarded: &[&str], dropped: &[&str]) {
    let normalized = normalize(given);
    assert_eq!(
        normalized.forwarded,
        os(forwarded),
        "forwarded for {given:?}"
    );
    assert_eq!(normalized.dropped, os(dropped), "dropped for {given:?}");
}

#[test]
fn the_reported_sweep_argument_is_dropped() {
    // `cargo test --all-targets -- --test-threads=1`: Criterion exited 2 on it.
    assert_forwarded(&["--test-threads=1"], &[], &["--test-threads=1"]);
    assert_forwarded(&["--test-threads", "8"], &[], &["--test-threads", "8"]);
}

#[test]
fn criterion_options_with_libtest_meaning_pass_through_untouched() {
    let criterion = [
        "--test",
        "--bench",
        "--list",
        "--ignored",
        "--exact",
        "--nocapture",
        "--show-output",
        "--quiet",
        "--color",
        "never",
        "--color=always",
        "--format",
        "terse",
        "--format=pretty",
        "--help",
        "-h",
        "incremental_bv",
    ];
    let normalized = normalize(&criterion);
    assert_eq!(normalized.forwarded, os(&criterion));
    assert!(normalized.is_identity(), "{normalized:?}");
}

#[test]
fn value_free_libtest_flags_are_dropped() {
    for flag in [
        "--exclude-should-panic",
        "--fail-fast",
        "--force-run-in-process",
        "--include-ignored",
        "--no-capture",
        "--report-time",
        "--shuffle",
    ] {
        assert_forwarded(&[flag, "routine"], &["routine"], &[flag]);
    }
}

#[test]
fn valued_libtest_options_are_dropped_in_both_spellings() {
    for (name, value) in [
        ("--test-threads", "1"),
        ("--shuffle-seed", "18446744073709551615"),
        ("--skip", "anything at all"),
        ("--logfile", "/tmp/libtest.log"),
        ("--format", "json"),
        ("--format", "junit"),
    ] {
        assert_forwarded(&[name, value], &[], &[name, value]);
        let attached = format!("{name}={value}");
        assert_forwarded(&[&attached], &[], &[&attached]);
    }
    assert_forwarded(
        &["-Z", "unstable-options"],
        &[],
        &["-Z", "unstable-options"],
    );
    assert_forwarded(&["-Zunstable-options"], &[], &["-Zunstable-options"]);
}

#[test]
fn a_skip_is_dropped_so_more_routines_run_never_fewer() {
    // Criterion 0.5 has no skip; honouring none of it can only add failures.
    assert_forwarded(
        &["--skip", "incremental_bv", "incremental_bv"],
        &["incremental_bv"],
        &["--skip", "incremental_bv"],
    );
}

#[test]
fn quiet_short_spelling_is_rewritten() {
    let normalized = normalize(&["-q", "routine"]);
    assert_eq!(normalized.forwarded, os(&["--quiet", "routine"]));
    assert!(normalized.dropped.is_empty());
    assert_eq!(
        normalized.rewritten,
        vec![(OsString::from("-q"), OsString::from("--quiet"))]
    );
    assert!(!normalized.is_identity());
}

#[test]
fn ensure_time_reaches_criterion_to_be_refused() {
    // It adds a failure condition; dropping it could turn a failure into a pass.
    assert_forwarded(&["--ensure-time"], &["--ensure-time"], &[]);
    assert!(normalize(&["--ensure-time"]).is_identity());
}

#[test]
fn values_libtest_refuses_are_forwarded_for_criterion_to_refuse() {
    for given in [
        &["--test-threads=0"][..],
        &["--test-threads", "0"],
        &["--test-threads", "-1"],
        &["--test-threads", "many"],
        &["--test-threads="],
        &["--shuffle-seed", "-1"],
        &["--shuffle-seed=seed"],
        &["-Z", "bogus"],
        &["-Zbogus"],
        &["--format", "xml"],
        &["--format=xml"],
    ] {
        let normalized = normalize(given);
        assert_eq!(normalized.forwarded, os(given), "{given:?}");
        assert!(normalized.is_identity(), "{given:?}");
    }
}

#[test]
fn a_valued_option_missing_its_value_is_forwarded() {
    for name in [
        "--test-threads",
        "--shuffle-seed",
        "--skip",
        "--logfile",
        "--format",
        "-Z",
    ] {
        assert_forwarded(&[name], &[name], &[]);
    }
}

#[test]
fn a_valued_option_consumes_the_next_token_as_libtest_does() {
    // libtest reads `--skip --test-threads=1` as a skip of that string.
    assert_forwarded(
        &["--skip", "--test-threads=1"],
        &[],
        &["--skip", "--test-threads=1"],
    );
    // An unaccepted value keeps its pairing, so the pair is refused together.
    assert_forwarded(
        &["--format", "--report-time"],
        &["--format", "--report-time"],
        &[],
    );
}

#[test]
fn nothing_after_a_bare_double_dash_is_touched() {
    assert_forwarded(
        &["--test-threads=1", "--", "--test-threads=1", "-q"],
        &["--", "--test-threads=1", "-q"],
        &["--test-threads=1"],
    );
}

#[test]
fn unknown_arguments_and_order_are_preserved() {
    assert_forwarded(
        &[
            "--bogus",
            "--report-time",
            "filter",
            "--test-threads",
            "2",
            "--exact",
        ],
        &["--bogus", "filter", "--exact"],
        &["--report-time", "--test-threads", "2"],
    );
}

#[cfg(unix)]
#[test]
fn a_non_utf8_argument_is_forwarded() {
    use std::os::unix::ffi::OsStringExt as _;
    let raw = OsString::from_vec(vec![0x66, 0xff, 0x6f]);
    let normalized = normalize_libtest_args(vec![raw.clone(), OsString::from("--shuffle")]);
    assert_eq!(normalized.forwarded, vec![raw]);
    assert_eq!(normalized.dropped, os(&["--shuffle"]));
}

#[test]
fn normalization_is_a_fixed_point_over_every_short_argument_list() {
    // `reexec_without_libtest_args` relies on this: the re-executed process must
    // find nothing left to change. Every list of up to three tokens drawn from
    // every class, including the adversarial pairings.
    let alphabet = [
        "--",
        "-q",
        "--quiet",
        "--test-threads",
        "--test-threads=1",
        "1",
        "0",
        "--skip",
        "--skip=x",
        "--format",
        "json",
        "pretty",
        "--format=junit",
        "-Z",
        "-Zunstable-options",
        "unstable-options",
        "--shuffle",
        "--shuffle-seed",
        "7",
        "--no-capture",
        "--nocapture",
        "--ensure-time",
        "--exact",
        "--list",
        "filter",
        "--logfile",
    ];
    let mut lists: Vec<Vec<&str>> = vec![Vec::new()];
    let mut frontier: Vec<Vec<&str>> = vec![Vec::new()];
    for _ in 0..3 {
        frontier = frontier
            .iter()
            .flat_map(|list| {
                alphabet.iter().map(move |token| {
                    let mut next = list.clone();
                    next.push(*token);
                    next
                })
            })
            .collect();
        lists.extend(frontier.iter().cloned());
    }
    let n = alphabet.len();
    assert_eq!(lists.len(), 1 + n + n * n + n * n * n);
    for list in &lists {
        let once = normalize(list);
        let twice = normalize_libtest_args(once.forwarded.clone());
        assert!(
            twice.is_identity(),
            "{list:?} -> {:?} -> {twice:?}",
            once.forwarded
        );
        assert_eq!(twice.forwarded, once.forwarded, "{list:?}");
    }
}

#[test]
fn the_notice_names_every_change() {
    let normalized = normalize(&["--test-threads=1", "-q", "filter"]);
    assert_eq!(
        normalized.notice("incremental_bench"),
        "incremental_bench: libtest arguments Criterion does not take: dropped \
         --test-threads=1; rewrote -q as --quiet; running Criterion with [--quiet filter]"
    );
}
