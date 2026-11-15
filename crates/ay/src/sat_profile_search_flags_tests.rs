// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The SAT profile matrix's `search_flags` parse as `ay solve` flags.
//!
//! `competition/sat_profile_matrix.json` gives a profile the search
//! configuration its claimed results were measured with, as `ay solve` argv
//! tokens in order. The SAT-COMP 2026 runner built from the matrix appends them
//! to its default solve; the probe and R500 slices run as measured, without.
//! The R500 slice's own argv (no search flags, its tail) is parsed too.
//! The tool that writes that runner checks only the tokens' shape (an option,
//! or a plain value after one), so these tests put the runner's argv through
//! the compiled parser. A flag renamed or removed, a switch the list gives a
//! value, a valued flag it gives none, or a value of the wrong type fails here,
//! instead of making each of those solves exit 2 at argument parsing while the
//! probe slice alone answers.

use super::Cli;
use clap::parser::ValueSource;
use clap::CommandFactory;

const MATRIX: &str = concat!(
    env!("CARGO_MANIFEST_DIR"),
    "/../../competition/sat_profile_matrix.json"
);

/// The flag the runner passes for a profile lever set to "1" (`profile_levers`).
const LEVER_FLAGS: [(&str, &str); 3] = [
    (
        "bcp_learned_1963_blocker_cert_elision",
        "--sat-bcp-learned-1963-blocker-cert-elision",
    ),
    (
        "bcp_learned_1963_blocker_cert_false_reject_demote",
        "--sat-bcp-learned-1963-blocker-cert-false-reject-demote",
    ),
    (
        "dense_clique_php_proof_route",
        "--sat-dense-clique-php-proof-route",
    ),
];

/// The R500 slice's own tail; the default solve has none, and the R500 slice
/// carries no search flags.
const R500_SLICE: [&str; 2] = ["--sat-reduce-low-permille", "500"];

struct Profile {
    id: String,
    levers: Vec<&'static str>,
    proof_format: String,
    proof_checker: String,
    search_flags: Vec<String>,
}

fn text(value: &serde_json::Value, what: &str) -> String {
    value
        .as_str()
        .unwrap_or_else(|| panic!("{what} must be a string, got {value}"))
        .to_string()
}

/// Every matrix profile that carries `search_flags`.
fn profiles_with_search_flags() -> Vec<Profile> {
    let raw = std::fs::read_to_string(MATRIX).unwrap_or_else(|e| panic!("read {MATRIX}: {e}"));
    let matrix: serde_json::Value = serde_json::from_str(&raw).expect("the matrix is JSON");
    let profiles = matrix["profiles"].as_array().expect("matrix profiles");
    let mut found = Vec::new();
    for profile in profiles {
        let Some(search) = profile.get("search_flags") else {
            continue;
        };
        let id = text(&profile["id"], "a profile id");
        let tokens = search
            .as_array()
            .unwrap_or_else(|| panic!("{id}: search_flags must be a list"));
        let unsat_proof = &profile["requirements"]["unsat_proof"];
        found.push(Profile {
            levers: LEVER_FLAGS
                .iter()
                .filter(|(key, _)| profile["profile_levers"][*key].as_str() == Some("1"))
                .map(|(_, flag)| *flag)
                .collect(),
            proof_format: text(&unsat_proof["format"], "unsat_proof.format"),
            proof_checker: text(&unsat_proof["checker"], "unsat_proof.checker"),
            search_flags: tokens
                .iter()
                .map(|token| text(token, "a search_flags token"))
                .collect(),
            id,
        });
    }
    found
}

/// The argv run.sh gives a non-probe solve: its fixed flags, the profile's
/// levers and proof surface, the per-solve timeout, the search flags, the
/// slice's own tail, then the instance.
fn solve_argv(profile: &Profile, slice: &[&str]) -> Vec<String> {
    let mut argv: Vec<String> = ["ay", "solve", "--sat-variant", "default"]
        .iter()
        .chain(&["--memory-ceiling-bytes", "32000000000"])
        .map(|s| (*s).to_string())
        .collect();
    argv.extend(profile.levers.iter().map(|flag| (*flag).to_string()));
    argv.extend(
        [
            "--proof",
            "out/proof.out",
            "--proof-format",
            profile.proof_format.as_str(),
            "--proof-checker",
            profile.proof_checker.as_str(),
            "--no-verify-proof",
            "--timeout=60000",
        ]
        .map(String::from),
    );
    argv.extend(profile.search_flags.iter().cloned());
    argv.extend(slice.iter().map(|s| (*s).to_string()));
    argv.push("instance.cnf".to_string());
    argv
}

fn raw_values(solve: &clap::ArgMatches, id: &str) -> Vec<String> {
    solve
        .get_raw(id)
        .map(|values| values.map(|v| v.to_string_lossy().into_owned()).collect())
        .unwrap_or_default()
}

/// Parse a solve's argv with the compiled parser and check that every search
/// flag reached it as the list spells it: a switch alone, a valued flag with
/// exactly the value after it, and the slice's tail and the instance intact.
fn parse_search_flags(profile: &Profile, slice: &[&str]) -> Result<(), String> {
    let argv = solve_argv(profile, slice);
    let matches = Cli::command()
        .try_get_matches_from(&argv)
        .map_err(|e| format!("{}: ay solve rejects {argv:?}:\n{e}", profile.id))?;
    let solve = matches
        .subcommand_matches("solve")
        .ok_or("the argv did not parse as a solve")?;
    let command = Cli::command();
    let solve_command = command.find_subcommand("solve").expect("a solve command");
    let flags = &profile.search_flags;
    let mut at = 0;
    while at < flags.len() {
        let option = &flags[at];
        let long = option
            .strip_prefix("--")
            .ok_or_else(|| format!("token {at} {option:?} is a value where an option belongs"))?;
        let arg = solve_command
            .get_arguments()
            .find(|arg| arg.get_long() == Some(long))
            .ok_or_else(|| format!("{option} is not an ay solve flag"))?;
        let id = arg.get_id().as_str();
        if solve.value_source(id) != Some(ValueSource::CommandLine) {
            return Err(format!(
                "{option} did not reach the parser from the command line"
            ));
        }
        let next = flags.get(at + 1).filter(|token| !token.starts_with("--"));
        if arg.get_action().takes_values() {
            let value =
                next.ok_or_else(|| format!("{option} takes a value; the list gives none"))?;
            if raw_values(solve, id) != [value.clone()] {
                return Err(format!(
                    "{option} parsed as {:?}, not [{value:?}]",
                    raw_values(solve, id)
                ));
            }
            at += 2;
        } else if let Some(value) = next {
            return Err(format!(
                "{option} is a switch; the list gives it the value {value:?}"
            ));
        } else {
            at += 1;
        }
    }
    if raw_values(solve, "file") != ["instance.cnf"] {
        return Err(format!(
            "the instance parsed as {:?}",
            raw_values(solve, "file")
        ));
    }
    let reduce_low = raw_values(solve, "sat_reduce_low_permille");
    let slice_value: Vec<String> = slice.get(1).map(|v| (*v).to_string()).into_iter().collect();
    if reduce_low != slice_value {
        return Err(format!(
            "--sat-reduce-low-permille parsed as {reduce_low:?}"
        ));
    }
    Ok(())
}

#[test]
fn every_profile_search_flag_parses_on_the_default_solve_and_the_r500_slice() {
    // Retain the parser API's legacy combination, not the shipped schedule:
    // DR-13 now correctly gives R500 no search flags. The separate upstream
    // test below checks those actual scheduled argv; both contracts matter.
    let profiles = profiles_with_search_flags();
    assert!(
        !profiles.is_empty(),
        "no matrix profile carries search_flags, so this test checks nothing; \
         delete it if that is intended"
    );
    for profile in &profiles {
        for slice in [&[][..], &R500_SLICE[..]] {
            if let Err(error) = parse_search_flags(profile, slice) {
                panic!("profile {} ({slice:?}): {error}", profile.id);
            }
        }
    }
}

#[test]
fn every_profile_search_flag_parses_on_the_default_solve_and_the_r500_slice_parses() {
    let profiles = profiles_with_search_flags();
    assert!(
        !profiles.is_empty(),
        "no matrix profile carries search_flags, so this test checks nothing; \
         delete it if that is intended"
    );
    for profile in &profiles {
        if let Err(error) = parse_search_flags(profile, &[]) {
            panic!("profile {} (default solve): {error}", profile.id);
        }
        let r500 = Profile {
            id: profile.id.clone(),
            levers: profile.levers.clone(),
            proof_format: profile.proof_format.clone(),
            proof_checker: profile.proof_checker.clone(),
            search_flags: Vec::new(),
        };
        if let Err(error) = parse_search_flags(&r500, &R500_SLICE) {
            panic!("profile {} (R500 slice): {error}", profile.id);
        }
    }
}

#[test]
fn the_search_flag_check_refuses_lists_ay_would_reject() {
    let shipped = profiles_with_search_flags()
        .into_iter()
        .next()
        .expect("a profile with search_flags");
    let cases: [(&str, &[&str]); 7] = [
        ("an unknown flag", &["--sat-no-such-flag", "true"]),
        ("a valued flag with no value", &["--sat-stable-lock-at"]),
        (
            "a valued flag missing its value mid-list",
            &["--sat-stable-lock-at", "--sat-stable-ema", "false"],
        ),
        ("a switch given a value", &["--no-cold-restart", "true"]),
        (
            "a value of the wrong type",
            &["--sat-stable-lock-at", "true"],
        ),
        (
            "a bool flag given a non-bool",
            &["--sat-stable-ema", "maybe"],
        ),
        (
            "a flag given twice",
            &["--sat-stable-ema", "false", "--sat-stable-ema", "true"],
        ),
    ];
    for (label, flags) in cases {
        let profile = Profile {
            id: label.to_string(),
            search_flags: flags.iter().map(|s| (*s).to_string()).collect(),
            levers: shipped.levers.clone(),
            proof_format: shipped.proof_format.clone(),
            proof_checker: shipped.proof_checker.clone(),
        };
        assert!(
            parse_search_flags(&profile, &[]).is_err(),
            "{label} passed the check"
        );
    }
}
