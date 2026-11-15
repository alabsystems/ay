// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Exact contracts for the retained18 zero-extension cases: three now use
//! standard checked derivations; the remaining fifteen keep Clean's consumer
//! rule only at their explicit identities.
//!
//! For the fifteen explicit remaining cases, pinned Carcara 9a352ee lacks
//! exactly that reading. Every
//! step that crosses the operator (`zero_extend_identity.rs`) is demoted to
//! `hole`, together with the steps the `bitblast_ashr` and divider detectors
//! name (the other two Clean-only spellings), and the document must then be
//! `holey` for pinned Carcara: every remaining step is standard Alethe it
//! checks. A reliance printed anywhere else, such as a `cong` across the
//! operator, leaves a step it refuses, and the verdict is `invalid`.
//!
//! The inputs: AY's conformance problems for the spelling
//! (`CleanOnlySpelling::ZeroExtendAsConcat.conformance_problems()`) and the
//! 14 external-codegen queries whose certificates kept the spelling when measured on
//! 2026-09-30 (`fixtures/external_codegen_consumer_certificates/`), each run with
//! external-codegen's argv. MEASURED before the complete bit-blast lane printed the
//! identity (2026-09-30): the 8 rows of that lane answered `invalid` at
//! `t1.cbb*.cg` under this demotion. Without pinned Carcara (`CARCARA_PATH`,
//! or `carcara` on `PATH`) the replays are skipped with a note, and the
//! in-repository checks still run; `scripts/land.sh`'s `alethe-dialect` gate
//! requires the checker.

use std::collections::HashSet;
use std::path::PathBuf;
use std::process::Command;

use crate::alethe_dialect_disclosure::{pinned_carcara_verdict, require_pinned_carcara_valid};
use crate::external_codegen_consumer_certificates::consumer_rules::{
    pinned_refused_ashr_steps, pinned_refused_divider_steps, pinned_refused_zero_extend_steps,
    zero_extend_identity_defects,
};
use crate::spawn::OutputTimeout;
use crate::strict_certificate_publication::{verdict_lines, without_script_timeout, QUERY_TIMEOUT};

/// external-codegen queries whose certificates kept the `zero_extend` spelling.
const FIXTURES: [&str; 14] = [
    "09059919a891",
    "0c91223861b2",
    "2438ac420e4d",
    "2d494502324b",
    "3605fa09f750",
    "4951160b6f7f",
    "69d10b9ab8e3",
    "737444dad611",
    "79e8748fb94e",
    "7ca8a6627cf4",
    "978dcd204719",
    "9a556d7b3408",
    "c1af6609fba6",
    "d27d9c2d0fd9",
];

#[derive(Clone, Copy)]
enum ExpectedReplay {
    Standard,
    CleanOnly,
}

fn expected_replay(name: &str) -> ExpectedReplay {
    match name {
        "conformance-1" | "conformance-3" | "09059919a891" => ExpectedReplay::Standard,
        "conformance-0" | "conformance-2" | "0c91223861b2" | "2438ac420e4d" | "2d494502324b"
        | "3605fa09f750" | "4951160b6f7f" | "69d10b9ab8e3" | "737444dad611" | "79e8748fb94e"
        | "7ca8a6627cf4" | "978dcd204719" | "9a556d7b3408" | "c1af6609fba6" | "d27d9c2d0fd9" => {
            ExpectedReplay::CleanOnly
        }
        _ => panic!("unclassified zero-extension case: {name}"),
    }
}

fn queries() -> Vec<(String, String)> {
    let dir = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("tests/group_soundness/fixtures/external_codegen_consumer_certificates");
    let conformance = ay_proof::CleanOnlySpelling::ZeroExtendAsConcat
        .conformance_problems()
        .iter()
        .enumerate()
        .map(|(index, problem)| (format!("conformance-{index}"), (*problem).to_string()));
    let fixtures = FIXTURES.iter().map(|id| {
        let script = std::fs::read_to_string(dir.join(format!("{id}.smt2")))
            .unwrap_or_else(|e| panic!("read {id}.smt2: {e}"));
        ((*id).to_string(), without_script_timeout(&script))
    });
    conformance.chain(fixtures).collect()
}

/// external-codegen's one-shot argv; the query and the certificate it wrote.
fn certify(dir: &std::path::Path, name: &str, script: &str) -> (PathBuf, String, String) {
    let problem = dir.join(format!("{name}.smt2"));
    let proof = dir.join(format!("{name}.alethe"));
    std::fs::write(&problem, script).expect("write query");
    let output = Command::new(env!("CARGO_BIN_EXE_ay"))
        .arg("-smt2")
        .arg(&problem)
        .arg("--strict-proofs")
        .arg("--proof")
        .arg(&proof)
        .args(["--proof-format", "alethe"])
        .output_timeout(QUERY_TIMEOUT)
        .expect("ay answers");
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert_eq!(
        verdict_lines(&stdout),
        ["unsat"],
        "{name}: {stdout}\n{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let stderr = String::from_utf8_lossy(&output.stderr);
    let reports: Vec<_> = stderr
        .lines()
        .filter(|line| line.starts_with("c ay.proof.certificate "))
        .collect();
    assert_eq!(reports.len(), 1, "{name}: {stderr}");
    assert!(
        reports[0].contains(" unproved_steps=0 ") && reports[0].contains(" trust_free=yes "),
        "{name}: {}",
        reports[0]
    );
    let certificate = std::fs::read_to_string(&proof).expect("the certificate was written");
    assert!(!certificate.contains(":rule hole") && !certificate.contains(":rule trust"));
    (problem, certificate, reports[0].to_string())
}

/// `proof` with the named steps' rules replaced by `hole`.
fn demote(proof: &str, steps: &HashSet<String>) -> (String, usize) {
    let mut demoted = 0;
    let text = proof
        .lines()
        .map(|line| {
            let id = line
                .strip_prefix("(step ")
                .and_then(|rest| rest.split_whitespace().next());
            match (id, line.rfind(" :rule ")) {
                (Some(id), Some(at)) if steps.contains(id) => {
                    demoted += 1;
                    let rest = &line[at + " :rule ".len()..];
                    let end = rest
                        .find(|c: char| c.is_whitespace() || c == ')')
                        .unwrap_or(rest.len());
                    format!("{} :rule hole{}", &line[..at], &rest[end..])
                }
                _ => line.to_string(),
            }
        })
        .collect::<Vec<_>>()
        .join("\n");
    (text + "\n", demoted)
}

#[test]
fn zero_extend_standard_cases_are_valid_and_remaining_reliance_is_only_at_identities() {
    let dir = tempfile::tempdir().expect("tempdir");
    let mut replayed = 0;
    let mut standard_replayed = 0;
    let mut failures = Vec::new();
    let cases = queries();
    assert_eq!(cases.len(), 18);
    let names: HashSet<_> = cases.iter().map(|(name, _)| name.as_str()).collect();
    assert_eq!(names.len(), 18, "each original case occurs exactly once");
    assert_eq!(
        cases
            .iter()
            .filter(|(name, _)| matches!(expected_replay(name), ExpectedReplay::Standard))
            .count(),
        3
    );
    for (name, script) in cases {
        let (problem, proof, report) = certify(dir.path(), &name, &script);
        let defects = zero_extend_identity_defects(&proof);
        if !defects.is_empty() {
            failures.push(format!("{name}: {defects:?}"));
            continue;
        }
        let identities = pinned_refused_zero_extend_steps(&proof);
        if matches!(expected_replay(&name), ExpectedReplay::Standard) {
            assert!(
                report.contains(" carcara_surface=supported "),
                "{name}: {report}"
            );
            assert!(
                identities.is_empty(),
                "{name}: unexpected consumer identity"
            );
            assert!(
                pinned_refused_ashr_steps(&proof).is_empty(),
                "{name}: unexpected Clean ashr layer"
            );
            assert!(
                pinned_refused_divider_steps(&proof).is_empty(),
                "{name}: unexpected Clean divider"
            );
            assert!(!proof.contains(":rule hole") && !proof.contains(":rule trust"));
            let path = dir.path().join(format!("{name}.alethe"));
            require_pinned_carcara_valid(&problem, &path);
            standard_replayed += 1;
            continue;
        }
        assert!(
            report.contains(" carcara_surface=clean-dialect "),
            "{name}: {report}"
        );
        if identities.is_empty() {
            failures.push(format!("{name}: no zero_extend identity step was printed"));
            continue;
        }
        let steps: HashSet<String> = identities
            .into_iter()
            .chain(pinned_refused_ashr_steps(&proof))
            .chain(pinned_refused_divider_steps(&proof))
            .collect();
        let (demoted, count) = demote(&proof, &steps);
        assert_eq!(
            count,
            steps.len(),
            "{name}: every named step is demoted once"
        );
        let path = dir.path().join(format!("{name}.demoted.alethe"));
        std::fs::write(&path, &demoted).expect("write the demoted certificate");
        if let Some((verdict, stderr)) = pinned_carcara_verdict(&problem, &path) {
            replayed += 1;
            if verdict != "holey" {
                failures.push(format!(
                    "{name}: with {count} identity/ashr/divider steps demoted, pinned \
                     Carcara answered `{verdict}`, not `holey`: {stderr}"
                ));
            }
        }
    }
    eprintln!(
        "zero_extend reliance: {replayed} demoted and {standard_replayed} standard certificates replayed through pinned Carcara"
    );
    assert!(failures.is_empty(), "{}", failures.join("\n\n"));
}

#[test]
fn zero_extend_reliance_demotion_rewrites_only_the_named_rules() {
    let proof = "(step a (cl (= x x)) :rule refl)\n\
                 (step ab (cl (= y y)) :rule refl)\n\
                 (step c (cl (= z z)) :rule trans :premises (a ab))\n";
    let steps: HashSet<String> = ["a", "c"].iter().map(|s| (*s).to_string()).collect();
    let (demoted, count) = demote(proof, &steps);
    assert_eq!(count, 2);
    assert_eq!(
        demoted,
        "(step a (cl (= x x)) :rule hole)\n\
         (step ab (cl (= y y)) :rule refl)\n\
         (step c (cl (= z z)) :rule hole :premises (a ab))\n"
    );
}
