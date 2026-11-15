// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The competition fast publication (2026-09-13): the shipped SAT-COMP posture
//! seals an UNSAT proof under the digest its writer took while writing, with no
//! read-back; every other posture still reads the proof back.

use ntest::timeout;
use std::process::Command;
use std::time::Duration;

use crate::spawn::OutputTimeout;

/// The pigeonhole formula: `pigeons` pigeons, `holes` holes, one per hole.
fn pigeonhole_cnf(pigeons: usize, holes: usize) -> String {
    let var = |pigeon: usize, hole: usize| pigeon * holes + hole + 1;
    let mut clauses = Vec::new();
    for pigeon in 0..pigeons {
        let row: Vec<String> = (0..holes)
            .map(|hole| var(pigeon, hole).to_string())
            .collect();
        clauses.push(format!("{} 0", row.join(" ")));
    }
    for hole in 0..holes {
        for first in 0..pigeons {
            for second in (first + 1)..pigeons {
                clauses.push(format!("-{} -{} 0", var(first, hole), var(second, hole)));
            }
        }
    }
    format!(
        "p cnf {} {}\n{}\n",
        pigeons * holes,
        clauses.len(),
        clauses.join("\n")
    )
}

/// `sat.proof_digest_streamed` from the stats JSON line ay prints on stderr.
fn proof_digest_streamed(stderr: &str) -> Option<u64> {
    stderr
        .lines()
        .filter(|line| line.trim_start().starts_with('{'))
        .filter_map(|line| serde_json::from_str::<serde_json::Value>(line.trim()).ok())
        .find_map(|stats| stats.get("sat.proof_digest_streamed")?.as_u64())
}

/// The seal-latency lever (2026-09-13): the shipped SAT-COMP posture seals its
/// UNSAT proof under the digest its writer took while writing, with no read-
/// back, and a run outside that posture still reads the proof back.
#[test]
#[timeout(120_000)]
fn satcomp_posture_seals_its_unsat_proof_from_the_writers_digest() {
    let ay_path = env!("CARGO_BIN_EXE_ay");
    let dir = tempfile::tempdir().expect("tempdir");
    let input = dir.path().join("php-6-5.cnf");
    std::fs::write(&input, pigeonhole_cnf(6, 5)).expect("write CNF");
    for competition in [true, false] {
        let proof_path = dir.path().join(format!("proof-{competition}.pbp"));
        let mut command = Command::new(ay_path);
        command
            .args(["solve", "--sat-variant", "default", "--proof"])
            .arg(&proof_path)
            .args([
                "--proof-format",
                "veripb",
                "--proof-checker",
                "veripb",
                "--stats-json",
            ])
            .env("AY_INTERNAL_PROVENANCE_CHILD", "1")
            .env_remove("AY_SAT_MAIN_ENABLE_STARTUP_PHASE_INIT");
        if competition {
            command
                .arg("--no-verify-proof")
                .env(
                    "AY_INTERNAL_SATCOMP_WRAPPER",
                    "main-regular-default-veripb-v1",
                )
                .env("AY_SAT_COMPETITION_PROFILE", "regular")
                .env("AY_SAT_PROFILE_ID", "ay-sat-regular-main")
                .env("AY_COMPETITION_JIT_MODE", "off")
                .env("AY_SAT_VARIANT", "default");
        } else {
            command
                .env_remove("AY_INTERNAL_SATCOMP_WRAPPER")
                .env_remove("AY_SAT_COMPETITION_PROFILE")
                .env_remove("AY_SAT_PROFILE_ID")
                .env_remove("AY_COMPETITION_JIT_MODE")
                .env_remove("AY_COMPETITION");
        }
        let output = command
            .arg(&input)
            .output_timeout(Duration::from_secs(100))
            .expect("spawn ay solve");
        let stdout = String::from_utf8_lossy(&output.stdout);
        let stderr = String::from_utf8_lossy(&output.stderr);
        let status_lines: Vec<&str> = stdout
            .lines()
            .filter(|line| line.starts_with("s "))
            .collect();
        assert_eq!(
            status_lines,
            ["s UNSATISFIABLE"],
            "competition={competition}: {stderr}"
        );
        let proof = std::fs::read_to_string(&proof_path).expect("the UNSAT proof is published");
        assert!(
            proof.starts_with("pseudo-Boolean proof version 3.0\n"),
            "competition={competition}"
        );
        assert!(
            proof.trim_end().ends_with("end pseudo-Boolean proof;"),
            "competition={competition}"
        );
        assert_eq!(
            proof_digest_streamed(&stderr),
            Some(u64::from(competition)),
            "competition={competition}: stderr={stderr}"
        );
    }
}
