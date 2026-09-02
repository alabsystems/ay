// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Ask, for an exported native replay artifact, whether AY actually builds a
//! derivation — and if not, WHICH mechanism declined.
//!
//! Motivation. A consumer census that buckets on
//! `VerificationSummary::unsat_proof_available` cannot answer "why is there no
//! proof object", because that flag is a PRESENTATION flag: it is
//! `is_unsat() && last_proof().is_some()`, and `last_proof()` yields `None`
//! whenever proof output was not requested AT SOLVE TIME. A consumer running
//! with `set_produce_proofs(false)` therefore reads `false` for every query it
//! ever solves, whatever the proof machinery did or did not do.
//!
//! This probe separates the two by replaying the SAME artifact twice:
//!
//!   1. `replay_native_replay_artifact` — proofs NOT requested. This mirrors a
//!      consumer's long-lived incremental encoder. Expect
//!      `available=false, decline=None`: nothing was asked for, so nothing was
//!      declined. That pair is the signature of "nobody requested a proof",
//!      NOT of "AY could not build one".
//!   2. `replay_native_replay_artifact_with_checked_proof` — proofs requested
//!      and strictly checked. THIS is the run whose answer is about AY. The
//!      refusal message carries the full authority breakdown, including
//!      `proof_decline=`, and with `--probe-cert-reject` armed below the
//!      certification funnel also prints which gate refused.
//!
//! Usage:
//!   proof_decline_probe FILE.ay-native-replay.json [FILE...]
//!
//! Environment:
//!   PROBE_TIMEOUT_SECS   per-artifact strict replay bound (default 60)

use std::time::Duration;

use ay_dpll::api::{NativeReplayArtifact, Solver};

fn main() {
    let paths: Vec<String> = std::env::args().skip(1).collect();
    if paths.is_empty() {
        eprintln!("usage: proof_decline_probe FILE.ay-native-replay.json [FILE...]");
        std::process::exit(2);
    }
    let timeout = Duration::from_secs(
        std::env::var("PROBE_TIMEOUT_SECS")
            .ok()
            .and_then(|value| value.parse().ok())
            .unwrap_or(60),
    );

    // Arm the certification-rejection channel process-wide. Without this the
    // funnel records WHICH gate refused a refutation and never prints it, so a
    // library consumer sees only the opaque outcome.
    let armed = ay_core::set_global_misc_cli_flags_with(|flags| {
        flags.probe_cert_reject = true;
    });
    eprintln!("# probe_cert_reject armed = {armed}");

    for path in paths {
        let name = path.rsplit('/').next().unwrap_or(&path).to_string();
        let json = match std::fs::read_to_string(&path) {
            Ok(json) => json,
            Err(err) => {
                println!("{name}\tREAD_ERROR\t{err}");
                continue;
            }
        };
        let artifact = match NativeReplayArtifact::from_json_str(&json) {
            Ok(artifact) => artifact,
            Err(err) => {
                println!("{name}\tPARSE_ERROR\t{err}");
                continue;
            }
        };

        // Pass 1 — proofs not requested (the consumer's incremental lane).
        match Solver::replay_native_replay_artifact(&artifact) {
            Ok(details) => println!(
                "{name}\tnoproofs\tresult={:?}\tlevel={}\tavailable={}\tdecline={:?}\tunknown={:?}",
                details.result.result(),
                details.verification_level.code(),
                details.verification.unsat_proof_available,
                details.verification.unsat_proof_decline.map(|m| m.tag()),
                details.unknown_reason,
            ),
            Err(err) => println!("{name}\tnoproofs\tERROR\t{err}"),
        }

        // Pass 2 — proofs requested and strictly checked (the real question).
        match Solver::replay_native_replay_artifact_with_checked_proof(&artifact, timeout) {
            Ok((details, proof)) => println!(
                "{name}\tproofs\tresult={:?}\tsteps={:?}\tartifact={}",
                details.result.result(),
                details.statistics.get_int("proof_checker_total_steps"),
                proof.is_some(),
            ),
            Err(err) => println!("{name}\tproofs\tREFUSED\t{err}"),
        }
    }
}
