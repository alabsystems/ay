// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use sha2::{Digest, Sha256};
use std::time::{Duration, Instant};

const ORIGINAL: &str = include_str!("fixtures/model_checker_consumer_test6_all.smt2");
const SHA256: &str = "1bb78d1891042eaaf6beae33ef9d7b4f7cf18680667fc81bbc3475d0d5abe68e";

fn original(logic: Option<&str>) {
    // This standalone diagnostic uses its own 15-second owner, including
    // hash/parse/solve/model admission and cleanup. It does not qualify the
    // separate 15-second BMC harness. The outer timeout detects hung tests.
    let started = Instant::now();
    let grant = Duration::from_secs(15);
    assert_eq!(ORIGINAL.len(), 27_012);
    assert_eq!(format!("{:x}", Sha256::digest(ORIGINAL.as_bytes())), SHA256);
    let query = match logic {
        None => ORIGINAL.to_string(),
        Some(logic) => {
            assert_eq!(ORIGINAL.matches("(set-logic ALL)").count(), 1);
            ORIGINAL.replacen("(set-logic ALL)", &format!("(set-logic {logic})"), 1)
        }
    };
    if logic == Some("QF_AUFBV") {
        assert_eq!(query.len(), 27_017);
        assert_eq!(
            format!("{:x}", Sha256::digest(query.as_bytes())),
            "bf10e081313e27b718cc0884792a89c3b582282959445d61b3c1d1d5ec1fa32b"
        );
    }
    let commands = parse(&query).unwrap();
    let mut executor = Executor::new();
    executor.set_solve_controls(None, Some(started + grant));
    let remaining = grant
        .checked_sub(started.elapsed())
        .expect("original allowance remains");
    assert!(!remaining.is_zero());
    executor.set_timeout(Some(remaining));
    let output = executor.execute_all(&commands).unwrap();
    assert_eq!(output, ["sat"], "logic={logic:?}");
    assert!(
        executor.was_model_validated(),
        "must validate the original assertions"
    );
    assert!(executor.last_model.is_some());
    drop(output);
    drop(executor);
    drop(commands);
    drop(query);
    assert!(
        started.elapsed() < grant,
        "original 15-second owner exhausted"
    );
}

#[test]
#[ntest::timeout(30_000)]
fn unchanged_model_checker_consumer_test6_all_is_sat_with_a_validated_original_model() {
    original(None);
}

#[test]
#[ntest::timeout(30_000)]
fn unchanged_test6_old_logic_control_retains_a_validated_model() {
    original(Some("QF_AUFBV"));
}

#[test]
#[ntest::timeout(30_000)]
fn original_test6_qf_fp_logic_control() {
    original(Some("QF_FP"));
}

#[test]
#[ntest::timeout(30_000)]
fn original_test6_qf_bvfp_logic_control() {
    original(Some("QF_BVFP"));
}

#[test]
#[ntest::timeout(30_000)]
fn original_test6_qf_abvfp_logic_control() {
    original(Some("QF_ABVFP"));
}
