// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Exact R24 input from model-checker-consumer's October 1 default-proof slowdown report.
//! This asserts one ordinary BMC CLI verdict within its original 30-second
//! request budget, not portable proof replay or all 38 consumer obligations.

use std::io::{Read, Seek, SeekFrom};
use std::path::Path;
use std::process::Command;

#[test]
fn original_walker_unsat_default_proof_within_thirty_seconds() {
    let tests = Path::new(env!("CARGO_MANIFEST_DIR")).join("tests");
    // The shared Python guard supplies authenticated process-tree cleanup and
    // bounded, complete capture; OutputTimeout alone supplies neither the RSS
    // envelope nor complete descendant cleanup. Admission is scheduling, before
    // the sole request deadline. The helper never renews that deadline.
    // Its file-size cap must apply to fresh owned captures, not the landing
    // parent's append-only log, which can already exceed that cap. Keep the
    // descriptors until the helper has settled and replay their bounded bytes
    // from this uncapped parent, including diagnostics on failure.
    let mut stdout = tempfile::tempfile().expect("retain helper stdout");
    let mut stderr = tempfile::tempfile().expect("retain helper stderr");
    let status = Command::new("python3")
        .arg("-B")
        .arg(tests.join("common/model_checker_consumer_default_proof.py"))
        .arg(env!("CARGO_BIN_EXE_ay"))
        .arg(tests.join("group_soundness/fixtures/model_checker_consumer_bmc_walker_original.smt2"))
        .stdout(stdout.try_clone().expect("lend helper stdout"))
        .stderr(stderr.try_clone().expect("lend helper stderr"))
        .status()
        .expect("start resource-owned default-proof regression");
    const CAPTURE_BYTES: u64 = 16 * 1024 * 1024;
    let captured = |file: &mut std::fs::File| {
        file.seek(SeekFrom::Start(0))
            .expect("rewind helper capture");
        let mut bytes = Vec::new();
        file.take(CAPTURE_BYTES + 1)
            .read_to_end(&mut bytes)
            .expect("read settled helper capture");
        assert!(
            bytes.len() as u64 <= CAPTURE_BYTES,
            "oversized helper capture"
        );
        String::from_utf8(bytes).expect("lossless helper diagnostics")
    };
    print!("{}", captured(&mut stdout));
    eprint!("{}", captured(&mut stderr));
    assert!(
        status.success(),
        "original R24 default-proof regression: {status}"
    );
}
