// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The SAT-COMP 2026 memory ceiling of the `ay submission generate sat`
//! runner (2026-09-12): ay must get the memory the rules allow on every
//! platform, read conservatively and never looser than a limit the kernel
//! shows, never a default sized from the node's RAM.

use super::*;

fn repo_file(relative: &str) -> String {
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    fs::read_to_string(root.join(relative)).unwrap_or_else(|err| panic!("read {relative}: {err}"))
}

/// One number across the tree: this constant, the limit file every SAT-COMP
/// shell launcher sources, and the SAT profile matrix's contract.
#[test]
fn sat_comp_memory_limit_matches_the_limit_file_and_the_matrix() {
    let from_file: u64 = repo_file("competition/sat26_memory_limit.sh")
        .lines()
        .find_map(|line| line.strip_prefix("SAT26_MEMORY_LIMIT_BYTES="))
        .expect("competition/sat26_memory_limit.sh sets SAT26_MEMORY_LIMIT_BYTES")
        .trim()
        .parse()
        .expect("SAT26_MEMORY_LIMIT_BYTES is an integer");
    assert_eq!(from_file, SAT_COMP_2026_MEMORY_LIMIT_BYTES);

    let matrix: serde_json::Value =
        serde_json::from_str(&repo_file("competition/sat_profile_matrix.json"))
            .expect("SAT profile matrix is JSON");
    let contract_gb = matrix["sat26_compliance"]["main_track_contract"]["memory_limit_gb"]
        .as_u64()
        .expect("main_track_contract.memory_limit_gb");
    // "32GB" read conservatively as decimal gigabytes.
    assert_eq!(
        contract_gb * 1_000_000_000,
        SAT_COMP_2026_MEMORY_LIMIT_BYTES
    );
}

/// Run the generated runner against a fake `ay` that records its argv and
/// environment: `--memory-ceiling-bytes` must carry the limit with no
/// `--memory` override, `GOVERN_AY_MB` the limit rounded up to MiB, and the
/// inherited govern markers must be scrubbed so ay re-arms. Fails if a
/// generated runner omits any part of the pin.
#[cfg(unix)]
#[test]
fn generated_sat_runner_pins_both_memory_bounds() {
    use std::os::unix::fs::PermissionsExt;

    let dir = tempfile::tempdir().expect("tempdir");
    generate_sat(dir.path()).expect("generate SAT skeleton");
    let run_sh = fs::read_to_string(dir.path().join("run.sh")).expect("read run.sh");
    assert!(
        !run_sh.contains(SAT_COMP_MEMORY_LIMIT_PLACEHOLDER),
        "the limit placeholder must be substituted"
    );

    let record = dir.path().join("record.txt");
    let fake_ay = dir.path().join("ay");
    let armed = ay_sys::govern::ARMED_ENV;
    let (peers, harness) = (ay_sys::CONCURRENCY_ENV, ay_sys::TEST_HARNESS_ENV);
    fs::write(
        &fake_ay,
        format!(
            "#!/usr/bin/env bash\nprintf 'GOVERN_AY_MB=%s\\n' \"${{GOVERN_AY_MB-unset}}\" >\"$PIN_RECORD\"\n\
             printf '{armed}=%s\\n' \"${{{armed}-unset}}\" >>\"$PIN_RECORD\"\n\
             printf 'peers=%s\\n' \"${{{peers}-unset}}/${{NEXTEST-unset}}/${{NEXTEST_EXECUTION_MODE-unset}}/${{{harness}-unset}}\" >>\"$PIN_RECORD\"\n\
             printf '%s\\n' \"$@\" >>\"$PIN_RECORD\"\nprintf 's UNKNOWN\\n'\n"
        ),
    )
    .expect("write fake ay");
    fs::set_permissions(&fake_ay, fs::Permissions::from_mode(0o755)).expect("chmod fake ay");
    let cnf = dir.path().join("tiny.cnf");
    fs::write(&cnf, "p cnf 1 1\n1 0\n").expect("write CNF");

    let status = Command::new("bash")
        .arg(dir.path().join("run.sh"))
        .arg(&cnf)
        .arg(dir.path().join("proof"))
        .env("PIN_RECORD", &record)
        .env("GOVERN_AY_MB", "1")
        .env(armed, "1")
        .env(peers, "7")
        .env("NEXTEST", "1")
        .env("NEXTEST_EXECUTION_MODE", "process-per-test")
        .env(harness, "1")
        .status()
        .expect("run generated run.sh");
    assert!(status.success(), "generated run.sh exited {status}");

    let recorded = fs::read_to_string(&record).expect("read record");
    let mut lines = recorded.lines();
    let limit = SAT_COMP_2026_MEMORY_LIMIT_BYTES.to_string();
    let govern_mb = SAT_COMP_2026_MEMORY_LIMIT_BYTES.div_ceil(1024 * 1024);
    assert_eq!(
        lines.next(),
        Some(format!("GOVERN_AY_MB={govern_mb}").as_str()),
        "GOVERN_AY_MB must be the limit rounded up to MiB, overriding an inherited value"
    );
    assert_eq!(
        lines.next(),
        Some(format!("{armed}=unset").as_str()),
        "the inherited govern marker must be scrubbed so ay re-arms"
    );
    assert_eq!(
        lines.next(),
        Some("peers=unset/unset/unset/unset"),
        "an inherited peer count or test-harness marker would split the ceiling"
    );
    let argv: Vec<&str> = lines.collect();
    let flag_values = |flag: &str| -> Vec<&str> {
        argv.windows(2)
            .filter(|pair| pair[0] == flag)
            .map(|pair| pair[1])
            .collect()
    };
    assert_eq!(
        flag_values("--memory-ceiling-bytes"),
        [limit.as_str()],
        "argv: {argv:?}"
    );
    assert!(flag_values("--memory").is_empty(), "no override: {argv:?}");
}
