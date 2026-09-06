// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Staging-file hygiene across an abnormal exit (#68).
//!
//! An unsealed DIMACS proof lives in `.ay-dimacs-proof-<pid>-<nonce>.stage`
//! beside its target until publication renames it onto that target. Nothing
//! unlinked that file when the process left through `process::exit`, which is
//! how every timeout, termination and fatal error ends an `ay` run: a sweep of
//! this repository's benchmark tree on 2026-08-27 found 86 stranded stages
//! holding 40.1 GB, the oldest from 7 August, several of them inside the shared
//! CNF corpus.
//!
//! The two cases below pin both halves of the fix at the process level: an
//! abandoned stage does not survive the exit, and a proof that WAS published
//! survives it untouched.

#[cfg(unix)]
mod unix_tests {
    use ntest::timeout;
    use std::io::{BufWriter, Write};
    use std::path::{Path, PathBuf};
    use std::process::{Command, Stdio};
    use std::time::{Duration, Instant};
    use wait_timeout::ChildExt;

    const STAGING_PREFIX: &str = ".ay-dimacs-proof-";

    fn staging_files(dir: &Path) -> Vec<PathBuf> {
        let Ok(entries) = std::fs::read_dir(dir) else {
            return Vec::new();
        };
        entries
            .flatten()
            .map(|entry| entry.path())
            .filter(|path| {
                path.extension()
                    .is_some_and(|extension| extension == "stage")
                    && path
                        .file_name()
                        .and_then(|name| name.to_str())
                        .is_some_and(|name| name.starts_with(STAGING_PREFIX))
            })
            .collect()
    }

    /// Write a CNF large enough that parsing it outlasts the two-second grace
    /// the SIGTERM poller allows before it hard-exits.
    ///
    /// The size is what makes the case reach the destructor-skipping exit: the
    /// solver is still inside the parser when the signal lands, never reaches a
    /// cancellation checkpoint, and therefore never runs the cooperative
    /// shutdown that would have discarded the proof itself. On a machine fast
    /// enough to finish parsing inside the grace, the cooperative path wins
    /// instead and the assertion below still has to hold — this test can lose
    /// coverage on faster hardware, never soundness.
    fn write_parse_bound_cnf(path: &Path) {
        const VARIABLES: u64 = 700_000;
        const CLAUSES: u64 = 2_982_000; // 700_000 * 4.26, the phase transition.
        let file = std::fs::File::create(path).expect("create CNF");
        let mut out = BufWriter::with_capacity(1 << 20, file);
        writeln!(out, "p cnf {VARIABLES} {CLAUSES}").expect("write CNF header");
        let mut state: u64 = 0x2026_0827;
        let mut literal = || {
            state = state
                .wrapping_mul(6364136223846793005)
                .wrapping_add(1442695040888963407);
            let variable = (state >> 33) % VARIABLES + 1;
            if state & 1 == 0 {
                variable as i64
            } else {
                -(variable as i64)
            }
        };
        for _ in 0..CLAUSES {
            writeln!(out, "{} {} {} 0", literal(), literal(), literal()).expect("write clause");
        }
        out.flush().expect("flush CNF");
    }

    fn wait_for_staging_file(dir: &Path, budget: Duration) -> bool {
        let deadline = Instant::now() + budget;
        while Instant::now() < deadline {
            if !staging_files(dir).is_empty() {
                return true;
            }
            std::thread::sleep(Duration::from_millis(20));
        }
        false
    }

    fn terminate(pid: u32) {
        let status = Command::new("kill")
            .args(["-TERM", &pid.to_string()])
            .status()
            .expect("signal the solver");
        assert!(status.success(), "kill -TERM should reach the solver");
    }

    #[test]
    #[timeout(120_000)]
    fn terminated_solve_strands_no_proof_staging_file() {
        let dir = tempfile::tempdir().expect("tempdir");
        let cnf = dir.path().join("parse-bound.cnf");
        let proof_dir = dir.path().join("proofs");
        std::fs::create_dir(&proof_dir).expect("create proof directory");
        write_parse_bound_cnf(&cnf);
        let proof = proof_dir.join("out.drat");

        let mut child = Command::new(env!("CARGO_BIN_EXE_ay"))
            .arg("--timeout")
            .arg("600000")
            .arg("--proof")
            .arg(&proof)
            .arg(&cnf)
            .stdin(Stdio::null())
            .stdout(Stdio::null())
            .stderr(Stdio::null())
            .spawn()
            .expect("spawn ay");

        // Linux stages an unsealed proof on an anonymous `O_TMPFILE` inode,
        // which has no pathname to strand and which the kernel reclaims at
        // exit; every other platform falls back to the named sibling stage this
        // waits for.
        let staged = wait_for_staging_file(&proof_dir, Duration::from_secs(30));
        if cfg!(not(target_os = "linux")) {
            assert!(
                staged,
                "the solver must stage its unsealed proof beside the target"
            );
        }

        terminate(child.id());
        let status = child
            .wait_timeout(Duration::from_secs(30))
            .expect("wait for the terminated solver");
        if status.is_none() {
            let _ = child.kill();
            let _ = child.wait();
            panic!("the terminated solver never exited");
        }

        assert!(
            staging_files(&proof_dir).is_empty(),
            "a terminated solve must strand no proof staging file; found {:?}",
            staging_files(&proof_dir)
        );
        assert!(
            !proof.exists(),
            "an unsealed proof must never be published by the exit sweep"
        );
    }

    #[test]
    #[timeout(60_000)]
    fn published_proof_survives_the_exit_sweep() {
        let dir = tempfile::tempdir().expect("tempdir");
        let cnf = dir.path().join("unsat.cnf");
        std::fs::write(&cnf, "p cnf 2 4\n1 2 0\n1 -2 0\n-1 2 0\n-1 -2 0\n").expect("write CNF");
        let proof = dir.path().join("out.drat");

        let status = Command::new(env!("CARGO_BIN_EXE_ay"))
            .arg("--timeout")
            .arg("30000")
            .arg("--proof")
            .arg(&proof)
            .arg(&cnf)
            .stdin(Stdio::null())
            .stdout(Stdio::null())
            .stderr(Stdio::null())
            .status()
            .expect("run ay");

        assert_eq!(status.code(), Some(20), "the instance is UNSAT");
        let published =
            std::fs::read(&proof).expect("the published proof must survive process exit");
        assert!(
            !published.is_empty(),
            "the published proof must keep its bytes"
        );
        assert!(
            staging_files(dir.path()).is_empty(),
            "publication must consume the staging name"
        );
    }
}
