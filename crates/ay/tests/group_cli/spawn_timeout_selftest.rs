// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Negative self-test for `crate::spawn::OutputTimeout` (Lever 4, CLI-spawn
//! orphan hygiene): a hung `ay` child must be SIGKILLed (whole process group)
//! by the helper itself, well before ntest's deadline, and must not survive
//! the test as an orphan.

#[cfg(unix)]
mod unix_tests {
    use ntest::timeout;
    use std::fs;
    use std::path::PathBuf;
    use std::process::Command;
    use std::time::{Duration, Instant};

    use crate::spawn::OutputTimeout;

    struct Cleanup(PathBuf);

    impl Drop for Cleanup {
        fn drop(&mut self) {
            let _ = fs::remove_file(&self.0);
        }
    }

    fn unique_fifo_path() -> PathBuf {
        let nanos = std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .expect("system clock should be after Unix epoch")
            .as_nanos();
        std::env::temp_dir().join(format!(
            "ay_spawn_selftest_fifo_{}_{}.opb",
            std::process::id(),
            nanos
        ))
    }

    /// Spawn `ay pb solve` on a FIFO that is never written: the child blocks
    /// forever reading its input (same deterministic-hang trick as
    /// pb26_sigterm.rs). `output_timeout(1s)` must return
    /// `io::ErrorKind::TimedOut` promptly and leave no surviving `ay`
    /// process behind.
    #[test]
    #[timeout(30_000)]
    fn output_timeout_kills_hung_ay_and_leaves_no_orphan() {
        let ay_path = env!("CARGO_BIN_EXE_ay");
        let fifo = unique_fifo_path();
        let mkfifo_status = Command::new("mkfifo")
            .arg(&fifo)
            .status()
            .expect("create selftest FIFO");
        assert!(mkfifo_status.success(), "mkfifo should create the FIFO");
        let _cleanup = Cleanup(fifo.clone());

        let started = Instant::now();
        let result = Command::new(ay_path)
            .args(["pb", "solve", "--timeout", "60000"])
            .arg(&fifo)
            .output_timeout(Duration::from_secs(1));
        let elapsed = started.elapsed();

        // 1. Honest TimedOut error, not a hang and not a success.
        let err = result.expect_err("hung ay child must yield a timeout error");
        assert_eq!(
            err.kind(),
            std::io::ErrorKind::TimedOut,
            "expected TimedOut, got {err:?}"
        );
        assert!(
            err.to_string().contains("process group killed"),
            "timeout error should describe the group kill: {err}"
        );

        // 2. The helper fired on its own deadline (1 s), far below ntest's.
        assert!(
            elapsed < Duration::from_secs(5),
            "output_timeout(1s) took {elapsed:?}; the bounded wait did not fire"
        );

        // 3. No orphan: nothing on the box still references the unique FIFO
        //    path on its command line. pgrep exits non-zero on no match.
        let fifo_name = fifo
            .file_name()
            .expect("fifo path has a file name")
            .to_string_lossy()
            .into_owned();
        let pgrep = Command::new("pgrep")
            .arg("-f")
            .arg(&fifo_name)
            .output()
            .expect("spawn pgrep");
        assert!(
            !pgrep.status.success(),
            "orphaned ay survived the group kill: pgrep -f {fifo_name} -> {}",
            String::from_utf8_lossy(&pgrep.stdout)
        );
    }
}
