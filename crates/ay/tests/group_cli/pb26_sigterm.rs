// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! PB26 SIGTERM subprocess contract.

#[cfg(unix)]
mod unix_tests {
    use ntest::timeout;
    use std::fs;
    use std::io::Read;
    use std::os::unix::process::ExitStatusExt;
    use std::path::PathBuf;
    use std::process::{Command, Stdio};
    use std::sync::mpsc;
    use std::time::Duration;
    use wait_timeout::ChildExt;

    struct Cleanup(PathBuf);

    impl Drop for Cleanup {
        fn drop(&mut self) {
            let _ = fs::remove_file(&self.0);
        }
    }

    fn unique_temp_opb_path() -> PathBuf {
        std::env::temp_dir().join(format!(
            "ay_pb26_sigterm_fifo_{}_{}.opb",
            std::process::id(),
            unique_suffix()
        ))
    }

    fn unique_suffix() -> u128 {
        std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .expect("system clock should be after Unix epoch")
            .as_nanos()
    }

    fn assert_pb_competition_lines(stdout: &str) {
        for line in stdout.lines() {
            let prefix = line
                .chars()
                .next()
                .expect("PB output lines should not be empty");
            assert!(
                matches!(prefix, 'c' | 'o' | 's' | 'v'),
                "unexpected PB output prefix after SIGTERM: {line:?}"
            );
            assert!(
                line.len() == 1 || line.as_bytes()[1] == b' ',
                "PB output lines must be prefixed as '<tag><space>...': {line:?}"
            );
        }
    }

    fn read_pipe(pipe: Option<impl Read>) -> Vec<u8> {
        let Some(mut pipe) = pipe else {
            return Vec::new();
        };
        let mut bytes = Vec::new();
        pipe.read_to_end(&mut bytes)
            .expect("child pipe should be readable after exit");
        bytes
    }

    #[test]
    #[timeout(30_000)]
    fn test_pb_solve_sigterm_after_monitor_install_emits_unknown_without_signal_exit() {
        let ay_path = env!("CARGO_BIN_EXE_ay");
        let input = unique_temp_opb_path();
        let mkfifo_status = Command::new("mkfifo")
            .arg(&input)
            .status()
            .expect("create PB SIGTERM FIFO");
        assert!(
            mkfifo_status.success(),
            "mkfifo should create the PB SIGTERM FIFO"
        );
        let _cleanup = Cleanup(input.clone());

        let mut child = Command::new(ay_path)
            .args(["pb", "solve", "--timeout", "60000"])
            .arg(&input)
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .spawn()
            .expect("spawn ay pb solve");

        let (opened_tx, opened_rx) = mpsc::channel();
        let (close_tx, close_rx) = mpsc::channel();
        let writer_path = input;
        let writer = std::thread::spawn(move || {
            let fifo = fs::OpenOptions::new()
                .write(true)
                .open(&writer_path)
                .expect("open PB SIGTERM FIFO for writing");
            opened_tx
                .send(())
                .expect("notify that child opened PB SIGTERM FIFO");
            let _ = close_rx.recv_timeout(Duration::from_secs(5));
            drop(fifo);
        });

        opened_rx
            .recv_timeout(Duration::from_secs(5))
            .expect("ay pb solve should open the FIFO after installing its SIGTERM monitor");

        nix::sys::signal::kill(
            nix::unistd::Pid::from_raw(child.id() as i32),
            nix::sys::signal::Signal::SIGTERM,
        )
        .expect("send SIGTERM to ay pb solve");

        std::thread::sleep(Duration::from_millis(100));
        close_tx
            .send(())
            .expect("release PB SIGTERM FIFO writer after signal");
        writer.join().expect("PB SIGTERM FIFO writer should finish");

        let status = match child
            .wait_timeout(Duration::from_secs(5))
            .expect("wait for ay pb solve after SIGTERM")
        {
            Some(status) => status,
            None => {
                let _ = child.kill();
                let _ = child.wait();
                panic!("ay pb solve did not exit within 5s of SIGTERM");
            }
        };

        let stdout =
            String::from_utf8(read_pipe(child.stdout.take())).expect("PB stdout should be UTF-8");
        let stderr =
            String::from_utf8(read_pipe(child.stderr.take())).expect("PB stderr should be UTF-8");

        assert_eq!(
            status.signal(),
            None,
            "PB SIGTERM handler should exit normally, status={status:?}, stdout={stdout:?}, stderr={stderr:?}"
        );
        assert_eq!(
            status.code(),
            Some(0),
            "interrupted PBS run should use UNKNOWN exit code, stdout={stdout:?}, stderr={stderr:?}"
        );
        assert_pb_competition_lines(&stdout);
        assert!(
            stdout.lines().any(|line| line == "s UNKNOWN"),
            "PB SIGTERM should emit s UNKNOWN when no solution is known, stdout={stdout:?}, stderr={stderr:?}"
        );
        assert!(
            !stdout.lines().any(|line| line.starts_with("v ")),
            "interrupted unsolved PBS run must not emit a witness, stdout={stdout:?}"
        );
    }
}
