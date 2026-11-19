// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! `ay maxsat solve` anytime answers, judged as the MaxSAT Evaluation does.
//!
//! MSE credits a model that is not proven optimal only under `s SATISFIABLE`,
//! and grades that claim: the `v` line must satisfy every hard clause and cost
//! exactly the last `o` line. These tests check both, independently of AY, on
//! a generated instance that AY cannot prove optimal within its budget.

use ntest::timeout;
use std::path::{Path, PathBuf};
use std::process::{Command, Output, Stdio};

struct Scratch(PathBuf);

impl Drop for Scratch {
    fn drop(&mut self) {
        let _ = std::fs::remove_dir_all(&self.0);
    }
}

fn scratch(label: &str) -> Scratch {
    let nanos = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .expect("clock after epoch")
        .as_nanos();
    let dir = std::env::temp_dir().join(format!(
        "ay-maxsat-anytime-{label}-{}-{nanos}",
        std::process::id()
    ));
    std::fs::create_dir_all(&dir).expect("create scratch dir");
    Scratch(dir)
}

struct Lcg(u64);

impl Lcg {
    fn below(&mut self, n: u64) -> u64 {
        self.0 = self
            .0
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        (self.0 >> 33) % n
    }
}

type Instance = (usize, Vec<Vec<i32>>, Vec<(u64, Vec<i32>)>);

/// Random 3-SAT hard clauses (ratio 2.5, satisfiable in practice) and a
/// weighted unit soft per variable plus some opposing units: easy to satisfy,
/// far beyond a few seconds of core-guided optimality proof.
fn hard_to_prove(num_vars: usize, seed: u64) -> Instance {
    let mut rng = Lcg(seed);
    let mut hard = Vec::new();
    for _ in 0..(num_vars * 5 / 2) {
        let mut clause = Vec::new();
        while clause.len() < 3 {
            let v = 1 + rng.below(num_vars as u64) as i32;
            if clause.iter().any(|&l: &i32| l.abs() == v) {
                continue;
            }
            clause.push(if rng.below(2) == 0 { v } else { -v });
        }
        hard.push(clause);
    }
    let mut soft = Vec::new();
    for v in 1..=num_vars as i32 {
        soft.push((1 + rng.below(100), vec![v]));
        if rng.below(10) < 3 {
            soft.push((1 + rng.below(100), vec![-v]));
        }
    }
    (num_vars, hard, soft)
}

fn write_wcnf(path: &Path, (_, hard, soft): &Instance) {
    let mut text = String::new();
    for c in hard {
        text.push('h');
        for l in c {
            text.push_str(&format!(" {l}"));
        }
        text.push_str(" 0\n");
    }
    for (w, c) in soft {
        text.push_str(&format!("{w}"));
        for l in c {
            text.push_str(&format!(" {l}"));
        }
        text.push_str(" 0\n");
    }
    std::fs::write(path, text).expect("write wcnf");
}

/// Check stdout as the MSE checker does. Returns the status word.
fn check_mse_output(stdout: &str, (num_vars, hard, soft): &Instance) -> String {
    let s_lines: Vec<&str> = stdout.lines().filter(|l| l.starts_with("s ")).collect();
    assert_eq!(s_lines.len(), 1, "exactly one s line expected:\n{stdout}");
    let status = s_lines[0][2..].to_string();
    let last_o: Option<u64> = stdout
        .lines()
        .filter_map(|l| l.strip_prefix("o "))
        .map(|o| o.trim().parse().expect("numeric o line"))
        .next_back();
    let v_lines: Vec<&str> = stdout.lines().filter(|l| l.starts_with("v ")).collect();
    match status.as_str() {
        "SATISFIABLE" | "OPTIMUM FOUND" => {
            assert_eq!(v_lines.len(), 1, "one v line expected:\n{stdout}");
            let bits = v_lines[0][2..].trim();
            assert_eq!(bits.len(), *num_vars, "v line covers every variable");
            let value =
                |l: i32| (bits.as_bytes()[l.unsigned_abs() as usize - 1] == b'1') == (l > 0);
            for c in hard {
                assert!(
                    c.iter().any(|&l| value(l)),
                    "v line falsifies hard clause {c:?}"
                );
            }
            let cost: u64 = soft
                .iter()
                .filter(|(_, c)| !c.iter().any(|&l| value(l)))
                .map(|(w, _)| w)
                .sum();
            assert_eq!(Some(cost), last_o, "v line cost must equal the last o line");
        }
        "UNKNOWN" => assert!(v_lines.is_empty(), "no v line under s UNKNOWN:\n{stdout}"),
        other => panic!("unexpected status {other:?}"),
    }
    status
}

fn run(args: &[&str], file: &Path) -> Output {
    Command::new(env!("CARGO_BIN_EXE_ay"))
        .args(["maxsat", "solve"])
        .args(args)
        .arg(file)
        .stdin(Stdio::null())
        .output()
        .expect("run ay maxsat solve")
}

#[test]
#[timeout(120_000)]
fn incumbent_at_own_timeout_is_reported_satisfiable_and_checks() {
    let dir = scratch("timeout");
    let inst = hard_to_prove(1000, 0x5eed_0001);
    let file = dir.0.join("in.wcnf");
    write_wcnf(&file, &inst);
    let out = run(&["--timeout", "2"], &file);
    let stdout = String::from_utf8_lossy(&out.stdout);
    assert_eq!(
        out.status.code(),
        Some(0),
        "stderr: {}",
        String::from_utf8_lossy(&out.stderr)
    );
    assert!(
        stdout.lines().any(|l| l.starts_with("o ")),
        "expected an incumbent:\n{stdout}"
    );
    let status = check_mse_output(&stdout, &inst);
    // Without a proof of optimality the incumbent is credited only as
    // SATISFIABLE; it was printed as `s UNKNOWN` before (AY-SAT-5).
    assert_eq!(status, "SATISFIABLE", "{stdout}");
}

/// AY-N1: the evaluator stops anytime runs with SIGTERM (and a user with
/// SIGINT). A stop request, or an overrun of AY's own deadline, must end with
/// the model of the last `o` line (or `s UNKNOWN` without one), exactly one
/// `s` line and status 0. Before, the default action killed the process with
/// no `s` or `v` line.
#[cfg(unix)]
mod stop {
    use super::*;
    use std::io::{BufRead, BufReader, Write};
    use std::process::Child;
    use std::sync::mpsc;
    use std::time::{Duration, Instant};
    use wait_timeout::ChildExt;

    fn spawn(args: &[&str], file: &Path) -> Child {
        Command::new(env!("CARGO_BIN_EXE_ay"))
            .args(["maxsat", "solve"])
            .args(args)
            .arg(file)
            .stdin(Stdio::null())
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .spawn()
            .expect("spawn ay maxsat solve")
    }

    /// Forward stdout lines to a channel, so the test can wait for an `o`
    /// line without blocking on the rest.
    fn lines(child: &mut Child) -> mpsc::Receiver<String> {
        let out = child.stdout.take().expect("stdout");
        let (tx, rx) = mpsc::channel();
        std::thread::spawn(move || {
            for line in BufReader::new(out).lines() {
                let Ok(line) = line else { break };
                if tx.send(line).is_err() {
                    break;
                }
            }
        });
        rx
    }

    fn signal(child: &Child, sig: nix::sys::signal::Signal) {
        nix::sys::signal::kill(nix::unistd::Pid::from_raw(child.id() as i32), sig)
            .expect("signal ay");
    }

    /// Wait for the exit (at most `limit`), then return status code and the
    /// whole stdout.
    fn finish(
        mut child: Child,
        rx: &mpsc::Receiver<String>,
        mut seen: Vec<String>,
        limit: Duration,
    ) -> (Option<i32>, String, Duration) {
        let started = Instant::now();
        let status = match child.wait_timeout(limit).expect("wait") {
            Some(status) => status,
            None => {
                let _ = child.kill();
                panic!("ay did not exit within {limit:?} of the stop");
            }
        };
        let took = started.elapsed();
        while let Ok(line) = rx.recv_timeout(Duration::from_secs(5)) {
            seen.push(line);
        }
        let mut text = seen.join("\n");
        text.push('\n');
        (status.code(), text, took)
    }

    fn stop_with_incumbent(sig: nix::sys::signal::Signal, label: &str) {
        let dir = scratch(label);
        let inst = hard_to_prove(1000, 0x5eed_0002);
        let file = dir.0.join("in.wcnf");
        write_wcnf(&file, &inst);
        let mut child = spawn(&["--timeout", "100"], &file);
        let rx = lines(&mut child);
        let mut seen = Vec::new();
        let deadline = Instant::now() + Duration::from_secs(60);
        while !seen.iter().any(|l: &String| l.starts_with("o ")) {
            let left = deadline.saturating_duration_since(Instant::now());
            match rx.recv_timeout(left) {
                Ok(line) => seen.push(line),
                Err(_) => {
                    let _ = child.kill();
                    panic!("no o line within 60 s: {seen:?}");
                }
            }
        }
        signal(&child, sig);
        let (code, stdout, took) = finish(child, &rx, seen, Duration::from_secs(20));
        assert_eq!(code, Some(0), "exit status after {sig:?}:\n{stdout}");
        assert!(
            took < Duration::from_secs(15),
            "answered {took:?} after {sig:?}"
        );
        assert_eq!(check_mse_output(&stdout, &inst), "SATISFIABLE", "{stdout}");
    }

    #[test]
    #[timeout(120_000)]
    fn sigterm_with_an_incumbent_prints_its_checked_model() {
        stop_with_incumbent(nix::sys::signal::Signal::SIGTERM, "sigterm");
    }

    #[test]
    #[timeout(120_000)]
    fn sigint_with_an_incumbent_prints_its_checked_model() {
        stop_with_incumbent(nix::sys::signal::Signal::SIGINT, "sigint");
    }

    /// A FIFO whose writer sends `head` and then stalls, holding the parser
    /// inside `read` where no deadline check can run: only the watchdog can
    /// answer.
    /// The receiver yields once AY has opened the FIFO, which it does only
    /// after its stop handler is installed.
    fn stalled_fifo(
        dir: &Path,
        head: &'static str,
    ) -> (PathBuf, mpsc::Receiver<()>, mpsc::Sender<()>) {
        let fifo = dir.join("in.wcnf");
        let made = Command::new("mkfifo").arg(&fifo).status().expect("mkfifo");
        assert!(made.success());
        let (release_tx, release_rx) = mpsc::channel::<()>();
        let (opened_tx, opened_rx) = mpsc::channel::<()>();
        let path = fifo.clone();
        std::thread::spawn(move || {
            let mut w = std::fs::OpenOptions::new()
                .write(true)
                .open(&path)
                .expect("open fifo");
            let _ = opened_tx.send(());
            w.write_all(head.as_bytes()).expect("write fifo");
            w.flush().expect("flush fifo");
            let _ = release_rx.recv_timeout(Duration::from_secs(60));
        });
        (fifo, opened_rx, release_tx)
    }

    #[test]
    #[timeout(60_000)]
    fn sigterm_while_reading_answers_unknown() {
        let dir = scratch("sigterm-read");
        let (fifo, opened, release) = stalled_fifo(&dir.0, "h 1 2 0\n3 1 0\n");
        let mut child = spawn(&["--timeout", "100"], &fifo);
        let rx = lines(&mut child);
        opened
            .recv_timeout(Duration::from_secs(20))
            .expect("ay opens the instance");
        std::thread::sleep(Duration::from_millis(200));
        signal(&child, nix::sys::signal::Signal::SIGTERM);
        let (code, stdout, took) = finish(child, &rx, Vec::new(), Duration::from_secs(20));
        drop(release);
        assert_eq!(code, Some(0), "{stdout}");
        assert_eq!(stdout, "s UNKNOWN\n");
        assert!(
            took < Duration::from_secs(15),
            "answered {took:?} after SIGTERM"
        );
    }

    #[test]
    #[timeout(60_000)]
    fn deadline_overrun_while_reading_answers_unknown() {
        let dir = scratch("overrun-read");
        let (fifo, _opened, release) = stalled_fifo(&dir.0, "h 1 2 0\n3 1 0\n");
        let child = spawn(&["--timeout", "1"], &fifo);
        let mut child = child;
        let rx = lines(&mut child);
        // No signal: AY must notice its own deadline passing.
        let (code, stdout, _) = finish(child, &rx, Vec::new(), Duration::from_secs(20));
        drop(release);
        assert_eq!(code, Some(0), "{stdout}");
        assert_eq!(stdout, "s UNKNOWN\n");
    }

    /// A reader that keeps delivering clauses past the deadline is stopped by
    /// the reader's own deadline check, before the watchdog's grace.
    #[test]
    #[timeout(60_000)]
    fn reader_observes_the_deadline() {
        let dir = scratch("slow-read");
        let fifo = dir.0.join("in.wcnf");
        let made = Command::new("mkfifo").arg(&fifo).status().expect("mkfifo");
        assert!(made.success());
        let path = fifo.clone();
        std::thread::spawn(move || {
            // Read-write: the writer is then also a reader, so a write after
            // AY has exited blocks instead of raising SIGPIPE in the test.
            let Ok(mut w) = std::fs::OpenOptions::new()
                .read(true)
                .write(true)
                .open(&path)
            else {
                return;
            };
            let mut v: u64 = 1;
            loop {
                let mut chunk = String::new();
                for _ in 0..1024 {
                    chunk.push_str(&format!("h {v} {} 0\n", v + 1));
                    v += 1;
                }
                if w.write_all(chunk.as_bytes()).is_err() {
                    return;
                }
                std::thread::sleep(Duration::from_millis(5));
            }
        });
        let mut child = spawn(&["--timeout", "1"], &fifo);
        let rx = lines(&mut child);
        let mut stderr = child.stderr.take().expect("stderr");
        let (code, stdout, _) = finish(child, &rx, Vec::new(), Duration::from_secs(20));
        let mut err = String::new();
        let _ = std::io::Read::read_to_string(&mut stderr, &mut err);
        assert_eq!(code, Some(0), "{stdout}{err}");
        assert_eq!(stdout, "s UNKNOWN\n");
        assert!(
            err.contains("before the instance was read"),
            "the reader, not the watchdog, should stop: {err}"
        );
    }
}
