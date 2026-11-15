// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The transcript contract when a budget or a signal ends a run: every query
//! gets exactly one response, a decisive answer is never followed by 124, and
//! the reason names what fired (`ay help exit-codes`, `ay help z3`
//! DIVERGENCES 2).

#[cfg(unix)]
mod unix_tests {
    use std::fs;
    use std::path::{Path, PathBuf};
    use std::process::{Child, Command, Output, Stdio};
    use std::time::{Duration, Instant};
    use wait_timeout::ChildExt;

    /// A QF_NRA body (meti-tarski `atan-vega`) ay cannot decide in seconds;
    /// its time goes to the multivariate witness search.
    const HARD_NRA: &str = r#"(push 1)
(declare-fun skoX () Real)
(declare-fun skoY () Real)
(declare-fun skoZ () Real)
(assert (let ((?v_2 (<= 0 skoY)) (?v_4 (* skoX skoX)) (?v_0 (* skoX (/ 157 100))) (?v_6 (* skoX (* skoX (- 1))))) (let ((?v_1 (+ (- 3) ?v_6))) (let ((?v_5 (* skoY (* skoX ?v_1))) (?v_3 (<= (* skoZ (+ (- 1) (* skoY skoX))) (+ skoX skoY)))) (and ?v_2 (and (<= (* skoZ (+ (+ (/ (- 471) 100) (* skoX (+ 3 (* skoX (/ (- 157) 100))))) (* skoY (+ (+ 3 (* skoX (+ (/ 471 100) (* skoX (+ (- 2) ?v_0))))) ?v_5)))) (+ (+ (- 3) (* skoX (+ (/ 471 100) (* skoX (+ (- 4) ?v_0))))) (* skoY (+ (+ (/ 471 100) (* skoX (+ (- 3) ?v_0))) (* skoY ?v_1))))) (and (not (<= ?v_4 (- 3))) (and (not ?v_3) (and (or (not ?v_2) (or ?v_3 (<= (* skoZ (+ (+ 3 ?v_4) ?v_5)) (+ (* skoX ?v_6) (* skoY (+ (* skoX (* skoX (- 3))) ?v_5)))))) (and (not (<= skoZ 0)) (and (not (<= skoX (- 1))) (and (not (<= 1 skoY)) (not (<= skoY skoX))))))))))))))
(check-sat)
(pop 1)
"#;

    /// One trivial `sat` query, then the hard one.
    fn sat_then_hard() -> String {
        format!(
            "(set-logic QF_NRA)\n(declare-const a Real)\n(assert (> a 0))\n(check-sat)\n{HARD_NRA}"
        )
    }

    struct Scratch(PathBuf);

    impl Scratch {
        fn new(tag: &str) -> Self {
            let nanos = std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .map(|elapsed| elapsed.as_nanos())
                .unwrap_or(0);
            let dir = std::env::temp_dir().join(format!(
                "ay_query_response_{tag}_{}_{nanos}",
                std::process::id()
            ));
            fs::create_dir_all(&dir).expect("create scratch dir");
            Self(dir)
        }

        fn file(&self, name: &str, text: &str) -> PathBuf {
            let path = self.0.join(name);
            fs::write(&path, text).expect("write input");
            path
        }
    }

    impl Drop for Scratch {
        fn drop(&mut self) {
            let _ = fs::remove_dir_all(&self.0);
        }
    }

    fn ay() -> Command {
        Command::new(env!("CARGO_BIN_EXE_ay"))
    }

    fn spawn(args: &[&str], input: &Path) -> Child {
        ay().args(args)
            .arg(input)
            .stdin(Stdio::null())
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .spawn()
            .expect("spawn ay")
    }

    /// Wait at most `limit` for the child, killing it past that.
    fn finish(mut child: Child, limit: Duration) -> Output {
        if child.wait_timeout(limit).expect("wait").is_none() {
            let _ = child.kill();
        }
        child.wait_with_output().expect("collect output")
    }

    fn lines(bytes: &[u8]) -> Vec<String> {
        String::from_utf8_lossy(bytes)
            .lines()
            .map(str::trim)
            .filter(|line| !line.is_empty() && !line.starts_with("c "))
            .map(str::to_string)
            .collect()
    }

    fn sigterm(child: &Child) {
        let pid = nix::unistd::Pid::from_raw(child.id() as i32);
        let _ = nix::sys::signal::kill(pid, nix::sys::signal::Signal::SIGTERM);
    }

    /// A deadline during the second query answers it `unknown`; the earlier
    /// `sat` stands and the run exits 0. The deadline's report is given once.
    #[test]
    fn a_later_query_cut_by_the_deadline_is_answered_unknown() {
        let scratch = Scratch::new("later");
        let input = scratch.file("later.smt2", &sat_then_hard());
        let started = Instant::now();
        let output = finish(spawn(&["-T:2"], &input), Duration::from_secs(20));
        let stderr = String::from_utf8_lossy(&output.stderr);
        assert_eq!(
            lines(&output.stdout),
            ["sat", "unknown"],
            "stderr: {stderr}"
        );
        assert_eq!(output.status.code(), Some(0), "stderr: {stderr}");
        assert!(stderr.contains("verdict stands"), "stderr: {stderr}");
        // The cut query's `unknown` names its cause once.
        assert_eq!(
            stderr.matches("(:reason-unknown \"timeout\")").count(),
            1,
            "stderr: {stderr}"
        );
        assert!(started.elapsed() < Duration::from_secs(10));
    }

    /// An `unknown` the deadline caused exits 124 with one timeout reason,
    /// even when the solve's own deadline answered before the watchdog woke.
    #[test]
    fn an_unknown_the_deadline_caused_exits_124() {
        let scratch = Scratch::new("single");
        let input = scratch.file("single.smt2", &format!("(set-logic QF_NRA)\n{HARD_NRA}"));
        let output = finish(spawn(&["-T:2"], &input), Duration::from_secs(20));
        let stderr = String::from_utf8_lossy(&output.stderr);
        assert_eq!(lines(&output.stdout), ["unknown"], "stderr: {stderr}");
        assert_eq!(output.status.code(), Some(124), "stderr: {stderr}");
        assert_eq!(
            stderr.matches("reason-unknown").count(),
            1,
            "one timeout report: {stderr}"
        );
    }

    /// A per-check `:timeout` bounds that check, QF_NRA included: the first
    /// query answers `unknown` near its 1 s budget and the second runs.
    #[test]
    fn a_per_check_timeout_bounds_a_nonlinear_real_check() {
        let scratch = Scratch::new("percheck");
        let script = format!(
            "(set-logic QF_NRA)\n(set-option :timeout 1000)\n{HARD_NRA}\
             (declare-const b Real)\n(assert (> b 1))\n(check-sat)\n"
        );
        let input = scratch.file("percheck.smt2", &script);
        let started = Instant::now();
        let output = finish(
            spawn(&["--z3-mode", "-T:30"], &input),
            Duration::from_secs(40),
        );
        let elapsed = started.elapsed();
        assert_eq!(lines(&output.stdout), ["unknown", "sat"]);
        assert!(
            elapsed < Duration::from_secs(12),
            "a 1 s check took {elapsed:?} (it ran to the -T deadline)"
        );
    }

    /// SIGTERM during a later query answers it `unknown`, keeps the earlier
    /// `sat` standing, and does not call the termination a timeout.
    #[test]
    fn sigterm_during_a_later_query_answers_it_and_says_terminated() {
        let scratch = Scratch::new("sigterm_later");
        let input = scratch.file("later.smt2", &sat_then_hard());
        let child = spawn(&[], &input);
        std::thread::sleep(Duration::from_millis(1_500));
        sigterm(&child);
        let output = finish(child, Duration::from_secs(20));
        let stderr = String::from_utf8_lossy(&output.stderr);
        assert_eq!(
            lines(&output.stdout),
            ["sat", "unknown"],
            "stderr: {stderr}"
        );
        assert_eq!(output.status.code(), Some(0), "stderr: {stderr}");
        assert!(
            !stderr.contains("reason-unknown \"timeout\"") && !stderr.contains("c timeout"),
            "no deadline fired: {stderr}"
        );
        assert!(stderr.contains("terminated"), "stderr: {stderr}");
    }

    /// SIGTERM in the first milliseconds answers like any other SIGTERM.
    #[test]
    fn sigterm_at_start_up_answers_unknown() {
        let scratch = Scratch::new("sigterm_early");
        let input = scratch.file("hard.smt2", &format!("(set-logic QF_NRA)\n{HARD_NRA}"));
        for _ in 0..4 {
            let child = spawn(&["--z3-mode"], &input);
            std::thread::sleep(Duration::from_millis(15));
            sigterm(&child);
            let output = finish(child, Duration::from_secs(20));
            assert_eq!(lines(&output.stdout), ["unknown"], "{output:?}");
            assert_eq!(output.status.code(), Some(124), "{output:?}");
        }
    }

    /// A CHC script with two checks and nothing between them gets two
    /// responses, as from z3; a CHC run in `--z3-mode` writes no ay comment
    /// to stderr.
    #[test]
    fn chc_answers_each_check_and_keeps_z3_mode_stderr_clean() {
        let scratch = Scratch::new("chc_two");
        let body = "(set-logic HORN)\n(declare-fun inv (Int) Bool)\n\
                    (assert (forall ((x Int)) (=> (= x 0) (inv x))))\n\
                    (assert (forall ((x Int)) (=> (and (inv x) (< x 10)) (inv (+ x 1)))))\n\
                    (assert (forall ((x Int)) (=> (and (inv x) (> x 10)) false)))\n";
        let two = scratch.file("two.smt2", &format!("{body}(check-sat)\n(check-sat)\n"));
        let output = finish(
            spawn(&["--z3-mode", "--timeout", "20000"], &two),
            Duration::from_secs(40),
        );
        assert_eq!(lines(&output.stdout), ["sat", "sat"], "{output:?}");

        let refused = scratch.file(
            "refused.smt2",
            "(set-logic HORN)\n(assert (frob))\n(check-sat)\n",
        );
        let output = finish(
            spawn(&["--z3-mode", "--chc"], &refused),
            Duration::from_secs(20),
        );
        let stderr = String::from_utf8_lossy(&output.stderr);
        assert!(!stderr.contains("build.stamp"), "stderr: {stderr}");
    }

    /// A breached `--memory` budget is a memout: never `unknown` at exit 0.
    #[test]
    fn a_memory_breach_is_reported_as_a_memout() {
        let scratch = Scratch::new("memout");
        let input = scratch.file(
            "t.smt2",
            "(declare-const x Int)(assert (> x 0))(check-sat)\n",
        );
        let output = finish(spawn(&["--memory", "1"], &input), Duration::from_secs(20));
        let stdout = lines(&output.stdout);
        let stderr = String::from_utf8_lossy(&output.stderr);
        if stdout == ["unknown"] {
            assert_eq!(output.status.code(), Some(124), "stderr: {stderr}");
            assert!(stderr.contains("memout"), "stderr: {stderr}");
            assert!(!stderr.contains("interrupted"), "stderr: {stderr}");
        } else {
            // The check answered before the watchdog's first poll.
            assert_eq!(stdout, ["sat"], "stderr: {stderr}");
        }
    }

    /// A deferred `unsat` (an Alethe proof requested) is decisive: a later
    /// deadline does not turn the run into a failure.
    #[test]
    fn a_deferred_unsat_is_decisive_for_a_later_deadline() {
        let scratch = Scratch::new("deferred");
        let script = format!(
            "(set-logic QF_NRA)\n(declare-const a Real)\n(push 1)\n(assert (> a 0))\n\
             (assert (< a 0))\n(check-sat)\n(pop 1)\n{HARD_NRA}"
        );
        let input = scratch.file("deferred.smt2", &script);
        let proof = scratch.0.join("p.alethe");
        let proof = proof.to_str().expect("utf-8 path");
        let output = finish(
            spawn(&["-T:2", "--proof", proof], &input),
            Duration::from_secs(20),
        );
        let stderr = String::from_utf8_lossy(&output.stderr);
        assert_eq!(
            lines(&output.stdout),
            ["unsat", "unknown"],
            "stderr: {stderr}"
        );
        assert_eq!(output.status.code(), Some(0), "stderr: {stderr}");
    }

    /// A CHC `sat` that lands inside the SIGTERM grace is decisive: never
    /// followed by a timeout reason or exit 124.
    #[test]
    fn a_chc_verdict_inside_the_sigterm_grace_stands() {
        let input = Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("../../benchmarks/chc-comp/2025/extra-small-lia/gj2007_m_1_000.smt2");
        let child = spawn(&["--z3-mode", "--timeout", "20000"], &input);
        std::thread::sleep(Duration::from_millis(400));
        sigterm(&child);
        let output = finish(child, Duration::from_secs(20));
        let stdout = lines(&output.stdout);
        let stderr = String::from_utf8_lossy(&output.stderr);
        if stdout
            .first()
            .is_some_and(|line| line == "sat" || line == "unsat")
        {
            assert_eq!(output.status.code(), Some(0), "stderr: {stderr}");
            assert!(!stderr.contains("reason-unknown"), "stderr: {stderr}");
        } else {
            assert_eq!(stdout, ["unknown"], "stderr: {stderr}");
            assert_eq!(output.status.code(), Some(124), "stderr: {stderr}");
        }
    }
}
