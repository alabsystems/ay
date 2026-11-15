// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The verifier's incremental `incr2_2609_0034` on the CLI (2026-09-24/25 arrays
//! fix-up), first two queries: the second (`p1`, `p0`: `a` equal to a store
//! chain over `c`) is `sat` (z3 5.1.0) and main answers it.
//!
//! Given as a FILE, the CLI decides both queries `sat` in both postures (a
//! file is read whole before solving). Fed on STDIN (the interactive,
//! incremental executor), the second query ends `unknown` in the default
//! posture: the assumption split loop spends its model-equality round budget
//! (#6851, 100 rounds with no theory conflict) because the D4-a repair's
//! store-chain conflicts now carry their index-distinctness reasons and prune
//! less (the verifier's mutant with the D4-a revert answers `sat`; measured
//! 2026-09-25). That is a LISTED lost verdict of this track, not a pass: the
//! stdin run here pins only that it is never a wrong answer.

use ntest::timeout;
use std::process::Command;
use std::time::Duration;

use crate::spawn::OutputTimeout;

const TIMEOUT: Duration = Duration::from_mins(2);

const INCR2_0034: &str = "\
(set-logic QF_ALIA)
(declare-fun a () (Array Int Int))
(declare-fun b () (Array Int Int))
(declare-fun c () (Array Int Int))
(declare-fun i () Int)
(declare-fun j () Int)
(declare-fun k () Int)
(declare-fun p0 () Bool)
(declare-fun p1 () Bool)
(declare-fun p2 () Bool)
(declare-fun p3 () Bool)
(declare-fun p4 () Bool)
(assert (=> p0 (= (store (store c 0 1) (+ i 1) (select b i)) a)))
(assert (=> p1 (< (select (store (store b i 0) (+ i 1) (select a 1)) j) 5)))
(assert (=> p2 (= (select a 0) 1)))
(assert (=> p3 (= j (+ i 1))))
(assert (=> p4 (= (store (store a j 5) 2 0) (store (store c 1 2) k (select a (+ i 1))))))
(push 1)
(assert (< (select c (+ i 1)) (select a 0)))
(check-sat)
(pop 1)
(check-sat-assuming (p1 p0))
";

fn verdicts(stdout: &str) -> Vec<&str> {
    stdout
        .lines()
        .map(str::trim)
        .filter(|l| matches!(*l, "sat" | "unsat" | "unknown"))
        .collect()
}

#[test]
#[timeout(300_000)]
fn assumption_query_resolve_decides_a_variable_equal_to_a_store_chain() {
    let dir = std::env::temp_dir().join(format!("ay-incr2-0034-{}", std::process::id()));
    std::fs::create_dir_all(&dir).expect("temp dir");
    let file = dir.join("incr2_2609_0034.smt2");
    std::fs::write(&file, INCR2_0034).expect("write input");
    for args in [&[][..], &["--z3-mode"][..]] {
        let output = Command::new(env!("CARGO_BIN_EXE_ay"))
            .args(args)
            .args(["-T:60", "--quiet-soundness-gate"])
            .arg(&file)
            .output_timeout(TIMEOUT)
            .expect("run ay");
        let stdout = String::from_utf8_lossy(&output.stdout);
        assert_eq!(
            verdicts(&stdout),
            vec!["sat", "sat"],
            "{args:?} (file): z3 5.1.0 answers sat, sat:\n{stdout}"
        );
    }
    let _ = std::fs::remove_dir_all(&dir);
}

#[test]
#[timeout(300_000)]
fn assumption_query_on_stdin_is_never_a_wrong_answer() {
    for args in [&[][..], &["--z3-mode"][..]] {
        let output = Command::new(env!("CARGO_BIN_EXE_ay"))
            .args(args)
            .args(["-T:60", "--quiet-soundness-gate"])
            .output_timeout_with_stdin(INCR2_0034.as_bytes(), TIMEOUT)
            .expect("run ay");
        let stdout = String::from_utf8_lossy(&output.stdout);
        let got = verdicts(&stdout);
        assert_eq!(got.len(), 2, "{args:?} (stdin): two verdicts:\n{stdout}");
        assert_eq!(
            got[0], "sat",
            "{args:?} (stdin): z3 5.1.0 answers sat:\n{stdout}"
        );
        assert!(
            matches!(got[1], "sat" | "unknown"),
            "{args:?} (stdin): z3 5.1.0 answers sat; never unsat:\n{stdout}"
        );
    }
}

/// Fresh `incr2_2809_0051` (session 5 of the fix-up): all five queries are
/// `sat` (z3 5.1.0, main). With the store-chain class reconciliation as the
/// ONLY array model, the second query ended `unknown` in 0.1 s: the reconciled
/// model gave `c` cells of `(store a k 5)` against
/// `(= (as const 1) (store c k 1))`. The reconciliation is now the second
/// candidate, gated only after the per-term model was refused
/// (#store-chain-class-candidate).
const INCR2_2809_0051: &str = "\
(set-logic QF_ALIA)
(declare-fun a () (Array Int Int))
(declare-fun b () (Array Int Int))
(declare-fun c () (Array Int Int))
(declare-fun i () Int)
(declare-fun j () Int)
(declare-fun k () Int)
(declare-fun p0 () Bool)
(declare-fun p1 () Bool)
(declare-fun p2 () Bool)
(declare-fun p3 () Bool)
(assert (=> p0 (= i j)))
(assert (=> p1 (= ((as const (Array Int Int)) 1) c)))
(assert (=> p2 (= (select (store a k 5) (+ i 1)) (select b (+ i 1)))))
(assert (=> p3 (= (select a 1) 2)))
(assert (< (select (store b k (select b 0)) k) (select b k)))
(check-sat-assuming (p0 (not p2) (not p3)))
(push 1)
(assert (= (select b k) 0))
(assert (= (store a 1 1) a))
(assert (= ((as const (Array Int Int)) 1) (store c k 1)))
(assert p2)
(check-sat)
(pop 1)
(push 1)
(assert (< (select (store ((as const (Array Int Int)) 1) 1 (select a j)) (+ i 1)) 1))
(assert (= k (+ i 1)))
(check-sat)
(pop 1)
(push 1)
(assert (= (select b (+ i 1)) 1))
(assert (= (select (store (store b (+ i 1) 0) k 0) i) (select b 0)))
(check-sat)
(pop 1)
(check-sat)
";

#[test]
#[timeout(300_000)]
fn store_chain_class_reconciliation_is_the_second_candidate_on_the_cli() {
    let dir = std::env::temp_dir().join(format!("ay-incr2-2809-0051-{}", std::process::id()));
    std::fs::create_dir_all(&dir).expect("temp dir");
    let file = dir.join("incr2_2809_0051.smt2");
    std::fs::write(&file, INCR2_2809_0051).expect("write input");
    for args in [&[][..], &["--z3-mode"][..]] {
        let output = Command::new(env!("CARGO_BIN_EXE_ay"))
            .args(args)
            .args(["-T:60", "--quiet-soundness-gate"])
            .arg(&file)
            .output_timeout(TIMEOUT)
            .expect("run ay");
        let stdout = String::from_utf8_lossy(&output.stdout);
        assert_eq!(
            verdicts(&stdout),
            vec!["sat"; 5],
            "{args:?}: z3 5.1.0 answers sat five times:\n{stdout}"
        );
    }
    let _ = std::fs::remove_dir_all(&dir);
}
