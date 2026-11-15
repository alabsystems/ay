// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The BV/LIA bridge's guarded mask residue (#guarded-mask-residue,
//! `combined/guarded_mask_residue.rs`), the pre-quantifier bridge SAT that
//! `check_sat` now keeps (#bridge-sat-kept), and the #3073 formula, which
//! must never be UNSAT.
//!
//! * **Trust row.** `finalize_tail_realmir` line 437 reads two pointers'
//!   alignment as `(bv2nat (bvand (int2bv_64 p) (int2bv_64 m)))` with the
//!   mask local pinned by `(= m 7)` only inside each path disjunct. No
//!   literal reaches `mk_bv2nat`'s residue fold, so the bridge's AUF/LIA
//!   candidate gave the opaque read a value no pointer realises and the
//!   model gate refused it. With `(= m 7) ==> read = p mod 8` the first
//!   bridge run (before quantifier preprocessing) finds a model the gate
//!   accepts; `check_sat` used to drop that SAT and solve the same roots
//!   again in the `QfBvLia` dispatch, whose second AUF/LIA search ended in a
//!   branch-and-bound cycle (`unknown`). Trust runs ay with
//!   `:produce-proofs`.
//! * **Family.** The same shape with a pointer-like `x`, over low-bit masks
//!   and one that is not, against the exact answer: as written, which the
//!   Int-blast lane decides through its split points
//!   (#int-blast-split-points), and with `y >= 2x` added, which keeps the
//!   lane out, so the residue clause alone decides it.
//! * **#3073.** `(distinct (mod x 3) (mod (+ x 1) 3)) /\ 0 <= x < 10` was a
//!   false UNSAT at z4 9208a5cf. Rebuilt there, it stays UNSAT with the cube
//!   test disabled: the slack-row construction of the time, not Gomory after
//!   a cube, broke the tableau (#4842 fixed it). Both spellings are pinned
//!   `sat`.

use ay_dpll::Executor;
use ay_frontend::parse;
use ntest::timeout;
use std::time::Duration;

#[derive(Clone, Copy, Debug)]
enum Posture {
    /// `Executor::new()` as is.
    Default,
    /// The CLI's `--z3-mode` / `--no-proof` posture.
    ProofShed,
    /// Trust's in-process backend: `(set-option :produce-proofs true)`.
    ProduceProofs,
}

const POSTURES: [Posture; 3] = [Posture::Default, Posture::ProofShed, Posture::ProduceProofs];

fn verdicts(smt: &str, posture: Posture) -> Vec<String> {
    let script = match posture {
        Posture::ProduceProofs => format!("(set-option :produce-proofs true)\n{smt}"),
        Posture::Default | Posture::ProofShed => smt.to_string(),
    };
    let commands = parse(&script).unwrap_or_else(|err| panic!("parse failed: {err}"));
    let mut exec = Executor::new();
    if matches!(posture, Posture::ProofShed) {
        exec.set_competition_mode(true);
    }
    exec.set_timeout(Some(Duration::from_secs(20)));
    exec.set_memory_limit(Some(8 << 30));
    let lines = exec
        .execute_all(&commands)
        .unwrap_or_else(|err| panic!("execution failed: {err}"));
    lines
        .iter()
        .map(|line| line.trim().to_string())
        .filter(|line| matches!(line.as_str(), "sat" | "unsat" | "unknown"))
        .collect()
}

#[test]
#[timeout(180_000)]
fn trust_static_read_null_check_is_sat() {
    let smt = include_str!(
        "../../../../benchmarks/smt/regression/trust_static_read_null_check_guarded_mask_sat.smt2"
    );
    for posture in POSTURES {
        assert_eq!(verdicts(smt, posture), ["sat"], "{posture:?}");
    }
}

#[test]
#[timeout(120_000)]
fn issue_3073_mod_distinct_plus_one_is_sat() {
    for (name, smt) in [
        (
            "native",
            include_str!("../../../../benchmarks/smt/QF_LIA/issue_3073_mod_distinct_plus_one_sat.smt2"),
        ),
        (
            "mod eliminated",
            include_str!(
                "../../../../benchmarks/smt/QF_LIA/issue_3073_mod_distinct_plus_one_eliminated_sat.smt2"
            ),
        ),
    ] {
        for posture in POSTURES {
            assert_eq!(verdicts(smt, posture), ["sat"], "{name} ({posture:?})");
        }
    }
}

/// `r = (x & m)` at width 64 with `m` pinned to `c` only inside each of two
/// path disjuncts, `x` a pointer-like Int (`window`) and `r` pinned to
/// `target`. `lane_blocked` adds `y >= 2x` for a fresh `y`: satisfiable for
/// every `x`, so the answer is unchanged, but it reads `x` outside an
/// `int2bv` and a constant comparison, so the Int-blast lane declines.
fn family_query(c: i128, window: Window, target: i128, lane_blocked: bool) -> String {
    let lit = |v: i128| {
        if v < 0 {
            format!("(- {})", -v)
        } else {
            v.to_string()
        }
    };
    let read = "(bv2nat (bvand ((_ int2bv 64) x) ((_ int2bv 64) m)))";
    let window = match window {
        Window::AtLeast(lo) => format!("(assert (>= x {}))", lit(lo)),
        Window::NonNullPointer => {
            "(assert (>= x 0)) (assert (<= x 18446744073709551615)) (assert (distinct x 0))"
                .to_string()
        }
    };
    let blocker = if lane_blocked {
        "(declare-const y Int) (assert (>= y (* 2 x)))\n"
    } else {
        ""
    };
    format!(
        "(set-logic ALL)\n\
         (declare-const x Int) (declare-const m Int) (declare-const r Int) (declare-const q Int)\n\
         (assert (or (and (= m {c}) (= r {read}) (= q 1)) (and (= q 2) (= r {read}) (= m {c}))))\n\
         {window}\n(assert (= r {target}))\n{blocker}(check-sat)\n",
        c = lit(c),
        target = lit(target),
    )
}

#[derive(Clone, Copy, Debug)]
enum Window {
    /// `x >= lo`, unbounded above.
    AtLeast(i128),
    /// `0 <= x <= 2^64 - 1`, `x != 0`.
    NonNullPointer,
}

/// Every mask and window against the exact answer: with `x` unbounded above
/// (or any non-null 64-bit pointer) `x mod 2^64` reaches every residue, so
/// `r` reaches exactly the submasks `s` of `v = c mod 2^64` (`s & !v == 0`),
/// except `0` for the all-ones mask on a non-null pointer. No query may
/// contradict its truth.
///
/// * **As written** the Int-blast lane decides every query: `m` and `q` are
///   read only by constant comparisons that are not asserted, and `x` has a
///   one-sided window, so the lane cuts its window at their constants
///   (#int-blast-split-points). Under `--z3-mode` every answer is exact.
///   Under `:produce-proofs` every `sat` is, and an `unsat` may stay
///   `unknown` (a lane `unsat` has no proof to publish).
/// * **With the lane kept out** (`y >= 2x`) the residue clause alone decides
///   every satisfiable low-bit-mask query. Before #guarded-mask-residue all
///   of them except `r = 0` answered `unknown` (measured 2026-11-08). The
///   non-mask `c = 5` has no residue clause and may stay `unknown`.
#[test]
#[timeout(600_000)]
fn alignment_mask_under_a_disjunct_matches_its_exact_answer() {
    let modulus: i128 = 1 << 64;
    let (mut lane_exact, mut lane_sat) = (0, 0);
    let (mut decided_sat, mut decided_unsat, mut unknown) = (0, 0, 0);
    for c in [1i128, 7, 255, -1, 5] {
        let v = c.rem_euclid(modulus);
        let low_bit_mask = v & (v + 1) == 0;
        for window in [
            Window::AtLeast(0),
            Window::AtLeast(1000),
            Window::NonNullPointer,
        ] {
            for target in [0i128, 1, 5, 6, 255, 256] {
                let submask = target & !v & (modulus - 1) == 0;
                let truth_sat = match window {
                    Window::AtLeast(_) => submask,
                    Window::NonNullPointer => submask && !(v == modulus - 1 && target == 0),
                };
                let truth = if truth_sat { "sat" } else { "unsat" };

                let smt = family_query(c, window, target, false);
                assert_eq!(
                    verdicts(&smt, Posture::ProofShed),
                    [truth],
                    "{smt}--z3-mode"
                );
                lane_exact += 1;
                let got = verdicts(&smt, Posture::ProduceProofs);
                match got.as_slice() {
                    [answer] if answer == truth => lane_sat += usize::from(truth_sat),
                    [answer] if answer == "unknown" && !truth_sat => {}
                    _ => panic!("{smt}ProduceProofs: the answer is {truth}, ay said {got:?}"),
                }

                let smt = family_query(c, window, target, true);
                for posture in [Posture::Default, Posture::ProduceProofs] {
                    let got = verdicts(&smt, posture);
                    assert_eq!(got.len(), 1, "{smt}{posture:?}: {got:?}");
                    match (got[0].as_str(), truth_sat) {
                        ("sat", true) => decided_sat += 1,
                        ("unsat", false) => decided_unsat += 1,
                        ("unknown", true) if !low_bit_mask => unknown += 1,
                        ("unknown", false) => unknown += 1,
                        (answer, _) => {
                            panic!("{smt}{posture:?}: the answer is {truth}, ay said {answer}")
                        }
                    }
                }
            }
        }
    }
    // 5 masks x 3 windows x 6 targets, 59 of them satisfiable.
    assert_eq!((lane_exact, lane_sat), (90, 59));
    // Low-bit masks: 1 -> {0, 1}, 7 -> {0, 1, 5, 6}, 255 -> 5 targets,
    // -1 -> 6 targets, each in 3 windows, minus `r = 0` on a non-null pointer
    // for -1: 50 satisfiable queries, x 2 postures.
    assert!(
        decided_sat >= 100,
        "sat {decided_sat}, unsat {decided_unsat}, unknown {unknown}"
    );
}
