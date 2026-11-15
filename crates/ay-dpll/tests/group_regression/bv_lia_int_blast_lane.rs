// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The BV/LIA bridge's exact Int-blast lane (`combined/int_blast.rs`) in
//! incremental sessions and at its soundness guards — witnesses from the
//! 2026-09-23 verification of the bit-vector repair (D5).
//!
//! * **History.** The lane used to build its Int→BV translation in the
//!   session's shared term store. The AUF/LIA search of every LATER check
//!   reads that whole store, so a check the lane had decided changed which
//!   candidate the next `check-sat` / `check-sat-assuming` found, and a
//!   cheap `sat` became `unknown` (`hi_00275` check 2 in both postures,
//!   `hi_00222` check 3 default, `hi_00483` check 3 `--z3-mode`; minimal form
//!   `im_275_asis`). The lane now translates inside its disposable probe.
//!   The pinned checks are decided by the AUF/LIA candidate, not by the lane:
//!   if one of them turns `unknown`, look first for a solve that leaves terms
//!   or search state behind for the next check. Exception: `hi_00483` reads
//!   `x0` through the Bool definition `q1 = (distinct c x0)`, which the lane
//!   declined until #int-blast-split-points, so its AUF/LIA candidate (blind
//!   to `extract`) decided check 3 only in some term-store layouts; with
//!   #bridge-sat-kept the session's first check left fewer terms and
//!   `--z3-mode` check 3 turned `unknown` (2026-11-08). The lane decides it
//!   now.
//! * **Guards.** `m7a`, `m15d` and `m18d` are satisfiable and decided by the
//!   lane; each turns into a wrong `unsat` when one guard of the half-bounded
//!   window is broken: the class residue width taken as the MIN over its
//!   members (m7), a strict bound read as non-strict (m15), and the offset
//!   union-find linking roots without their find-offsets (m18).
//! * **Push.** `lm2_01`'s second check sits inside a `push`, where the
//!   partition rescue is off (it decides the same assertions without the
//!   push); it is decided by the lane once the lane reads the scaled bound
//!   `(>= (* 3 x0) (- 1021))`, which the store keeps as
//!   `(<= (- 1021) (* x0 3))`. `v5_01017` bounds `x0` by a negated atom and
//!   also reads it under `=>`, which a class bounded on both sides allows.
//!   Base answered both only through D5's unsound one-sided residue bound.

use ay_dpll::Executor;
use ay_frontend::parse;
use ntest::timeout;
use std::time::Duration;

fn verdicts(smt: &str, proof_shed: bool) -> Vec<String> {
    let commands = parse(smt).unwrap_or_else(|err| panic!("parse failed: {err}"));
    let mut exec = Executor::new();
    if proof_shed {
        // The CLI's `--z3-mode` / `--no-proof` posture.
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

/// Per check: `Some(v)` must be answered exactly, `None` may be `unknown`
/// but never contradicts `truth`.
fn check(
    name: &str,
    smt: &str,
    truth: &[&str],
    default: &[Option<&str>],
    z3_mode: &[Option<&str>],
) {
    for (proof_shed, pinned) in [(false, default), (true, z3_mode)] {
        let posture = if proof_shed { "--z3-mode" } else { "default" };
        let got = verdicts(smt, proof_shed);
        assert_eq!(got.len(), truth.len(), "{name} ({posture}): {got:?}");
        for (index, answer) in got.iter().enumerate() {
            let expected = truth[index];
            match pinned[index] {
                Some(pin) => assert_eq!(
                    answer,
                    pin,
                    "{name} ({posture}) check {}: {got:?}",
                    index + 1
                ),
                None => assert!(
                    answer == expected || answer == "unknown",
                    "{name} ({posture}) check {}: the answer is {expected}, AY said {got:?}",
                    index + 1
                ),
            }
        }
    }
}

/// `hi_00275` (the verification's minimal form `im_275_asis` is the same
/// file): the lane decides check 1 (`x0 < 65509` with a 33-bit residue pin);
/// check 2 assumes a disequality that the residue already implies, so it is
/// `sat` with the same models, and so is check 3.
const IM_275_ASIS: &str = "(set-logic ALL)
(declare-fun x0 () Int)
(declare-fun q0 () Bool)
(assert (= ((_ int2bv 33) x0) #b001010110110011010111001001011100))
(assert (< x0 65509))
(assert (bvslt ((_ int2bv 33) (- x0 255)) ((_ int2bv 33) x0)))
(assert (not (= ((_ int2bv 33) (* 3 x0)) (bvsub ((_ int2bv 33) (+ (* 2 (- x0 (- 256))) (- 1))) ((_ int2bv 33) (+ (+ x0 255) (+ x0 x0)))))))
(check-sat)
(assert (= q0 (distinct (- 25769803804) x0)))
(check-sat-assuming (q0))
(check-sat)";

const HI_00222: &str = "(set-logic ALL)
(declare-fun x0 () Int)
(declare-fun q2 () Bool)
(declare-fun q1 () Bool)
(declare-fun q0 () Bool)
(assert (distinct 123 x0))
(assert (= ((_ zero_extend 6) ((_ int2bv 1) x0)) (_ bv1 7)))
(assert (not (> (bv2nat ((_ int2bv 7) x0)) 124)))
(check-sat)
(assert (= q0 (not (= ((_ int2bv 7) (- x0 3)) ((_ int2bv 7) (+ x0 (- 256)))))))
(assert (= q1 (= ((_ int2bv 7) (+ x0 (- 258))) #b1011010)))
(assert (= q2 (= 251 x0)))
(check-sat-assuming (q0 q1 q2))
(check-sat)";

const HI_00483: &str = "(set-logic ALL)
(declare-fun x0 () Int)
(declare-fun b0 () (_ BitVec 1))
(declare-fun q1 () Bool)
(declare-fun q0 () Bool)
(assert (= ((_ extract 1 1) ((_ int2bv 8) (- x0 3))) (_ bv1 1)))
(check-sat)
(assert (= q0 (= ((_ int2bv 2) (+ (* (- 2) x0) 7)) #b01)))
(assert (= q1 (distinct 1091634752581323207310 x0)))
(check-sat-assuming (q0 q1))
(check-sat)";

#[test]
#[timeout(600_000)]
fn a_check_the_lane_decided_does_not_cost_a_later_check() {
    let sat = Some("sat");
    // --z3-mode checks 2-3 were `sat unknown unknown` on main from
    // `bff0049422` (the LIA justified-bounds exit guard) to `c24f74c15d`: the
    // guard refused every conflict PROBE `Unsat` that needed a shared
    // equality (the probe asserts its candidates without reasons, so its
    // conflict names their placeholders), the AUF/LIA augmentation fell back
    // to the whole shared-equality closure, and that search ended `unknown`
    // on checks 2-3. The "(= ((_ int2bv 33) x0) #b0010...) evaluates to false"
    // detail it printed is the pure-BV relaxation probe's model, not the
    // AUF/LIA candidate. Fixed by #probe-hypothesis-premise
    // (`ay-lia/src/tests/probe_hypothesis_premise.rs`).
    check(
        "im_275_asis",
        IM_275_ASIS,
        &["sat", "sat", "sat"],
        &[sat, sat, None],
        &[sat, sat, sat],
    );
    check(
        "hi_00222",
        HI_00222,
        &["sat", "unsat", "sat"],
        &[sat, Some("unsat"), sat],
        &[sat, Some("unsat"), None],
    );
    check(
        "hi_00483",
        HI_00483,
        &["sat", "sat", "sat"],
        &[sat, None, None],
        &[sat, None, sat],
    );
}

/// `x <= 0`, `y = x + 1`, a 16-bit residue of `y` and a nibble of the 8-bit
/// residue of `x` (`x = -48193`). With the class residue width taken as the
/// MIN over its members the window holds 256 integers and misses the model.
const M7A: &str = "(set-logic ALL)
(declare-fun x () Int)
(declare-fun y () Int)
(assert (<= x 0))
(assert (= y (+ x 1)))
(assert (= (bvnot ((_ int2bv 16) y)) #x63bf))
(assert (= ((_ extract 3 0) ((_ int2bv 8) x)) #xf))
(check-sat)";

/// `x < 5` with `int2bv_16(x) = #x0005` (`x = -65531`): read as `x <= 5`, the
/// window of 65536 integers ends at 5, holds `x = 5` instead, and the strict
/// atom refutes it.
const M15D: &str = "(set-logic ALL)
(declare-fun x () Int)
(assert (< x 5))
(assert (= (bvnot ((_ int2bv 16) x)) #xfffa))
(check-sat)";

/// `x = y + 1000`, `z = x + 1000`: linking `z` to the class needs `x`'s own
/// offset from the root; without it `z` sits 1000 too low and the window
/// misses the residue the nibble of `z` asks for.
const M18D: &str = "(set-logic ALL)
(declare-fun x () Int)
(declare-fun y () Int)
(declare-fun z () Int)
(assert (= x (+ y 1000)))
(assert (= z (+ x 1000)))
(assert (>= y 0))
(assert (= (bvnot ((_ int2bv 16) y)) #x0217))
(assert (= ((_ extract 3 0) ((_ int2bv 16) z)) #x8))
(check-sat)";

#[test]
#[timeout(240_000)]
fn half_bounded_window_guards_keep_their_witnesses_sat() {
    let sat = Some("sat");
    check("m7a", M7A, &["sat"], &[sat], &[sat]);
    check("m15d", M15D, &["sat"], &[sat], &[sat]);
    check("m18d", M18D, &["sat"], &[sat], &[sat]);
}

/// `y = x + 257` makes `int2bv_8(y) = 1` require `x = 0 (mod 256)`.
/// The two disequalities reject the first two nonnegative representatives;
/// `x = 512, y = 769` is a witness in the third period of the class window.
const OFFSET_THIRD_REPRESENTATIVE: &str = "(set-logic ALL)
(declare-fun x () Int)
(declare-fun y () Int)
(assert (>= x 0))
(assert (= y (+ x 257)))
(assert (distinct x 0))
(assert (distinct x 256))
(assert (= ((_ int2bv 8) y) #x01))
(check-sat)";

/// `not (-3*x < -4)` means `x <= 1`. The residue `x = 2 (mod 16)`
/// first reaches that half-line at `-14`, which is excluded; `x = -30`
/// witnesses why the one-disequality window must span a second period.
const NEGATED_SCALED_SECOND_REPRESENTATIVE: &str = "(set-logic ALL)
(declare-fun x () Int)
(assert (not (< (* (- 3) x) (- 4))))
(assert (distinct x (- 14)))
(assert (= ((_ int2bv 4) x) #x2))
(check-sat)";

#[test]
#[timeout(240_000)]
fn offset_and_negated_scaled_windows_keep_later_residue_witnesses_sat() {
    for (name, smt) in [
        ("offset third representative", OFFSET_THIRD_REPRESENTATIVE),
        (
            "negated scaled second representative",
            NEGATED_SCALED_SECOND_REPRESENTATIVE,
        ),
    ] {
        check(name, smt, &["sat"], &[Some("sat")], &[Some("sat")]);
    }
}

/// The first two checks of the verification's `v5_01594`: check 2 is inside
/// a `push` and `x0 = 1` satisfies it.
const LM2_01: &str = "(set-logic ALL)
(declare-fun x0 () Int)
(declare-fun x1 () Int)
(declare-fun x2 () Int)
(declare-fun b0 () (_ BitVec 10))
(declare-fun b1 () (_ BitVec 10))
(assert (>= (* 3 x0) (- 1021)))
(assert (not (not (= (bv2nat (bvurem ((_ int2bv 10) x1) (_ bv3 10))) 0))))
(assert (not (< (bv2nat (bvneg ((_ int2bv 10) (+ x0 (bv2nat b1))))) 0)))
(check-sat)
(push 1)
(assert (distinct x2 19 17))
(assert (> (bv2nat ((_ int2bv 10) (bv2nat ((_ int2bv 13) x0)))) 0))
(assert (>= 249 x0))
(check-sat)";

/// The verification's `v5_01017`: `x0` is bounded by `(not (< x0 ...))` and
/// `(<= x0 109398917)` and also read under `=>`, which a two-sided class
/// allows. Base answered `sat` in `--z3-mode` only through the unsound
/// one-sided residue bound (D5).
const V5_01017: &str = "(set-logic ALL)
(declare-fun x0 () Int)
(assert (not (= (bv2nat ((_ int2bv 32) x0)) 0)))
(assert (not (bvsge ((_ extract 31 0) #b000000000000000000000000000000000000001) #x59390308)))
(assert (=> (>= x0 109398657) (<= x0 109398667)))
(assert (not (< x0 (- 8480535930))))
(assert (not (bvsle (bvnot (bvadd ((_ int2bv 32) (- x0)) ((_ int2bv 32) (- (- 121) x0)))) ((_ int2bv 32) (- x0)))))
(assert (<= x0 109398917))
(check-sat)";

#[test]
#[timeout(240_000)]
fn a_push_does_not_cost_the_lane_its_scaled_and_negated_bounds() {
    let sat = Some("sat");
    check("lm2_01", LM2_01, &["sat", "sat"], &[sat, sat], &[sat, sat]);
    check("v5_01017", V5_01017, &["sat"], &[sat], &[sat]);
}

#[test]
#[timeout(240_000)]
fn scoped_bridge_retry_does_not_retain_an_independent_assumption() {
    // The q0 window exercises the previously undecided proof-shed bridge.
    // A separate free Boolean makes retaining the temporary assumption
    // observable: the later negation must still leave the base satisfiable.
    let script = IM_275_ASIS
        .replace(
            "(set-logic ALL)",
            "(set-logic ALL)\n(declare-fun scoped_probe_flag () Bool)",
        )
        .replace(
            "(check-sat-assuming (q0))",
            "(check-sat-assuming (q0 scoped_probe_flag))",
        )
        + "\n(assert (not scoped_probe_flag))\n(check-sat)\n";
    check(
        "temporary independent assumption",
        &script,
        &["sat", "sat", "sat", "sat"],
        &[Some("sat"); 4],
        &[Some("sat"); 4],
    );
}
