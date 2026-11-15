// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Wrong-UNSAT regressions from the 2026-09-23 bit-vector hunt (D5, D9).
//!
//! Every formula here is satisfiable (z3 5.1.0 answers `sat`, and each model
//! z3 printed was pinned back into the formula and re-checked), and AY on
//! main `f399eca07a` answered `unsat`:
//!
//! * **D5** — `BvLiaBitblastTranslator::push_range_assertions`
//!   (`executor/theories/combined/mod.rs`) copied the Int bounds of `x` onto
//!   the bit-blast probe's residue var for `int2bv_w(x)` one side at a time.
//!   `x <= 5` became `(bvule r #x05)`, although `int2bv_8(-1) = #xff`, so the
//!   probe "proved" `bv2nat(int2bv_8 x) <= 5` and the BV/LIA bridge
//!   published `unsat` — in the default posture too, admitted
//!   `discharged-trust` with a `fresh-executor-resolve` corroboration that
//!   re-ran the same code. The residue range now comes from both bounds and
//!   the period arithmetic of `x mod 2^w`.
//! * **D9** — `bv_range_extract` (`executor/theories/bv_finite_array.rs`)
//!   clamped `v >> low` to the extract width instead of reducing it, so an
//!   index in `[256, 511]` read through `extract[7:0]` was given the range
//!   `[255, 255]`; the dense-initializer rewrite (proof-free postures only)
//!   then answered the read from the single known cell `T[#xff]`.
//!
//! Each file runs in the default posture and in the proof-shed posture
//! (`--z3-mode`). `sat` and `unknown` are accepted; `unsat` never is.

use ay_dpll::Executor;
use ay_frontend::parse;
use ntest::timeout;
use std::time::Duration;

fn verdict(smt: &str, proof_shed: bool) -> String {
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
        .find(|line| matches!(line.as_str(), "sat" | "unsat" | "unknown"))
        .unwrap_or_else(|| "none".to_string())
}

fn assert_never_unsat(name: &str, smt: &str) {
    for proof_shed in [false, true] {
        let posture = if proof_shed { "--z3-mode" } else { "default" };
        let got = verdict(smt, proof_shed);
        assert!(
            got == "sat" || got == "unknown",
            "{name} ({posture}): z3 5.1.0 answers sat and its model checks; AY answered {got:?}"
        );
    }
}

// ---- D5: int2bv residue bounds ----

/// `x = -1`: `int2bv_8(-1) = #xff`, `bv2nat = 255 > 5`.
const INT2BV_UPPER_RANGE: &str = "(set-logic ALL)
(declare-fun x () Int)
(assert (<= x 5))
(assert (> (bv2nat ((_ int2bv 8) x)) 5))
(check-sat)";

/// `x = 256`: `bvnot(int2bv_8(256)) = #xff`.
const INT2BV_LOWER_RANGE: &str = "(set-logic ALL)
(declare-fun x () Int)
(assert (>= x 250))
(assert (> (bv2nat (bvnot ((_ int2bv 8) x))) 5))
(check-sat)";

/// `x = -1` again, inside a two-sided bound that straddles zero. The default
/// posture's independent check withheld this one (`unknown`); `--z3-mode`
/// published `unsat`.
const INT2BV_STRADDLE_RANGE: &str = "(set-logic ALL)
(declare-fun x () Int)
(assert (>= x (- 3)))
(assert (<= x 5))
(assert (> (bv2nat ((_ int2bv 8) x)) 5))
(check-sat)";

/// A 16-bit residue under `concat`, bounded above only (hunt g6_00047).
const INT2BV_CONCAT_16: &str = "(set-logic ALL)
(declare-fun x () Int)
(assert (> (bv2nat (concat #b0 ((_ int2bv 16) (+ x 2)))) 11012))
(assert (<= x 9858))
(check-sat)";

/// A 32-bit residue of `x - 3` under `bvadd` (hunt g6_00304).
const INT2BV_BVADD_32: &str = "(set-logic ALL)
(declare-fun x () Int)
(assert (<= x 642687403))
(assert (< 4192820028 (bv2nat (bvadd ((_ int2bv 32) (+ x (- 3))) (_ bv2101131879 32)))))
(check-sat)";

/// An extract of a 5-bit residue, bounded above only (hunt g6_00420).
const INT2BV_EXTRACT_5: &str = "(set-logic ALL)
(declare-fun x () Int)
(assert (< 6 (bv2nat ((_ extract 4 1) ((_ int2bv 5) x)))))
(assert (<= x 5))
(check-sat)";

/// A 32-bit `bvnot` residue bounded below only (hunt g6_00561).
const INT2BV_BVNOT_32: &str = "(set-logic ALL)
(declare-fun x () Int)
(assert (>= x 883368329))
(assert (not (<= (bv2nat (bvnot ((_ int2bv 32) (+ x (- 1))))) 3762505226)))
(check-sat)";

/// The bound reaches `x` only through `z = x + 0` (the hunt generator's
/// `eq-var` shape; fresh seed 9301, idx 334): `x = 2` gives `bvor(#b10, #b01)
/// = #b11 > 2`. Base answered `sat` here only because its search happened to
/// meet a validating candidate; the fix's first cut left it `unknown` until the
/// Int-blast lane learned to move bounds across offset equalities.
const INT2BV_BOUND_THROUGH_OFFSET_EQUALITY: &str = "(set-logic ALL)
(declare-fun x () Int)
(declare-fun z () Int)
(assert (= z (+ x 0)))
(assert (>= z 1))
(assert (< 2 (bv2nat (bvor ((_ int2bv 2) x) #b01))))
(check-sat)";

#[test]
#[timeout(240_000)]
fn d5_bound_through_an_offset_equality_is_decided() {
    for proof_shed in [false, true] {
        let got = verdict(INT2BV_BOUND_THROUGH_OFFSET_EQUALITY, proof_shed);
        assert_eq!(
            got,
            "sat",
            "eq-var shape ({}): z3 5.1.0 answers sat; AY answered {got:?}",
            if proof_shed { "--z3-mode" } else { "default" }
        );
    }
}

#[test]
#[timeout(240_000)]
fn d5_one_sided_int_bound_is_not_a_residue_bound() {
    assert_never_unsat("int2bv upper range", INT2BV_UPPER_RANGE);
    assert_never_unsat("int2bv lower range", INT2BV_LOWER_RANGE);
    assert_never_unsat("int2bv straddling range", INT2BV_STRADDLE_RANGE);
}

#[test]
#[timeout(240_000)]
fn d5_residue_bounds_through_bv_operators_and_wide_residues() {
    assert_never_unsat("g6_00047 concat 16", INT2BV_CONCAT_16);
    assert_never_unsat("g6_00304 bvadd 32", INT2BV_BVADD_32);
    assert_never_unsat("g6_00420 extract 5", INT2BV_EXTRACT_5);
    assert_never_unsat("g6_00561 bvnot 32", INT2BV_BVNOT_32);
}

// ---- D9: extract index ranges in the dense-initializer rewrite ----

/// The arrays hunter's witness: the read index is every byte.
const EXTRACT_WRAP_PREDICATE: &str = "(set-logic QF_ABV)
(declare-fun t () (Array (_ BitVec 8) (_ BitVec 8)))
(declare-fun y () (_ BitVec 8))
(assert (= (select t #xff) #x00))
(assert (not (= (select t ((_ extract 7 0) (bvadd #x0100 ((_ zero_extend 8) y)))) #x00)))
(check-sat)";

/// Store peeling: the read index was "provably disjoint" from `#x05`.
const EXTRACT_WRAP_STORE_PEEL: &str = "(set-logic QF_ABV)
(declare-fun T () (Array (_ BitVec 8) (_ BitVec 8)))
(declare-fun y () (_ BitVec 8))
(assert (= (select T #xff) #x00))
(assert (= (select (store T #x05 #x07) ((_ extract 7 0) (bvadd ((_ zero_extend 8) y) #x0100))) #x07))
(check-sat)";

/// The masked offset `(bvand y #x003f) + #x012c` spans low bytes 44..107.
const EXTRACT_WRAP_OFFSET: &str = "(set-logic QF_ABV)
(declare-fun T () (Array (_ BitVec 8) (_ BitVec 8)))
(declare-fun y () (_ BitVec 16))
(assert (= (select T #xff) #x00))
(assert (= (select T ((_ extract 7 0) (bvadd (bvand y #x003f) #x012c))) #x07))
(check-sat)";

/// The value path: the claimed `[255, 255]` sat inside the dense run
/// `T[240..255] = 0`, so the read was replaced by `#x00`.
const EXTRACT_WRAP_DENSE_VALUE: &str = "(set-logic QF_ABV)
(declare-fun T () (Array (_ BitVec 8) (_ BitVec 8)))
(declare-fun y () (_ BitVec 8))
(assert (= (select T #xf0) #x00))
(assert (= (select T #xf1) #x00))
(assert (= (select T #xf2) #x00))
(assert (= (select T #xf3) #x00))
(assert (= (select T #xf4) #x00))
(assert (= (select T #xf5) #x00))
(assert (= (select T #xf6) #x00))
(assert (= (select T #xf7) #x00))
(assert (= (select T #xf8) #x00))
(assert (= (select T #xf9) #x00))
(assert (= (select T #xfa) #x00))
(assert (= (select T #xfb) #x00))
(assert (= (select T #xfc) #x00))
(assert (= (select T #xfd) #x00))
(assert (= (select T #xfe) #x00))
(assert (= (select T #xff) #x00))
(assert (bvult y #x10))
(assert (= (select T ((_ extract 7 0) (bvadd ((_ zero_extend 8) y) #x0100))) #x07))
(check-sat)";

/// A 32-bit KLEE-style offset.
const EXTRACT_WRAP_KLEE32: &str = "(set-logic QF_ABV)
(declare-fun t () (Array (_ BitVec 8) (_ BitVec 8)))
(declare-fun off () (_ BitVec 8))
(assert (= (select t #xff) #x2a))
(assert (not (= (select t ((_ extract 7 0) (bvadd #x00001000 ((_ zero_extend 24) off)))) #x2a)))
(check-sat)";

/// A non-zero low bit: `extract[8:1]` of `[512, 767]` is `[0, 127]`.
const EXTRACT_WRAP_LOW_BIT: &str = "(set-logic QF_ABV)
(declare-fun t () (Array (_ BitVec 8) (_ BitVec 8)))
(declare-fun y () (_ BitVec 8))
(assert (= (select t #xff) #x00))
(assert (not (= (select t ((_ extract 8 1) (bvadd #x0200 ((_ zero_extend 8) y)))) #x00)))
(check-sat)";

/// Four-bit indices, one-bit elements.
const EXTRACT_WRAP_TINY: &str = "(set-logic QF_ABV)
(declare-fun t () (Array (_ BitVec 4) (_ BitVec 1)))
(declare-fun y () (_ BitVec 2))
(assert (= (select t #xf) #b0))
(assert (= (select t ((_ extract 3 0) (bvadd #b10000 ((_ zero_extend 3) y)))) #b1))
(check-sat)";

#[test]
#[timeout(240_000)]
fn d9_wrapping_extract_index_is_not_a_single_cell() {
    assert_never_unsat("extract wrap predicate", EXTRACT_WRAP_PREDICATE);
    assert_never_unsat("extract wrap store peel", EXTRACT_WRAP_STORE_PEEL);
    assert_never_unsat("extract wrap masked offset", EXTRACT_WRAP_OFFSET);
}

#[test]
#[timeout(240_000)]
fn d9_wrapping_extract_index_value_klee_and_narrow_shapes() {
    assert_never_unsat("extract wrap dense value", EXTRACT_WRAP_DENSE_VALUE);
    assert_never_unsat("extract wrap klee32", EXTRACT_WRAP_KLEE32);
    assert_never_unsat("extract wrap extract[8:1]", EXTRACT_WRAP_LOW_BIT);
    assert_never_unsat("extract wrap 4-bit index", EXTRACT_WRAP_TINY);
}
