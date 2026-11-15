// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Pin for `#dt-lazy-pre-attempt`
//! (`executor/theories/euf/dt.rs`, `try_dt_auf_lazy_pre_attempt`).
//!
//! Greedy-minimized from the Certora QF_UFDTLIA benchmark
//! `65782_cd31513fdcd15701933b_6_QF_UFDTLIA.smt2` (one assertion kept,
//! declarations pruned to the reachable set). z3 4.16.0 answers `sat`
//! instantly. Before the pre-attempt, the DT+LIA dispatch ran the
//! array-free UF route first: its call-site exclusion skipped the lazy
//! lane on this UF-at-datatype-sort shape (`x30 : Int -> x122` applied
//! under `x69`), and its eager authority wandered to the deadline
//! (`unknown` at 10s on this reduction; the full file at 30s+), so the
//! array sibling's lazy attempt — the lane that decides it — never got
//! budget. With the lane attempted at dispatch, ahead of both eager
//! authorities, the verdict is a gate-confirmed `sat`.

use crate::Executor;
use ay_frontend::parse;

const CERTORA_65782_REDUCED: &str = r#"
(set-logic QF_UFDTLIA)
(declare-datatypes ((x122 0)) (((x26 (x36 Int)) (x1 (x90 x122) (x134 x122) (x144 Int)) (x58 (x76 x122) (x39 Int)))))
(declare-fun x4 (x122) Int)
(declare-fun x30 (Int) x122)
(declare-fun x193 () Int)
(declare-fun x81 () Int)
(declare-fun x43 (Int Int) Int)
(declare-fun x177 () Int)
(declare-fun x75 () x122)
(declare-fun x62 () Int)
(declare-fun x87 () Int)
(declare-fun x72 () Int)
(declare-fun x92 () Bool)
(declare-fun x158 () Int)
(declare-fun x27 () Bool)
(declare-fun x128 () Int)
(declare-fun x57 () Int)
(declare-fun x168 () Int)
(declare-fun x105 () Int)
(declare-fun x34 () Bool)
(declare-fun x59 () Int)
(declare-fun x184 () Int)
(declare-fun x89 () Int)
(declare-fun x157 () Bool)
(declare-fun x119 () Int)
(declare-fun x115 () Int)
(declare-fun x145 () Int)
(declare-fun x164 () Int)
(declare-fun x67 () Bool)
(declare-fun x154 () Bool)
(declare-fun x14 () Int)
(declare-fun x200 (Int Int) Int)
(declare-fun x129 () Int)
(declare-fun x48 () x122)
(declare-fun x166 () Bool)
(declare-fun x106 () Bool)
(declare-fun x35 () Int)
(declare-fun x100 () Bool)
(declare-fun x96 () Int)
(declare-fun x60 () Int)
(declare-fun x15 () Int)
(declare-fun x141 () Int)
(declare-fun x23 () Int)
(declare-fun x123 () Int)
(declare-fun x153 (Int Int) Int)
(declare-fun x70 () Int)
(declare-fun x11 () Bool)
(declare-fun x93 () Int)
(declare-fun x121 () Int)
(declare-fun x150 () Int)
(declare-fun x139 () Bool)
(declare-fun x85 () Int)
(declare-fun x77 () Bool)
(declare-fun x32 (x122) Int)
(declare-fun x38 () Int)
(declare-fun x49 () Int)
(declare-fun x46 () Int)
(declare-fun x159 () Bool)
(declare-fun x101 () Int)
(declare-fun x69 (x122) Int)
(declare-fun x140 () Int)
(declare-fun x80 () Int)
(declare-fun x112 () Int)
(define-fun x137 ((x122 x122) (x173 Int)) x122 (ite ((_ is x1) x122) (x1 (x90 x122) (x134 x122) (+ (x144 x122) x173)) (ite ((_ is x58) x122) (x58 (x76 x122) (+ x173 (x39 x122))) (x26 (+ (x36 x122) x173)))))
(define-fun x127 ((x131 Int)) Int (ite (and (> 115792089237316195423570985008687907853269984665640564039457584007913129639936 x131) (>= x131 0)) x131 (- x131 115792089237316195423570985008687907853269984665640564039457584007913129639936)))
(define-fun x54 ((x131 Int)) Int (ite (and (>= x131 0) (> 115792089237316195423570985008687907853269984665640564039457584007913129639936 x131)) x131 (ite (and (<= 115792089237316195423570985008687907853269984665640564039457584007913129639936 x131) (< x131 231584178474632390847141970017375815706539969331281128078915168015826259279872)) (- x131 115792089237316195423570985008687907853269984665640564039457584007913129639936) (ite (and (<= (- 115792089237316195423570985008687907853269984665640564039457584007913129639936) x131) (> 0 x131)) (+ x131 115792089237316195423570985008687907853269984665640564039457584007913129639936) (x200 x131 115792089237316195423570985008687907853269984665640564039457584007913129639936)))))
(assert (= (=> (and (and (>= 1461501637330902918203684832716283019655932542975 x119) (>= 1461501637330902918203684832716283019655932542975 x81) x106 (= x139 (< 0 (x69 (x30 x164)))) (= 2514000705 x96) (= 404098525 x49) (<= x59 1461501637330902918203684832716283019655932542975) (>= x119 0) (>= x60 0) (not (= x49 117300739)) (< 0 x15) (<= 0 x59) (>= x35 0) x139 (not (= x81 x164)) (= 0 x72) (> x81 0) (> x164 0) (= (x32 (x30 x81)) x38) (= false x67) (>= x23 0) (< x49 826074471) (= x105 x60) (<= x35 1461501637330902918203684832716283019655932542975) (<= x35 1461501637330902918203684832716283019655932542975) (<= x60 115792089237316195423570985008687907853269984665640564039457584007913129639935) (= x15 (x69 (x30 x81))) (>= 1461501637330902918203684832716283019655932542975 x164) (= x154 false) (= 0 x168) (>= x101 0) (<= 0 x38) (= (> (x69 (x30 x81)) 0) x106) (not (= 157198259 x49)) (<= x23 1461501637330902918203684832716283019655932542975) (<= 0 x62) (= x157 false) (= x59 x177) (<= x101 1461501637330902918203684832716283019655932542975) (= x62 (x32 (x30 x164))) (= x77 true) (<= 0 x35)) (and (> 3337024914 x128) (not (< x145 4)) (>= 1461501637330902918203684832716283019655932542975 x14) (= x89 (x54 (* x80 32))) (<= 0 x14) (= (x127 (+ 32 x89)) x57) (not (= x150 x140)) (>= x35 0) (>= 1461501637330902918203684832716283019655932542975 x35) (>= 1461501637330902918203684832716283019655932542975 x85) (= x166 (= 0 x184)) (= (x43 x123 2) x141) (= (x69 (x30 x164)) x193) (= x129 (x127 (+ 31 x184))) (not (= x128 2376452955)) (= x177 x14) (= (ite (< x184 32) 1 0) x140) (= x150 (x153 1 x123)) (<= 0 x85) (= 0 x72) (= x158 x105) (< x128 3017275065) (= (x43 x129 32) x80) (and (< 3 x145) (= (>= 57896044618658097711785492504343953926634992332820282019728792003956564819967 x145) true)) (= 2514000705 x128) (not (< x128 2376452955)) (< 0 x193) (not (= 2495578189 x128)) (= x184 (ite (< 0 x150) x141 (x153 127 x141))) (= (x127 (+ x57 128)) x115))) (and (=> (and (= x46 x121) x166) x159) (=> (and (= x92 (< 31 x184)) (not x166)) (and (=> (and (not x92) (and (= x70 (x54 (* x93 256))) (= x93 (x43 x123 256)) (= x46 x121))) x159) (=> (and (and (= (x58 (x26 1) 0) x75) (= (x127 (+ x184 160)) x112) (= (x137 x75 1) x48) (= (> x112 192) x34) (= (x4 x75) x87)) x92) (and (=> (not x34) x11) (=> x34 x27))))))) x100))
(check-sat)
"#;

#[test]
fn certora_65782_reduction_publishes_a_confirmed_sat() {
    let commands = parse(CERTORA_65782_REDUCED).expect("valid SMT-LIB test input");
    let mut executor = Executor::new();
    let output = executor
        .execute_all(&commands)
        .expect("commands must execute");
    let verdict = output
        .iter()
        .rev()
        .map(|line| line.trim())
        .find(|line| matches!(*line, "sat" | "unsat" | "unknown"))
        .unwrap_or_default();
    assert_eq!(verdict, "sat", "output: {output:?}");
    assert_eq!(
        executor
            .statistics()
            .get_string("model_check_gate.result")
            .map(str::to_owned),
        Some("confirmed-sat".to_string()),
        "the published sat must carry the independent gate's confirmation"
    );
}
