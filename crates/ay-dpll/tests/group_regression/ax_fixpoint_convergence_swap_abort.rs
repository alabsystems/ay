// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Process-abort regression: the Array+EUF lane must never trip its own
//! Nelson-Oppen convergence assertion on a decided input.
//!
//! On main c4cad0aa11 (2026-09-21) QF_AUFLIA
//! `swap_invalid_t1_pp_sf_ai_00010_002` (`:status sat`, z3 5.1.0 `sat` in
//! 0.007 s) aborted the solver process in every proof-free posture
//! (`--z3-mode`, `--no-proof`; the batteries-on default ran to the deadline
//! on a different search path):
//!
//! ```text
//! thread 'ay-smt-file' panicked at
//! crates/ay-dpll/src/combined_solvers/check_loops/result_protocol.rs:189:9:
//! BUG: AX fixpoint violation — sub-theory has 25 undrained equalities and
//! no conflict after Sat
//! ```
//!
//! The always-on assertion is right and stays: after the N-O loop declares
//! Sat, re-draining every sub-theory must yield nothing. The corpus refuted
//! it because `ArraySolver::propagate_equalities` was not a function of the
//! theory state — the #8785 "one representative select equality per (array
//! pair, index class)" bound skipped an already-sent pair BEFORE it consumed
//! the class slot, so every re-scan of an unchanged assignment elected one
//! more representative per class. The split-loop's post-SAT full check
//! (#5462 Packet 3) re-runs `check()` on exactly the state the extension's
//! check just accepted, `import_sent_equality_replays` drops the
//! `prop_eq_snapshot` short-circuit at the top of every `check()`, the
//! quiescent array epoch skips the loop's own drain, and the Sat-time
//! re-drain then found 25 "new" `same_array_read_congruence` equalities.
//! Fixed in `crates/ay-theories/arrays/src/propagation.rs`
//! (`note_index_class_covered`); the crate-level idempotence pins live in
//! `ay-arrays/src/tests/propagation_idempotence.rs`.
//!
//! The instance is embedded verbatim (PDPAR'05 crafted family; the
//! `:source` banner is dropped), so this pin needs no corpus. Greedy
//! assertion-level reduction kept the abort alive for 1 of 82 removals, so
//! the full 82-assertion instance is the reproducer. It asserts only what a
//! process abort denies: a verdict or an honest `unknown`. On today's tree
//! the search runs to the budget and answers `unknown`; a later throughput
//! change may turn that into `sat`, never `unsat`.

use std::time::Duration;

use ay_dpll::Executor;
use ay_frontend::parse;
use ntest::timeout;

const SWAP_INVALID_T1_PP_SF_AI_00010_002: &str = r#"
(set-logic QF_AUFLIA)
(set-info :status sat)
(declare-fun a_1054 () (Array Int Int))
(declare-fun a_1056 () (Array Int Int))
(declare-fun a_1058 () (Array Int Int))
(declare-fun a_1060 () (Array Int Int))
(declare-fun a_1062 () (Array Int Int))
(declare-fun a_1064 () (Array Int Int))
(declare-fun a_1066 () (Array Int Int))
(declare-fun a_1068 () (Array Int Int))
(declare-fun a_1070 () (Array Int Int))
(declare-fun a_1072 () (Array Int Int))
(declare-fun a_1074 () (Array Int Int))
(declare-fun a_1076 () (Array Int Int))
(declare-fun a_1078 () (Array Int Int))
(declare-fun a_1080 () (Array Int Int))
(declare-fun a_1082 () (Array Int Int))
(declare-fun a_1084 () (Array Int Int))
(declare-fun a_1086 () (Array Int Int))
(declare-fun a_1088 () (Array Int Int))
(declare-fun a_1090 () (Array Int Int))
(declare-fun a_1092 () (Array Int Int))
(declare-fun a_1093 () (Array Int Int))
(declare-fun a_1094 () (Array Int Int))
(declare-fun a_1096 () (Array Int Int))
(declare-fun a_1098 () (Array Int Int))
(declare-fun a_1100 () (Array Int Int))
(declare-fun a_1102 () (Array Int Int))
(declare-fun a_1104 () (Array Int Int))
(declare-fun a_1106 () (Array Int Int))
(declare-fun a_1108 () (Array Int Int))
(declare-fun a_1110 () (Array Int Int))
(declare-fun a_1112 () (Array Int Int))
(declare-fun a_1114 () (Array Int Int))
(declare-fun a_1116 () (Array Int Int))
(declare-fun a_1118 () (Array Int Int))
(declare-fun a_1120 () (Array Int Int))
(declare-fun a_1122 () (Array Int Int))
(declare-fun a_1124 () (Array Int Int))
(declare-fun a_1126 () (Array Int Int))
(declare-fun a_1128 () (Array Int Int))
(declare-fun a_1130 () (Array Int Int))
(declare-fun e_1053 () Int)
(declare-fun e_1055 () Int)
(declare-fun e_1057 () Int)
(declare-fun e_1059 () Int)
(declare-fun e_1061 () Int)
(declare-fun e_1063 () Int)
(declare-fun e_1065 () Int)
(declare-fun e_1067 () Int)
(declare-fun e_1069 () Int)
(declare-fun e_1071 () Int)
(declare-fun e_1073 () Int)
(declare-fun e_1075 () Int)
(declare-fun e_1077 () Int)
(declare-fun e_1079 () Int)
(declare-fun e_1081 () Int)
(declare-fun e_1083 () Int)
(declare-fun e_1085 () Int)
(declare-fun e_1087 () Int)
(declare-fun e_1089 () Int)
(declare-fun e_1091 () Int)
(declare-fun e_1095 () Int)
(declare-fun e_1097 () Int)
(declare-fun e_1099 () Int)
(declare-fun e_1101 () Int)
(declare-fun e_1103 () Int)
(declare-fun e_1105 () Int)
(declare-fun e_1107 () Int)
(declare-fun e_1109 () Int)
(declare-fun e_1111 () Int)
(declare-fun e_1113 () Int)
(declare-fun e_1115 () Int)
(declare-fun e_1117 () Int)
(declare-fun e_1119 () Int)
(declare-fun e_1121 () Int)
(declare-fun e_1123 () Int)
(declare-fun e_1125 () Int)
(declare-fun e_1127 () Int)
(declare-fun e_1129 () Int)
(declare-fun e_1132 () Int)
(declare-fun e_1133 () Int)
(declare-fun i_1131 () Int)
(declare-fun a1 () (Array Int Int))
(declare-fun i0 () Int)
(declare-fun i1 () Int)
(declare-fun i2 () Int)
(declare-fun i3 () Int)
(declare-fun i4 () Int)
(declare-fun i5 () Int)
(declare-fun i6 () Int)
(declare-fun i7 () Int)
(declare-fun i8 () Int)
(declare-fun i9 () Int)
(declare-fun sk ((Array Int Int) (Array Int Int)) Int)
(assert (= a_1054 (store a1 i3 e_1053)))
(assert (= a_1056 (store a_1054 i9 e_1055)))
(assert (= a_1058 (store a_1056 i2 e_1057)))
(assert (= a_1060 (store a_1058 i7 e_1059)))
(assert (= a_1062 (store a_1060 i0 e_1061)))
(assert (= a_1064 (store a_1062 i2 e_1063)))
(assert (= a_1066 (store a_1064 i8 e_1065)))
(assert (= a_1068 (store a_1066 i9 e_1067)))
(assert (= a_1070 (store a_1068 i6 e_1069)))
(assert (= a_1072 (store a_1070 i3 e_1071)))
(assert (= a_1074 (store a_1072 i7 e_1073)))
(assert (= a_1076 (store a_1074 i9 e_1075)))
(assert (= a_1078 (store a_1076 i5 e_1077)))
(assert (= a_1080 (store a_1078 i1 e_1079)))
(assert (= a_1082 (store a_1080 i6 e_1081)))
(assert (= a_1084 (store a_1082 i4 e_1083)))
(assert (= a_1086 (store a_1084 i0 e_1085)))
(assert (= a_1088 (store a_1086 i3 e_1087)))
(assert (= a_1090 (store a_1088 i8 e_1089)))
(assert (= a_1092 (store a_1090 i3 e_1091)))
(assert (= a_1093 (store a1 i9 e_1055)))
(assert (= a_1094 (store a_1093 i3 e_1053)))
(assert (= a_1096 (store a_1094 i2 e_1095)))
(assert (= a_1098 (store a_1096 i7 e_1097)))
(assert (= a_1100 (store a_1098 i2 e_1099)))
(assert (= a_1102 (store a_1100 i0 e_1101)))
(assert (= a_1104 (store a_1102 i9 e_1103)))
(assert (= a_1106 (store a_1104 i8 e_1105)))
(assert (= a_1108 (store a_1106 i6 e_1107)))
(assert (= a_1110 (store a_1108 i3 e_1109)))
(assert (= a_1112 (store a_1110 i9 e_1111)))
(assert (= a_1114 (store a_1112 i7 e_1113)))
(assert (= a_1116 (store a_1114 i1 e_1115)))
(assert (= a_1118 (store a_1116 i5 e_1117)))
(assert (= a_1120 (store a_1118 i6 e_1119)))
(assert (= a_1122 (store a_1120 i4 e_1121)))
(assert (= a_1124 (store a_1122 i3 e_1123)))
(assert (= a_1126 (store a_1124 i0 e_1125)))
(assert (= a_1128 (store a_1126 i9 e_1127)))
(assert (= a_1130 (store a_1128 i3 e_1129)))
(assert (= e_1053 (select a1 i9)))
(assert (= e_1055 (select a1 i3)))
(assert (= e_1057 (select a_1056 i7)))
(assert (= e_1059 (select a_1056 i2)))
(assert (= e_1061 (select a_1060 i2)))
(assert (= e_1063 (select a_1060 i0)))
(assert (= e_1065 (select a_1064 i9)))
(assert (= e_1067 (select a_1064 i8)))
(assert (= e_1069 (select a_1068 i3)))
(assert (= e_1071 (select a_1068 i6)))
(assert (= e_1073 (select a_1072 i9)))
(assert (= e_1075 (select a_1072 i7)))
(assert (= e_1077 (select a_1076 i1)))
(assert (= e_1079 (select a_1076 i5)))
(assert (= e_1081 (select a_1080 i4)))
(assert (= e_1083 (select a_1080 i6)))
(assert (= e_1085 (select a_1084 i3)))
(assert (= e_1087 (select a_1084 i0)))
(assert (= e_1089 (select a_1088 i3)))
(assert (= e_1091 (select a_1088 i8)))
(assert (= e_1095 (select a_1094 i7)))
(assert (= e_1097 (select a_1094 i2)))
(assert (= e_1099 (select a_1098 i0)))
(assert (= e_1101 (select a_1098 i2)))
(assert (= e_1103 (select a_1102 i8)))
(assert (= e_1105 (select a_1102 i9)))
(assert (= e_1107 (select a_1106 i3)))
(assert (= e_1109 (select a_1106 i6)))
(assert (= e_1111 (select a_1110 i7)))
(assert (= e_1113 (select a_1110 i9)))
(assert (= e_1115 (select a_1114 i5)))
(assert (= e_1117 (select a_1114 i1)))
(assert (= e_1119 (select a_1118 i4)))
(assert (= e_1121 (select a_1118 i6)))
(assert (= e_1123 (select a_1122 i0)))
(assert (= e_1125 (select a_1122 i3)))
(assert (= e_1127 (select a_1126 i3)))
(assert (= e_1129 (select a_1126 i9)))
(assert (= e_1132 (select a_1092 i_1131)))
(assert (= e_1133 (select a_1130 i_1131)))
(assert (= i_1131 (sk a_1092 a_1130)))
(assert (not (= e_1132 e_1133)))
(check-sat)"#;

#[test]
#[timeout(180_000)]
fn ax_lane_swap_00010_002_answers_or_says_unknown_never_aborts() {
    let commands = parse(SWAP_INVALID_T1_PP_SF_AI_00010_002)
        .unwrap_or_else(|err| panic!("parse failed: {err}"));
    let mut exec = Executor::new();
    // The CLI's `--no-proof` / `--z3-mode` posture: shed the internal proof
    // cycle. The abort is path-dependent and fired only there — the proof
    // cycle changes the SAT search, and with it the state the combiner's
    // post-SAT full check re-drains. Measured 2026-09-21: this executor with
    // the default (batteries-on) posture ran the file to its budget on the
    // parent of the fix; with the shed posture it aborted at the site above.
    exec.set_competition_mode(true);
    // The abort fired 1.1 s into the search on an idle machine; the budget
    // leaves room for a loaded one and bounds the honest-`unknown` outcome.
    exec.set_timeout(Some(Duration::from_secs(20)));
    exec.set_memory_limit(Some(8 << 30));
    // A panic inside the solver propagates out of `execute_all` and fails
    // this test at the site that fired — that is the regression this pins.
    let outputs = exec
        .execute_all(&commands)
        .unwrap_or_else(|err| panic!("execution failed: {err}"));
    let verdict = outputs.last().cloned().unwrap_or_default();
    assert!(
        verdict == "sat" || verdict == "unknown",
        "the file declares :status sat and z3 5.1.0 answers sat; AY answered {verdict:?}"
    );
}
