// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::panic)]

//! Models of FP-to-Real formulas over a symbolic rounding mode (2026-09-30
//! FP verify, `invalid_model_fplra_symbolic_rm.smt2`).
//!
//! The FP-to-Real lane solves the FP circuit, then a Real subproblem with each
//! `fp.to_real` replaced by its value. That subproblem also chose the rounding
//! mode again, from the domain axioms alone, and get-model printed its choice
//! (`r = RNE`) beside an `x` computed under the circuit's mode (RTZ): a model
//! that falsifies the formula, while get-value printed RTZ. Every model here
//! is replayed: each printed constant is asserted back into the formula, which
//! must stay satisfiable.

use ntest::timeout;
use std::fmt::Write as _;

/// The top-level s-expressions of `text`.
fn items(text: &str) -> Vec<&str> {
    let mut out = Vec::new();
    let (mut depth, mut start) = (0usize, None);
    for (i, c) in text.char_indices() {
        match c {
            '(' => {
                if depth == 0 {
                    start = Some(i);
                }
                depth += 1;
            }
            ')' => {
                depth -= 1;
                if depth == 0 {
                    out.push(&text[start.take().unwrap_or(i)..=i]);
                }
            }
            c if depth == 0 && !c.is_whitespace() => {
                if start.is_none() {
                    start = Some(i);
                }
            }
            c if depth == 0 && c.is_whitespace() => {
                if let Some(s) = start.take() {
                    out.push(&text[s..i]);
                }
            }
            _ => {}
        }
    }
    if let Some(s) = start {
        out.push(&text[s..]);
    }
    out
}

/// `(name, value)` of every nullary `define-fun` in a get-model response.
fn model_constants(model: &str) -> Vec<(String, String)> {
    let body = model.trim().trim_start_matches('(').trim_end_matches(')');
    let body = body.trim_start().strip_prefix("model").unwrap_or(body);
    items(body)
        .into_iter()
        .filter_map(|def| {
            let inner = def.strip_prefix("(define-fun")?.strip_suffix(')')?;
            let parts = items(inner);
            match parts.as_slice() {
                [name, "()", _sort, value] => Some((name.to_string(), value.to_string())),
                _ => None,
            }
        })
        .collect()
}

/// Solve `formula`, print the model and `(get-value (<mode>))`, and replay the
/// model. Returns the printed mode.
fn solve_and_replay(formula: &str, mode: &str) -> String {
    let outputs = crate::common::solve_vec(&format!(
        "(set-option :produce-models true){formula}(check-sat)(get-model)(get-value ({mode}))"
    ));
    assert_eq!(
        outputs.first().map(String::as_str),
        Some("sat"),
        "{outputs:?}"
    );
    let constants = model_constants(&outputs[1]);
    let printed = constants
        .iter()
        .find(|(name, _)| name == mode)
        .map(|(_, value)| value.clone())
        .unwrap_or_else(|| panic!("no `{mode}` in the model: {outputs:?}"));
    assert_eq!(
        outputs[2],
        format!("(({mode} {printed}))"),
        "get-value must print the mode get-model prints"
    );
    let mut pins = String::new();
    for (name, value) in &constants {
        write!(&mut pins, "(assert (= {name} {value}))").expect("write to String");
    }
    let replay = crate::common::solve_vec(&format!("{formula}{pins}(check-sat)"));
    assert_eq!(
        replay.first().map(String::as_str),
        Some("sat"),
        "the printed model falsifies the formula: {}\n{pins}",
        outputs[1]
    );
    printed
}

const TO_FP_UNDER_R: &str = "(set-logic QF_FPLRA)
    (declare-const r RoundingMode)
    (declare-const x (_ FloatingPoint 4 5))
    (assert (= x ((_ to_fp 4 5) r (/ 7 3))))";

#[test]
#[timeout(60_000)]
fn fp_to_real_model_prints_the_mode_the_circuit_used() {
    // 7/3 rounds to 2.25 under RTZ and RTN, and to 2.375 under the other
    // three modes, so only RTZ and RTN satisfy the bound.
    let mode = solve_and_replay(
        &format!("{TO_FP_UNDER_R}(assert (< (fp.to_real x) (/ 7 3)))"),
        "r",
    );
    assert!(
        mode == "roundTowardZero" || mode == "roundTowardNegative",
        "{mode}"
    );
}

#[test]
#[timeout(60_000)]
fn folded_fp_to_real_model_prints_the_modes_the_circuit_used() {
    // The verifier's fold repro: two symbolic modes, one of them under an ite.
    solve_and_replay(
        "(set-logic QF_FPLRA)
         (declare-const r1 RoundingMode)
         (declare-const r2 RoundingMode)
         (declare-const b1 Bool)
         (declare-const b2 Bool)
         (declare-const x0 (_ FloatingPoint 3 4))
         (declare-const x1 (_ FloatingPoint 3 4))
         (assert (= x0 (fp.add r2 (fp.div r1 ((_ to_fp 3 4) (ite b1 r1 roundTowardPositive)
            (ite b1 (fp #b0 #b00000000 #b00011011010000010111110)
                    (fp #b1 #b01111110 #b11011011101101100101000))) (fp #b1 #b011 #b000))
            (fp.mul RNA (fp.abs (ite b1 (fp #b1 #b001 #b011) (fp #b0 #b011 #b110)))
                        (fp.add (ite b1 RTP RTP) (_ +zero 3 4) (fp #b0 #b000 #b000))))))
         (assert (fp.isNegative x0))
         (assert (= x1 (ite b2 (fp #b1 #b110 #b101) (fp #b1 #b000 #b111))))
         (assert (fp.isNormal x1))
         (assert (= (fp.to_real x1) (- (/ 13 1))))",
        "r1",
    );
}

#[test]
#[timeout(60_000)]
fn real_side_reading_the_mode_keeps_its_model() {
    // The Real side reads the mode: only RNE is allowed, and RNE gives 2.375.
    let mode = solve_and_replay(
        &format!("{TO_FP_UNDER_R}(assert (and (= r RNE) (< (fp.to_real x) 3.0)))"),
        "r",
    );
    assert_eq!(mode, "roundNearestTiesToEven");
}

#[test]
#[timeout(60_000)]
fn real_side_reading_the_mode_is_not_refuted_by_a_site_block() {
    // Only RNE satisfies the Real side. A circuit assignment (RTP, x = 2.375)
    // fails the Real subproblem because of its mode, not its value: a block
    // on x = 2.375 without the mode's bits would refute the witness
    // (RNE, 2.375) and answer unsat (z3: sat).
    let outputs = crate::common::solve_vec(&format!(
        "{TO_FP_UNDER_R}(assert (or (= r RNE) (> (fp.to_real x) 5.0)))
         (assert (> (fp.to_real x) 2.3))(check-sat)"
    ));
    assert_eq!(
        outputs.first().map(String::as_str),
        Some("sat"),
        "{outputs:?}"
    );
    let outputs = crate::common::solve_vec(&format!(
        "{TO_FP_UNDER_R}(assert (and (= r RNE) (< (fp.to_real x) 2.3)))(check-sat)"
    ));
    assert_ne!(
        outputs.first().map(String::as_str),
        Some("sat"),
        "{outputs:?}"
    );
}

/// The name and full text of every function (`define-fun` with parameters)
/// in a get-model response.
fn function_definitions(model: &str) -> Vec<(String, String)> {
    let body = model.trim().trim_start_matches('(').trim_end_matches(')');
    let body = body.trim_start().strip_prefix("model").unwrap_or(body);
    items(body)
        .into_iter()
        .filter_map(|def| {
            let inner = def.strip_prefix("(define-fun")?.strip_suffix(')')?;
            match items(inner).as_slice() {
                [name, params, ..] if *params != "()" => Some((name.to_string(), def.to_string())),
                _ => None,
            }
        })
        .collect()
}

const FIVE_MODES: [&str; 5] = [
    "roundNearestTiesToEven",
    "roundNearestTiesToAway",
    "roundTowardPositive",
    "roundTowardNegative",
    "roundTowardZero",
];

/// Solve `declarations` + `assertions` and replay the WHOLE printed model:
/// each printed function replaces its declaration, as z3 reads a model, and
/// each printed constant is asserted equal to its value. No printed value may
/// be a minted `@RoundingMode!n` element, which is not a value of the sort
/// (2026-09-30 FP verify 2: z3 rejects such a model). Returns the model.
fn solve_and_replay_whole_model(declarations: &str, assertions: &str) -> String {
    let outputs = crate::common::solve_vec(&format!(
        "(set-option :produce-models true)(set-logic ALL){declarations}{assertions}\
         (check-sat)(get-model)"
    ));
    assert_eq!(
        outputs.first().map(String::as_str),
        Some("sat"),
        "{outputs:?}"
    );
    let model = outputs[1].clone();
    assert!(
        !model.contains("@RoundingMode"),
        "a printed RoundingMode value must be one of the five modes: {model}"
    );
    let functions = function_definitions(&model);
    let mut replay = String::from("(set-logic ALL)");
    for declaration in items(declarations) {
        let function = functions.iter().find(|(name, _)| {
            declaration.starts_with(&format!("(declare-fun {name} ("))
                && !declaration.starts_with(&format!("(declare-fun {name} ()"))
        });
        replay.push_str(function.map_or(declaration, |(_, definition)| definition.as_str()));
    }
    replay.push_str(assertions);
    for (name, value) in model_constants(&model) {
        replay.push_str(&format!("(assert (= {name} {value}))"));
    }
    let replayed = crate::common::solve_vec(&format!("{replay}(check-sat)"));
    assert_eq!(
        replayed.first().map(String::as_str),
        Some("sat"),
        "the printed model falsifies the formula: {model}\n{replay}"
    );
    model
}

/// The verifier's repro (`abstract_rm_unused_constant.smt2`): `r2` occurs in
/// no assertion, the lane is FP-to-Real and a UF over RoundingMode is in
/// scope. The Real subproblem's EUF model named `r2`'s class
/// `@RoundingMode!1`, and get-model and get-value printed it.
const UNUSED_MODE_DECLARATIONS: &str = "(declare-const r1 RoundingMode)
    (declare-const r2 RoundingMode)
    (declare-const x (_ FloatingPoint 3 5))
    (declare-const q Real)
    (declare-fun g (RoundingMode) Int)";
const UNUSED_MODE_ASSERTIONS: &str = "(assert (< (fp.to_real x) (/ 89 3)))
    (assert (< q (/ 89 3)))
    (assert (distinct r1 RNE))";

#[test]
#[timeout(60_000)]
fn an_unused_mode_constant_prints_a_mode() {
    let mode = solve_and_replay(
        &format!("(set-logic ALL){UNUSED_MODE_DECLARATIONS}{UNUSED_MODE_ASSERTIONS}"),
        "r2",
    );
    assert!(FIVE_MODES.contains(&mode.as_str()), "{mode}");
    solve_and_replay_whole_model(UNUSED_MODE_DECLARATIONS, UNUSED_MODE_ASSERTIONS);
}

#[test]
#[timeout(60_000)]
fn a_uf_over_modes_prints_its_table_over_modes() {
    // `rmuf_930204_0012`: the Real subproblem sees `(g RTZ)` once the circuit
    // decides `r1`, while its EUF model still holds the stale `(g r1)` in a
    // minted class; the printed table was keyed by `@RoundingMode!0`. The row
    // must yield to the RTZ row the solve constrained, or `(= (g r1) i)`
    // breaks.
    solve_and_replay_whole_model(
        "(declare-const r1 RoundingMode)
         (declare-const r2 RoundingMode)
         (declare-const x (_ FloatingPoint 3 5))
         (declare-const y (_ FloatingPoint 3 5))
         (declare-const q Real)
         (declare-const i Int)
         (declare-const A (Array Int RoundingMode))
         (declare-fun k (Real) RoundingMode)
         (declare-fun g (RoundingMode) Int)",
        "(assert (= x ((_ to_fp 3 5) r1 (/ 49 10))))
         (assert (= q (fp.to_real x)))
         (assert (= (g r1) i))
         (assert (= y ((_ to_fp 3 5) r2 (/ 49 10))))",
    );
}

#[test]
#[timeout(60_000)]
fn an_array_of_modes_in_scope_keeps_every_mode_concrete() {
    // `rmuf_930201_0447`: an array of modes and UFs into and out of modes in
    // scope, `r2` unused.
    solve_and_replay_whole_model(
        "(declare-const r1 RoundingMode)
         (declare-const r2 RoundingMode)
         (declare-const x (_ FloatingPoint 3 5))
         (declare-const q Real)
         (declare-const A (Array Int RoundingMode))
         (declare-fun k (Real) RoundingMode)
         (declare-fun g (RoundingMode) Int)",
        "(assert (= x ((_ to_fp 3 5) r1 (/ 89 3))))
         (assert (< (fp.to_real x) (/ 89 3)))
         (assert (< q (/ 89 3)))
         (assert (distinct r1 RNE))",
    );
}

#[test]
#[timeout(60_000)]
fn a_mode_constant_beside_a_real_side_prints_its_class_mode() {
    // `preexisting_rm_value_0_0.smt2` without its unused FP constant (base
    // prints it too): the combined EUF+LRA lane merged LRA's value for `r1`
    // into its EUF entry, and get-model printed `r1 = |0.0|` under
    // `(distinct r1 RNE)`. (With the FP constant pinned, the replay is a
    // formula AY answers `unknown` on every build: FP and Real atoms side by
    // side with no conversion between them.)
    solve_and_replay_whole_model(
        "(declare-const r1 RoundingMode)
         (declare-const r2 RoundingMode)
         (declare-const q Real)
         (declare-fun g (RoundingMode) Int)",
        "(assert (< q (/ 89 3)))
         (assert (distinct r1 RNE))",
    );
}
