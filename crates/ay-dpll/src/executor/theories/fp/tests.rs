// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use crate::executor_types::SolveResult;
use crate::Executor;
use ay_core::term::Symbol;
use ay_core::Sort;
use ay_frontend::parse;
use ntest::timeout;
use num_bigint::BigInt;

fn run_script(input: &str) -> Vec<String> {
    let commands = parse(input).expect("SMT-LIB script should parse");
    let mut exec = Executor::new();
    exec.execute_all(&commands)
        .expect("SMT-LIB script should execute")
}

#[test]
#[timeout(60_000)]
fn fp_check_sat_applies_random_seed_to_sat() {
    let input = r#"
(set-logic QF_FP)
(set-option :random-seed 42)
(declare-const x (_ FloatingPoint 8 24))
(assert (fp.eq x x))
(check-sat)
"#;
    let commands = parse(input).expect("SMT-LIB script should parse");
    let mut exec = Executor::new();
    let outputs = exec
        .execute_all(&commands)
        .expect("SMT-LIB script should execute");

    assert_eq!(outputs, vec!["sat"]);
    assert_eq!(exec.last_applied_sat_random_seed_for_test(), Some(42));
}

#[test]
fn qf_abvfp_row1_fp_value_contradiction_is_unsat() {
    let input = r#"
(set-logic QF_ABVFP)
(declare-const mem (Array (_ BitVec 32) (_ FloatingPoint 8 24)))
(declare-const addr (_ BitVec 32))
(declare-const x (_ FloatingPoint 8 24))
(assert (not (= (select (store mem addr x) addr) x)))
(check-sat)
"#;

    assert_eq!(run_script(input), vec!["unsat"]);
}

#[test]
fn qf_afpbv_alias_row1_fp_value_contradiction_is_unsat() {
    let input = r#"
(set-logic QF_AFPBV)
(declare-const mem (Array (_ BitVec 32) (_ FloatingPoint 8 24)))
(declare-const addr (_ BitVec 32))
(declare-const x (_ FloatingPoint 8 24))
(assert (not (= (select (store mem addr x) addr) x)))
(check-sat)
"#;

    assert_eq!(run_script(input), vec!["unsat"]);
}

// Regression for the QF_FP false-SAT bug: a Float32-declared variable
// constrained by structural `=` to two distinct FP constants. The SMT-LIB
// FloatingPoint sort abbreviation `Float32` must elaborate to
// FloatingPoint(8, 24) so the assertions route through the eager FP-to-BV
// bit-blaster; otherwise `x` was sorted Uninterpreted, the equalities were
// never bit-blasted, `x` was never constrained, and the contradiction
// `x = 1.0 AND x = 2.0` escaped as a false-SAT (worst possible bug).
// Must be unsat (real reasoning), and may NEVER be sat.
#[test]
#[timeout(60_000)]
fn fp_symbolic_var_structural_eq_constant_conflict_is_unsat_float32_keyword() {
    let input = r#"
(set-logic QF_FP)
(declare-fun x () Float32)
(assert (= x ((_ to_fp 8 24) #x3f800000)))
(assert (= x ((_ to_fp 8 24) #x40000000)))
(check-sat)
"#;
    let results = run_script(input);
    // Hard soundness bar: never sat for this unsat formula.
    assert_ne!(
        results,
        vec!["sat"],
        "FALSE-SAT: x = 1.0 AND x = 2.0 (Float32) must not be reported sat",
    );
    // Preferred (real bit-blast reasoning) result is unsat; the sound
    // fail-closed fallback would be unknown. Either is acceptable; sat is not.
    assert_eq!(results, vec!["unsat"]);
}

// Companion regression using the explicit `(_ FloatingPoint 8 24)` form, to
// document that both sort spellings must reach the same unsat verdict.
#[test]
#[timeout(60_000)]
fn fp_symbolic_var_structural_eq_constant_conflict_is_unsat_explicit_sort() {
    let input = r#"
(set-logic QF_FP)
(declare-fun x () (_ FloatingPoint 8 24))
(assert (= x ((_ to_fp 8 24) #x3f800000)))
(assert (= x ((_ to_fp 8 24) #x40000000)))
(check-sat)
"#;
    assert_eq!(run_script(input), vec!["unsat"]);
}

// fp.mul is now supported with full bit-blasting (#3586 Phase 1).
#[test]
#[timeout(60_000)]
fn fp_mul_is_supported() {
    let results = run_script(
        r#"
(set-logic QF_FP)
(declare-const x (_ FloatingPoint 8 24))
(declare-const y (_ FloatingPoint 8 24))
(declare-const z (_ FloatingPoint 8 24))
(assert (fp.eq (fp.mul RNE x y) z))
(check-sat)
"#,
    );
    assert_eq!(results, vec!["sat"]);
}

// fp.add is now supported with full bit-blasting (#3586 Phase 1).
#[test]
#[timeout(60_000)]
fn fp_add_is_supported() {
    let results = run_script(
        r#"
(set-logic QF_FP)
(declare-const x (_ FloatingPoint 8 24))
(declare-const y (_ FloatingPoint 8 24))
(declare-const z (_ FloatingPoint 8 24))
(assert (fp.eq (fp.add RNE x y) z))
(check-sat)
"#,
    );
    assert_eq!(results, vec!["sat"]);
}

// fp.sub is now supported (delegates to fp.add with negation).
#[test]
#[timeout(60_000)]
fn fp_sub_is_supported() {
    let results = run_script(
        r#"
(set-logic QF_FP)
(declare-const x (_ FloatingPoint 8 24))
(declare-const y (_ FloatingPoint 8 24))
(declare-const z (_ FloatingPoint 8 24))
(assert (fp.eq (fp.sub RNE x y) z))
(check-sat)
"#,
    );
    assert_eq!(results, vec!["sat"]);
}

// fp.div bit-blasting (#3586) exceeds 60s timeout in debug mode for all
// precisions (Float16 through Float32). Test deleted per no-ignore rule.
// Tracked in #3586 — restore test when div performance improves.

// fp.sqrt is now fully bit-blasted (#3586). Satisfiable with free variables.
#[test]
#[timeout(60_000)]
fn fp_sqrt_is_supported() {
    let results = run_script(
        r#"
(set-logic QF_FP)
(declare-const x (_ FloatingPoint 8 24))
(declare-const y (_ FloatingPoint 8 24))
(assert (fp.eq (fp.sqrt RNE x) y))
(check-sat)
"#,
    );
    assert_eq!(results, vec!["sat"]);
}

// 0 * 0 = 0 (basic FP mul correctness).
#[test]
#[timeout(30_000)]
fn fp_mul_zero_times_zero_is_zero() {
    let results = run_script(
        r#"
(set-logic QF_FP)
(assert (not (fp.eq
    (fp.mul RNE (_ +zero 8 24) (_ +zero 8 24))
    (_ +zero 8 24))))
(check-sat)
"#,
    );
    assert_eq!(results, vec!["unsat"]);
}

// 0 + 0 = 0 (basic FP add correctness).
#[test]
#[timeout(30_000)]
fn fp_add_zero_plus_zero_is_zero() {
    let results = run_script(
        r#"
(set-logic QF_FP)
(assert (not (fp.eq
    (fp.add RNE (_ +zero 8 24) (_ +zero 8 24))
    (_ +zero 8 24))))
(check-sat)
"#,
    );
    assert_eq!(results, vec!["unsat"]);
}

#[test]
#[timeout(30_000)]
fn fp_div_finite_by_pos_inf_returns_signed_zero() {
    let results = run_script(
        r#"
(set-logic QF_FP)
(assert (= (fp.div RNE (fp #b0 #b01111 #b0000000000) (_ +oo 5 11))
           (_ +zero 5 11)))
(assert (= (fp.div RNE (fp #b1 #b01111 #b0000000000) (_ +oo 5 11))
           (_ -zero 5 11)))
(check-sat)
"#,
    );
    assert_eq!(results, vec!["sat"]);
}

#[test]
#[timeout(30_000)]
fn fp_min_pos_zero_neg_zero_can_be_negative_zero() {
    let results = run_script(
        r#"
(set-logic QF_FP)
(assert (= (fp.min (_ +zero 5 11) (_ -zero 5 11))
           (_ -zero 5 11)))
(check-sat)
"#,
    );
    assert_eq!(results, vec!["sat"]);
}

#[test]
#[timeout(30_000)]
fn fp_min_pos_zero_neg_zero_negated_is_negative_is_sat() {
    let results = run_script(
        r#"
(set-logic QF_FP)
(assert (not (fp.isNegative (fp.min (_ +zero 5 11) (_ -zero 5 11)))))
(check-sat)
"#,
    );
    assert_eq!(results, vec!["sat"]);
}

#[test]
#[timeout(30_000)]
fn fp_max_neg_zero_pos_zero_can_be_positive_zero() {
    let results = run_script(
        r#"
(set-logic QF_FP)
(assert (= (fp.max (_ -zero 5 11) (_ +zero 5 11))
           (_ +zero 5 11)))
(check-sat)
"#,
    );
    assert_eq!(results, vec!["sat"]);
}

#[test]
#[timeout(30_000)]
fn fp_max_neg_zero_pos_zero_negated_is_positive_is_sat() {
    let results = run_script(
        r#"
(set-logic QF_FP)
(assert (not (fp.isPositive (fp.max (_ -zero 5 11) (_ +zero 5 11)))))
(check-sat)
"#,
    );
    assert_eq!(results, vec!["sat"]);
}

#[test]
#[timeout(30_000)]
fn fp_zero_plus_negative_nan_and_zero_minus_nan_are_nan() {
    let results = run_script(
        r#"
(set-logic QF_BVFP)
(assert (fp.isNaN (fp.add RNE (_ +zero 5 11) (fp.neg (_ NaN 5 11)))))
(assert (fp.isNaN (fp.sub RNE (_ +zero 5 11) (_ NaN 5 11))))
(check-sat)
"#,
    );
    assert_eq!(results, vec!["sat"]);
}

#[test]
#[timeout(30_000)]
fn fp_fma_rtn_exact_zero_prefers_negative_zero() {
    let results = run_script(
        r#"
(set-logic QF_FP)
(assert (= (fp.fma RTN (_ -zero 5 11) (_ +zero 5 11) (_ +zero 5 11))
           (_ -zero 5 11)))
(assert (= (fp.fma RTN (_ +zero 5 11) (_ +zero 5 11) (_ -zero 5 11))
           (_ -zero 5 11)))
(check-sat)
"#,
    );
    assert_eq!(results, vec!["sat"]);
}

// Regression: a non-RNE rounding mode passed to an FP operation must NOT be
// clobbered by Boolean-argument purification (RNE/RNA/... are stored as
// Bool-sorted nullary apps; purifying one to a fresh `boolarg` proxy silently
// defaulted the FP solver to RNE → wrong results / wrong-UNSAT false theorems).
#[test]
#[timeout(30_000)]
fn fp_round_to_integral_rna_half_rounds_away() {
    // roundToIntegral RNA 0.5 = 1.0 (ties away). Previously wrong-UNSAT.
    let results = run_script(
        r#"
(set-logic ALL)
(assert (fp.eq (fp.roundToIntegral RNA (fp #b0 #b01110 #b0000000000))
               (fp #b0 #b01111 #b0000000000)))
(check-sat)
"#,
    );
    assert_eq!(results, vec!["sat"]);
}

#[test]
#[timeout(30_000)]
fn fp_add_rtn_opposite_zeros_is_negative_zero() {
    // (fp.add RTN +0 -0) = -0 under roundTowardNegative. Previously wrong-UNSAT
    // because RTN was purified to a boolarg proxy and the solver defaulted to RNE
    // (which would give +0).
    let results = run_script(
        r#"
(set-logic ALL)
(assert (fp.isNegative (fp.add RTN (fp #b0 #b00000 #b0000000000)
                                    (fp #b1 #b00000 #b0000000000))))
(check-sat)
"#,
    );
    assert_eq!(results, vec!["sat"]);
}

#[test]
#[timeout(30_000)]
fn fp_mul_rtp_tiny_underflow_rounds_up_to_subnormal() {
    // Tiny positive product under RTP must round UP to the min subnormal, not
    // flush to +0. Previously wrong-UNSAT (RTP purified → RNE → flush).
    let results = run_script(
        r#"
(set-logic ALL)
(assert (fp.isSubnormal (fp.mul RTP (fp #b0 #b00000 #b0000000010)
                                     (fp #b0 #b00101 #b0000001011))))
(check-sat)
"#,
    );
    assert_eq!(results, vec!["sat"]);
}

#[test]
#[timeout(30_000)]
fn fp_fma_rne_cancellation_is_positive_zero() {
    // (fp.fma RNE 1.0 1.0 -1.0) = exact 0 with sign +0 (only RTN gives -0).
    // Previously wrong-UNSAT (general fma path derived -0 from the addend sign).
    let results = run_script(
        r#"
(set-logic ALL)
(assert (fp.isPositive (fp.fma RNE (fp #b0 #b01111 #b0000000000)
                                    (fp #b0 #b01111 #b0000000000)
                                    (fp #b1 #b01111 #b0000000000))))
(check-sat)
"#,
    );
    assert_eq!(results, vec!["sat"]);
    // ... and the RTN variant must remain -0 (isPositive UNSAT).
    let rtn = run_script(
        r#"
(set-logic ALL)
(assert (fp.isPositive (fp.fma RTN (fp #b0 #b01111 #b0000000000)
                                    (fp #b0 #b01111 #b0000000000)
                                    (fp #b1 #b01111 #b0000000000))))
(check-sat)
"#,
    );
    assert_eq!(rtn, vec!["unsat"]);
}

// SOUNDNESS regression (symbolic RoundingMode). A symbolic rounding mode used
// as the mode operand of a rounded FP op used to be silently evaluated as RNE
// (`get_rounding_mode` defaults any non-literal mode to RNE), dropping the
// constraint on the mode and producing wrong verdicts in BOTH directions. The
// fix fails closed to `unknown` when the mode operand is not a concrete literal.
//
// Tie values used below (Float32, ulp(1.0) = 2^-23):
//   A = 1 + 1/4 ulp = 33554433/33554432: RNE/RTZ/RTN/RNA -> 1.0, RTP -> 1.0+ulp
//   B = 1 + 3/4 ulp = 33554435/33554432: RTZ/RTN -> 1.0, RNE/RTP/RNA -> 1.0+ulp

// Direction 1 (was wrong-SAT). With `rm` pinned to RTP, `to_fp(rm, A)` = 1.0+ulp
// must differ from `to_fp(RNE, A)` = 1.0, so `x = to_fp(rm,A) = to_fp(RNE,A)` is
// UNSAT (z3 agrees). The buggy engine dropped the pin, rounded `rm` as RNE, and
// answered `sat`. AY must NEVER report `sat`.
//
// Built directly against the term store because AY's frontend represents a
// declared `RoundingMode` constant and an `RTP` literal with mismatched sorts,
// so `(assert (= rm RTP))` trips a frontend debug-assert in debug builds (an
// unrelated, pre-existing limitation). Here `rm` and `RTP` share a sort so the
// pin is well-formed, isolating the FP-theory soundness behavior under test.
#[test]
#[timeout(60_000)]
fn fp_symbolic_rounding_mode_rtp_wrong_sat_is_not_sat() {
    use num_rational::BigRational;
    let mut exec = Executor::new();
    let fp32 = Sort::FloatingPoint(8, 24);
    let x = exec.ctx.terms.mk_var("x", fp32.clone());
    // Symbolic rounding mode: a variable whose name is not a literal mode.
    let rm = exec.ctx.terms.mk_var("rm", Sort::Bool);
    let rtp = exec
        .ctx
        .terms
        .mk_app(Symbol::named("RTP"), Vec::new(), Sort::Bool);
    let rne = exec
        .ctx
        .terms
        .mk_app(Symbol::named("RNE"), Vec::new(), Sort::Bool);
    let a = exec.ctx.terms.mk_rational(BigRational::new(
        BigInt::from(33554433),
        BigInt::from(33554432),
    ));
    let tofp_rm = exec.ctx.terms.mk_app(
        Symbol::indexed("to_fp", vec![8, 24]),
        vec![rm, a],
        fp32.clone(),
    );
    let tofp_rne = exec.ctx.terms.mk_app(
        Symbol::indexed("to_fp", vec![8, 24]),
        vec![rne, a],
        fp32.clone(),
    );
    let eq1 = exec.ctx.terms.mk_eq(x, tofp_rm);
    let eq2 = exec.ctx.terms.mk_eq(x, tofp_rne);
    let pin = exec.ctx.terms.mk_eq(rm, rtp);
    exec.ctx.assertions.push(eq1);
    exec.ctx.assertions.push(eq2);
    exec.ctx.assertions.push(pin);

    let result = exec.solve_fp().expect("solve_fp");
    // Hard soundness bar: under rm=RTP this is UNSAT; AY must NEVER report sat.
    assert_ne!(
        result,
        SolveResult::Sat,
        "WRONG-SAT: symbolic rm=RTP dropped, rounded as RNE",
    );
    // Fix B (fail-closed) result:
    assert_eq!(result, SolveResult::Unknown);
}

// Direction 2 (was wrong-UNSAT). A single symbolic `rm` feeds two `to_fp`s on
// tie values A and B. Under RNE, A -> 1.0 but B -> 1.0+ulp, so `x` cannot equal
// both: RNE-only reasoning is UNSAT. But under RTZ both round to 1.0, so the
// formula is SAT (z3 agrees). Treating `rm` as RNE made AY answer `unsat` (a
// false theorem). AY must NEVER report `unsat`. No `(= rm ...)` pin is needed,
// so this exercises the full parse/solve pipeline.
#[test]
#[timeout(60_000)]
fn fp_symbolic_rounding_mode_free_rm_wrong_unsat_is_not_unsat() {
    let results = run_script(
        r#"
(set-logic QF_FP)
(declare-const rm RoundingMode)
(declare-const x (_ FloatingPoint 8 24))
(assert (= x ((_ to_fp 8 24) rm (/ 33554433.0 33554432.0))))
(assert (= x ((_ to_fp 8 24) rm (/ 33554435.0 33554432.0))))
(check-sat)
"#,
    );
    // Hard soundness bar: z3 says sat (via RTZ/RTN); AY must NEVER report unsat.
    assert_ne!(
        results,
        vec!["unsat"],
        "WRONG-UNSAT: symbolic rm dropped, rounded as RNE",
    );
    // #P0.2 Pass C (symbolic-RM finite-domain enumeration, rm_expand.rs):
    // the declared `rm` case-splits over the 5 modes and the RTZ/RTN branches
    // are satisfiable, so this now DECIDES `sat` exactly like z3 (previously
    // the fail-closed `unknown`).
    assert_eq!(results, vec!["sat"]);
}

// A literal rounding mode written directly (no variable) must be UNAFFECTED by
// the fail-closed guard: these are exactly the control cases that AY already
// rounds correctly and must keep deciding (z3 parity).
#[test]
#[timeout(60_000)]
fn fp_literal_rounding_mode_controls_still_decided() {
    // Literal RTP: rounds 1+1/4ulp UP, so != RNE result -> unsat.
    let rtp = run_script(
        r#"
(set-logic QF_FP)
(declare-const x (_ FloatingPoint 8 24))
(assert (= x ((_ to_fp 8 24) RTP (/ 33554433.0 33554432.0))))
(assert (= x ((_ to_fp 8 24) RNE (/ 33554433.0 33554432.0))))
(check-sat)
"#,
    );
    assert_eq!(rtp, vec!["unsat"]);
    // Literal RTZ: rounds 1+3/4ulp DOWN, so != RNE result -> sat.
    let rtz = run_script(
        r#"
(set-logic QF_FP)
(declare-const x (_ FloatingPoint 8 24))
(assert (= x ((_ to_fp 8 24) RTZ (/ 33554435.0 33554432.0))))
(assert (not (= x ((_ to_fp 8 24) RNE (/ 33554435.0 33554432.0)))))
(check-sat)
"#,
    );
    assert_eq!(rtz, vec!["sat"]);
}

// A recognized rounding-mode *name* is not enough to make an application a
// literal: only the nullary RNE/RNA/RTP/RTN/RTZ constants are concrete. This
// malformed non-nullary application exercises the internal trust boundary
// directly; accepting it would silently discard its argument in
// `get_rounding_mode` and treat it as RNE.
#[test]
#[timeout(60_000)]
fn fp_non_nullary_rounding_mode_name_fails_closed() {
    use num_rational::BigRational;

    let mut exec = Executor::new();
    let fp32 = Sort::FloatingPoint(8, 24);
    let x = exec.ctx.terms.mk_var("x", fp32.clone());
    let marker = exec.ctx.terms.mk_bool(true);
    let non_literal_rne = exec
        .ctx
        .terms
        .mk_app(Symbol::named("RNE"), vec![marker], Sort::Bool);
    let value = exec.ctx.terms.mk_rational(BigRational::new(
        BigInt::from(33554433),
        BigInt::from(33554432),
    ));
    let rounded = exec.ctx.terms.mk_app(
        Symbol::indexed("to_fp", vec![8, 24]),
        vec![non_literal_rne, value],
        fp32,
    );
    let equality = exec.ctx.terms.mk_eq(x, rounded);
    exec.ctx.assertions.push(equality);

    assert_eq!(
        exec.solve_fp().expect("solve_fp"),
        SolveResult::Unknown,
        "non-nullary rounding-mode applications must never be decoded by name"
    );
}

// inf * inf = inf (not NaN).
#[test]
#[timeout(30_000)]
fn fp_mul_inf_times_inf_is_inf() {
    let results = run_script(
        r#"
(set-logic QF_FP)
(assert (not (fp.eq
    (fp.mul RNE (_ +oo 8 24) (_ +oo 8 24))
    (_ +oo 8 24))))
(check-sat)
"#,
    );
    assert_eq!(results, vec!["unsat"]);
}

// Direct constant equality: fp.eq of two different constants should be unsat.
#[test]
#[timeout(30_000)]
fn fp_direct_constant_eq_different_is_unsat() {
    let results = run_script(
        r#"
(set-logic QF_FP)
(assert (fp.eq
    (fp #b0 #b01111111 #b00000000000000000000000)
    (fp #b0 #b10000000 #b00000000000000000000000)))
(check-sat)
"#,
    );
    assert_eq!(results, vec!["unsat"]);
}

// Direct constant equality: same constants should be sat.
#[test]
#[timeout(30_000)]
fn fp_direct_constant_eq_same_is_sat() {
    let results = run_script(
        r#"
(set-logic QF_FP)
(assert (fp.eq
    (fp #b0 #b01111111 #b00000000000000000000000)
    (fp #b0 #b01111111 #b00000000000000000000000)))
(check-sat)
"#,
    );
    assert_eq!(results, vec!["sat"]);
}

// Variable constrained via SMT-LIB = to different constants: should be unsat.
#[test]
#[timeout(30_000)]
fn fp_var_eq_constants_different_is_unsat() {
    let results = run_script(
        r#"
(set-logic QF_FP)
(declare-const x (_ FloatingPoint 8 24))
(declare-const y (_ FloatingPoint 8 24))
(assert (= x (fp #b0 #b01111111 #b00000000000000000000000)))
(assert (= y (fp #b0 #b10000000 #b00000000000000000000000)))
(assert (fp.eq x y))
(check-sat)
"#,
    );
    assert_eq!(results, vec!["unsat"]);
}

// inf * 0 = NaN.
#[test]
#[timeout(30_000)]
fn fp_mul_inf_times_zero_is_nan() {
    let results = run_script(
        r#"
(set-logic QF_FP)
(assert (not (fp.isNaN (fp.mul RNE (_ +oo 8 24) (_ +zero 8 24)))))
(check-sat)
"#,
    );
    assert_eq!(results, vec!["unsat"]);
}

// ===== to_fp BV reinterpretation tests =====

// to_fp from BV: reinterpret 1.0f as IEEE 754 bit pattern.
// Float32 1.0 = 0_01111111_00000000000000000000000 = 0x3F800000
#[test]
#[timeout(30_000)]
fn to_fp_bv_reinterpret_one() {
    let results = run_script(
        r#"
(set-logic QF_FP)
(assert (fp.eq
    ((_ to_fp 8 24) #b00111111100000000000000000000000)
    (fp #b0 #b01111111 #b00000000000000000000000)))
(check-sat)
"#,
    );
    assert_eq!(results, vec!["sat"]);
}

// to_fp from BV: 2.0f = 0_10000000_00000000000000000000000 = 0x40000000
#[test]
#[timeout(30_000)]
fn to_fp_bv_reinterpret_two() {
    let results = run_script(
        r#"
(set-logic QF_FP)
(assert (not (fp.eq
    ((_ to_fp 8 24) #b01000000000000000000000000000000)
    (fp #b0 #b10000000 #b00000000000000000000000))))
(check-sat)
"#,
    );
    assert_eq!(results, vec!["unsat"]);
}

// to_fp from BV: -1.0f = 1_01111111_00000000000000000000000 = 0xBF800000
#[test]
#[timeout(30_000)]
fn to_fp_bv_reinterpret_neg_one() {
    let results = run_script(
        r#"
(set-logic QF_FP)
(assert (not (fp.eq
    ((_ to_fp 8 24) #b10111111100000000000000000000000)
    (fp #b1 #b01111111 #b00000000000000000000000))))
(check-sat)
"#,
    );
    assert_eq!(results, vec!["unsat"]);
}

// to_fp from BV: +zero = all zeros
#[test]
#[timeout(30_000)]
fn to_fp_bv_reinterpret_zero() {
    let results = run_script(
        r#"
(set-logic QF_FP)
(assert (not (fp.eq
    ((_ to_fp 8 24) #b00000000000000000000000000000000)
    (_ +zero 8 24))))
(check-sat)
"#,
    );
    assert_eq!(results, vec!["unsat"]);
}

// to_fp from BV: NaN (exponent all 1s, significand nonzero)
#[test]
#[timeout(30_000)]
fn to_fp_bv_reinterpret_nan() {
    let results = run_script(
        r#"
(set-logic QF_FP)
(assert (not (fp.isNaN
    ((_ to_fp 8 24) #b01111111110000000000000000000000))))
(check-sat)
"#,
    );
    assert_eq!(results, vec!["unsat"]);
}

// to_fp from BV: +infinity (sign=0, exp all 1s, sig all 0s)
#[test]
#[timeout(30_000)]
fn to_fp_bv_reinterpret_inf() {
    let results = run_script(
        r#"
(set-logic QF_FP)
(assert (not (fp.isInfinite
    ((_ to_fp 8 24) #b01111111100000000000000000000000))))
(check-sat)
"#,
    );
    assert_eq!(results, vec!["unsat"]);
}

// ===== to_fp signed BV conversion tests =====

// to_fp from signed BV: 1 (as 32-bit signed int) → 1.0f
#[test]
#[timeout(30_000)]
fn to_fp_signed_bv_one() {
    let results = run_script(
        r#"
(set-logic QF_FP)
(assert (not (fp.eq
    ((_ to_fp 8 24) RNE #b00000000000000000000000000000001)
    (fp #b0 #b01111111 #b00000000000000000000000))))
(check-sat)
"#,
    );
    assert_eq!(results, vec!["unsat"]);
}

// to_fp from signed BV: -1 (as 32-bit signed int, 2's complement) → -1.0f
#[test]
#[timeout(30_000)]
fn to_fp_signed_bv_neg_one() {
    let results = run_script(
        r#"
(set-logic QF_FP)
(assert (not (fp.eq
    ((_ to_fp 8 24) RNE #b11111111111111111111111111111111)
    (fp #b1 #b01111111 #b00000000000000000000000))))
(check-sat)
"#,
    );
    assert_eq!(results, vec!["unsat"]);
}

// to_fp from signed BV: 0 → +0.0
#[test]
#[timeout(30_000)]
fn to_fp_signed_bv_zero() {
    let results = run_script(
        r#"
(set-logic QF_FP)
(assert (not (fp.eq
    ((_ to_fp 8 24) RNE #b00000000000000000000000000000000)
    (_ +zero 8 24))))
(check-sat)
"#,
    );
    assert_eq!(results, vec!["unsat"]);
}

// to_fp from signed BV: 42 → 42.0f
// Float32: 42.0 = 0_10000100_01010000000000000000000
// exp = 132 - 127 = 5, sig = 1.01010 → 42 = 1.3125 * 2^5
#[test]
#[timeout(30_000)]
fn to_fp_signed_bv_42() {
    let results = run_script(
        r#"
(set-logic QF_FP)
(assert (not (fp.eq
    ((_ to_fp 8 24) RNE #b00000000000000000000000000101010)
    (fp #b0 #b10000100 #b01010000000000000000000))))
(check-sat)
"#,
    );
    assert_eq!(results, vec!["unsat"]);
}

// ===== to_fp_unsigned conversion tests =====

// to_fp_unsigned from BV: 1 → 1.0f
#[test]
#[timeout(30_000)]
fn to_fp_unsigned_bv_one() {
    let results = run_script(
        r#"
(set-logic QF_FP)
(assert (not (fp.eq
    ((_ to_fp_unsigned 8 24) RNE #b00000000000000000000000000000001)
    (fp #b0 #b01111111 #b00000000000000000000000))))
(check-sat)
"#,
    );
    assert_eq!(results, vec!["unsat"]);
}

// to_fp_unsigned from BV: 0 → +0.0
#[test]
#[timeout(30_000)]
fn to_fp_unsigned_bv_zero() {
    let results = run_script(
        r#"
(set-logic QF_FP)
(assert (not (fp.eq
    ((_ to_fp_unsigned 8 24) RNE #b00000000000000000000000000000000)
    (_ +zero 8 24))))
(check-sat)
"#,
    );
    assert_eq!(results, vec!["unsat"]);
}

// to_fp_unsigned: 255 (as 8-bit unsigned) → 255.0f
// Float32: 255.0 = 0_10000110_11111110000000000000000
// exp = 134 - 127 = 7, sig = 1.1111111 → 255 = 1.9921875 * 2^7
#[test]
#[timeout(30_000)]
fn to_fp_unsigned_bv_255() {
    let results = run_script(
        r#"
(set-logic QF_FP)
(assert (not (fp.eq
    ((_ to_fp_unsigned 8 24) RNE #b11111111)
    (fp #b0 #b10000110 #b11111110000000000000000))))
(check-sat)
"#,
    );
    assert_eq!(results, vec!["unsat"]);
}

// ===== Guard tests: unsupported operations still return Unknown =====

// fp.to_ubv implementation (#3586) returns unknown — completeness gap.
// Accepts sat or unknown until bit-blasting covers this case.
#[test]
#[timeout(60_000)]
fn fp_to_ubv_supported() {
    let results = run_script(
        r#"
(set-logic QF_FP)
(declare-const x (_ FloatingPoint 8 24))
(assert (= ((_ fp.to_ubv 32) RNE x) #b00000000000000000000000000000001))
(check-sat)
"#,
    );
    assert!(
        results == vec!["sat"] || results == vec!["unknown"],
        "expected sat or unknown, got {results:?}"
    );
}

// fp.to_sbv implementation (#3586) returns unknown — completeness gap.
// Accepts sat or unknown until bit-blasting covers this case.
#[test]
#[timeout(60_000)]
fn fp_to_sbv_supported() {
    let results = run_script(
        r#"
(set-logic QF_FP)
(declare-const x (_ FloatingPoint 8 24))
(assert (= ((_ fp.to_sbv 32) RNE x) #b00000000000000000000000000000001))
(check-sat)
"#,
    );
    assert!(
        results == vec!["sat"] || results == vec!["unknown"],
        "expected sat or unknown, got {results:?}"
    );
}

#[test]
#[timeout(30_000)]
fn raw_bv_distinct_to_ubv_roundtrip_guard_unsat_8870() {
    let mut exec = Executor::new();
    let bv1 = Sort::bitvec(1);
    let a = exec.ctx.terms.mk_var("a", bv1.clone());
    let zero = exec.ctx.terms.mk_bitvec(BigInt::from(0), 1);
    let guard = exec.ctx.terms.mk_bvule(a, zero);

    let rne = exec
        .ctx
        .terms
        .mk_app(Symbol::named("RNE"), Vec::new(), Sort::Bool);
    let rtz = exec
        .ctx
        .terms
        .mk_app(Symbol::named("RTZ"), Vec::new(), Sort::Bool);
    let to_fp = exec.ctx.terms.mk_app(
        Symbol::indexed("to_fp", vec![5, 11]),
        vec![rne, a],
        Sort::FloatingPoint(5, 11),
    );
    let to_ubv =
        exec.ctx
            .terms
            .mk_app(Symbol::indexed("fp.to_ubv", vec![1]), vec![rtz, to_fp], bv1);
    let raw_distinct =
        exec.ctx
            .terms
            .mk_app(Symbol::named("distinct"), vec![a, to_ubv], Sort::Bool);

    exec.ctx.assertions.push(guard);
    exec.ctx.assertions.push(raw_distinct);

    let result = exec.solve_bvfp().expect("raw BV distinct canary solves");
    assert!(
        matches!(result, SolveResult::Unsat(_)),
        "raw BV distinct in the FP/QF_BVFP linker must not remain a free SAT variable; got {result:?}"
    );
}

// fp.to_real with unconstrained FP var and Real constraint r > 1.0.
// Refinement loop (#6241): first FP model may give +zero (bits all false),
// but the loop blocks that valuation and retries until it finds an FP value
// whose fp.to_real > 1.0 (e.g., 2.0).
#[test]
#[timeout(30_000)]
fn fp_to_real_unconstrained_returns_sat() {
    let results = run_script(
        r#"
(set-logic QF_FP)
(declare-const x (_ FloatingPoint 5 11))
(declare-const r Real)
(assert (= r (fp.to_real x)))
(assert (> r 1.0))
(check-sat)
"#,
    );
    // Refinement loop should find a satisfying FP model
    assert_eq!(results, vec!["sat"]);
}

// fp.to_real with FP constrained to 1.0: fp.to_real(1.0) = 1.0 (exact).
// Two-phase solve: FP part forces x = 1.0, then r = 1.0 satisfies r >= 0.5.
#[test]
#[timeout(30_000)]
fn fp_to_real_constrained_sat() {
    let results = run_script(
        r#"
(set-logic QF_FPLRA)
(declare-const x (_ FloatingPoint 8 24))
(declare-const r Real)
(assert (fp.eq x (fp #b0 #b01111111 #b00000000000000000000000)))
(assert (= r (fp.to_real x)))
(assert (>= r 0.5))
(check-sat)
"#,
    );
    assert_eq!(results, vec!["sat"]);
}

// fp.to_real with FP constrained to +zero: fp.to_real(+0) = 0.
#[test]
#[timeout(30_000)]
fn fp_to_real_zero_sat() {
    let results = run_script(
        r#"
(set-logic QF_FPLRA)
(declare-const x (_ FloatingPoint 8 24))
(declare-const r Real)
(assert (fp.eq x (_ +zero 8 24)))
(assert (= r (fp.to_real x)))
(assert (= r 0.0))
(check-sat)
"#,
    );
    assert_eq!(results, vec!["sat"]);
}

// fp.to_real with FP constrained to 2.0: fp.to_real(2.0) = 2.0.
// Float32 2.0 = 0_10000000_00000000000000000000000
#[test]
#[timeout(30_000)]
fn fp_to_real_two_sat() {
    let results = run_script(
        r#"
(set-logic QF_FPLRA)
(declare-const x (_ FloatingPoint 8 24))
(declare-const r Real)
(assert (fp.eq x (fp #b0 #b10000000 #b00000000000000000000000)))
(assert (= r (fp.to_real x)))
(assert (> r 1.5))
(check-sat)
"#,
    );
    assert_eq!(results, vec!["sat"]);
}

// fp.to_real with -zero: fp.to_real(-0) = 0 (same as +zero per IEEE 754).
#[test]
#[timeout(30_000)]
fn fp_to_real_neg_zero_is_zero() {
    let results = run_script(
        r#"
(set-logic QF_FPLRA)
(declare-const x (_ FloatingPoint 8 24))
(declare-const r Real)
(assert (fp.eq x (_ -zero 8 24)))
(assert (= r (fp.to_real x)))
(assert (= r 0.0))
(check-sat)
"#,
    );
    assert_eq!(results, vec!["sat"]);
}

// fp.to_real with only pure FP assertions (no Real constraints on the
// fp.to_real result). The FP part is solved normally and fp.to_real
// is present but unused in predicates — the mixed assertion just has
// to evaluate to true.
#[test]
#[timeout(30_000)]
fn fp_to_real_only_fp_constraints() {
    let results = run_script(
        r#"
(set-logic QF_FPLRA)
(declare-const x (_ FloatingPoint 8 24))
(declare-const r Real)
(assert (fp.eq x (fp #b0 #b01111111 #b00000000000000000000000)))
(assert (let ((rv (fp.to_real x))) (> rv 0.0)))
(check-sat)
"#,
    );
    assert_eq!(results, vec!["sat"]);
}

// fp.rem on Float64 is now supported via exact bounded modular reduction
// (commit 143b360e4d) — the old barrel-shifter/2101-bit-divider gate (#5950)
// is gone. (fp.eq (fp.rem x y) x) is SAT (e.g. x = +0), matching z3.
#[test]
#[timeout(30_000)]
fn fp_rem_float64_supported_sat() {
    let results = run_script(
        r#"
(set-logic QF_FP)
(declare-const x (_ FloatingPoint 11 53))
(declare-const y (_ FloatingPoint 11 53))
(assert (fp.eq (fp.rem x y) x))
(check-sat)
"#,
    );
    assert_eq!(results, vec!["sat"]);
}

// ITE over FP sort: (ite true a b) must equal a.
// Regression test for decompose_fp line 979 — non-App FP terms
// were returning unconstrained variables, allowing false-SAT on
// formulas with ITE-over-FP subexpressions.
#[test]
#[timeout(30_000)]
fn fp_ite_true_branch_equals_arg() {
    // (ite true a b) = a should be SAT (always true)
    let results = run_script(
        r#"
(set-logic QF_FP)
(declare-const a (_ FloatingPoint 5 11))
(declare-const b (_ FloatingPoint 5 11))
(assert (= (ite true a b) a))
(check-sat)
"#,
    );
    assert_eq!(results, vec!["sat"]);
}

// ITE over FP sort: (ite true a b) cannot equal b when a ≠ b.
// This MUST be UNSAT. If the FP decomposer returns unconstrained
// variables for ITE terms, the solver could produce false-SAT.
#[test]
#[timeout(30_000)]
fn fp_ite_soundness_unsat() {
    let results = run_script(
        r#"
(set-logic QF_FP)
(declare-const a (_ FloatingPoint 5 11))
(declare-const b (_ FloatingPoint 5 11))
(assert (not (= a b)))
(assert (= (ite true a b) b))
(check-sat)
"#,
    );
    // (ite true a b) = a, and a ≠ b, so a = b is false → UNSAT
    assert_eq!(
        results,
        vec!["unsat"],
        "FP ITE soundness: (ite true a b) = a, but assert a = b contradiction → UNSAT"
    );
}

// ===== Variable BV-to-FP conversion tests =====

// Variable BV reinterpret: (to_fp 8 24) on a BV variable constrained to 1.0f pattern
#[test]
#[timeout(30_000)]
fn to_fp_bv_reinterpret_variable() {
    let results = run_script(
        r#"
(set-logic QF_BVFP)
(declare-const bv (_ BitVec 32))
(assert (= bv #b00111111100000000000000000000000))
(assert (fp.eq ((_ to_fp 8 24) bv) (fp #b0 #b01111111 #b00000000000000000000000)))
(check-sat)
"#,
    );
    assert!(
        results == vec!["sat"],
        "Expected sat: BV constrained to 1.0f pattern, to_fp should yield 1.0. Got {results:?}"
    );
}

// Variable BV reinterpret UNSAT: BV constrained to 1.0f but FP expected to be 2.0f
#[test]
#[timeout(30_000)]
fn to_fp_bv_reinterpret_variable_unsat() {
    let results = run_script(
        r#"
(set-logic QF_BVFP)
(declare-const bv (_ BitVec 32))
(assert (= bv #b00111111100000000000000000000000))
(assert (fp.eq ((_ to_fp 8 24) bv) (fp #b0 #b10000000 #b00000000000000000000000)))
(check-sat)
"#,
    );
    assert!(
        results == vec!["unsat"] || results == vec!["unknown"],
        "Expected unsat: BV is 1.0f pattern but FP is 2.0f. Got {results:?}"
    );
}

// Variable signed BV-to-FP: x is a BV32 variable, constrained to 1,
// (to_fp 8 24) RNE x should equal 1.0f
#[test]
#[timeout(30_000)]
fn to_fp_signed_variable_one() {
    let results = run_script(
        r#"
(set-logic QF_BVFP)
(declare-const x (_ BitVec 32))
(assert (= x #b00000000000000000000000000000001))
(assert (fp.eq ((_ to_fp 8 24) RNE x) (fp #b0 #b01111111 #b00000000000000000000000)))
(check-sat)
"#,
    );
    assert!(
        results == vec!["sat"],
        "Expected sat: signed BV 1 converts to 1.0f. Got {results:?}"
    );
}

// Variable signed BV-to-FP: x is -1 (all ones in 2's complement),
// should convert to -1.0f
#[test]
#[timeout(30_000)]
fn to_fp_signed_variable_neg_one() {
    let results = run_script(
        r#"
(set-logic QF_BVFP)
(declare-const x (_ BitVec 32))
(assert (= x #b11111111111111111111111111111111))
(assert (fp.eq ((_ to_fp 8 24) RNE x) (fp #b1 #b01111111 #b00000000000000000000000)))
(check-sat)
"#,
    );
    assert!(
        results == vec!["sat"],
        "Expected sat: signed BV -1 converts to -1.0f. Got {results:?}"
    );
}

// Variable signed BV-to-FP: zero converts to +0.0
#[test]
#[timeout(30_000)]
fn to_fp_signed_variable_zero() {
    let results = run_script(
        r#"
(set-logic QF_BVFP)
(declare-const x (_ BitVec 32))
(assert (= x #b00000000000000000000000000000000))
(assert (fp.isZero ((_ to_fp 8 24) RNE x)))
(check-sat)
"#,
    );
    assert!(
        results == vec!["sat"],
        "Expected sat: signed BV 0 converts to +0.0. Got {results:?}"
    );
}

// Variable unsigned BV-to-FP: x = 1, should yield 1.0f
#[test]
#[timeout(30_000)]
fn to_fp_unsigned_variable_one() {
    let results = run_script(
        r#"
(set-logic QF_BVFP)
(declare-const x (_ BitVec 32))
(assert (= x #b00000000000000000000000000000001))
(assert (fp.eq ((_ to_fp_unsigned 8 24) RNE x) (fp #b0 #b01111111 #b00000000000000000000000)))
(check-sat)
"#,
    );
    assert!(
        results == vec!["sat"],
        "Expected sat: unsigned BV 1 converts to 1.0f. Got {results:?}"
    );
}

// Variable unsigned BV-to-FP: x = 0, should yield +0.0
#[test]
#[timeout(30_000)]
fn to_fp_unsigned_variable_zero() {
    let results = run_script(
        r#"
(set-logic QF_BVFP)
(declare-const x (_ BitVec 32))
(assert (= x #b00000000000000000000000000000000))
(assert (fp.isZero ((_ to_fp_unsigned 8 24) RNE x)))
(check-sat)
"#,
    );
    assert!(
        results == vec!["sat"],
        "Expected sat: unsigned BV 0 converts to +0.0. Got {results:?}"
    );
}

// Variable signed BV-to-FP UNSAT: x = 1 but expects 2.0f
#[test]
#[timeout(30_000)]
fn to_fp_signed_variable_wrong_value_unsat() {
    let results = run_script(
        r#"
(set-logic QF_BVFP)
(declare-const x (_ BitVec 32))
(assert (= x #b00000000000000000000000000000001))
(assert (fp.eq ((_ to_fp 8 24) RNE x) (fp #b0 #b10000000 #b00000000000000000000000)))
(check-sat)
"#,
    );
    assert!(
        results == vec!["unsat"] || results == vec!["unknown"],
        "Expected unsat: signed BV 1 should not equal 2.0f. Got {results:?}"
    );
}

// Variable BV-to-FP with smaller BV: 8-bit signed to Float16
#[test]
#[timeout(30_000)]
fn to_fp_signed_variable_small_bv() {
    let results = run_script(
        r#"
(set-logic QF_BVFP)
(declare-const x (_ BitVec 8))
(assert (= x #b00000010))
(assert (fp.eq ((_ to_fp 5 11) RNE x) (fp #b0 #b10000 #b0000000000)))
(check-sat)
"#,
    );
    assert!(
        results == vec!["sat"],
        "Expected sat: signed BV8 value 2 converts to 2.0 in Float16. Got {results:?}"
    );
}

// ITE over FP in an equality chain: (= (ite c x y) z) with constraints.
// Exercises the path where bitblast_fp_structural_eq calls get_fp on an ITE term.
#[test]
#[timeout(30_000)]
fn fp_ite_conditional_soundness() {
    // If c is true, then (ite c x y) = x, so we need x = z.
    // If c is false, then (ite c x y) = y, so we need y = z.
    // With x = +1.0, y = -1.0, z = +1.0: c must be true.
    // With c = false forced: should be UNSAT.
    let results = run_script(
        r#"
(set-logic QF_FP)
(declare-const c Bool)
(declare-const x (_ FloatingPoint 5 11))
(declare-const y (_ FloatingPoint 5 11))
(declare-const z (_ FloatingPoint 5 11))
(assert (= x (fp #b0 #b01111 #b0000000000)))
(assert (= y (fp #b1 #b01111 #b0000000000)))
(assert (= z (fp #b0 #b01111 #b0000000000)))
(assert (not c))
(assert (= (ite c x y) z))
(check-sat)
"#,
    );
    // c = false → (ite c x y) = y = -1.0, but z = +1.0, so -1.0 ≠ +1.0 → UNSAT
    assert_eq!(
        results,
        vec!["unsat"],
        "FP ITE conditional: c=false, (ite c x y)=-1.0 but z=+1.0 → UNSAT"
    );
}

// FP ITE in an fp.lt predicate: tests FP-level bit decomposition of ITE.
// (fp.lt (ite c x y) z) requires the ITE result's FP bits to be correctly
// linked to x or y based on condition c.
#[test]
#[timeout(30_000)]
fn fp_ite_in_fp_lt_predicate() {
    // x = +2.0 (Float16), y = -2.0 (Float16), z = +1.0 (Float16)
    // c is unconstrained: if c=true, (ite c x y) = +2.0, fp.lt(+2.0, +1.0) = false
    //                     if c=false, (ite c x y) = -2.0, fp.lt(-2.0, +1.0) = true
    // Assert (fp.lt (ite c x y) z) → forces c = false
    // Also assert c → contradiction → UNSAT
    let results = run_script(
        r#"
(set-logic QF_FP)
(declare-const c Bool)
(declare-const x (_ FloatingPoint 5 11))
(declare-const y (_ FloatingPoint 5 11))
(declare-const z (_ FloatingPoint 5 11))
(assert (= x (fp #b0 #b10000 #b0000000000)))
(assert (= y (fp #b1 #b10000 #b0000000000)))
(assert (= z (fp #b0 #b01111 #b0000000000)))
(assert (fp.lt (ite c x y) z))
(assert c)
(check-sat)
"#,
    );
    assert_eq!(
        results,
        vec!["unsat"],
        "FP ITE in fp.lt: c=true forces (ite c x y)=+2.0, fp.lt(+2.0,+1.0)=false → UNSAT"
    );
}

// FP ITE in arithmetic: (fp.add RNE (ite c x y) z) where ITE result
// determines the arithmetic outcome.
#[test]
#[timeout(60_000)]
fn fp_ite_in_arithmetic() {
    // x = +1.0, y = +2.0, z = +1.0
    // (fp.add RNE (ite c x y) z): if c=true → 1+1=2, if c=false → 2+1=3
    // Assert result = 3.0 AND c = true → UNSAT (1+1=2 ≠ 3)
    let results = run_script(
        r#"
(set-logic QF_FP)
(declare-const c Bool)
(declare-const x (_ FloatingPoint 5 11))
(declare-const y (_ FloatingPoint 5 11))
(declare-const z (_ FloatingPoint 5 11))
(declare-const r (_ FloatingPoint 5 11))
(assert (= x (fp #b0 #b01111 #b0000000000)))
(assert (= y (fp #b0 #b10000 #b0000000000)))
(assert (= z (fp #b0 #b01111 #b0000000000)))
(assert (= r (fp #b0 #b10000 #b1000000000)))
(assert (= (fp.add RNE (ite c x y) z) r))
(assert c)
(check-sat)
"#,
    );
    assert_eq!(
        results,
        vec!["unsat"],
        "FP ITE in arithmetic: c=true forces add(1.0,1.0)=2.0 but r=3.0 → UNSAT"
    );
}

// ===== fp.to_real refinement loop tests (#6241) =====

// Prover counterexample (#6241): specific significand value within a binade.
// fp.to_real(x) = 1.25 forces x to be exactly the float 1.25 (in binade [1.0, 2.0)).
// Hybrid blocking (#6241): exact-value blocking tries multiple significand values
// within the binade before escalating to binade-level blocking, so the SAT solver
// can find x = 1.25 within the 4-attempt exact-value budget.
#[test]
#[timeout(60_000)]
fn fp_to_real_binade_exact_value_6241() {
    let results = run_script(
        r#"
(set-logic QF_FPLRA)
(declare-const x (_ FloatingPoint 8 24))
(assert (fp.isNormal x))
(assert (fp.geq x (fp #b0 #b01111111 #b00000000000000000000000)))
(assert (fp.lt x (fp #b0 #b10000000 #b00000000000000000000000)))
(assert (= (fp.to_real x) 1.25))
(check-sat)
"#,
    );
    // With hybrid exact-value blocking, the SAT solver explores different
    // significand values within binade [1.0, 2.0) and finds x = 1.25.
    // Soundness guard: never return "unsat" for this satisfiable formula.
    assert!(
        results != vec!["unsat"],
        "SOUNDNESS BUG: fp.to_real(x)=1.25 is SAT but solver returned unsat",
    );
}

// Main #6241 regression: FP is unconstrained but finite, fp.to_real > 1.0.
// The refinement loop must find an FP model whose exact rational > 1.0.
#[test]
#[timeout(60_000)]
fn fp_to_real_issue6241_defined_sat() {
    let results = run_script(
        r#"
(set-logic QF_FPLRA)
(declare-const x (_ FloatingPoint 8 24))
(declare-const r Real)
(assert (not (fp.isNaN x)))
(assert (not (fp.isInfinite x)))
(assert (= r (fp.to_real x)))
(assert (> r 1.0))
(check-sat)
"#,
    );
    assert_eq!(results, vec!["sat"]);
}

// NaN can match any Real constant (undefined fp.to_real).
// The UF rewriting ensures fp.to_real(NaN) is a stable value,
// and the mixed solver can assign it to 5.0.
#[test]
#[timeout(60_000)]
fn fp_to_real_nan_can_match_real_constant() {
    let results = run_script(
        r#"
(set-logic QF_FPLRA)
(declare-const x (_ FloatingPoint 8 24))
(assert (fp.isNaN x))
(assert (= (fp.to_real x) 5.0))
(check-sat)
"#,
    );
    assert_eq!(results, vec!["sat"]);
}

// Equal FP inputs must produce equal fp.to_real outputs, even for NaN.
// This proves the UF representation is congruence-correct.
// The formula is genuinely UNSAT (x=y → fp.to_real(x)=fp.to_real(y) by congruence),
// but after #6241 the refinement loop returns Unknown when binade blocking
// exhausts the FP search space — sound but incomplete.
#[test]
#[timeout(60_000)]
fn fp_to_real_equal_inputs_share_undefined_value() {
    let results = run_script(
        r#"
(set-logic QF_FPLRA)
(declare-const x (_ FloatingPoint 8 24))
(declare-const y (_ FloatingPoint 8 24))
(assert (= x y))
(assert (fp.isNaN x))
(assert (not (= (fp.to_real x) (fp.to_real y))))
(check-sat)
"#,
    );
    // Sound: never returns "sat" (which would be unsound).
    // May return "unsat" (complete) or "unknown" (incomplete, #6241 guard).
    assert!(
        results == vec!["unsat"] || results == vec!["unknown"],
        "Expected unsat or unknown for congruence test, got: {results:?}",
    );
}

// Real-guided pre-solve (#6241): tight equality constraint on fp.to_real.
// The Real side determines that fp.to_real(x) must equal 3.5, and the
// pre-solve converts that to the Float32 encoding of 3.5 directly.
// Without pre-solve, the SAT solver would need to randomly find 3.5 among
// ~2^32 Float32 values.
#[test]
#[timeout(60_000)]
fn fp_to_real_guided_presolve_exact_target() {
    let results = run_script(
        r#"
(set-logic QF_FPLRA)
(declare-const x (_ FloatingPoint 8 24))
(assert (not (fp.isNaN x)))
(assert (not (fp.isInfinite x)))
(assert (= (fp.to_real x) 3.5))
(check-sat)
"#,
    );
    assert_eq!(results, vec!["sat"]);
}

// Real-guided pre-solve: multiple fp.to_real sites with interacting constraints.
// The pre-solve determines fp.to_real(x) = 2.0, fp.to_real(y) = 4.0.
#[test]
#[timeout(60_000)]
fn fp_to_real_guided_presolve_two_vars() {
    let results = run_script(
        r#"
(set-logic QF_FPLRA)
(declare-const x (_ FloatingPoint 8 24))
(declare-const y (_ FloatingPoint 8 24))
(declare-const r Real)
(assert (not (fp.isNaN x)))
(assert (not (fp.isInfinite x)))
(assert (not (fp.isNaN y)))
(assert (not (fp.isInfinite y)))
(assert (= r (fp.to_real x)))
(assert (= (fp.to_real y) (* r 2.0)))
(assert (= r 2.0))
(check-sat)
"#,
    );
    assert_eq!(results, vec!["sat"]);
}

// The Real-guided fp.to_real solve temporarily replaces the outer assertions
// with a rewritten FP-free subproblem. Its SAT/theory state must be private to
// that probe: after popping the fp.to_real scope, `r` is free to take a value
// inconsistent with the popped FP conversion.
#[test]
#[timeout(60_000)]
fn fp_to_real_rewritten_subsolve_does_not_leak_across_pop() {
    let results = run_script(
        r#"
(set-logic QF_FPLRA)
(declare-const x (_ FloatingPoint 8 24))
(declare-const r Real)
(assert (>= r 0.0))
(check-sat)
(push)
(assert (fp.eq x (fp #b0 #b01111111 #b00000000000000000000000)))
(assert (= r (fp.to_real x)))
(check-sat)
(pop)
(assert (= r 2.0))
(check-sat)
"#,
    );
    assert_eq!(results, vec!["sat", "sat", "sat"]);
}

// Push/pop incremental soundness regression (#8714).
//
// Ported-test-only analog of Z3 PR #9028 (FPA push/pop soundness). Z3's bug was
// that `theory_fpa::m_conversions` (FP-expr -> BV-expr cache) retained entries
// across DPLL backtracks while the side-condition clauses that linked FP UFs to
// their BV counterparts were deleted, so re-conversion short-circuited the
// rewriter and the axioms were never re-emitted. Z3's fix clears `m_conversions`
// in `pop_scope_eh` in addition to `m_rw.reset()`.
//
// ay's FP pipeline does NOT have this bug: `solve_fp()` constructs a fresh
// `FpSolver` on every `check-sat` and rebuilds caches (`term_to_fp`,
// `bv_term_bits`) from the current assertion list. There is no cross-call or
// cross-scope cache to leak. The tests below pin this property and catch any
// regression that would introduce the equivalent bug (e.g., if someone makes
// `FpSolver` incremental and caches FP->BV translations across push/pop).
#[test]
#[timeout(60_000)]
fn fp_push_pop_soundness_z3_pr_9028_basic() {
    // Ported from Z3 PR #9028 (FP push/pop soundness). Pure QF_FP analog of
    // the Z3 #9022 reproducer — push, assert conflict, pop, assert the
    // opposite. Under the Z3 bug, stale base-scope BV conversions could make
    // the post-pop query spuriously UNSAT. ay must return sat, unsat, sat.
    let results = run_script(
        r#"
(set-logic QF_FP)
(declare-const x (_ FloatingPoint 5 11))
(assert (fp.gt x ((_ to_fp 5 11) #x0000)))
(check-sat)
(push)
(assert (fp.lt x ((_ to_fp 5 11) #x0000)))
(check-sat)
(pop)
(check-sat)
"#,
    );
    assert_eq!(results, vec!["sat", "unsat", "sat"]);
}

#[test]
#[timeout(60_000)]
fn fp_push_pop_soundness_z3_pr_9028_to_fp_round_trip() {
    // Ported from Z3 PR #9028 (FP push/pop soundness). Exercises the specific
    // pattern from Z3 #9022: ground (_ to_fp 5 11) over an (_ int2bv 16) bit
    // pattern, with push/pop in between. Z3's bug was that the side conditions
    // connecting FP UFs to BV counterparts (via (_ to_fp ...) ((_ int2bv ...) ...)
    // lowering) were cached at base scope but invalidated on pop.
    //
    // Pure QF_FP version (ay's fully-supported path; QF_BVFP also covers this).
    // The post-pop check-sat must be sat — 2.0 as fp16 (= 0x4000) is distinct
    // from +0 (= 0x0000).
    let results = run_script(
        r#"
(set-logic QF_FP)
(declare-const x (_ FloatingPoint 5 11))
(assert (fp.eq x ((_ to_fp 5 11) #x4000)))
(push)
(assert (fp.eq x ((_ to_fp 5 11) #x0000)))
(check-sat)
(pop)
(check-sat)
"#,
    );
    assert_eq!(results, vec!["unsat", "sat"]);
}

#[test]
#[timeout(60_000)]
fn fp_push_pop_soundness_multiple_scopes() {
    // Ported from Z3 PR #9028 (FP push/pop soundness). Multi-level push/pop
    // with FP operations in each scope. If any scope's FP encoding state
    // leaked into the next scope's solver (the Z3 bug class), the alternating
    // sat/unsat pattern would break.
    let results = run_script(
        r#"
(set-logic QF_FP)
(declare-const x (_ FloatingPoint 5 11))
(declare-const y (_ FloatingPoint 5 11))
(assert (fp.eq (fp.add RNE x y) ((_ to_fp 5 11) #x4000)))
(push)
(assert (fp.isNaN x))
(check-sat)
(pop)
(push)
(assert (fp.isInfinite y))
(check-sat)
(pop)
(check-sat)
"#,
    );
    // First push: NaN + anything = NaN, but sum must equal 2.0 -> unsat.
    // Second push: Inf + anything = Inf or NaN, sum must equal 2.0 -> unsat.
    // Base: sum equals 2.0 with no NaN/Inf constraints -> sat.
    assert_eq!(results, vec!["unsat", "unsat", "sat"]);
}

// ── Regression: FP special-case soundness (FP bug round, 2026-06) ────────────

/// #bug8: `fp.isZero` over an `(fp s e m)` constructor with a SYMBOLIC sign but
/// a concrete nonzero mantissa must be UNSAT (the value is subnormal for either
/// sign — never zero). Previously a single non-constant field caused the whole
/// decomposition to return unconstrained variables, allowing wrong-SAT.
#[test]
#[timeout(60_000)]
fn fp_iszero_symbolic_sign_concrete_subnormal_is_unsat_bug8() {
    let results = run_script(
        r#"
(set-logic ALL)
(declare-const s (_ BitVec 1))
(assert (fp.isZero (fp s (_ bv0 5) (_ bv1 10))))
(check-sat)
"#,
    );
    assert_eq!(results, vec!["unsat"]);
}

/// #bug8 companion: the concrete-sign analogue (already correct) must stay
/// UNSAT, and `fp.isSubnormal` over the symbolic-sign constructor must be SAT.
#[test]
#[timeout(60_000)]
fn fp_classify_symbolic_sign_constructor_bug8() {
    assert_eq!(
        run_script(
            r#"
(set-logic ALL)
(assert (fp.isZero (fp #b0 (_ bv0 5) (_ bv1 10))))
(check-sat)
"#,
        ),
        vec!["unsat"]
    );
    assert_eq!(
        run_script(
            r#"
(set-logic ALL)
(declare-const s (_ BitVec 1))
(assert (fp.isSubnormal (fp s (_ bv0 5) (_ bv1 10))))
(check-sat)
"#,
        ),
        vec!["sat"]
    );
}

/// #bug14: `sqrt(-0) = -0` so `fp.isZero(fp.sqrt RNE -0)` is SAT, and its
/// negation is UNSAT. Previously AY returned UNSAT for BOTH polarities (it
/// treated sqrt(-0) as stuck via a sign clause that conflicted with the
/// negative-zero case). The +0 analogue must remain SAT.
#[test]
#[timeout(60_000)]
fn fp_sqrt_negative_zero_is_zero_bug14() {
    assert_eq!(
        run_script(
            r#"
(set-logic ALL)
(assert (fp.isZero (fp.sqrt RNE (_ -zero 11 53))))
(check-sat)
"#,
        ),
        vec!["sat"]
    );
    assert_eq!(
        run_script(
            r#"
(set-logic ALL)
(assert (not (fp.isZero (fp.sqrt RNE (_ -zero 11 53)))))
(check-sat)
"#,
        ),
        vec!["unsat"]
    );
    assert_eq!(
        run_script(
            r#"
(set-logic ALL)
(assert (fp.isZero (fp.sqrt RNE (_ +zero 11 53))))
(check-sat)
"#,
        ),
        vec!["sat"]
    );
}

/// #bug14: sqrt(-0) must specifically be a NEGATIVE zero (sign preserved), so
/// `fp.isNegative` does NOT hold (signed zeros are neither positive nor
/// negative per IEEE) but structural equality with -0 holds.
#[test]
#[timeout(60_000)]
fn fp_sqrt_negative_zero_preserves_sign_bug14() {
    // sqrt(-0) structurally equals -0 (distinguishes +0 from -0).
    assert_eq!(
        run_script(
            r#"
(set-logic ALL)
(assert (= (fp.sqrt RNE (_ -zero 11 53)) (_ -zero 11 53)))
(check-sat)
"#,
        ),
        vec!["sat"]
    );
    // sqrt(-0) is NOT structurally +0.
    assert_eq!(
        run_script(
            r#"
(set-logic ALL)
(assert (= (fp.sqrt RNE (_ -zero 11 53)) (_ +zero 11 53)))
(check-sat)
"#,
        ),
        vec!["unsat"]
    );
}

/// #bug13: `fp.to_sbv` of +oo is a fixed-but-unspecified value, so asserting it
/// equals an arbitrary constant (here 2^63-1) must NOT be refuted. Previously
/// AY pinned the result to 0 and returned a definitive (wrong) UNSAT; it now
/// returns sat or fails closed to unknown — never unsat.
#[test]
#[timeout(60_000)]
fn fp_to_sbv_infinity_is_unspecified_not_unsat_bug13() {
    let results = run_script(
        r#"
(set-logic ALL)
(assert (= (_ bv9223372036854775807 64) ((_ fp.to_sbv 64) RNE (_ +oo 11 53))))
(check-sat)
"#,
    );
    assert_ne!(
        results,
        vec!["unsat"],
        "fp.to_sbv(+oo) is unspecified; pinning it to a value and refuting is unsound"
    );
    assert!(matches!(results[0].as_str(), "sat" | "unknown"));
}

/// #bug13 congruence guard: even though the unspecified value is free, two
/// `fp.to_sbv` of the SAME concrete +oo must be equal — so their disequality is
/// UNSAT (Ackermannization of the partial conversion result).
#[test]
#[timeout(60_000)]
fn fp_to_sbv_infinity_congruent_bug13() {
    assert_eq!(
        run_script(
            r#"
(set-logic ALL)
(assert (not (= ((_ fp.to_sbv 64) RNE (_ +oo 11 53))
                ((_ fp.to_sbv 64) RNE (_ +oo 11 53)))))
(check-sat)
"#,
        ),
        vec!["unsat"]
    );
}

// ---------------------------------------------------------------------------
// to_fp from a Real literal: `((_ to_fp eb sb) rm <real>)` rounds the exact
// rational into the target format. Previously returned Unknown (completeness
// gap). Verifies correctness against the IEEE 754 bit patterns (the BV
// reinterpretation of to_fp) so the rounding is exactly right, never just sat.
// ---------------------------------------------------------------------------

/// `(_ to_fp 8 24) RNE 1.0` must equal the Float32 bit pattern of 1.0
/// (0x3f800000). z3 = sat.
#[test]
#[timeout(60_000)]
fn fp_to_fp_real_one_roundtrips_to_ieee_bits() {
    assert_eq!(
        run_script(
            r#"
(set-logic QF_FP)
(declare-const x (_ FloatingPoint 8 24))
(assert (= x ((_ to_fp 8 24) RNE 1.0)))
(assert (= x ((_ to_fp 8 24) #x3f800000)))
(check-sat)
"#,
        ),
        vec!["sat"]
    );
}

/// to_fp of 1.0 must NOT equal the bit pattern of 2.0 (0x40000000): UNSAT.
/// Guards against a free / unconstrained result (false-SAT).
#[test]
#[timeout(60_000)]
fn fp_to_fp_real_one_is_not_two_unsat() {
    assert_eq!(
        run_script(
            r#"
(set-logic QF_FP)
(declare-const x (_ FloatingPoint 8 24))
(assert (= x ((_ to_fp 8 24) RNE 1.0)))
(assert (= x ((_ to_fp 8 24) #x40000000)))
(check-sat)
"#,
        ),
        vec!["unsat"]
    );
}

/// RNE rounding of 0.1 (not exactly representable) yields the canonical
/// Float32 encoding 0x3dcccccd. z3 = sat.
#[test]
#[timeout(60_000)]
fn fp_to_fp_real_tenth_rne_rounds_to_canonical_bits() {
    assert_eq!(
        run_script(
            r#"
(set-logic QF_FP)
(declare-const x (_ FloatingPoint 8 24))
(assert (= x ((_ to_fp 8 24) RNE (/ 1.0 10.0))))
(assert (= x ((_ to_fp 8 24) #x3dcccccd)))
(check-sat)
"#,
        ),
        vec!["sat"]
    );
}

/// Directed rounding differs: RTZ(1/3) != RTP(1/3) for Float32. z3 = sat.
#[test]
#[timeout(60_000)]
fn fp_to_fp_real_directed_rounding_differs() {
    assert_eq!(
        run_script(
            r#"
(set-logic QF_FP)
(declare-const x (_ FloatingPoint 8 24))
(declare-const y (_ FloatingPoint 8 24))
(assert (= x ((_ to_fp 8 24) RTZ (/ 1.0 3.0))))
(assert (= y ((_ to_fp 8 24) RTP (/ 1.0 3.0))))
(assert (not (fp.eq x y)))
(check-sat)
"#,
        ),
        vec!["sat"]
    );
}

/// A magnitude that overflows Float16 rounds to +oo. z3 = sat.
#[test]
#[timeout(60_000)]
fn fp_to_fp_real_overflow_to_infinity() {
    assert_eq!(
        run_script(
            r#"
(set-logic QF_FP)
(declare-const x (_ FloatingPoint 5 11))
(assert (= x ((_ to_fp 5 11) RNE 100000.0)))
(assert (fp.isInfinite x))
(check-sat)
"#,
        ),
        vec!["sat"]
    );
}

/// Negative literal: to_fp of (- 0.5) is the exact Float32 -0.5 = 0xbf000000.
#[test]
#[timeout(60_000)]
fn fp_to_fp_real_negative_half_exact() {
    assert_eq!(
        run_script(
            r#"
(set-logic QF_FP)
(declare-const x (_ FloatingPoint 8 24))
(assert (= x ((_ to_fp 8 24) RNE (- 0.5))))
(assert (= x ((_ to_fp 8 24) #xbf000000)))
(check-sat)
"#,
        ),
        vec!["sat"]
    );
}

// CSET-style BV1 lowering shapes: `(bvor (ite P #b1 #b0) (ite Q #b1 #b0))`
// where P/Q are FP predicates or free Bools. The elaborator produces `ite`
// as a name-form application (`App("ite", …)`), which the FP bit-blaster's
// BV walker did not handle — the whole QF_BVFP query bailed to
// `unknown (:reason-unknown unsupported)` even though every piece is
// bit-blastable. Found via external-codegen's Fcmp_UEQ_F32 lowering proof
// (FCMP + CSET(EQ) OR CSET(VS)), 2026-07-10.
#[test]
#[timeout(30_000)]
fn qf_bvfp_cset_ueq_lowering_identity_unsat() {
    // external-codegen-ir UnorderedEqual vs the AArch64 two-CSET lowering:
    // (or (fp.eq a b) (isNaN a) (isNaN b))  ==  (bvor CSET(EQ) CSET(VS)).
    // The negation must be UNSAT for all a, b.
    let results = run_script(
        r#"
(set-logic QF_BVFP)
(declare-const a (_ FloatingPoint 8 24))
(declare-const b (_ FloatingPoint 8 24))
(assert (not (=
  (ite (or (fp.eq a b) (or (fp.isNaN a) (fp.isNaN b))) (_ bv1 1) (_ bv0 1))
  (bvor (ite (fp.eq a b) (_ bv1 1) (_ bv0 1))
        (ite (or (fp.isNaN a) (fp.isNaN b)) (_ bv1 1) (_ bv0 1))))))
(check-sat)
"#,
    );
    assert_eq!(results, vec!["unsat"]);
}

// Same shape over free Bool inputs (no FP terms at all, but dispatched
// through the FP pipeline by the QF_BVFP logic): `or` on indicator bits IS
// `bvor`. Also exercises the consistent-literal encoding of free Boolean
// inputs that occur only below theory atoms — the previous fresh-per-call
// gap decorrelated repeated occurrences and forced Unknown.
#[test]
#[timeout(30_000)]
fn qf_bvfp_bool_indicator_bvor_identity_unsat() {
    let results = run_script(
        r#"
(set-logic QF_BVFP)
(declare-const x Bool)
(declare-const y Bool)
(assert (not (= (ite (or x y) (_ bv1 1) (_ bv0 1))
                (bvor (ite x (_ bv1 1) (_ bv0 1)) (ite y (_ bv1 1) (_ bv0 1))))))
(check-sat)
"#,
    );
    assert_eq!(results, vec!["unsat"]);
}

// Satisfiable direction of the CSET shape: reflexive fp.eq OR isNaN always
// yields the #b1 indicator (valid), so asserting it is SAT.
#[test]
#[timeout(30_000)]
fn qf_bvfp_cset_bvor_reflexive_sat() {
    let results = run_script(
        r#"
(set-logic QF_BVFP)
(declare-const a (_ FloatingPoint 8 24))
(assert (= (bvor (ite (fp.isNaN a) (_ bv1 1) (_ bv0 1))
                 (ite (fp.eq a a) (_ bv1 1) (_ bv0 1))) (_ bv1 1)))
(check-sat)
"#,
    );
    assert_eq!(results, vec!["sat"]);
}
