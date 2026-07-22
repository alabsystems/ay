// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

// #4169/#4087: CertificateConsumer Seq pattern — quantified array with BV64 indices and bvzeroext
// Mimics: s.drop_first().index(0) == 42 given s.index(1) == 42
#[test]
fn test_certificate_consumer_seq_drop_first_pattern_unsat() {
    let input = r#"
        (set-logic ALL)
        (declare-const s (Array (_ BitVec 64) (_ BitVec 32)))
        (declare-const result (Array (_ BitVec 64) (_ BitVec 32)))
        (declare-const len (_ BitVec 32))
        ; len == 5
        (assert (= len #x00000005))
        ; s[1] == 42
        (assert (= (select s #x0000000000000001) #x0000002A))
        ; forall i: result[i] = s[i + 1] (drop_first shifts indices by 1)
        (assert (forall ((i (_ BitVec 64)))
            (! (= (select result i) (select s (bvadd i #x0000000000000001)))
               :pattern ((select result i)))))
        ; negation of assertion: result[0] != 42
        (assert (not (= (select result #x0000000000000000) #x0000002A)))
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(
        outputs,
        vec!["unsat"],
        "deductive-checks drop_first pattern: result[0] should equal s[1]=42"
    );
}

// #4169: Same pattern but with bvzeroext indices (matching deductive-checks coerce_seq_index)
#[test]
fn test_certificate_consumer_seq_zeroext_index_pattern_unsat() {
    let input = r#"
        (set-logic ALL)
        (declare-const s (Array (_ BitVec 64) (_ BitVec 32)))
        (declare-const result (Array (_ BitVec 64) (_ BitVec 32)))
        (declare-const len (_ BitVec 32))
        ; len == 5
        (assert (= len #x00000005))
        ; s[zext(1)] == 42 (index via zero-extend from BV32 to BV64)
        (assert (= (select s ((_ zero_extend 32) #x00000001)) #x0000002A))
        ; forall i: result[i] = s[i + 1]
        (assert (forall ((i (_ BitVec 64)))
            (! (= (select result i) (select s (bvadd i #x0000000000000001)))
               :pattern ((select result i)))))
        ; negation: result[zext(0)] != 42
        (assert (not (= (select result ((_ zero_extend 32) #x00000000)) #x0000002A)))
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(
        outputs,
        vec!["unsat"],
        "deductive-checks zeroext index pattern: result[zext(0)] should equal s[zext(1)]=42"
    );
}

// #4169: CertificateConsumer seq_last pattern — self-contradictory assertion with symbolic index
#[test]
fn test_certificate_consumer_seq_last_pattern_unsat() {
    let input = r#"
        (set-logic ALL)
        (declare-const s (Array (_ BitVec 64) (_ BitVec 32)))
        (declare-const len (_ BitVec 32))
        ; len == 3
        (assert (= len #x00000003))
        ; s[len-1] == 42 (last element)
        (assert (= (select s ((_ zero_extend 32) (bvsub len #x00000001))) #x0000002A))
        ; negation: s.last() != 42
        (assert (not (= (select s ((_ zero_extend 32) (bvsub len #x00000001))) #x0000002A)))
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(
        outputs,
        vec!["unsat"],
        "deductive-checks last pattern: s[len-1] == 42 and NOT s[len-1] == 42 should be unsat"
    );
}

/// Regression: BV-return UF congruence via check-sat-assuming (#5437).
#[test]
fn test_executor_qf_ufbv_check_sat_assuming_congruence_unsat_5437() {
    let input = r#"
        (set-logic QF_UFBV)
        (declare-fun f ((_ BitVec 8)) (_ BitVec 8))
        (declare-fun x () (_ BitVec 8))
        (declare-fun y () (_ BitVec 8))
        (assert (= x y))
        (check-sat-assuming ((distinct (f x) (f y))))
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs, vec!["unsat"]);
}

/// Regression: non-BV-return UF congruence via check-sat-assuming (#5437).
#[test]
fn test_executor_qf_ufbv_non_bv_return_check_sat_assuming_unsat_5437() {
    let input = r#"
        (set-logic QF_UFBV)
        (declare-sort U 0)
        (declare-fun f ((_ BitVec 8)) U)
        (declare-fun x () (_ BitVec 8))
        (declare-fun y () (_ BitVec 8))
        (assert (= x y))
        (check-sat-assuming ((distinct (f x) (f y))))
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs, vec!["unsat"]);
}

/// Regression: AUFBV UF congruence via check-sat-assuming (#5437).
/// Uses AUFBV logic with only UF (no array terms) to test congruence path.
#[test]
fn test_executor_qf_aufbv_check_sat_assuming_congruence_unsat_5437() {
    let input = r#"
        (set-logic QF_AUFBV)
        (declare-fun f ((_ BitVec 8)) (_ BitVec 8))
        (declare-fun x () (_ BitVec 8))
        (declare-fun y () (_ BitVec 8))
        (assert (= x y))
        (check-sat-assuming ((distinct (f x) (f y))))
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs, vec!["unsat"]);
}

/// Regression: empty assumptions on UFBV still works (#5437).
#[test]
fn test_executor_qf_ufbv_check_sat_assuming_empty_unsat_5437() {
    let input = r#"
        (set-logic QF_UFBV)
        (declare-fun f ((_ BitVec 8)) (_ BitVec 8))
        (declare-fun x () (_ BitVec 8))
        (declare-fun y () (_ BitVec 8))
        (assert (= x y))
        (assert (distinct (f x) (f y)))
        (check-sat-assuming ())
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs, vec!["unsat"]);
}

/// Regression: check-sat-assuming BV SAT must extract BvModel for get-value (#5443).
/// Previously, the check-sat-assuming path called solve_and_store_model with bv_model=None,
/// causing get-value to return empty/missing BV values after assumption-based SAT.
#[test]
fn test_executor_qf_bv_check_sat_assuming_get_value_5443() {
    let input = r#"
        (set-logic QF_BV)
        (declare-fun x () (_ BitVec 8))
        (declare-const p Bool)
        (assert (= p (bvuge x #x42)))
        (check-sat-assuming (p))
        (get-value (x))
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs[0], "sat");
    // get-value must return a BV value for x, not empty/error
    assert!(
        outputs[1].contains("x") && outputs[1].contains("#x"),
        "Expected BV value for x in get-value output, got: {}",
        outputs[1]
    );
}

/// Probe: Bool variable substituted with bvult predicate.
/// When preprocessing substitutes `p → (bvult x #x42)`, the model recovery code
/// must correctly evaluate the bvult predicate to recover p's value.
/// This exercises the `_ => None` fallthrough in Bool substitution recovery.
#[test]
fn test_executor_qf_bv_bool_subst_bvult_get_value() {
    let input = r#"
        (set-logic QF_BV)
        (declare-fun x () (_ BitVec 8))
        (declare-const p Bool)
        (assert (= p (bvult x #x42)))
        (assert p)
        (check-sat)
        (get-value (p x))
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs[0], "sat");
    // p must be true (we asserted it)
    assert!(
        outputs[1].contains("p") && outputs[1].contains("true"),
        "Expected p=true in get-value output, got: {}",
        outputs[1]
    );
    // x must be < #x42 (66)
    assert!(
        outputs[1].contains("x") && outputs[1].contains("#x"),
        "Expected BV value for x in get-value output, got: {}",
        outputs[1]
    );
}

/// Regression: check-sat-assuming UFBV SAT must extract BvModel for get-value (#5443).
#[test]
fn test_executor_qf_ufbv_check_sat_assuming_get_value_5443() {
    let input = r#"
        (set-logic QF_UFBV)
        (declare-fun f ((_ BitVec 8)) (_ BitVec 8))
        (declare-fun x () (_ BitVec 8))
        (declare-const p Bool)
        (assert (= p (= (f x) #xFF)))
        (check-sat-assuming (p))
        (get-value (x))
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs[0], "sat");
    // get-value must return a BV value for x
    assert!(
        outputs[1].contains("x") && outputs[1].contains("#x"),
        "Expected BV value for x in get-value output, got: {}",
        outputs[1]
    );
}

/// Regression test for #5115: MCMPC circuit with Bool-gate wires over BV extracts.
///
/// Variable substitution eliminates intermediate Bool variables (b0-b3, xor_out)
/// that are defined via BV extract predicates and Bool gates (and, or, xor).
/// Without the Tseitin SAT seeding + evaluate_bool_substitution fix, model
/// validation fails because eliminated Bool wires referencing non-eliminated
/// Bool variables (and01, or23) cannot be resolved.
#[test]
fn test_bv_bool_gate_wires_mcmpc_5115() {
    let input = r#"
        (set-logic QF_BV)
        (declare-fun x () (_ BitVec 8))
        (declare-fun b0 () Bool) (declare-fun b1 () Bool)
        (declare-fun b2 () Bool) (declare-fun b3 () Bool)
        (assert (= b0 (= #b1 ((_ extract 0 0) x))))
        (assert (= b1 (= #b1 ((_ extract 1 1) x))))
        (assert (= b2 (= #b1 ((_ extract 2 2) x))))
        (assert (= b3 (= #b1 ((_ extract 3 3) x))))
        (declare-fun and01 () Bool)
        (declare-fun or23 () Bool)
        (declare-fun xor_out () Bool)
        (assert (= and01 (and b0 b1)))
        (assert (= or23 (or b2 b3)))
        (assert (= xor_out (xor and01 or23)))
        (assert xor_out)
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(
        outputs[0], "sat",
        "#5115: MCMPC Bool-gate circuit should be SAT, got: {}",
        outputs[0]
    );
}

/// Regression test: BV shift operations in substitution targets (#5115).
/// When VariableSubstitution eliminates a variable whose definition uses
/// bvshl/bvlshr/bvashr, the model evaluator must handle these operations
/// to recover the variable's value. Without the shift evaluator, the model
/// is incomplete and validation fails.
#[test]
fn test_bv_shift_model_recovery_5115() {
    let input = r#"
        (set-logic QF_BV)
        (declare-fun x () (_ BitVec 8))
        (declare-fun shifted () (_ BitVec 8))
        (declare-fun lshifted () (_ BitVec 8))
        (assert (= x #xAB))
        (assert (= shifted (bvshl x #x02)))
        (assert (= lshifted (bvlshr x #x04)))
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(
        outputs[0], "sat",
        "#5115: BV shift model recovery should be SAT, got: {}",
        outputs[0]
    );
}

/// Regression: QF_ABV wide_div_array spurious UNSAT (#8480).
/// 32-bit bvudiv with array store/select interaction.
/// Z3 returns SAT; AY previously returned UNSAT.
#[test]
fn test_regression_8480_wide_div_array_sat() {
    let input = r#"
        (set-logic QF_ABV)
        (declare-fun a () (Array (_ BitVec 8) (_ BitVec 32)))
        (declare-fun x () (_ BitVec 32))
        (declare-fun y () (_ BitVec 32))
        (assert (= (select (store a #x01 (bvudiv x y)) #x01) (bvudiv x y)))
        (assert (not (= y #x00000000)))
        (assert (bvugt x y))
        (assert (bvugt x #x00010000))
        (assert (bvugt y #x00000100))
        (assert (bvult (bvudiv x y) #x00001000))
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(
        outputs,
        vec!["sat"],
        "#8480: wide_div_array should be SAT (32-bit bvudiv + array store/select)"
    );
}

/// Regression: QF_ABV wide_mul_64bit_stress spurious UNSAT (#8480).
/// 64-bit bvmul with array, constrained to small region.
/// Z3 returns SAT; AY previously returned UNSAT.
#[test]
fn test_regression_8480_wide_mul_64bit_stress_sat() {
    let input = r#"
        (set-logic QF_ABV)
        (declare-fun a () (Array (_ BitVec 8) (_ BitVec 64)))
        (declare-fun x () (_ BitVec 64))
        (declare-fun y () (_ BitVec 64))
        (declare-fun prod () (_ BitVec 64))
        (assert (= prod (bvmul x y)))
        (assert (= (select (store a #x00 prod) #x00) prod))
        (assert (bvugt x #x0000000000000010))
        (assert (bvult x #x00000000000000FF))
        (assert (bvugt y #x0000000000000010))
        (assert (bvult y #x00000000000000FF))
        (assert (bvugt prod #x0000000000000100))
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(
        outputs,
        vec!["sat"],
        "#8480: wide_mul_64bit_stress should be SAT (64-bit bvmul + array store/select)"
    );
}

/// Regression: QF_ABV model_checker_consumer_pattern_mul_store spurious UNSAT (#8480).
/// model-checker-consumer-style pointer arithmetic: array[base + i*stride] with variable stride.
/// Z3 returns SAT; AY previously returned UNSAT.
#[test]
fn test_regression_8480_model_checker_consumer_pattern_mul_store_sat() {
    let input = r#"
        (set-logic QF_ABV)
        (declare-fun mem () (Array (_ BitVec 32) (_ BitVec 32)))
        (declare-fun base () (_ BitVec 32))
        (declare-fun i () (_ BitVec 32))
        (declare-fun stride () (_ BitVec 32))
        (declare-fun val () (_ BitVec 32))
        (declare-fun addr () (_ BitVec 32))
        (assert (= addr (bvadd base (bvmul i stride))))
        (declare-fun mem2 () (Array (_ BitVec 32) (_ BitVec 32)))
        (assert (= mem2 (store mem addr val)))
        (assert (= (select mem2 addr) val))
        (assert (= base #x10000000))
        (assert (bvugt stride #x00000004))
        (assert (bvult stride #x00000100))
        (assert (bvult i #x00000100))
        (assert (= val #xDEADBEEF))
        (declare-fun j () (_ BitVec 32))
        (assert (not (= i j)))
        (assert (bvult j #x00000100))
        (declare-fun addr2 () (_ BitVec 32))
        (assert (= addr2 (bvadd base (bvmul j stride))))
        (assert (not (= addr addr2)))
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(
        outputs,
        vec!["sat"],
        "#8480: model_checker_consumer_pattern_mul_store should be SAT (pointer arithmetic with variable stride)"
    );
}

/// Regression test for #6248: BV solver must not panic in CONDITIONING.
///
/// The BV bit-blasting path creates a fresh SAT solver where conditioning
/// (GBCE) was previously enabled by default. For certain BV-array formulas,
/// conditioning's root-satisfied invariant could be violated, causing a
/// debug assertion panic. The fix disables conditioning for all BV solve
/// paths since BV instances are one-shot.
#[test]
fn test_regression_6248_bv_conditioning_no_panic() {
    // QF_ABV formula with multiple array ops and BV arithmetic.
    // Generates enough clauses from bit-blasting to potentially trigger
    // conditioning during preprocessing or inprocessing.
    let input = r#"
        (set-logic QF_ABV)
        (declare-const a (Array (_ BitVec 8) (_ BitVec 8)))
        (declare-const b (Array (_ BitVec 8) (_ BitVec 8)))
        (declare-const x (_ BitVec 8))
        (declare-const y (_ BitVec 8))
        (declare-const z (_ BitVec 8))

        ; Store and select chain
        (assert (= (select (store a x #xFF) x) #xFF))
        (assert (= (select (store b y #x01) y) #x01))

        ; Cross-array constraint forcing search
        (assert (= (bvadd (select a z) (select b z)) #x00))

        ; Arithmetic constraints that increase variable count
        (assert (bvult x y))
        (assert (bvult y z))
        (assert (not (= x #x00)))

        (check-sat)
        (get-value (x y z))
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    // The formula is satisfiable. The key assertion is that we don't panic.
    assert_eq!(
        outputs[0], "sat",
        "#6248: QF_ABV formula should be SAT without CONDITIONING panic, got: {}",
        outputs[0]
    );

    // Model verification: get-value must return BV hex values for all three variables.
    // The formula requires bvult x y, bvult y z, and x != #x00.
    let model_output = &outputs[1];
    // Must contain at least one hex BV literal
    assert!(
        model_output.contains("#x"),
        "#6248: get-value must return BV hex values; got: {model_output}",
    );
    // x must not be assigned #x00 (constraint: not (= x #x00))
    assert!(
        !model_output.contains("(x #x00)"),
        "#6248: model has x = #x00 which violates (not (= x #x00)); got: {model_output}",
    );
}

// ---------------------------------------------------------------------------
// BV-lane substituted Bool/BV value recovery (mirrors LIA lane, #3201).
//
// VariableSubstitution eliminates Bool variables via direct equalities
// (e.g. `b -> a` from `(assert (= b a))`). When the representative is itself
// unconstrained in the post-substitution SAT instance, it has no SAT/Tseitin
// assignment, so model recovery previously left BOTH variables without
// values. Model validation then evaluated the restored assertion to Unknown
// and fail-closed SAT to `unknown (:reason-unknown incomplete)`. The fix
// seeds defaults (Bool: false, BV: zero) for unconstrained substitution
// representatives BEFORE the recovery fixpoint, so eliminated variables get
// values evaluated consistently with what the validation evaluator sees.
// ---------------------------------------------------------------------------

/// Trivially-SAT mix of a BV assertion and a Bool-equality assertion where
/// both Bool variables are otherwise unconstrained.
#[test]
fn test_qf_bv_bool_eq_mix_substitution_recovery() {
    let input = r#"
        (declare-const x (_ BitVec 32))
        (assert (= x #x00000001))
        (declare-const a Bool)
        (declare-const b Bool)
        (assert (= b a))
        (check-sat)
        (get-value (a b))
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(
        outputs[0], "sat",
        "BV + Bool-eq mix must be SAT, got: {}",
        outputs[0]
    );
    // Recovered values must satisfy (= b a): both true or both false.
    let values = &outputs[1];
    assert!(
        (values.contains("(a true)") && values.contains("(b true)"))
            || (values.contains("(a false)") && values.contains("(b false)")),
        "model must satisfy (= b a), got: {values}"
    );
}

/// Negated-variable RHS: `b -> (not a)` with `a` unconstrained.
#[test]
fn test_qf_bv_bool_eq_not_rhs_substitution_recovery() {
    let input = r#"
        (declare-const x (_ BitVec 32))
        (assert (= x #x00000001))
        (declare-const a Bool)
        (declare-const b Bool)
        (assert (= b (not a)))
        (check-sat)
        (get-value (a b))
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(
        outputs[0], "sat",
        "BV + (= b (not a)) must be SAT, got: {}",
        outputs[0]
    );
    let values = &outputs[1];
    assert!(
        (values.contains("(a true)") && values.contains("(b false)"))
            || (values.contains("(a false)") && values.contains("(b true)")),
        "model must satisfy (= b (not a)), got: {values}"
    );
}

/// Bool-gate RHS: `b -> (and (not a) (not c))` with `a`, `c` unconstrained.
#[test]
fn test_qf_bv_bool_eq_and_not_rhs_substitution_recovery() {
    let input = r#"
        (declare-const x (_ BitVec 32))
        (assert (= x #x00000001))
        (declare-const a Bool)
        (declare-const b Bool)
        (declare-const c Bool)
        (assert (= b (and (not a) (not c))))
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(
        outputs[0], "sat",
        "BV + (= b (and (not a) (not c))) must be SAT, got: {}",
        outputs[0]
    );
}

/// Transitive substitution chain: `b -> a`, `c -> b`. Recovery must resolve
/// the chain in dependency order against the seeded representative.
#[test]
fn test_qf_bv_bool_eq_transitive_chain_substitution_recovery() {
    let input = r#"
        (declare-const x (_ BitVec 32))
        (assert (= x #x00000001))
        (declare-const a Bool)
        (declare-const b Bool)
        (declare-const c Bool)
        (assert (= b a))
        (assert (= c b))
        (check-sat)
        (get-value (a b c))
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(
        outputs[0], "sat",
        "transitive Bool-eq chain must be SAT, got: {}",
        outputs[0]
    );
    let values = &outputs[1];
    assert!(
        (values.contains("(a true)") && values.contains("(b true)") && values.contains("(c true)"))
            || (values.contains("(a false)")
                && values.contains("(b false)")
                && values.contains("(c false)")),
        "model must satisfy b = a and c = b, got: {values}"
    );
}

/// Recovery must respect what the SAT solver actually decided: when the
/// representative IS constrained (here `a` is asserted true), the eliminated
/// variable must get the evaluated RHS value, never a blind default.
#[test]
fn test_qf_bv_bool_eq_constrained_representative_recovery() {
    let input = r#"
        (declare-const x (_ BitVec 32))
        (assert (= x #x00000001))
        (declare-const a Bool)
        (declare-const b Bool)
        (assert (= b (not a)))
        (assert a)
        (check-sat)
        (get-value (a b))
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs[0], "sat");
    let values = &outputs[1];
    assert!(
        values.contains("(a true)") && values.contains("(b false)"),
        "asserted a forces b = false, got: {values}"
    );
}

/// False-Violated hazard probe: a negated Bool equality is NOT a direct
/// equality, so neither variable is eliminated; default seeding must not
/// override the SAT solver's assignment and flip the result to a model
/// validation failure.
#[test]
fn test_qf_bv_bool_negated_eq_assertion_stays_sat() {
    let input = r#"
        (declare-const x (_ BitVec 32))
        (assert (= x #x00000001))
        (declare-const a Bool)
        (declare-const b Bool)
        (assert (not (= a b)))
        (check-sat)
        (get-value (a b))
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(
        outputs[0], "sat",
        "BV + (not (= a b)) is satisfiable and must stay SAT, got: {}",
        outputs[0]
    );
    let values = &outputs[1];
    assert!(
        (values.contains("(a true)") && values.contains("(b false)"))
            || (values.contains("(a false)") && values.contains("(b true)")),
        "model must satisfy (not (= a b)), got: {values}"
    );
}

/// Genuinely-UNSAT probe: recovery must not paper over a real contradiction.
#[test]
fn test_qf_bv_bool_eq_contradiction_stays_unsat() {
    let input = r#"
        (declare-const x (_ BitVec 32))
        (assert (= x #x00000001))
        (declare-const a Bool)
        (declare-const b Bool)
        (assert (= a b))
        (assert (= a (not b)))
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(
        outputs[0], "unsat",
        "a = b together with a = (not b) must be UNSAT, got: {}",
        outputs[0]
    );
}

/// BV-sorted representative left unconstrained after substitution:
/// `y -> (bvadd z #x00000001)` where `z` is otherwise unconstrained. The
/// recovery must seed `z` and evaluate `y` from it so the reported model
/// satisfies the restored defining equality. Before the fix the model
/// reported the inconsistent pair z = 0, y = 0.
#[test]
fn test_qf_bv_bv_eq_unconstrained_representative_recovery() {
    let input = r#"
        (declare-const w (_ BitVec 32))
        (assert (= w #x00000005))
        (declare-const z (_ BitVec 32))
        (declare-const y (_ BitVec 32))
        (assert (= y (bvadd z #x00000001)))
        (check-sat)
        (get-value (z y))
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs[0], "sat");
    let values = &outputs[1];
    let extract = |name: &str| -> u64 {
        let pat = format!("({name} #x");
        let start = values
            .find(&pat)
            .map(|i| i + pat.len())
            .unwrap_or_else(|| panic!("missing {name} in get-value output: {values}"));
        u64::from_str_radix(&values[start..start + 8], 16)
            .unwrap_or_else(|_| panic!("malformed hex for {name} in: {values}"))
    };
    let z_val = extract("z");
    let y_val = extract("y");
    assert_eq!(
        y_val,
        (z_val + 1) & 0xFFFF_FFFF,
        "model must satisfy (= y (bvadd z #x00000001)), got: {values}"
    );
}

/// QF_AUFBV routing (early Phase 0 preprocessing lane, #8140): the same
/// Bool-eq + BV mix must recover through the ABV branch as well. Slimmed
/// from a model-checker-consumer BMC query that previously degraded to unknown.
#[test]
fn test_qf_aufbv_bool_eq_mix_substitution_recovery() {
    let input = r#"
        (set-logic QF_AUFBV)
        (declare-const x (_ BitVec 32))
        (assert (= x #x00000001))
        (declare-const y (_ BitVec 32))
        (assert (= y #x00000002))
        (declare-const ok Bool)
        (assert (= ok (not (= x y))))
        (declare-const a Bool)
        (declare-const b Bool)
        (assert (= b a))
        (check-sat)
        (get-value (ok))
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(
        outputs[0], "sat",
        "QF_AUFBV BV + Bool-eq mix must be SAT, got: {}",
        outputs[0]
    );
    assert!(
        outputs[1].contains("(ok true)"),
        "x=1, y=2 forces ok = true, got: {}",
        outputs[1]
    );
}

/// model-checker-consumer BMC shape: Bool guards and BV locals defined through ITE chains
/// (`TermData::Ite`) that VariableSubstitution eliminates. Recovery must
/// evaluate Bool-sorted ITEs and BV-sorted ITEs whose conditions are
/// recovered Bool variables (previously both fell through to None, leaving
/// the model incomplete and degrading SAT to unknown).
#[test]
fn test_qf_bv_bool_ite_guard_substitution_recovery() {
    let input = r#"
        (set-logic QF_BV)
        (declare-const x (_ BitVec 32))
        (assert (= x #x00000001))
        (declare-const y (_ BitVec 32))
        (assert (= y #x00000002))
        (declare-const guard Bool)
        (assert (= guard (not (= x y))))
        (declare-const v (_ BitVec 32))
        (declare-const v_init (_ BitVec 32))
        (assert (= v (ite guard (bvadd x #x00000001) v_init)))
        (declare-const ok Bool)
        (declare-const ok_init Bool)
        (assert (= ok (ite guard (= x y) ok_init)))
        (declare-const viol Bool)
        (assert (= viol (and guard (not ok))))
        (assert viol)
        (check-sat)
        (get-value (guard ok viol v))
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(
        outputs[0], "sat",
        "ITE guard chain must be SAT, got: {}",
        outputs[0]
    );
    let values = &outputs[1];
    assert!(
        values.contains("(guard true)")
            && values.contains("(ok false)")
            && values.contains("(viol true)")
            && values.contains("(v #x00000002)"),
        "x=1, y=2 force guard=true, ok=false, viol=true, v=2; got: {values}"
    );
}

/// Same ITE guard chain routed through the QF_AUFBV early-preprocessing
/// lane (Phase 0, #8140) — slimmed from the model-checker-consumer `nomem.smt2` BMC query.
#[test]
fn test_qf_aufbv_bool_ite_guard_substitution_recovery() {
    let input = r#"
        (set-logic QF_AUFBV)
        (declare-const x (_ BitVec 32))
        (assert (= x #x00000001))
        (declare-const y (_ BitVec 32))
        (assert (= y #x00000002))
        (declare-const guard Bool)
        (assert (= guard (not (= x y))))
        (declare-const ok Bool)
        (declare-const ok_init Bool)
        (assert (= ok (ite guard (= x y) ok_init)))
        (declare-const viol Bool)
        (assert (= viol (and guard (not ok))))
        (assert viol)
        (check-sat)
        (get-value (viol))
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(
        outputs[0], "sat",
        "QF_AUFBV ITE guard chain must be SAT, got: {}",
        outputs[0]
    );
    assert!(
        outputs[1].contains("(viol true)"),
        "asserted violation must be true in the model, got: {}",
        outputs[1]
    );
}

// SORT-COHERENCE regression (deductive-checks mk_eq_coerce crash): a BV32 spec-fn body
// axiom `forall vx. f(vx) = bvmul(vx, vx)` alongside the 64-bit ground
// `bvmul` that the unsigned mul-no-overflow expansion mints (zero_extend to
// 2N, multiply, check high half). E-matching's by-name candidate index used
// to offer the 64-bit mul to the 32-bit body pattern and bind vx to a BV64
// operand — instantiation then built the ill-sorted `(= (f vx) bvmul64)`,
// panicking in mk_eq_coerce on debug builds. The formula is satisfiable; the
// pin is "no crash, never unsat".
#[test]
fn test_cross_width_bvmul_axiom_overflow_shape_no_crash() {
    let input = r#"
        (set-logic ALL)
        (declare-fun f ((_ BitVec 32)) (_ BitVec 32))
        (declare-const x (_ BitVec 32))
        (assert (forall ((vx (_ BitVec 32))) (= (f vx) (bvmul vx vx))))
        (assert (= ((_ extract 63 32)
                    (bvmul ((_ zero_extend 32) x) ((_ zero_extend 32) x)))
                   #x00000000))
        (assert (= (f x) (bvmul x x)))
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs.len(), 1);
    assert_ne!(
        outputs[0], "unsat",
        "satisfiable cross-width bvmul + axiom shape must never be unsat"
    );
}

// =========================================================================
// Item 4 Stage 2: non-BV congruence pair-loop hardening (poll + bail flag
// + hoisted consumer pre-filter).
// =========================================================================

/// SAT under a BAILED (partial) non-BV congruence axiomatization must
/// degrade to Unknown: a model may violate an unemitted congruence
/// constraint (wrong-SAT class). Uses the deterministic test hook that
/// forces the pass to bail at pair 0.
#[test]
fn test_non_bv_congruence_bail_degrades_sat_to_unknown_item4() {
    let input = r#"
        (set-logic QF_UFBV)
        (declare-sort U 0)
        (declare-fun f ((_ BitVec 8)) U)
        (declare-fun x () (_ BitVec 8))
        (declare-fun y () (_ BitVec 8))
        (assert (distinct (f x) (f y)))
        (check-sat)
    "#;
    let commands = parse(input).unwrap();

    // Sanity: without the forced bail this instance is SAT.
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();
    assert_eq!(outputs, vec!["sat"], "baseline must be sat");

    // Forced bail: the CDCL SAT must be degraded to Unknown fail-closed.
    let mut bailed_exec = Executor::new();
    bailed_exec.test_force_non_bv_congruence_bail = true;
    let bailed_outputs = bailed_exec.execute_all(&commands).unwrap();
    assert_eq!(
        bailed_outputs,
        vec!["unknown"],
        "SAT under a bailed partial congruence axiomatization must degrade to Unknown"
    );
}

/// UNSAT remains reportable under a bailed axiomatization: partial
/// congruence axioms are a subset of the full set, so an UNSAT derived from
/// them (here: a plain BV contradiction) is still valid.
#[test]
fn test_non_bv_congruence_bail_keeps_unsat_reportable_item4() {
    let input = r#"
        (set-logic QF_UFBV)
        (declare-sort U 0)
        (declare-fun f ((_ BitVec 8)) U)
        (declare-fun x () (_ BitVec 8))
        (declare-fun y () (_ BitVec 8))
        (assert (distinct (f x) (f y)))
        (assert (= x #x01))
        (assert (= x #x02))
        (check-sat)
    "#;
    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    exec.test_force_non_bv_congruence_bail = true;
    let outputs = exec.execute_all(&commands).unwrap();
    assert_eq!(
        outputs,
        vec!["unsat"],
        "UNSAT must remain reportable under a bailed axiomatization"
    );
}

/// The hoisted consumer pre-filter (groups > SMALL_GROUP_MAX applications)
/// must never skip a CONSUMED pair: with ten same-symbol applications the
/// load-bearing (f x, f y) congruence still refutes the instance.
#[test]
fn test_non_bv_congruence_prefilter_preserves_unsat_large_group_item4() {
    let input = r#"
        (set-logic QF_UFBV)
        (declare-sort U 0)
        (declare-fun f ((_ BitVec 8)) U)
        (declare-fun x () (_ BitVec 8))
        (declare-fun y () (_ BitVec 8))
        (declare-fun z1 () (_ BitVec 8))
        (declare-fun z2 () (_ BitVec 8))
        (declare-fun z3 () (_ BitVec 8))
        (declare-fun z4 () (_ BitVec 8))
        (declare-fun z5 () (_ BitVec 8))
        (declare-fun z6 () (_ BitVec 8))
        (declare-fun z7 () (_ BitVec 8))
        (declare-fun z8 () (_ BitVec 8))
        (assert (= x y))
        (assert (distinct (f x) (f y)))
        (assert (distinct (f z1) (f z2)))
        (assert (distinct (f z3) (f z4)))
        (assert (distinct (f z5) (f z6)))
        (assert (distinct (f z7) (f z8)))
        (check-sat)
    "#;
    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();
    assert_eq!(
        outputs,
        vec!["unsat"],
        "pre-filter must keep congruence for consumed pairs in large groups"
    );
}

/// SAT twin of the large-group case (no x = y): the pre-filter may only
/// SKIP consumer-less pairs, never manufacture an unsat.
#[test]
fn test_non_bv_congruence_prefilter_preserves_sat_large_group_item4() {
    let input = r#"
        (set-logic QF_UFBV)
        (declare-sort U 0)
        (declare-fun f ((_ BitVec 8)) U)
        (declare-fun x () (_ BitVec 8))
        (declare-fun y () (_ BitVec 8))
        (declare-fun z1 () (_ BitVec 8))
        (declare-fun z2 () (_ BitVec 8))
        (declare-fun z3 () (_ BitVec 8))
        (declare-fun z4 () (_ BitVec 8))
        (declare-fun z5 () (_ BitVec 8))
        (declare-fun z6 () (_ BitVec 8))
        (declare-fun z7 () (_ BitVec 8))
        (declare-fun z8 () (_ BitVec 8))
        (assert (distinct (f x) (f y)))
        (assert (distinct (f z1) (f z2)))
        (assert (distinct (f z3) (f z4)))
        (assert (distinct (f z5) (f z6)))
        (assert (distinct (f z7) (f z8)))
        (check-sat)
    "#;
    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();
    assert_eq!(outputs, vec!["sat"]);
}
