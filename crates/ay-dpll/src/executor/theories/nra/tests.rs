// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use crate::Executor;
use ay_frontend::parse;

fn run_script(input: &str) -> Vec<String> {
    let commands = parse(input).expect("SMT-LIB script should parse");
    let mut exec = Executor::new();
    exec.execute_all(&commands)
        .expect("SMT-LIB script should execute")
}

// Basic QF_NRA: x*y > 0 with x > 0 and y > 0
#[test]
fn nra_sat_positive_product() {
    let results = run_script(
        r#"
(set-logic QF_NRA)
(declare-const x Real)
(declare-const y Real)
(assert (> x 1.0))
(assert (> y 1.0))
(assert (> (* x y) 0.0))
(check-sat)
"#,
    );
    assert_eq!(results, vec!["sat"]);
}

// QF_NRA: x*x >= 0 is always true (square is non-negative)
#[test]
fn nra_sat_square_nonneg() {
    let results = run_script(
        r#"
(set-logic QF_NRA)
(declare-const x Real)
(assert (>= (* x x) 0.0))
(check-sat)
"#,
    );
    assert_eq!(results, vec!["sat"]);
}

// QF_NRA UNSAT: x > 0, y > 0, x*y < 0 is impossible
#[test]
fn nra_unsat_sign_conflict() {
    let results = run_script(
        r#"
(set-logic QF_NRA)
(declare-const x Real)
(declare-const y Real)
(assert (> x 0.0))
(assert (> y 0.0))
(assert (< (* x y) 0.0))
(check-sat)
"#,
    );
    assert_eq!(results, vec!["unsat"]);
}

// QF_NRA: constant * variable (linear) - should be straightforward
#[test]
fn nra_sat_constant_mul() {
    let results = run_script(
        r#"
(set-logic QF_NRA)
(declare-const x Real)
(assert (= (* 2.0 x) 6.0))
(check-sat)
"#,
    );
    assert_eq!(results, vec!["sat"]);
}

// QF_NRA: product with fixed values (tangent plane converges trivially)
#[test]
fn nra_sat_fixed_product() {
    let results = run_script(
        r#"
(set-logic QF_NRA)
(declare-const x Real)
(declare-const y Real)
(assert (= x 2.0))
(assert (= y 3.0))
(assert (<= (* x y) 7.0))
(check-sat)
"#,
    );
    assert_eq!(results, vec!["sat"]);
}

// QF_NRA: negative × negative = positive via sign reasoning
#[test]
fn nra_unsat_neg_neg_product_positive() {
    let results = run_script(
        r#"
(set-logic QF_NRA)
(declare-const x Real)
(declare-const y Real)
(assert (< x 0.0))
(assert (< y 0.0))
(assert (< (* x y) 0.0))
(check-sat)
"#,
    );
    assert_eq!(results, vec!["unsat"]);
}

// --- Tests exercising order lemmas ---

// Order lemma: bounded product with ordering constraint
// x in [1,3], y in [2,4], x*y <= 5 is SAT (e.g., x=1, y=2, x*y=2)
#[test]
fn nra_sat_bounded_product_order() {
    let results = run_script(
        r#"
(set-logic QF_NRA)
(declare-const x Real)
(declare-const y Real)
(assert (>= x 1.0))
(assert (<= x 3.0))
(assert (>= y 2.0))
(assert (<= y 4.0))
(assert (<= (* x y) 5.0))
(check-sat)
"#,
    );
    // Debug mode limits NRA iterations (BigRational ~100x slower), so
    // tangent-plane convergence may not complete. Accept "unknown" as well.
    let result = &results[0];
    assert!(
        result == "sat" || result == "unknown",
        "expected sat or unknown, got {result}"
    );
}

// Order lemma: tight product bound that requires ordering reasoning
// x in [2,3], y in [2,3], x*y >= 10 is UNSAT (max product is 3*3=9)
#[test]
fn nra_unsat_product_exceeds_bound() {
    let results = run_script(
        r#"
(set-logic QF_NRA)
(declare-const x Real)
(declare-const y Real)
(assert (>= x 2.0))
(assert (<= x 3.0))
(assert (>= y 2.0))
(assert (<= y 3.0))
(assert (>= (* x y) 10.0))
(check-sat)
"#,
    );
    assert_ne!(
        results,
        vec!["sat"],
        "unsatisfiable product bound must not be reported SAT"
    );
}

// --- Tests exercising monotonicity lemmas ---

// Monotonicity: product with tighter bounds
// x in [1,2], y in [1,2], x*y in [1,4] is SAT
#[test]
fn nra_sat_monotone_bounded_product() {
    let results = run_script(
        r#"
(set-logic QF_NRA)
(declare-const x Real)
(declare-const y Real)
(assert (>= x 1.0))
(assert (<= x 2.0))
(assert (>= y 1.0))
(assert (<= y 2.0))
(assert (>= (* x y) 1.0))
(assert (<= (* x y) 4.0))
(check-sat)
"#,
    );
    assert_eq!(results, vec!["sat"]);
}

// Monotonicity: product with impossible lower bound
// x in [0,1], y in [0,1], x*y >= 2 is UNSAT
#[test]
fn nra_unsat_monotone_product_too_large() {
    let results = run_script(
        r#"
(set-logic QF_NRA)
(declare-const x Real)
(declare-const y Real)
(assert (>= x 0.0))
(assert (<= x 1.0))
(assert (>= y 0.0))
(assert (<= y 1.0))
(assert (>= (* x y) 2.0))
(check-sat)
"#,
    );
    assert_ne!(
        results,
        vec!["sat"],
        "unsatisfiable monotone product bound must not be reported SAT"
    );
}

// --- Quadratic constraint tests (neural-verification-consumer patterns) ---

// Quadratic: x^2 + y^2 <= 1 with x,y > 0.5 is UNSAT
// (0.5^2 + 0.5^2 = 0.5, but x > 0.5 means x^2 > 0.25 for each)
#[test]
fn nra_sat_quadratic_unit_circle() {
    let results = run_script(
        r#"
(set-logic QF_NRA)
(declare-const x Real)
(declare-const y Real)
(assert (<= (+ (* x x) (* y y)) 1.0))
(assert (> x 0.0))
(assert (> y 0.0))
(check-sat)
"#,
    );
    assert_eq!(results, vec!["sat"]);
}

// Polynomial approximation pattern (neural-verification-consumer style):
// a*x^2 + b*x + c = y with bounds
#[test]
fn nra_sat_polynomial_approx() {
    let results = run_script(
        r#"
(set-logic QF_NRA)
(declare-const x Real)
(declare-const y Real)
(assert (>= x 0.0))
(assert (<= x 1.0))
(assert (= y (+ (* x x) x 1.0)))
(assert (>= y 1.0))
(assert (<= y 3.0))
(check-sat)
"#,
    );
    assert_eq!(results, vec!["sat"]);
}

// --- Acceptance criteria tests (Phase 2 design) ---

// Model patching: fixed product value (patching makes the model consistent
// without needing lemma refinement)
#[test]
fn nra_sat_model_patching_fixed() {
    let results = run_script(
        r#"
(set-logic QF_NRA)
(declare-const x Real)
(declare-const y Real)
(assert (= x 3.0))
(assert (= y 4.0))
(assert (= (* x y) 12.0))
(check-sat)
"#,
    );
    assert_eq!(results, vec!["sat"]);
}

// Model patching: product with bounded region (tangent + order + monotone
// should converge via model patching shortcut)
#[test]
fn nra_sat_model_patching_bounded() {
    let results = run_script(
        r#"
(set-logic QF_NRA)
(declare-const x Real)
(declare-const y Real)
(assert (= x 2.0))
(assert (>= y 1.0))
(assert (<= y 5.0))
(assert (>= (* x y) 2.0))
(assert (<= (* x y) 10.0))
(check-sat)
"#,
    );
    assert_eq!(results, vec!["sat"]);
}

// Order + tangent convergence: product tightly bounded
// x = 5, x*y = 15, so y must be 3
#[test]
fn nra_sat_order_tangent_convergence() {
    let results = run_script(
        r#"
(set-logic QF_NRA)
(declare-const x Real)
(declare-const y Real)
(assert (= x 5.0))
(assert (= (* x y) 15.0))
(check-sat)
"#,
    );
    assert_eq!(results, vec!["sat"]);
}

// Tangent plane refinement: narrow interval around a product value
// x in [1,2], y in [1,2], x*y in [3,5]
// Feasible: x=2, y=2, x*y=4
//
// In debug mode, the NRA iteration limit is reduced (#6785) so this
// may return "unknown" instead of "sat". Release mode with the full
// 50-iteration budget always finds the solution.
#[test]
fn nra_sat_tangent_narrow_interval() {
    let results = run_script(
        r#"
(set-logic QF_NRA)
(declare-const x Real)
(declare-const y Real)
(assert (>= x 1.0))
(assert (<= x 2.0))
(assert (>= y 1.0))
(assert (<= y 2.0))
(assert (>= (* x y) 3.0))
(assert (<= (* x y) 5.0))
(check-sat)
"#,
    );
    let result = &results[0];
    assert!(
        result == "sat" || result == "unknown",
        "expected sat or unknown, got {result}"
    );
}

// --- Unbounded square tests (tangent fallback for McCormick) ---

// Square non-negativity: x^2 < 0 is impossible (no bounds on x needed)
#[test]
fn nra_unsat_square_negative() {
    let results = run_script(
        r#"
(set-logic QF_NRA)
(declare-const x Real)
(assert (< (* x x) 0.0))
(check-sat)
"#,
    );
    assert_eq!(results, vec!["unsat"]);
}

// Square non-negativity with stricter bound: x^2 < -1 is impossible
#[test]
fn nra_unsat_square_less_than_neg1() {
    let results = run_script(
        r#"
(set-logic QF_NRA)
(declare-const x Real)
(assert (< (* x x) (- 1.0)))
(check-sat)
"#,
    );
    assert_ne!(
        results,
        vec!["sat"],
        "negative square bound must not be reported SAT"
    );
}

// Unbounded product: x=2, y=3, xy=6 (model patching, no explicit bounds)
#[test]
fn nra_sat_unbounded_fixed_product() {
    let results = run_script(
        r#"
(set-logic QF_NRA)
(declare-const x Real)
(declare-const y Real)
(assert (= x 2.0))
(assert (= y 3.0))
(assert (= (* x y) 6.0))
(check-sat)
"#,
    );
    assert_eq!(results, vec!["sat"]);
}

// x^2 >= 0 is trivially satisfiable (any x works)
#[test]
fn nra_sat_square_nonneg_trivial() {
    let results = run_script(
        r#"
(set-logic QF_NRA)
(declare-const x Real)
(assert (>= (* x x) 0.0))
(check-sat)
"#,
    );
    assert_eq!(results, vec!["sat"]);
}

// --- neural-verification-consumer neural network verification patterns ---

// Quadratic bound: x^2+y^2 > 2 on unit box is UNSAT (max is 1+1=2)
#[test]
fn nra_unsat_quadratic_box_bound() {
    let results = run_script(
        r#"
(set-logic QF_NRA)
(declare-const x Real)
(declare-const y Real)
(assert (>= x 0.0))
(assert (<= x 1.0))
(assert (>= y 0.0))
(assert (<= y 1.0))
(assert (> (+ (* x x) (* y y)) 2.0))
(check-sat)
"#,
    );
    assert_ne!(
        results,
        vec!["sat"],
        "quadratic box contradiction must not be reported SAT"
    );
}

// NN layer with product weights: max(w1*x1+w2*x2) = 1.5+1.5 = 3, so y>4 is UNSAT
#[test]
fn nra_unsat_nn_layer_product_bound() {
    let results = run_script(
        r#"
(set-logic QF_NRA)
(declare-const x1 Real)
(declare-const x2 Real)
(declare-const w1 Real)
(declare-const w2 Real)
(declare-const y Real)
(assert (>= x1 (- 1.0)))
(assert (<= x1 1.0))
(assert (>= x2 (- 1.0)))
(assert (<= x2 1.0))
(assert (>= w1 0.5))
(assert (<= w1 1.5))
(assert (>= w2 0.5))
(assert (<= w2 1.5))
(assert (= y (+ (* w1 x1) (* w2 x2))))
(assert (> y 4.0))
(check-sat)
"#,
    );
    assert_ne!(
        results,
        vec!["sat"],
        "neural-network product bound must not be reported SAT"
    );
}

// #5959: x^2 = 2 has solutions at x = ±√2 but the NRA solver's
// incremental linearization used to incorrectly return UNSAT when the
// linear relaxation became infeasible around the irrational solution.
// The fix ensures post-refinement LRA UNSAT is demoted to Unknown when
// the UNSAT depends on approximation lemmas (tangent planes, sign cuts).
#[test]
fn nra_irrational_solution_not_false_unsat_5959() {
    let results = run_script(
        r#"
(set-logic QF_NRA)
(declare-const x Real)
(assert (= (* x x) 2.0))
(check-sat)
"#,
    );
    // Must NOT return "unsat" — x = ±√2 are valid solutions.
    // "unknown" or "sat" are acceptable.
    assert_ne!(results, vec!["unsat"], "BUG #5959: false UNSAT on x^2 = 2");
}

// x^2 = -1 has no real solutions (x^2 >= 0 for all real x).
// Even-power non-negativity lemma (exact algebraic) should detect this.
#[test]
fn nra_even_power_negative_is_genuine_unsat_5959() {
    let results = run_script(
        r#"
(set-logic QF_NRA)
(declare-const x Real)
(assert (= (* x x) (- 1.0)))
(check-sat)
"#,
    );
    assert_ne!(
        results,
        vec!["sat"],
        "negative even-power equality must not be reported SAT"
    );
}

// --- Phase 2 acceptance criteria (#5712) ---

// Order lemma (bounded variant): a ∈ [0,1], b ∈ [2,3], c ∈ [1,2]
// max(a*c) = 1*2 = 2, min(b*c) = 2*1 = 2. For a*c >= b*c we need
// a*c >= 2, which forces a=1, c=2 (corner). But then b*c = 2*b >= 4
// (since b >= 2), so b*c >= 4 > 2 = a*c. Contradiction.
// McCormick envelope detects this via upper bound on a*c and lower
// bound on b*c.
#[test]
fn nra_unsat_order_bounded_acceptance_5712() {
    let results = run_script(
        r#"
(set-logic QF_NRA)
(declare-const a Real)
(declare-const b Real)
(declare-const c Real)
(assert (>= a 0.0))
(assert (<= a 1.0))
(assert (>= b 2.0))
(assert (<= b 3.0))
(assert (>= c 1.0))
(assert (<= c 2.0))
(assert (>= (* a c) (* b c)))
(check-sat)
"#,
    );
    assert_ne!(
        results,
        vec!["sat"],
        "bounded order contradiction must not be reported SAT"
    );
}

// Order lemma (unbounded): a < b, c > 0 => a*c < b*c
// Without bounds on a,b,c, McCormick cannot produce envelopes.
// Currently returns "unknown" — order lemmas need DPLL(T) theory
// lemma channel to handle unbounded cases (#5712).
#[test]
fn nra_order_unbounded_known_limitation_5712() {
    let results = run_script(
        r#"
(set-logic QF_NRA)
(declare-const a Real)
(declare-const b Real)
(declare-const c Real)
(assert (< a b))
(assert (> c 0.0))
(assert (>= (* a c) (* b c)))
(check-sat)
"#,
    );
    // "unsat" is correct, "unknown" is acceptable (incomplete).
    // "sat" would be a soundness bug.
    assert_ne!(results, vec!["sat"], "BUG: sat on unsatisfiable formula");
}

// Monotonicity acceptance criterion: x ∈ [1,2], y ∈ [3,4], x*y > 10 is UNSAT
// (max product is 2*4 = 8 < 10)
// McCormick upper bound 2 at (xL=1, yU=4): m ≤ xL*y + yU*x - xL*yU = y + 4x - 4
// At x=2,y=4: m ≤ 4+8-4 = 8 < 10, so UNSAT.
#[test]
fn nra_unsat_monotone_acceptance_5712() {
    let results = run_script(
        r#"
(set-logic QF_NRA)
(declare-const x Real)
(declare-const y Real)
(assert (>= x 1.0))
(assert (<= x 2.0))
(assert (>= y 3.0))
(assert (<= y 4.0))
(assert (> (* x y) 10.0))
(check-sat)
"#,
    );
    assert_ne!(
        results,
        vec!["sat"],
        "monotone acceptance contradiction must not be reported SAT"
    );
}

// Higher-degree acceptance criterion: x > 0, y > 0, z > 0, x*y*z < 0 is UNSAT
// (positive * positive * positive is always positive)
// Detected by sign propagation across nested monomials.
#[test]
fn nra_unsat_higher_degree_acceptance_5712() {
    let results = run_script(
        r#"
(set-logic QF_NRA)
(declare-const x Real)
(declare-const y Real)
(declare-const z Real)
(assert (> x 0.0))
(assert (> y 0.0))
(assert (> z 0.0))
(assert (< (* x (* y z)) 0.0))
(check-sat)
"#,
    );
    assert_eq!(results, vec!["unsat"]);
}

// --- UF+NRA combined solver tests (#6294) ---

#[test]
fn test_uf_nra_sat_basic() {
    // f(x*x) = x+1 with x > 0 is SAT
    let results = run_script(
        r#"
(set-logic QF_UFNRA)
(declare-fun f (Real) Real)
(declare-fun x () Real)
(assert (= (f (* x x)) (+ x 1.0)))
(assert (> x 0.0))
(check-sat)
"#,
    );
    assert_eq!(results, vec!["sat"]);
}

#[test]
fn test_uf_nra_unsat_zero_square() {
    // x = 0, x*x > 0 is UNSAT (0*0 = 0, not > 0)
    let results = run_script(
        r#"
(set-logic QF_UFNRA)
(declare-fun x () Real)
(assert (= x 0.0))
(assert (> (* x x) 0.0))
(check-sat)
"#,
    );
    assert_eq!(results, vec!["unsat"]);
}

#[test]
fn test_uf_nra_congruence() {
    // f is uninterpreted; if x = y then f(x) = f(y)
    // f(x) != f(y), x = y is UNSAT by EUF congruence
    let results = run_script(
        r#"
(set-logic QF_UFNRA)
(declare-fun f (Real) Real)
(declare-fun x () Real)
(declare-fun y () Real)
(assert (= x y))
(assert (not (= (f x) (f y))))
(check-sat)
"#,
    );
    assert_eq!(results, vec!["unsat"]);
}

#[test]
fn test_uf_nra_interface_propagation() {
    // Tests Nelson-Oppen interface propagation between NRA and EUF.
    // x > 0, y > 0, x*y < 0 is UNSAT (positive product is positive).
    // Combined with UF: f(x) = f(y) is satisfiable on its own.
    // The UNSAT comes purely from NRA; EUF adds no conflict.
    // This exercises the combined solver without requiring nonlinear
    // terms inside UF function arguments (#6890).
    let results = run_script(
        r#"
(set-logic QF_UFNRA)
(declare-fun f (Real) Real)
(declare-fun x () Real)
(declare-fun y () Real)
(assert (> x 0.0))
(assert (> y 0.0))
(assert (< (* x y) 0.0))
(assert (= (f x) (f y)))
(check-sat)
"#,
    );
    // x>0, y>0, x*y<0 is UNSAT by NRA sign reasoning
    assert_eq!(results, vec!["unsat"]);
}

#[test]
fn test_uf_nra_nonlinear_sat() {
    // NRA with UF: f(x*x) > 0, x > 1 is SAT (any f works)
    let results = run_script(
        r#"
(set-logic QF_UFNRA)
(declare-fun f (Real) Real)
(declare-fun x () Real)
(assert (> (f (* x x)) 0.0))
(assert (> x 1.0))
(check-sat)
"#,
    );
    assert_eq!(results, vec!["sat"]);
}

// QF_NRA symbolic division SAT: x > 2 AND (/ 1 x) > 0
#[test]
fn nra_sat_symbolic_division() {
    let results = run_script(
        r#"
(set-logic QF_NRA)
(declare-const x Real)
(assert (> x 2))
(assert (> (/ 1 x) 0))
(check-sat)
"#,
    );
    assert_eq!(results, vec!["sat"]);
}

// --- clauseSMT NLSAT technique tests (#8445) ---

// Feasible-set look-ahead: product constraint where feasible set analysis
// immediately determines the solution. x = 2, x*y = 10, so y must be 5.
// The feasible set for y is {5}, a singleton (fixed variable).
#[test]
fn nra_clausesmt_fixed_variable_by_feasible_set() {
    let results = run_script(
        r#"
(set-logic QF_NRA)
(declare-const x Real)
(declare-const y Real)
(assert (= x 2.0))
(assert (= (* x y) 10.0))
(assert (>= y 4.0))
(assert (<= y 6.0))
(check-sat)
"#,
    );
    assert_eq!(results, vec!["sat"]);
}

// Arithmetic propagation branching: conflicting constraints create a blocked
// variable. x in [1,2], y in [1,2], but x*y must be >= 5 (impossible since
// max x*y = 4). The feasible set intersection for the product becomes empty.
#[test]
fn nra_clausesmt_blocked_variable_conflict() {
    let results = run_script(
        r#"
(set-logic QF_NRA)
(declare-const x Real)
(declare-const y Real)
(assert (>= x 1.0))
(assert (<= x 2.0))
(assert (>= y 1.0))
(assert (<= y 2.0))
(assert (>= (* x y) 5.0))
(check-sat)
"#,
    );
    assert_ne!(
        results,
        vec!["sat"],
        "blocked clauseSMT variable conflict must not be reported SAT"
    );
}

// clauseSMT path case: multiple constraints that narrow the feasible set
// to a small interval. x in [0,10], x >= 3, x <= 7, x*x <= 20.
// Feasible set for x: [3, sqrt(20)] ~ [3, 4.47].
// With theory-aware branching, solver should find solution quickly.
#[test]
fn nra_clausesmt_narrowed_feasible_set_sat() {
    let results = run_script(
        r#"
(set-logic QF_NRA)
(declare-const x Real)
(assert (>= x 0.0))
(assert (<= x 10.0))
(assert (>= x 3.0))
(assert (<= x 7.0))
(assert (<= (* x x) 20.0))
(check-sat)
"#,
    );
    assert_eq!(results, vec!["sat"]);
}

// Feasible set with multiple variables: x in [1,3], y in [1,3],
// x*y = 6 forces x=2,y=3 or x=3,y=2.
// Theory-aware branching should try phases consistent with feasible sets.
#[test]
fn nra_clausesmt_multi_var_feasible_set() {
    let results = run_script(
        r#"
(set-logic QF_NRA)
(declare-const x Real)
(declare-const y Real)
(assert (>= x 1.0))
(assert (<= x 3.0))
(assert (>= y 1.0))
(assert (<= y 3.0))
(assert (= (* x y) 6.0))
(check-sat)
"#,
    );
    // SAT: x=2,y=3 or x=3,y=2. Debug mode may return unknown due to
    // iteration limits on BigRational.
    let result = &results[0];
    assert!(
        result == "sat" || result == "unknown",
        "expected sat or unknown, got {result}"
    );
}

// Phase suggestion test: x > 0 and x*x < 0 is unsat.
// With feasible-set phase suggestions, the solver should immediately
// see that the product constraint creates an empty feasible set.
#[test]
fn nra_clausesmt_phase_suggestion_conflict() {
    let results = run_script(
        r#"
(set-logic QF_NRA)
(declare-const x Real)
(assert (> x 0.0))
(assert (< (* x x) 0.0))
(check-sat)
"#,
    );
    assert_eq!(results, vec!["unsat"]);
}

// Disequality feasible set: x != 3, x in [2,4] => feasible set is [2,3) U (3,4].
// Should still be sat (e.g., x = 2.5).
#[test]
fn nra_clausesmt_disequality_feasible_set() {
    let results = run_script(
        r#"
(set-logic QF_NRA)
(declare-const x Real)
(assert (>= x 2.0))
(assert (<= x 4.0))
(assert (not (= x 3.0)))
(assert (>= (* x x) 4.0))
(check-sat)
"#,
    );
    assert_eq!(results, vec!["sat"]);
}

include!("../nra_sign_tests.rs");

// Polynomial-identity normalization (commutative-ring normal form).
//
// These were all `unknown` before monomial canonicalization landed in `mk_mul`
// (sort non-constant factors + lift unary negations to a `-1` coefficient). With
// canonical monomials, `mk_add`'s coefficient collection cancels like terms, so a
// ring identity reduces both sides to the same term and its negation is UNSAT.

#[test]
fn nia_commutativity_is_unsat() {
    // (* a b) = (* b a): the canonical-monomial canary.
    let r = run_script(
        r#"
(set-logic QF_NIA)
(declare-fun a () Int)
(declare-fun b () Int)
(assert (not (= (* a b) (* b a))))
(check-sat)
"#,
    );
    assert_eq!(r, vec!["unsat"]);
}

#[test]
fn nia_difference_of_squares_identity_is_unsat() {
    // (a - b)(a + b) = a*a - b*b — requires lifting the sign out of the (- b)
    // cross term so it cancels (* a b).
    let r = run_script(
        r#"
(set-logic QF_NIA)
(declare-fun a () Int)
(declare-fun b () Int)
(assert (not (= (* (- a b) (+ a b)) (- (* a a) (* b b)))))
(check-sat)
"#,
    );
    assert_eq!(r, vec!["unsat"]);
}

#[test]
fn nia_square_of_sum_identity_is_unsat() {
    // (a + b)^2 = a*a + 2*a*b + b*b.
    let r = run_script(
        r#"
(set-logic QF_NIA)
(declare-fun a () Int)
(declare-fun b () Int)
(assert (not (= (* (+ a b) (+ a b)) (+ (* a a) (* 2 (* a b)) (* b b)))))
(check-sat)
"#,
    );
    assert_eq!(r, vec!["unsat"]);
}

#[test]
fn nia_distributivity_identity_is_unsat() {
    let r = run_script(
        r#"
(set-logic QF_NIA)
(declare-fun a () Int)
(declare-fun b () Int)
(declare-fun c () Int)
(assert (not (= (* a (+ b c)) (+ (* a b) (* a c)))))
(check-sat)
"#,
    );
    assert_eq!(r, vec!["unsat"]);
}

#[test]
fn nra_commutativity_and_diffsq_identities_are_unsat() {
    // Same identities over the reals.
    let comm = run_script(
        r#"
(set-logic QF_NRA)
(declare-fun a () Real)
(declare-fun b () Real)
(assert (not (= (* a b) (* b a))))
(check-sat)
"#,
    );
    assert_eq!(comm, vec!["unsat"]);
    let diffsq = run_script(
        r#"
(set-logic QF_NRA)
(declare-fun a () Real)
(declare-fun b () Real)
(assert (not (= (* (- a b) (+ a b)) (- (* a a) (* b b)))))
(check-sat)
"#,
    );
    assert_eq!(diffsq, vec!["unsat"]);
}

// ============================================================================
// NRA irrational-witness ALGEBRAIC MODEL regressions (TARGET nra_irrational).
//
// `x*x = 2 ∧ x > 0` is SAT only at the irrational `√2`. The solver used to
// report `sat` from the exact Sturm/IVT certificate but then FABRICATE a
// rational model (`x = 0` via completion defaulting) and blind the model-
// validation gates (`skip_model_eval` + `nra_algebraic_sat_active`) so the
// self-contradictory model shipped unchecked — `(get-value (x (* x x)))`
// returned `((x 0) ((* x x) 0))`, refuting the solver's own assertions.
//
// The real fix carries the witness end-to-end as an exact algebraic number
// (z3 `root-obj` parity): these tests pin the exact printed model, the exact
// compound evaluation, AND that full model validation genuinely ran and
// confirmed the model (the blinding flags are gone).
// ============================================================================

/// Run a script and return (outputs, last_model_validated).
fn run_script_with_validation(input: &str) -> (Vec<String>, bool) {
    let commands = parse(input).expect("SMT-LIB script should parse");
    let mut exec = Executor::new();
    let out = exec
        .execute_all(&commands)
        .expect("SMT-LIB script should execute");
    (out, exec.last_model_validated)
}

#[test]
fn nra_algebraic_sqrt2_model_is_exact_and_validated() {
    let (out, validated) = run_script_with_validation(
        r#"
(set-logic QF_NRA)
(declare-fun x () Real)
(assert (= (* x x) 2.0))
(assert (> x 0.0))
(check-sat)
(get-value (x (* x x) (> x 0.0)))
"#,
    );
    assert_eq!(out[0], "sat");
    // z3 4.15 parity: positive root of x^2 - 2 is root index 2; the compound
    // (* x x) reduces to the exact rational 2; the predicate is true.
    assert_eq!(
        out[1],
        "((x (root-obj (+ (^ x 2) (- 2)) 2)) ((* x x) 2.0) ((> x 0.0) true))"
    );
    assert!(
        validated,
        "full model validation must RUN and CONFIRM the algebraic model \
         (the skip_model_eval/nra_algebraic_sat_active blinding is gone)"
    );
}

#[test]
fn nra_algebraic_negative_root_index_matches_z3() {
    let (out, validated) = run_script_with_validation(
        r#"
(set-logic QF_NRA)
(declare-fun x () Real)
(assert (= (* x x) 2.0))
(assert (< x 0.0))
(check-sat)
(get-value (x (* x x) (< x 0.0)))
"#,
    );
    assert_eq!(out[0], "sat");
    // Negative root of x^2 - 2 is root index 1 (ascending order), like z3.
    assert_eq!(
        out[1],
        "((x (root-obj (+ (^ x 2) (- 2)) 1)) ((* x x) 2.0) ((< x 0.0) true))"
    );
    assert!(validated, "model validation must run and confirm");
}

#[test]
fn nra_algebraic_cbrt2_model() {
    let (out, validated) = run_script_with_validation(
        r#"
(set-logic QF_NRA)
(declare-fun x () Real)
(assert (= (* x x x) 2.0))
(check-sat)
(get-value (x (* x x x)))
"#,
    );
    assert_eq!(out[0], "sat");
    // Unique real root of x^3 - 2 (index 1); the cube evaluates to exactly 2.
    assert_eq!(
        out[1],
        "((x (root-obj (+ (^ x 3) (- 2)) 1)) ((* x x x) 2.0))"
    );
    assert!(validated, "model validation must run and confirm");
}

#[test]
fn nra_algebraic_get_model_prints_root_obj() {
    let (out, _) = run_script_with_validation(
        r#"
(set-logic QF_NRA)
(declare-fun x () Real)
(assert (= (* x x) 2.0))
(assert (> x 0.0))
(check-sat)
(get-model)
"#,
    );
    assert_eq!(out[0], "sat");
    assert!(
        out[1].contains("(define-fun x () Real (root-obj (+ (^ x 2) (- 2)) 2))"),
        "get-model must print the exact root-obj witness, got: {}",
        out[1]
    );
}

#[test]
fn nra_rational_root_still_plain_rational() {
    // x^2 = 4 ∧ x > 0 has the rational solution x = 2: no root-obj involved.
    let (out, validated) = run_script_with_validation(
        r#"
(set-logic QF_NRA)
(declare-fun x () Real)
(assert (= (* x x) 4.0))
(assert (> x 0.0))
(check-sat)
(get-value (x (* x x)))
"#,
    );
    assert_eq!(out[0], "sat");
    assert_eq!(out[1], "((x 2.0) ((* x x) 4.0))");
    assert!(validated, "rational-model validation must run and confirm");
}

#[test]
fn nra_algebraic_mixed_with_linear_substitution() {
    // y = 2 eliminates linearly; x*x = y then forces x = √2. Both variables
    // must carry exact, mutually consistent values.
    let (out, validated) = run_script_with_validation(
        r#"
(set-logic QF_NRA)
(declare-fun x () Real)
(declare-fun y () Real)
(assert (= y 2.0))
(assert (= (* x x) y))
(assert (> x 0.0))
(check-sat)
(get-value (x y (* x x)))
"#,
    );
    assert_eq!(out[0], "sat");
    assert_eq!(
        out[1],
        "((x (root-obj (+ (^ x 2) (- 2)) 2)) (y 2.0) ((* x x) 2.0))"
    );
    assert!(validated, "mixed model validation must run and confirm");
}

#[test]
fn nra_algebraic_compound_values_match_z3_derivations() {
    // x = -(5^(1/4)): compounds derive NEW algebraic numbers via resultants,
    // byte-identical to z3 4.15's root-obj output for the same query.
    let (out, validated) = run_script_with_validation(
        r#"
(set-logic QF_NRA)
(declare-fun x () Real)
(assert (= (* x x x x) 5.0))
(assert (< x 0.0))
(check-sat)
(get-value (x (* x x) (+ x 1.0) (* 3.0 x)))
"#,
    );
    assert_eq!(out[0], "sat");
    assert_eq!(
        out[1],
        "((x (root-obj (+ (^ x 4) (- 5)) 1)) \
         ((* x x) (root-obj (+ (^ x 2) (- 5)) 2)) \
         ((+ x 1.0) (root-obj (+ (^ x 4) (* (- 4) (^ x 3)) (* 6 (^ x 2)) (* (- 4) x) (- 4)) 1)) \
         ((* 3.0 x) (root-obj (+ (^ x 4) (- 405)) 1)))"
    );
    assert!(validated, "model validation must run and confirm");
}

#[test]
fn nra_algebraic_division_and_cross_variable_compounds() {
    // Two INDEPENDENT algebraic witnesses (x = sqrt2, y = sqrt3). Division by
    // an algebraic value inverts exactly via the reversed defining polynomial;
    // cross-variable compounds combine exactly via sum/product resultants.
    // Every printed root-obj below is byte-identical to z3 4.15's output for
    // the same query.
    let (out, validated) = run_script_with_validation(
        r#"
(set-logic QF_NRA)
(declare-fun x () Real)
(declare-fun y () Real)
(assert (= (* x x) 2.0))
(assert (= (* y y) 3.0))
(assert (> x 0.0))
(assert (> y 0.0))
(check-sat)
(get-value ((/ x 2.0) (/ 2.0 x) (+ x y) (* x y)))
"#,
    );
    assert_eq!(out[0], "sat");
    assert_eq!(
        out[1],
        "(((/ x 2.0) (root-obj (+ (* 2 (^ x 2)) (- 1)) 2)) \
         ((/ 2.0 x) (root-obj (+ (^ x 2) (- 2)) 2)) \
         ((+ x y) (root-obj (+ (^ x 4) (* (- 10) (^ x 2)) 1) 4)) \
         ((* x y) (root-obj (+ (^ x 2) (- 6)) 2)))"
    );
    assert!(validated, "model validation must run and confirm");
}

// ============================================================================
// Mandatory UNSAT-certificate funnel end-to-end (#nra-cert)
// ============================================================================
//
// Under the mandatory publication funnel every published `unsat` requires a
// strict certificate; a published "unsat" below therefore PROVES the pure-NRA
// theory lemma was classified (`NraIntervalUnsat`/`NraUnivariateUnsat`) and
// accepted by the independent checker kernel. Before #nra-cert these
// conflicts carried `TheoryLemmaKind::Generic` and the funnel demoted the
// answer to `unknown`.

/// Miniature Sturm-MBO shape: positive-orthant atoms plus an all-positive-
/// coefficient polynomial equated to zero, published as unsat THROUGH the
/// strict funnel via the interval certificate.
#[test]
fn nra_funnel_publishes_unsat_mini_mbo() {
    let results = run_script(
        r#"
(set-logic QF_NRA)
(declare-const h1 Real)
(declare-const h2 Real)
(declare-const j2 Real)
(assert (and (> h1 0.0) (> h2 0.0) (> j2 0.0)
             (= (+ (* 2.0 h1 h1 j2) (* 3.0 h2 j2 j2) (* h1 h2)) 0.0)))
(check-sat)
"#,
    );
    assert_eq!(
        results,
        vec!["unsat"],
        "mini-mbo must publish certified unsat"
    );
}

/// Miniature hong shape: sum of squares < 1 with product > 1.
#[test]
fn nra_funnel_publishes_unsat_mini_hong() {
    let results = run_script(
        r#"
(set-logic QF_NRA)
(declare-const x Real)
(declare-const y Real)
(declare-const z Real)
(assert (< (+ (* x x) (* y y) (* z z)) 1.0))
(assert (> (* x (* y z)) 1.0))
(check-sat)
"#,
    );
    assert_eq!(
        results,
        vec!["unsat"],
        "mini-hong must publish certified unsat"
    );
}

/// hong_1 itself: univariate x^2 < 1 against x > 1.
#[test]
fn nra_funnel_publishes_unsat_univariate_hong_one() {
    let results = run_script(
        r#"
(set-logic QF_NRA)
(declare-const x Real)
(assert (< (* x x) 1.0))
(assert (> x 1.0))
(check-sat)
"#,
    );
    assert_eq!(
        results,
        vec!["unsat"],
        "hong_1 shape must publish certified unsat"
    );
}

/// Negative guard: a SATISFIABLE univariate system (satisfiable only at the
/// irrational sqrt(2)) must never be claimed unsat — the sqrt(2) trap at the
/// solver level.
#[test]
fn nra_funnel_never_claims_satisfiable_univariate() {
    let results = run_script(
        r#"
(set-logic QF_NRA)
(declare-const x Real)
(assert (= (* x x) 2.0))
(assert (> x 0.0))
(check-sat)
"#,
    );
    assert_eq!(results.len(), 1);
    assert_ne!(
        results[0], "unsat",
        "satisfiable-at-sqrt(2) system must NEVER publish unsat"
    );
}
