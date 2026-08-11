// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use crate::Executor;
use ay_core::{Sort, TermStore};
use ay_frontend::parse;
use num_bigint::BigInt;
use num_rational::BigRational;
use num_traits::FromPrimitive;

fn rat(n: i64) -> BigRational {
    BigRational::from_i64(n).unwrap()
}

fn run_script(input: &str) -> Vec<String> {
    let commands = parse(input).expect("SMT-LIB script should parse");
    let mut exec = Executor::new();
    exec.execute_all(&commands)
        .expect("SMT-LIB script should execute")
}

#[test]
fn test_check_split_oscillation_first_call_returns_false() {
    let mut tracking = SplitOscillationMap::default();
    let var = TermId(1);
    assert!(!check_split_oscillation(&mut tracking, var, &rat(5)));
    // Variable should be seeded with count 0
    assert_eq!(tracking[&var].1, 0);
}

#[test]
fn test_check_split_oscillation_monotonic_increase_triggers() {
    let mut tracking = SplitOscillationMap::default();
    let var = TermId(1);
    // Seed
    assert!(!check_split_oscillation(&mut tracking, var, &rat(0)));
    // 20 consecutive increases should trigger at UNBOUNDED_THRESHOLD=20
    for i in 1..=19 {
        assert!(
            !check_split_oscillation(&mut tracking, var, &rat(i)),
            "should not trigger at step {i}"
        );
    }
    // The 20th increase hits the threshold
    assert!(check_split_oscillation(&mut tracking, var, &rat(20)));
}

#[test]
fn test_check_split_oscillation_monotonic_decrease_triggers() {
    let mut tracking = SplitOscillationMap::default();
    let var = TermId(1);
    // Seed at 100
    assert!(!check_split_oscillation(&mut tracking, var, &rat(100)));
    // 20 consecutive decreases
    for i in 1..=19 {
        assert!(
            !check_split_oscillation(&mut tracking, var, &rat(100 - i)),
            "should not trigger at step {i}"
        );
    }
    assert!(check_split_oscillation(&mut tracking, var, &rat(80)));
}

#[test]
fn test_check_split_oscillation_direction_reversal_resets() {
    let mut tracking = SplitOscillationMap::default();
    let var = TermId(1);
    // Seed
    assert!(!check_split_oscillation(&mut tracking, var, &rat(0)));
    // 10 increases
    for i in 1..=10 {
        assert!(!check_split_oscillation(&mut tracking, var, &rat(i)));
    }
    assert_eq!(tracking[&var].1, 10); // count is +10
                                      // One decrease resets to -1
    assert!(!check_split_oscillation(&mut tracking, var, &rat(9)));
    assert_eq!(tracking[&var].1, -1);
    // Now 18 more decreases (total 19 including the first reversal)
    for i in 2..=19 {
        assert!(
            !check_split_oscillation(&mut tracking, var, &rat(9 - i)),
            "should not trigger at decrease step {i}"
        );
    }
    // 20th decrease triggers
    assert!(check_split_oscillation(&mut tracking, var, &rat(-12)));
}

#[test]
fn test_check_split_oscillation_equal_value_resets_to_zero() {
    let mut tracking = SplitOscillationMap::default();
    let var = TermId(1);
    assert!(!check_split_oscillation(&mut tracking, var, &rat(5)));
    // Increase 15 times
    for i in 1..=15 {
        assert!(!check_split_oscillation(&mut tracking, var, &rat(5 + i)));
    }
    assert_eq!(tracking[&var].1, 15);
    // Same value → count resets to 0
    assert!(!check_split_oscillation(&mut tracking, var, &rat(20)));
    assert_eq!(tracking[&var].1, 0);
}

#[test]
fn test_check_split_oscillation_independent_variables() {
    let mut tracking = SplitOscillationMap::default();
    let var_a = TermId(1);
    let var_b = TermId(2);
    // Seed both
    assert!(!check_split_oscillation(&mut tracking, var_a, &rat(0)));
    assert!(!check_split_oscillation(&mut tracking, var_b, &rat(0)));
    // Increase var_a 19 times
    for i in 1..=19 {
        assert!(!check_split_oscillation(&mut tracking, var_a, &rat(i)));
    }
    // var_b has its own count — 1 increase does not trigger
    assert!(!check_split_oscillation(&mut tracking, var_b, &rat(1)));
    assert_eq!(tracking[&var_b].1, 1);
    // var_a's 20th triggers
    assert!(check_split_oscillation(&mut tracking, var_a, &rat(20)));
}

#[test]
fn test_create_disequality_split_atoms_skips_non_numeric_variables() {
    let mut terms = TermStore::new();
    let b = terms.mk_var("b", Sort::Bool);
    let split = ay_core::DisequalitySplitRequest {
        variable: b,
        excluded_value: rat(1),
        disequality_term: None,
        is_distinct: false,
    };

    assert!(matches!(
        create_disequality_split_atoms(&mut terms, &split),
        DisequalitySplitAtoms::Skip
    ));
}

#[test]
fn test_create_disequality_split_atoms_int_fractional_uses_floor_ceil_bounds() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let split = ay_core::DisequalitySplitRequest {
        variable: x,
        excluded_value: BigRational::new(BigInt::from(7), BigInt::from(2)),
        disequality_term: None,
        is_distinct: false,
    };

    let three = terms.mk_int(BigInt::from(3));
    let four = terms.mk_int(BigInt::from(4));
    let expected_le = terms.mk_le(x, three);
    let expected_ge = terms.mk_ge(x, four);

    match create_disequality_split_atoms(&mut terms, &split) {
        DisequalitySplitAtoms::IntFractional { le, ge } => {
            assert_eq!(le, expected_le);
            assert_eq!(ge, expected_ge);
        }
        _ => panic!("expected IntFractional split atoms"),
    }
}

#[test]
fn test_create_disequality_split_atoms_int_exact_preserves_context() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let five = terms.mk_int(BigInt::from(5));
    let eq = terms.mk_eq(x, five);
    let diseq = terms.mk_not(eq);
    let split = ay_core::DisequalitySplitRequest {
        variable: x,
        excluded_value: rat(5),
        disequality_term: Some(diseq),
        is_distinct: true,
    };

    let four = terms.mk_int(BigInt::from(4));
    let six = terms.mk_int(BigInt::from(6));
    let expected_le = terms.mk_le(x, four);
    let expected_ge = terms.mk_ge(x, six);

    match create_disequality_split_atoms(&mut terms, &split) {
        DisequalitySplitAtoms::IntExact {
            le,
            ge,
            disequality_term,
            is_distinct,
        } => {
            assert_eq!(le, expected_le);
            assert_eq!(ge, expected_ge);
            assert_eq!(disequality_term, Some(diseq));
            assert!(is_distinct);
        }
        _ => panic!("expected IntExact split atoms"),
    }
}

#[test]
fn test_create_disequality_split_atoms_real_uses_strict_inequalities() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let excluded_term_for_eq =
        terms.mk_rational(BigRational::new(BigInt::from(9), BigInt::from(4)));
    let eq = terms.mk_eq(x, excluded_term_for_eq);
    let excluded = BigRational::new(BigInt::from(9), BigInt::from(4));
    let split = ay_core::DisequalitySplitRequest {
        variable: x,
        excluded_value: excluded.clone(),
        disequality_term: Some(eq),
        is_distinct: false,
    };

    let excluded_term = terms.mk_rational(excluded);
    let expected_lt = terms.mk_lt(x, excluded_term);
    let expected_gt = terms.mk_gt(x, excluded_term);

    match create_disequality_split_atoms(&mut terms, &split) {
        DisequalitySplitAtoms::Real {
            lt,
            gt,
            disequality_term,
            is_distinct,
        } => {
            assert_eq!(lt, expected_lt);
            assert_eq!(gt, expected_gt);
            assert_eq!(disequality_term, Some(eq));
            assert!(!is_distinct);
        }
        _ => panic!("expected Real split atoms"),
    }
}

#[test]
fn test_create_int_split_atoms_real_sort_uses_rational_constants_and_prefer_ceil() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let split = ay_core::SplitRequest {
        variable: x,
        value: BigRational::new(BigInt::from(7), BigInt::from(4)),
        floor: BigInt::from(1),
        ceil: BigInt::from(2),
    };

    let one = terms.mk_rational(BigRational::from(BigInt::from(1)));
    let two = terms.mk_rational(BigRational::from(BigInt::from(2)));
    let expected_le = terms.mk_le(x, one);
    let expected_ge = terms.mk_ge(x, two);

    let (le, ge, prefer_ceil) = create_int_split_atoms(&mut terms, &split);
    assert_eq!(le, expected_le);
    assert_eq!(ge, expected_ge);
    assert_eq!(prefer_ceil, Some(true));
}

#[test]
fn test_create_int_split_atoms_exact_half_prefers_floor_first() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let split = ay_core::SplitRequest {
        variable: x,
        value: BigRational::new(BigInt::from(3), BigInt::from(2)),
        floor: BigInt::from(1),
        ceil: BigInt::from(2),
    };

    let one = terms.mk_int(BigInt::from(1));
    let two = terms.mk_int(BigInt::from(2));
    let expected_le = terms.mk_le(x, one);
    let expected_ge = terms.mk_ge(x, two);

    let (le, ge, prefer_ceil) = create_int_split_atoms(&mut terms, &split);
    assert_eq!(le, expected_le);
    assert_eq!(ge, expected_ge);
    assert_eq!(prefer_ceil, Some(false));
}

#[test]
fn auflia_mod_by_propagated_constant_reaches_lia_8961() {
    let input = r#"
        (set-logic QF_UFLIA)
        (declare-fun f (Int) Int)
        (declare-const x Int)
        (declare-const k Int)
        (assert (= (f 0) 1))
        (assert (= x 3))
        (assert (= k 2))
        (assert (= (mod x k) 0))
        (check-sat)
    "#;

    assert_eq!(run_script(input), vec!["unsat"]);
}

/// Inc-18: a guarded var-var equality script that makes the EqDiffVar pass
/// fire (two syntactic variants of the same difference under guards).
const EQ_DIFFVAR_GUARDED_SCRIPT: &str = r#"
    (set-logic QF_LIA)
    {OPT}
    (declare-const g1 Bool)
    (declare-const g2 Bool)
    (declare-const x Int)
    (declare-const y Int)
    (assert (or g1 (= x y)))
    (assert (or g2 (= y x)))
    (assert (or (not g1) (not g2)))
    (check-sat)
"#;

/// Inc-18 / #eq-diffvar-uncertifiable: `:ay-eq-diffvar` selects the EqDiffVar
/// pass for THIS executor only, and the default is OFF.
///
/// The arms drive `preprocess_lia_artifacts` DIRECTLY rather than through
/// `(check-sat)`: that isolates the option from solve-time routing, so this
/// test pins the option's meaning and nothing else. The published-verdict
/// consequence is pinned separately by
/// `eq_diffvar_must_not_break_mandatory_unsat_certification`.
#[test]
fn set_option_ay_eq_diffvar_selects_pass_per_run() {
    /// Load the declares/asserts (no `(check-sat)`, so no public solve begins),
    /// then run LIA preprocessing directly.
    fn preprocess_only(opt: &str) -> Executor {
        let script = EQ_DIFFVAR_GUARDED_SCRIPT
            .replace("{OPT}", opt)
            .replace("(check-sat)", "");
        let commands = parse(&script).expect("parse");
        let mut exec = Executor::new();
        exec.execute_all(&commands).expect("exec");
        let _ = exec.preprocess_lia_artifacts();
        exec
    }

    // Default: OFF. The reduction is opt-in because it costs correct `unsat`
    // verdicts — see `Executor::eq_diffvar_pass_enabled`.
    let exec = preprocess_only("");
    assert!(!exec.eq_diffvar_pass_enabled());
    assert_eq!(
        exec.statistics().get_int("preprocess.eq_diffvar.diff_vars"),
        None,
        "the EqDiffVar reduction must be opt-in"
    );

    // Explicit opt-in still runs the pass, unchanged.
    let exec = preprocess_only("(set-option :ay-eq-diffvar true)");
    assert!(exec.eq_diffvar_pass_enabled());
    assert!(
        exec.statistics()
            .get_int("preprocess.eq_diffvar.diff_vars")
            .is_some_and(|n| n > 0),
        "(set-option :ay-eq-diffvar true) must still enable the pass"
    );

    // Explicit opt-out is honoured too (ay-chc's retry writes it literally).
    let exec = preprocess_only("(set-option :ay-eq-diffvar false)");
    assert!(!exec.eq_diffvar_pass_enabled());

    // The verdict is the same in every mode: the pass is a pure reduction.
    for opt in [
        "",
        "(set-option :ay-eq-diffvar true)",
        "(set-option :ay-eq-diffvar false)",
    ] {
        let script = EQ_DIFFVAR_GUARDED_SCRIPT.replace("{OPT}", opt);
        let commands = parse(&script).expect("parse");
        let mut exec = Executor::new();
        assert_eq!(exec.execute_all(&commands).expect("exec"), vec!["sat"]);
    }
}

/// Inc-21: a script where top-level unit-clause propagation (inc-13) fires —
/// the unit `p` deletes the `(not p)` disjunct from both or-assertions.
const UNIT_PROP_SCRIPT: &str = r#"
    (set-logic QF_LIA)
    {OPT}
    (declare-const p Bool)
    (declare-const q Bool)
    (declare-const x Int)
    (assert p)
    (assert (or (not p) (= x 1)))
    (assert (or (not p) q))
    (check-sat)
"#;

/// Inc-21: `(set-option :ay-unit-prop false)` disables the inc-13 top-level
/// unit-clause propagation for THIS executor only — the rewrite statistic
/// must be absent, and the verdict must be unchanged (the pass is a pure
/// simplification).
#[test]
fn set_option_ay_unit_prop_false_disables_pass_per_run() {
    // Default run (no option): pass fires, statistic present.
    let on_script = UNIT_PROP_SCRIPT.replace("{OPT}", "");
    let commands = parse(&on_script).expect("parse");
    let mut exec = Executor::new();
    let out = exec.execute_all(&commands).expect("exec");
    assert_eq!(out, vec!["sat"]);
    assert!(
        exec.statistics()
            .get_int("preprocess.unit_prop.rewritten_assertions")
            .is_some_and(|n| n > 0),
        "unit propagation should rewrite the or-assertions by default"
    );

    // Option run: pass disabled per-run, same verdict.
    let off_script = UNIT_PROP_SCRIPT.replace("{OPT}", "(set-option :ay-unit-prop false)");
    let commands = parse(&off_script).expect("parse");
    let mut exec = Executor::new();
    let out = exec.execute_all(&commands).expect("exec");
    assert_eq!(out, vec!["sat"]);
    assert_eq!(
        exec.statistics()
            .get_int("preprocess.unit_prop.rewritten_assertions"),
        None,
        "(set-option :ay-unit-prop false) must disable the pass for this run"
    );
}

/// #eq-diffvar-uncertifiable: the difference-variable reduction must not run
/// on a DEFAULT-mode public solve.
///
/// The pass asserts a fresh `d` via the definitional pair `(<= d lin)` /
/// `(>= d lin)`. Those assertions are solver-invented, so the reconstructed
/// refutation's leaves for them carry no `assume` authority and are demoted
/// to unit `trust` — which the MANDATORY UNSAT certification rejects, turning
/// a correct `unsat` into `unknown`. The certification's rescue re-solve is
/// no way out either: that executor inherits `ctx`, so it inherits the pass,
/// and on the guarded shape the pass is what makes it miss its 2000ms budget.
///
/// This pins the PUBLISHED VERDICT, not the pass wiring — the point is the
/// answer, and both queries below published `unknown` while the pass defaulted
/// on. z3 agrees `unsat` on both. `preprocess.eq_diffvar.diff_vars` is asserted
/// absent only as the attribution: it says WHY the verdict came back, so a
/// future change that re-enables the pass fails here loudly instead of
/// silently trading the verdict away again.
#[test]
fn eq_diffvar_must_not_break_mandatory_unsat_certification() {
    // (a) Unguarded: `distinct` over three ints in a two-value range. Three
    // disequality atoms, three difference variables, no sharing at all.
    let pigeon = r#"
        (set-logic QF_LIA)
        (declare-const p1 Int)
        (declare-const p2 Int)
        (declare-const p3 Int)
        (assert (>= p1 1))
        (assert (<= p1 2))
        (assert (>= p2 1))
        (assert (<= p2 2))
        (assert (>= p3 1))
        (assert (<= p3 2))
        (assert (distinct p1 p2 p3))
        (check-sat)
    "#;
    let commands = parse(pigeon).expect("parse");
    let mut exec = Executor::new();
    assert_eq!(
        exec.execute_all(&commands).expect("exec"),
        vec!["unsat"],
        "3 pigeons / 2 holes is UNSAT (z3 agrees); a preprocessing pass that \
         costs the mandatory UNSAT certificate must not run here"
    );
    assert_eq!(
        exec.statistics().get_int("preprocess.eq_diffvar.diff_vars"),
        None,
        "the verdict must come from the plain pipeline, not from a run that \
         happened to certify despite the reduction"
    );

    // (b) Guarded var-var equality chain — the pass's own target shape.
    let guarded = r#"
        (set-logic QF_LIA)
        (declare-const g1 Bool)
        (declare-const g2 Bool)
        (declare-const x Int)
        (declare-const y Int)
        (declare-const a Int)
        (declare-const b Int)
        (assert (or (not g1) (= a x)))
        (assert (or (not g1) (= b y)))
        (assert (or g1 (= a y)))
        (assert (or g1 (= b x)))
        (assert (or (not g2) (= (+ x y) 1)))
        (assert (or g2 (= (+ a b) 1)))
        (assert (not (= (+ x y) 1)))
        (check-sat)
    "#;
    let commands = parse(guarded).expect("parse");
    let mut exec = Executor::new();
    assert_eq!(
        exec.execute_all(&commands).expect("exec"),
        vec!["unsat"],
        "the guarded conservation network is UNSAT and must certify"
    );
    assert_eq!(
        exec.statistics().get_int("preprocess.eq_diffvar.diff_vars"),
        None,
        "the verdict must come from the plain pipeline, not from a run that \
         happened to certify despite the reduction"
    );
}
