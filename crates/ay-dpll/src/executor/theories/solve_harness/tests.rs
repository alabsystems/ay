// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use crate::Executor;
use ay_frontend::parse;
use num_rational::BigRational;
use num_traits::FromPrimitive;

mod split_atoms;
mod var_subst_provenance;

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
/// pass for THIS executor only, and the default is ON again.
///
/// The arms drive `preprocess_lia_artifacts` DIRECTLY rather than through
/// `(check-sat)`: that isolates the option from solve-time routing, so this
/// test pins the option's meaning and nothing else. The published-verdict
/// consequence is pinned separately by
/// `eq_diffvar_runs_and_mandatory_unsat_certification_survives`.
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

    // Default: ON. The two failures that made it opt-in no longer reproduce —
    // see `Executor::eq_diffvar_pass_enabled` for today's measurements.
    let exec = preprocess_only("");
    assert!(exec.eq_diffvar_pass_enabled());
    assert!(
        exec.statistics()
            .get_int("preprocess.eq_diffvar.diff_vars")
            .is_some_and(|n| n > 0),
        "the EqDiffVar reduction runs by default"
    );

    // Explicit opt-in is still honoured, unchanged.
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

/// #eq-diffvar-uncertifiable: the difference-variable reduction RUNS on a
/// default-mode public solve, and the mandatory UNSAT certification survives it.
///
/// This test used to assert the opposite — that the pass must not run — because
/// its fresh `d`, asserted via the definitional pair `(<= d lin)` / `(>= d lin)`,
/// is solver-invented: the reconstructed refutation's leaves for it carried no
/// `assume` authority, were demoted to unit `trust`, and mandatory certification
/// turned a correct `unsat` into `unknown`. On today's certification lanes
/// neither of the two historical failures reproduces, so the pass is enabled
/// again and this pins the property that actually matters.
///
/// It asserts three things per shape, and the third is the point: the verdict is
/// `unsat`, the pass DID run (so the verdict is not coming from a fallback that
/// quietly skipped the reduction), and the `unsat` is backed by a REAL
/// certificate rather than published as a bare admission. Without the third
/// assertion a future regression could re-introduce the downgrade and still pass
/// here by publishing an uncertified verdict.
///
/// (a) certifies STRICTLY; (b) certifies through the deferred-trust discharge
/// lane, which is a sanctioned discharge and not a downgrade — see the RESIDUAL
/// GAP note on `Executor::eq_diffvar_pass_enabled` for why (b) is not strict and
/// what the sound repair is.
#[test]
fn eq_diffvar_runs_and_mandatory_unsat_certification_survives() {
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
    assert!(
        exec.statistics()
            .get_int("preprocess.eq_diffvar.diff_vars")
            .is_some_and(|n| n > 0),
        "the reduction must actually have run — otherwise this proves nothing \
         about certification surviving it"
    );
    assert!(
        exec.last_command_unsat_was_strictly_verified()
            || exec.last_command_unsat_was_independently_verified()
            || exec.last_command_unsat_was_exact_semantically_verified(),
        "the `unsat` must be backed by a real certificate, not published as a \
         bare admission"
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
    assert!(
        exec.statistics()
            .get_int("preprocess.eq_diffvar.diff_vars")
            .is_some_and(|n| n > 0),
        "the reduction must actually have run — otherwise this proves nothing \
         about certification surviving it"
    );
    assert!(
        exec.last_command_unsat_was_strictly_verified()
            || exec.last_command_unsat_was_independently_verified()
            || exec.last_command_unsat_was_exact_semantically_verified(),
        "the `unsat` must be backed by a real certificate, not published as a \
         bare admission"
    );
}

// ---- #ppp-l3 licensing-source augmentation (template + helpers) ----

/// A rewritten assertion keeps its provenance, augmented with the licensing
/// definition's own sources, instead of the pre-L3 blanket `None`.
#[test]
fn int_const_substitution_augments_provenance_with_licensing_definition() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("l3_subst_x", Sort::Int);
    let y = terms.mk_var("l3_subst_y", Sort::Int);
    let five = terms.mk_int(num_bigint::BigInt::from(5));
    let definition = terms.mk_eq(x, five);
    let dependent = terms.mk_gt(x, y);
    // Original-root ids the window slots cite (stand-ins for authored roots).
    let def_root = definition;
    let dependent_root = dependent;
    let mut assertions = vec![definition, dependent];
    let mut source_sets = vec![Some(vec![vec![def_root]]), Some(vec![vec![dependent_root]])];

    let changed = substitute_int_constants_preserving_definitions(
        &mut terms,
        &mut assertions,
        &mut source_sets,
    );

    assert!(changed, "the dependent assertion must be rewritten");
    assert_eq!(assertions[0], definition, "definitions are preserved");
    let rewritten = assertions[1];
    assert_ne!(rewritten, dependent, "x must be replaced by 5");
    let mut expected = vec![def_root, dependent_root];
    expected.sort_by_key(|term| term.index());
    assert_eq!(
        source_sets[1],
        Some(vec![expected]),
        "the rewritten slot must cite its original AND the licensing definition"
    );
    assert_eq!(
        source_sets[0],
        Some(vec![vec![def_root]]),
        "the definition's own provenance is untouched"
    );
}

/// Fail-closed: a licensing definition whose own slot carries no provenance
/// must decline augmentation (the rewritten slot falls back to `None`).
#[test]
fn int_const_substitution_declines_augmentation_without_definition_provenance() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("l3_noprov_x", Sort::Int);
    let y = terms.mk_var("l3_noprov_y", Sort::Int);
    let five = terms.mk_int(num_bigint::BigInt::from(5));
    let definition = terms.mk_eq(x, five);
    let dependent = terms.mk_gt(x, y);
    let mut assertions = vec![definition, dependent];
    let mut source_sets = vec![None, Some(vec![vec![dependent]])];

    let changed = substitute_int_constants_preserving_definitions(
        &mut terms,
        &mut assertions,
        &mut source_sets,
    );

    assert!(changed);
    assert_eq!(
        source_sets[1], None,
        "an unprovenanced licensing definition must decline the augmentation"
    );
}

/// Guard-removal-proven cap: an augmented group above
/// `MAX_AUGMENTED_SOURCE_GROUP` members declines whole (fail-closed).
#[test]
fn augmented_source_groups_declines_over_cap() {
    let base = vec![vec![TermId(1)]];
    let extra_ok: Vec<TermId> = (2..=16).map(TermId).collect();
    assert!(
        augmented_source_groups(&base, &extra_ok).is_some(),
        "16 members total is within the cap"
    );
    let extra_over: Vec<TermId> = (2..=17).map(TermId).collect();
    assert!(
        augmented_source_groups(&base, &extra_over).is_none(),
        "17 members must decline the whole slot"
    );
}

/// The licensing walk maps every used replacement key through its recorded
/// definition and fails closed on a missing one.
#[test]
fn collect_used_int_const_definitions_is_exact_and_fail_closed() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("l3_walk_x", Sort::Int);
    let y = terms.mk_var("l3_walk_y", Sort::Int);
    let z = terms.mk_var("l3_walk_z", Sort::Int);
    let five = terms.mk_int(num_bigint::BigInt::from(5));
    let six = terms.mk_int(num_bigint::BigInt::from(6));
    let def_x = terms.mk_eq(x, five);
    let def_y = terms.mk_eq(y, six);
    let sum = terms.mk_add(vec![x, y]);
    let uses_both = terms.mk_gt(sum, z);
    let uses_none = terms.mk_gt(z, five);

    let mut replacements: HashMap<TermId, TermId> = HashMap::default();
    replacements.insert(x, five);
    replacements.insert(y, six);
    let mut definition_of: HashMap<TermId, TermId> = HashMap::default();
    definition_of.insert(x, def_x);
    definition_of.insert(y, def_y);

    let both = collect_used_int_const_definitions(&terms, &replacements, &definition_of, uses_both)
        .expect("both keys occur");
    assert_eq!(both.len(), 2);
    assert!(both.contains(&def_x) && both.contains(&def_y));
    assert!(
        collect_used_int_const_definitions(&terms, &replacements, &definition_of, uses_none)
            .is_none(),
        "no used key means no licensing claim"
    );

    definition_of.remove(&y);
    assert!(
        collect_used_int_const_definitions(&terms, &replacements, &definition_of, uses_both)
            .is_none(),
        "a used key without a recorded definition must fail closed"
    );
}
