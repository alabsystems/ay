// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Design §8 Rung 1 — `pushpop_fuzz`: random Bool/QF_LRA push/pop scripts
//! (≤ 12 vars, ≤ 40 assertions, ≤ 6 scopes, ≤ 30 checks) through the
//! session's API path vs from-scratch legacy `check_sat` and, when z3 is
//! available, vs z3. Seeded; fixed sample size (CLI-owned convention: no
//! env-tunable sample count/seed here — bump the constants to widen the
//! search locally). The z3-mandatory registration is
//! `tests/group_soundness/session_pushpop_vs_z3.rs`.

use crate::smt::session::harness::{gen_pushpop_script, run_pushpop_fuzz, Rng, Step};

/// Fixed sample size for [`pushpop_scripts_agree_with_legacy_and_z3`].
const FUZZ_N: u64 = 500;
/// Fixed seed for [`pushpop_scripts_agree_with_legacy_and_z3`].
const FUZZ_SEED: u64 = 2026;

#[test]
fn generator_respects_the_design_bounds() {
    let mut rng = Rng::new(7);
    for _ in 0..200 {
        let s = gen_pushpop_script(&mut rng);
        let vars = s.vocab.reals.len() + s.vocab.bools.len();
        assert!((2..=12).contains(&vars), "vars={vars}");
        let asserts = s
            .steps
            .iter()
            .filter(|x| matches!(x, Step::Assert(_)))
            .count();
        let checks = s.steps.iter().filter(|x| matches!(x, Step::Check)).count();
        assert!((1..=40).contains(&asserts), "asserts={asserts}");
        assert!((1..=30).contains(&checks), "checks={checks}");
        let mut depth = 0i64;
        for st in &s.steps {
            match st {
                Step::Push => depth += 1,
                Step::Pop => depth -= 1,
                _ => {}
            }
            assert!((0..=6).contains(&depth), "depth={depth}");
        }
    }
}

#[test]
fn pushpop_scripts_agree_with_legacy_and_z3() {
    let n = FUZZ_N;
    let seed = FUZZ_SEED;
    let report = run_pushpop_fuzz(seed, n, true);
    eprintln!("[pushpop_fuzz] {}", report.summary());
    for d in report.disagreements.iter().take(5) {
        eprintln!("[pushpop_fuzz] DISAGREEMENT {d}");
    }
    for e in report.errors.iter().take(5) {
        eprintln!("[pushpop_fuzz] ERROR {e}");
    }
    assert!(
        report.errors.is_empty(),
        "harness errors: {:?}",
        report.errors
    );
    assert!(
        report.disagreements.is_empty(),
        "{} disagreements (first: {})",
        report.disagreements.len(),
        report.disagreements[0]
    );
    assert_eq!(report.real_false_unsat, 0, "Real false-UNSAT counter");
    assert!(report.checks >= n, "every script has at least one check");
    // The session must decide the bulk of these tiny scripts.
    let decided = report.session_sat + report.session_unsat;
    assert!(
        decided * 100 >= report.checks * 95,
        "session decided {decided}/{} (< 95 %): {}",
        report.checks,
        report.summary()
    );
    assert_eq!(report.ext_full_reset_hits, 0, "ext_full_reset_hits");
}

/// Regression lock for the bridge's scope cursor (WP-4 integration finding,
/// found by this fuzz): after a backjump ay-sat appends the learned clause's
/// literal at the trail positions the popped level's non-atom prefix used to
/// occupy; with the ATOM's position as the scope cursor those literals were
/// never fed, and `(E ∨ b) ∧ (E ∨ ¬b) ∧ i = -1 ∧ x0 = 0` with `E = (i = x0)`
/// came back SAT with a model violating E. Every shape below is UNSAT (or
/// SAT with the documented model) through the session's API path.
#[test]
fn backjump_appended_literals_are_fed_after_scope_restore() {
    use crate::smt::session::{HornCheck, HornSmt, SessionConfig};
    use crate::smt::types::Partition;
    use crate::ChcExpr;
    use std::sync::Arc;
    let cases = backjump_regression_cases();
    for (name, expect_sat, exprs) in cases {
        for cold in [true, false] {
            let mut cfg = SessionConfig::new();
            cfg.cold_theory_assignment = cold;
            let mut s = HornSmt::new(cfg, None);
            let ids: Vec<_> = exprs
                .iter()
                .map(|e| {
                    s.assert_persistent(&Arc::new(e.clone()), Partition::AB)
                        .unwrap()
                })
                .collect();
            // Strictly verified: a wrong model would come back as Unknown here.
            let r = s.check_assuming(&ids, &[], Some(std::time::Duration::from_secs(5)));
            match (expect_sat, &r) {
                (true, HornCheck::Sat(_)) | (false, HornCheck::Unsat { .. }) => {}
                _ => panic!("{name} (cold={cold}): expected sat={expect_sat}, got {r:?}"),
            }
            let conj = ChcExpr::and_all(exprs.clone());
            let l = crate::smt::SmtContext::new()
                .check_sat_with_timeout(&conj, std::time::Duration::from_secs(5));
            assert_eq!(l.is_sat(), expect_sat, "{name}: legacy disagrees");
        }
    }
}

/// The shapes `backjump_appended_literals_are_fed_after_scope_restore` runs,
/// each with whether it is satisfiable.
fn backjump_regression_cases() -> Vec<(&'static str, bool, Vec<crate::ChcExpr>)> {
    let vars = CaseVars::new();
    let mut cases = backjump_first_shapes(&vars);
    cases.extend(backjump_later_shapes(&vars));
    cases
}

/// The variables every backjump regression shape is built from.
struct CaseVars {
    b1: crate::ChcExpr,
    b2: crate::ChcExpr,
    x4: crate::ChcExpr,
    x0: crate::ChcExpr,
    i: crate::ChcExpr,
}

impl CaseVars {
    fn new() -> Self {
        use crate::{ChcExpr, ChcSort, ChcVar};
        let var = |name: &str, sort: ChcSort| ChcExpr::var(ChcVar::new(name, sort));
        Self {
            b1: var("b1", ChcSort::Bool),
            b2: var("b2", ChcSort::Bool),
            x4: var("x4", ChcSort::Real),
            x0: var("x0", ChcSort::Real),
            i: var("i", ChcSort::Real),
        }
    }
}

/// The Bool/ITE/OR shapes of the original finding.
fn backjump_first_shapes(v: &CaseVars) -> Vec<(&'static str, bool, Vec<crate::ChcExpr>)> {
    use crate::ChcExpr;
    let CaseVars { b1, b2, x4, x0, i } = v;
    let e = || ChcExpr::eq(i.clone(), x0.clone());
    vec![
        (
            "bool-eq",
            false,
            vec![
                ChcExpr::eq(b1.clone(), ChcExpr::eq(x4.clone(), ChcExpr::Real(5, 1))),
                ChcExpr::not(b1.clone()),
                ChcExpr::eq(x4.clone(), ChcExpr::Real(5, 1)),
            ],
        ),
        (
            "ite-same",
            false,
            vec![
                ChcExpr::eq(
                    ChcExpr::ite(b2.clone(), x0.clone(), x0.clone()),
                    ChcExpr::Real(-1, 1),
                ),
                ChcExpr::eq(x0.clone(), ChcExpr::Real(0, 1)),
            ],
        ),
        (
            "ite-same swapped",
            false,
            vec![
                ChcExpr::eq(x0.clone(), ChcExpr::Real(0, 1)),
                ChcExpr::eq(
                    ChcExpr::ite(b2.clone(), x0.clone(), x0.clone()),
                    ChcExpr::Real(-1, 1),
                ),
            ],
        ),
        (
            "hand-ite",
            false,
            vec![
                ChcExpr::and_all([
                    ChcExpr::implies(b2.clone(), e()),
                    ChcExpr::implies(ChcExpr::not(b2.clone()), e()),
                    ChcExpr::eq(i.clone(), ChcExpr::Real(-1, 1)),
                ]),
                ChcExpr::eq(x0.clone(), ChcExpr::Real(0, 1)),
            ],
        ),
        (
            "or-shape",
            false,
            vec![
                ChcExpr::or(e(), b2.clone()),
                ChcExpr::or(e(), ChcExpr::not(b2.clone())),
                ChcExpr::eq(i.clone(), ChcExpr::Real(-1, 1)),
                ChcExpr::eq(x0.clone(), ChcExpr::Real(0, 1)),
            ],
        ),
    ]
}

/// The fuzz script's prefix, the constant-equality shapes, and the SAT
/// controls.
fn backjump_later_shapes(v: &CaseVars) -> Vec<(&'static str, bool, Vec<crate::ChcExpr>)> {
    use crate::{ChcExpr, ChcSort, ChcVar};
    let CaseVars { b1, b2, x4, x0, .. } = v;
    vec![
        (
            "script21-prefix",
            true,
            vec![
                ChcExpr::eq(
                    ChcExpr::ite(b2.clone(), x0.clone(), x0.clone()),
                    ChcExpr::Real(-1, 1),
                ),
                ChcExpr::eq(b1.clone(), ChcExpr::eq(x4.clone(), ChcExpr::Real(5, 1))),
                ChcExpr::or_vec(vec![
                    ChcExpr::gt(
                        ChcExpr::sub(
                            ChcExpr::mul(ChcExpr::Real(-1, 1), x4.clone()),
                            ChcExpr::var(ChcVar::new("x3", ChcSort::Real)),
                        ),
                        ChcExpr::Real(-5, 1),
                    ),
                    ChcExpr::eq(x0.clone(), ChcExpr::Real(-1, 1)),
                    ChcExpr::gt(
                        ChcExpr::var(ChcVar::new("x2", ChcSort::Real)),
                        ChcExpr::Real(-7, 1),
                    ),
                ]),
            ],
        ),
        (
            "constant-eq x0+7=x0",
            false,
            vec![ChcExpr::eq(
                ChcExpr::add(x0.clone(), ChcExpr::Real(7, 1)),
                x0.clone(),
            )],
        ),
        (
            "constant-eq with a bound",
            false,
            vec![
                ChcExpr::eq(ChcExpr::add(x0.clone(), ChcExpr::Real(7, 1)), x0.clone()),
                ChcExpr::ge(x0.clone(), ChcExpr::Real(1, 1)),
            ],
        ),
        (
            "ite-same alone",
            true,
            vec![ChcExpr::eq(
                ChcExpr::ite(b2.clone(), x0.clone(), x0.clone()),
                ChcExpr::Real(-1, 1),
            )],
        ),
        (
            "bool-eq alone",
            true,
            vec![
                ChcExpr::eq(b1.clone(), ChcExpr::eq(x4.clone(), ChcExpr::Real(5, 1))),
                ChcExpr::not(b1.clone()),
            ],
        ),
    ]
}

/// ay-sat-level twin of `backjump_appended_literals_are_fed_after_scope_restore`
/// (no theory): the session's SAT profile with the exact Tseitin clauses of
/// fuzz script 21's first assertion, one assumption. The model must satisfy
/// every clause (a missing propagation of var 3 from `[-5, 4, 3]` under
/// `5 ∧ ¬4` is what the session trace showed).
#[test]
fn session_sat_profile_propagates_deferred_definition_clauses() {
    use ay_sat::Literal;
    let mut sat = ay_sat::Solver::new(0);
    sat.set_ic3_mode();
    sat.set_bve_enabled(false);
    sat.set_inc_engine_reset_mode(true);
    sat.set_random_seed(0);
    sat.set_unsat_certificate_enabled(false);
    sat.set_preprocess_enabled(false);
    for _ in 0..7 {
        let _ = sat.new_var();
    }
    let clauses: Vec<Vec<i32>> = vec![
        vec![-2, 3, -4],
        vec![-3, 2],
        vec![4, 2],
        vec![-5, 4, 3],
        vec![-4, 5],
        vec![-3, 5],
        vec![-1, 2],
        vec![-1, 5],
        vec![-1, 6],
        vec![-2, -5, -6, 1],
        // (root ∨ act)
        vec![1, 7],
    ];
    for c in &clauses {
        sat.add_clause_global(c.iter().map(|&d| Literal::from_dimacs(d)).collect());
    }
    // Force b2 (var 4) false through the search: a second assumption.
    for round in 0..2 {
        let assumptions = if round == 0 {
            vec![Literal::from_dimacs(-7)]
        } else {
            vec![Literal::from_dimacs(-7), Literal::from_dimacs(-4)]
        };
        let r = sat.solve_with_assumptions(&assumptions);
        assert!(r.is_sat(), "round {round}: expected SAT");
        let model = r.model().expect("model").to_vec();
        let val = |d: i32| {
            let v = model[(d.unsigned_abs() - 1) as usize];
            if d > 0 {
                v
            } else {
                !v
            }
        };
        for c in &clauses {
            assert!(
                c.iter().any(|&d| val(d)),
                "round {round}: clause {c:?} falsified by model {model:?}"
            );
        }
        assert!(!val(7), "assumption ¬act holds");
        if round == 1 {
            assert!(
                !val(4) && val(3),
                "¬b2 forces E (var 3) true; model {model:?}"
            );
        }
    }
}
