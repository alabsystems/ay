// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Unit tests for the bounded Nielsen word-equation solver.

use super::*;

fn var(v: u32) -> WeSym {
    WeSym::Var(v)
}

fn lit(s: &str) -> Vec<WeSym> {
    s.chars().map(WeSym::Ch).collect()
}

fn word(parts: &[&[WeSym]]) -> WeWord {
    parts.iter().flat_map(|p| p.iter().copied()).collect()
}

fn eq(lhs: WeWord, rhs: WeWord) -> WeEquation {
    WeEquation { lhs, rhs }
}

fn check(assignment: &WeAssignment, eqn: &WeEquation) -> bool {
    let eval = |w: &WeWord| -> String {
        w.iter()
            .map(|s| match s {
                WeSym::Ch(c) => c.to_string(),
                WeSym::Var(v) => assignment
                    .iter()
                    .find(|(u, _)| u == v)
                    .map(|(_, s)| s.clone())
                    .unwrap_or_default(),
            })
            .collect()
    };
    eval(&eqn.lhs) == eval(&eqn.rhs)
}

fn solve(problem: &WeProblem) -> WeOutcome {
    let outcome = solve_word_equations(problem, &WeConfig::default());
    // Internal consistency: every returned assignment must satisfy every
    // equation (the solver's own ground check, independent of the caller's).
    if let WeOutcome::Sat(sols) = &outcome {
        assert!(!sols.is_empty());
        for sol in sols {
            for e in &problem.equations {
                assert!(check(sol, e), "candidate {sol:?} violates {e:?}");
            }
            for d in &problem.disequations {
                assert!(!check(sol, d), "candidate {sol:?} violates diseq {d:?}");
            }
            for m in &problem.memberships {
                let value = sol
                    .iter()
                    .find(|(u, _)| *u == m.var)
                    .map(|(_, s)| s.clone())
                    .unwrap_or_default();
                assert_eq!(
                    m.regex.matches(&value),
                    Some(m.positive),
                    "candidate {sol:?} violates membership {m:?}"
                );
            }
            for b in &problem.len_bounds {
                let n = sol
                    .iter()
                    .find(|(u, _)| *u == b.var)
                    .map(|(_, s)| s.chars().count())
                    .unwrap_or_default();
                assert!(
                    n >= b.lo && b.hi.is_none_or(|h| n <= h),
                    "candidate {sol:?} violates length bound {b:?}"
                );
            }
        }
    }
    outcome
}

#[test]
fn sat_x_ab_eq_a_y() {
    // x ++ "ab" = "a" ++ y   (sat: x="", y="b" among others)
    let p = WeProblem {
        equations: vec![eq(
            word(&[&[var(0)], &lit("ab")]),
            word(&[&lit("a"), &[var(1)]]),
        )],
        num_vars: 2,
        ..Default::default()
    };
    assert!(matches!(solve(&p), WeOutcome::Sat(_)));
}

#[test]
fn unsat_xx_eq_aba_by_parity() {
    // x ++ x = "aba"  (unsat: 2|x| = 3)
    let p = WeProblem {
        equations: vec![eq(word(&[&[var(0)], &[var(0)]]), lit("aba"))],
        num_vars: 1,
        ..Default::default()
    };
    assert_eq!(solve(&p), WeOutcome::Unsat);
}

#[test]
fn unsat_parikh_a_x_eq_x_b() {
    // "a" ++ x = x ++ "b"  (unsat: char counts differ once x cancels)
    let p = WeProblem {
        equations: vec![eq(
            word(&[&lit("a"), &[var(0)]]),
            word(&[&[var(0)], &lit("b")]),
        )],
        num_vars: 1,
        ..Default::default()
    };
    assert_eq!(solve(&p), WeOutcome::Unsat);
}

#[test]
fn sat_commutation_a_x_eq_x_a() {
    // "a" ++ x = x ++ "a"  (sat: x = "", "a", "aa", ...)
    let p = WeProblem {
        equations: vec![eq(
            word(&[&lit("a"), &[var(0)]]),
            word(&[&[var(0)], &lit("a")]),
        )],
        num_vars: 1,
        ..Default::default()
    };
    assert!(matches!(solve(&p), WeOutcome::Sat(_)));
}

#[test]
fn unsat_middle_char_clash() {
    // x ++ "ab" ++ x = x ++ "ba" ++ x  (unsat after stripping both x)
    let p = WeProblem {
        equations: vec![eq(
            word(&[&[var(0)], &lit("ab"), &[var(0)]]),
            word(&[&[var(0)], &lit("ba"), &[var(0)]]),
        )],
        num_vars: 1,
        ..Default::default()
    };
    assert_eq!(solve(&p), WeOutcome::Unsat);
}

#[test]
fn sat_var_var_system() {
    // x ++ y = y ++ x (sat trivially)
    let p = WeProblem {
        equations: vec![eq(
            word(&[&[var(0)], &[var(1)]]),
            word(&[&[var(1)], &[var(0)]]),
        )],
        num_vars: 2,
        ..Default::default()
    };
    assert!(matches!(solve(&p), WeOutcome::Sat(_)));
}

#[test]
fn sat_with_diseq_needs_distinct_values() {
    // x ++ y = y ++ x  AND  x != y (needs the distinct-values variant)
    let p = WeProblem {
        equations: vec![eq(
            word(&[&[var(0)], &[var(1)]]),
            word(&[&[var(1)], &[var(0)]]),
        )],
        disequations: vec![eq(vec![var(0)], vec![var(1)])],
        num_vars: 2,
        ..Default::default()
    };
    assert!(matches!(solve(&p), WeOutcome::Sat(_)));
}

#[test]
fn unsat_syntactically_violated_diseq() {
    // x != x
    let p = WeProblem {
        disequations: vec![eq(vec![var(0)], vec![var(0)])],
        num_vars: 1,
        ..Default::default()
    };
    assert_eq!(solve(&p), WeOutcome::Unsat);
}

#[test]
fn unsat_exact_len_conflict() {
    // x ++ "ab" = "a" ++ y with |x| = 1, |y| = 1 → |lhs|=3, |rhs|=2
    let p = WeProblem {
        equations: vec![eq(
            word(&[&[var(0)], &lit("ab")]),
            word(&[&lit("a"), &[var(1)]]),
        )],
        num_vars: 2,
        exact_lens: vec![(0, 1), (1, 1)],
        ..Default::default()
    };
    assert_eq!(solve(&p), WeOutcome::Unsat);
}

#[test]
fn sat_exact_len_guided() {
    // x ++ "ab" = "a" ++ y with |x| = 2 → x = "a?" ... x="ax'", y = x'·"ab"…
    // e.g. x = "aa", y = "aab".
    let p = WeProblem {
        equations: vec![eq(
            word(&[&[var(0)], &lit("ab")]),
            word(&[&lit("a"), &[var(1)]]),
        )],
        num_vars: 2,
        exact_lens: vec![(0, 2)],
        ..Default::default()
    };
    match solve(&p) {
        WeOutcome::Sat(sols) => {
            assert!(sols.iter().all(|s| {
                s.iter()
                    .find(|(v, _)| *v == 0)
                    .is_some_and(|(_, val)| val.chars().count() == 2)
            }));
        }
        other => panic!("expected Sat, got {other:?}"),
    }
}

#[test]
fn unsat_ground_mismatch() {
    // "abc" = "abd"
    let p = WeProblem {
        equations: vec![eq(lit("abc"), lit("abd"))],
        num_vars: 0,
        ..Default::default()
    };
    assert_eq!(solve(&p), WeOutcome::Unsat);
}

#[test]
fn sat_ground_match() {
    let p = WeProblem {
        equations: vec![eq(lit("abc"), lit("abc"))],
        num_vars: 0,
        ..Default::default()
    };
    assert!(matches!(solve(&p), WeOutcome::Sat(_)));
}

#[test]
fn sat_multi_equation_chain() {
    // x ++ "b" = "ab" ++ y  AND  y ++ "c" = z   (x="a"·y ... solvable)
    let p = WeProblem {
        equations: vec![
            eq(
                word(&[&[var(0)], &lit("b")]),
                word(&[&lit("ab"), &[var(1)]]),
            ),
            eq(word(&[&[var(1)], &lit("c")]), vec![var(2)]),
        ],
        num_vars: 3,
        ..Default::default()
    };
    assert!(matches!(solve(&p), WeOutcome::Sat(_)));
}

#[test]
fn quadratic_loop_is_bounded() {
    // x ++ "a" ++ y = y ++ "b" ++ x is unsat (Parikh catches it: swapping x,y
    // cancels nothing here — coefficient of x is net 0, of y net 0 → char
    // counts 'a' vs 'b' differ → conflict at the root).
    let p = WeProblem {
        equations: vec![eq(
            word(&[&[var(0)], &lit("a"), &[var(1)]]),
            word(&[&[var(1)], &lit("b"), &[var(0)]]),
        )],
        num_vars: 2,
        ..Default::default()
    };
    assert_eq!(solve(&p), WeOutcome::Unsat);
}

// ── Stage 2: quadratic depth ────────────────────────────────────────────

#[test]
fn quadratic_xax_bxc_unsat() {
    // x·a·x = b·x·c: the length abstraction pins |x| = 1, then x = "b"
    // forces "bab" = "bbc" — conflict on every branch. Pre-Stage-2 this
    // grew unboundedly (each Nielsen step lengthened the literal run).
    let p = WeProblem {
        equations: vec![eq(
            word(&[&[var(0)], &lit("a"), &[var(0)]]),
            word(&[&lit("b"), &[var(0)], &lit("c")]),
        )],
        num_vars: 1,
        ..Default::default()
    };
    assert_eq!(solve(&p), WeOutcome::Unsat);
}

#[test]
fn quadratic_xax_axa_sat() {
    // x·a·x = a·x·a: |x| = 1 pinned, x = "a" works.
    let p = WeProblem {
        equations: vec![eq(
            word(&[&[var(0)], &lit("a"), &[var(0)]]),
            word(&[&lit("a"), &[var(0)], &lit("a")]),
        )],
        num_vars: 1,
        ..Default::default()
    };
    assert!(matches!(solve(&p), WeOutcome::Sat(_)));
}

#[test]
fn square_literal_sat_and_unsat() {
    // x·x = "abab" (sat: x = "ab"); x·x = "abac" (unsat: |x| = 2 forces
    // x = "ab" from the head and x = "ac" from the tail).
    let sat = WeProblem {
        equations: vec![eq(word(&[&[var(0)], &[var(0)]]), lit("abab"))],
        num_vars: 1,
        ..Default::default()
    };
    assert!(matches!(solve(&sat), WeOutcome::Sat(_)));
    let unsat = WeProblem {
        equations: vec![eq(word(&[&[var(0)], &[var(0)]]), lit("abac"))],
        num_vars: 1,
        ..Default::default()
    };
    assert_eq!(solve(&unsat), WeOutcome::Unsat);
}

#[test]
fn commutation_primitive_root_unsat() {
    // (x·a·x)·b = b·(x·a·x): σ(x·a·x) must be a power of "b", but it
    // contains 'a' — Lyndon–Schützenberger refutation, no search needed.
    let p = WeProblem {
        equations: vec![eq(
            word(&[&[var(0)], &lit("a"), &[var(0)], &lit("b")]),
            word(&[&lit("b"), &[var(0)], &lit("a"), &[var(0)]]),
        )],
        num_vars: 1,
        ..Default::default()
    };
    assert_eq!(solve(&p), WeOutcome::Unsat);
}

#[test]
fn quadratic_two_var_sat() {
    // x·ab·y = y·ab·x — strictly quadratic; per-lineage fresh budget lets
    // the deduplicated graph complete (x = y = "" solves it).
    let p = WeProblem {
        equations: vec![eq(
            word(&[&[var(0)], &lit("ab"), &[var(1)]]),
            word(&[&[var(1)], &lit("ab"), &[var(0)]]),
        )],
        num_vars: 2,
        ..Default::default()
    };
    assert!(matches!(solve(&p), WeOutcome::Sat(_)));
}

// ── Stage 2: regex coupling ─────────────────────────────────────────────

fn member(v: u32, regex: WeRegex, positive: bool) -> WeMembership {
    WeMembership {
        var: v,
        regex,
        positive,
    }
}

#[test]
fn bkt_b_lone_negative_literal_sat() {
    // x ∉ "a"  ≡  x ∈ ¬"a" — satisfiable (e.g. "").
    let p = WeProblem {
        num_vars: 1,
        memberships: vec![member(0, WeRegex::lit("a"), false)],
        ..Default::default()
    };
    assert!(
        matches!(solve(&p), WeOutcome::Sat(_)),
        "got {:?}",
        solve(&p)
    );
}

#[test]
fn bkt_b_pos_and_neg_sat() {
    // x ∈ a·b*  ∧  x ∉ "a"  — witness "ab".
    let p = WeProblem {
        num_vars: 1,
        memberships: vec![
            member(
                0,
                WeRegex::concat(vec![WeRegex::lit("a"), WeRegex::star(WeRegex::lit("b"))]),
                true,
            ),
            member(0, WeRegex::lit("a"), false),
        ],
        ..Default::default()
    };
    assert!(
        matches!(solve(&p), WeOutcome::Sat(_)),
        "got {:?}",
        solve(&p)
    );
}

#[test]
fn bkt_b_contradiction_unsat() {
    // x ∈ "foo"  ∧  x ∉ "foo"  — unsat.
    let p = WeProblem {
        num_vars: 1,
        memberships: vec![
            member(0, WeRegex::lit("foo"), true),
            member(0, WeRegex::lit("foo"), false),
        ],
        ..Default::default()
    };
    assert_eq!(solve(&p), WeOutcome::Unsat);
}

#[test]
fn regex_derivative_prunes_to_unsat() {
    // x·a = a·x (⇒ x ∈ a*) with x ∈ a*·b: both branches close — x = ""
    // is not nullable for a*·b, and d_a(a*·b) cycles back to the same
    // deduplicated state.
    let p = WeProblem {
        equations: vec![eq(
            word(&[&[var(0)], &lit("a")]),
            word(&[&lit("a"), &[var(0)]]),
        )],
        num_vars: 1,
        memberships: vec![member(
            0,
            WeRegex::concat(vec![WeRegex::star(WeRegex::lit("a")), WeRegex::lit("b")]),
            true,
        )],
        ..Default::default()
    };
    assert_eq!(solve(&p), WeOutcome::Unsat);
}

#[test]
fn regex_head_char_mismatch_unsat() {
    // x·a = a·x with x ∈ b+: the empty branch violates nullability and the
    // char branch derives b+ by 'a' — empty. Unsat at depth 1.
    let p = WeProblem {
        equations: vec![eq(
            word(&[&[var(0)], &lit("a")]),
            word(&[&lit("a"), &[var(0)]]),
        )],
        num_vars: 1,
        memberships: vec![member(0, WeRegex::plus(WeRegex::lit("b")), true)],
        ..Default::default()
    };
    assert_eq!(solve(&p), WeOutcome::Unsat);
}

#[test]
fn regex_disjoint_commutation_unsat() {
    // x·y = y·x with x ∈ a+, y ∈ b+: commuting non-empty words share a
    // primitive root, impossible with disjoint alphabets.
    let p = WeProblem {
        equations: vec![eq(
            word(&[&[var(0)], &[var(1)]]),
            word(&[&[var(1)], &[var(0)]]),
        )],
        num_vars: 2,
        memberships: vec![
            member(0, WeRegex::plus(WeRegex::lit("a")), true),
            member(1, WeRegex::plus(WeRegex::lit("b")), true),
        ],
        ..Default::default()
    };
    assert_eq!(solve(&p), WeOutcome::Unsat);
}

#[test]
fn regex_guides_sat_witness() {
    // a·x = x·a (⇒ x ∈ a*) with x ∈ [a-b]* ∩ (aa)? and x ≠ "" → x = "aa".
    let p = WeProblem {
        equations: vec![eq(
            word(&[&lit("a"), &[var(0)]]),
            word(&[&[var(0)], &lit("a")]),
        )],
        disequations: vec![eq(vec![var(0)], Vec::new())],
        num_vars: 1,
        memberships: vec![member(
            0,
            WeRegex::inter(vec![
                WeRegex::star(WeRegex::range("a", "b")),
                WeRegex::opt(WeRegex::lit("aa")),
            ]),
            true,
        )],
        ..Default::default()
    };
    match solve(&p) {
        WeOutcome::Sat(sols) => {
            assert!(sols
                .iter()
                .any(|s| s.iter().any(|(v, val)| *v == 0 && val == "aa")));
        }
        other => panic!("expected Sat, got {other:?}"),
    }
}

#[test]
fn regex_negative_membership_filters_sat() {
    // x·ab = ab·x with ¬(x ∈ {""}): x = "ab" is the first surviving leaf.
    let p = WeProblem {
        equations: vec![eq(
            word(&[&[var(0)], &lit("ab")]),
            word(&[&lit("ab"), &[var(0)]]),
        )],
        num_vars: 1,
        memberships: vec![member(0, WeRegex::lit(""), false)],
        ..Default::default()
    };
    assert!(matches!(solve(&p), WeOutcome::Sat(_)));
}

#[test]
fn regex_empty_language_membership_unsat() {
    // x ∈ ∅ is false outright (and ¬(x ∈ Σ*) likewise).
    let p = WeProblem {
        equations: vec![eq(
            word(&[&[var(0)], &lit("a")]),
            word(&[&lit("a"), &[var(0)]]),
        )],
        num_vars: 1,
        memberships: vec![member(0, WeRegex::None, true)],
        ..Default::default()
    };
    assert_eq!(solve(&p), WeOutcome::Unsat);
    let p2 = WeProblem {
        equations: vec![eq(
            word(&[&[var(0)], &lit("a")]),
            word(&[&lit("a"), &[var(0)]]),
        )],
        num_vars: 1,
        memberships: vec![member(0, WeRegex::All, false)],
        ..Default::default()
    };
    assert_eq!(solve(&p2), WeOutcome::Unsat);
}

#[test]
fn regex_membership_with_exact_len_sat() {
    // x ∈ (ab)* with |x| = 4 and x·ab = ab·x → x = "abab".
    let p = WeProblem {
        equations: vec![eq(
            word(&[&[var(0)], &lit("ab")]),
            word(&[&lit("ab"), &[var(0)]]),
        )],
        num_vars: 1,
        exact_lens: vec![(0, 4)],
        memberships: vec![member(0, WeRegex::star(WeRegex::lit("ab")), true)],
        ..Default::default()
    };
    match solve(&p) {
        WeOutcome::Sat(sols) => {
            assert!(sols
                .iter()
                .all(|s| s.iter().any(|(v, val)| *v == 0 && val == "abab")));
        }
        other => panic!("expected Sat, got {other:?}"),
    }
}

#[test]
fn regex_free_var_takes_witness() {
    // y unconstrained by equations but y ∈ b+ — the leaf materializer must
    // produce a regex witness, not "".
    let p = WeProblem {
        equations: vec![eq(
            word(&[&[var(0)], &lit("a")]),
            word(&[&lit("a"), &[var(0)]]),
        )],
        num_vars: 2,
        memberships: vec![member(1, WeRegex::plus(WeRegex::lit("b")), true)],
        ..Default::default()
    };
    assert!(matches!(solve(&p), WeOutcome::Sat(_)));
}

#[test]
fn exhaustion_is_reported_not_wrong() {
    // x ++ "ab" ++ y = y ++ "ab" ++ x with a diseq that all small candidates
    // fail is at worst Exhausted — never Unsat (the equations are satisfiable).
    let p = WeProblem {
        equations: vec![eq(
            word(&[&[var(0)], &lit("ab"), &[var(1)]]),
            word(&[&[var(1)], &lit("ab"), &[var(0)]]),
        )],
        num_vars: 2,
        ..Default::default()
    };
    assert!(matches!(
        solve(&p),
        WeOutcome::Sat(_) | WeOutcome::Exhausted
    ));
}

// ── Stage 3a: var-var regex decomposition ──────────────────────────────────

fn bound(v: u32, lo: usize, hi: Option<usize>) -> WeLenBound {
    WeLenBound { var: v, lo, hi }
}

#[test]
fn varvar_regex_decomposition_unsat() {
    // x = y·z with y ∈ a+, z ∈ b+, x ∈ (aa)*: σ(x) would contain a 'b' but
    // (aa)* admits only 'a's. The var-var split must PROPAGATE x's regex
    // onto y·z (Stage 3a) and the leaf emptiness product must refute it.
    let p = WeProblem {
        equations: vec![eq(vec![var(0)], word(&[&[var(1)], &[var(2)]]))],
        num_vars: 3,
        memberships: vec![
            member(0, WeRegex::star(WeRegex::lit("aa")), true),
            member(1, WeRegex::plus(WeRegex::lit("a")), true),
            member(2, WeRegex::plus(WeRegex::lit("b")), true),
        ],
        ..Default::default()
    };
    assert_eq!(solve(&p), WeOutcome::Unsat);
}

#[test]
fn varvar_regex_decomposition_sat() {
    // x = y·z with y ∈ a+, z ∈ b+, x ∈ (ab)* → x = "ab", y = "a", z = "b".
    let p = WeProblem {
        equations: vec![eq(vec![var(0)], word(&[&[var(1)], &[var(2)]]))],
        num_vars: 3,
        memberships: vec![
            member(0, WeRegex::star(WeRegex::lit("ab")), true),
            member(1, WeRegex::plus(WeRegex::lit("a")), true),
            member(2, WeRegex::plus(WeRegex::lit("b")), true),
        ],
        ..Default::default()
    };
    assert!(matches!(solve(&p), WeOutcome::Sat(_)));
}

// ── Stage 3b: length-interval coupling ─────────────────────────────────────

#[test]
fn interval_infeasible_equation_unsat() {
    // x = y·"ab" forces |x| ≥ 2, but |x| ≤ 1 (faithful interval) → Unsat.
    let p = WeProblem {
        equations: vec![eq(vec![var(0)], word(&[&[var(1)], &lit("ab")]))],
        num_vars: 2,
        len_bounds: vec![bound(0, 0, Some(1))],
        ..Default::default()
    };
    assert_eq!(solve(&p), WeOutcome::Unsat);
}

#[test]
fn interval_lower_bound_guides_witness_sat() {
    // x·ab = ab·x (⇒ x ∈ (ab)*) with |x| ≥ 1 → x = "ab" (the "" leaf is
    // filtered by the bound; the witness must respect the window).
    let p = WeProblem {
        equations: vec![eq(
            word(&[&[var(0)], &lit("ab")]),
            word(&[&lit("ab"), &[var(0)]]),
        )],
        num_vars: 1,
        len_bounds: vec![bound(0, 1, None)],
        ..Default::default()
    };
    match solve(&p) {
        WeOutcome::Sat(sols) => {
            assert!(sols
                .iter()
                .any(|s| s.iter().any(|(v, val)| *v == 0 && val == "ab")));
        }
        other => panic!("expected Sat, got {other:?}"),
    }
}

#[test]
fn interval_window_collapse_unsat_commutation() {
    // x·ab = ab·x (⇒ σ(x) ∈ (ab)*, so |x| is even) with 1 ≤ |x| ≤ 1 given
    // as two interval bounds that collapse to an exact length → Unsat.
    let p = WeProblem {
        equations: vec![eq(
            word(&[&[var(0)], &lit("ab")]),
            word(&[&lit("ab"), &[var(0)]]),
        )],
        num_vars: 1,
        len_bounds: vec![bound(0, 1, None), bound(0, 0, Some(1))],
        ..Default::default()
    };
    assert_eq!(solve(&p), WeOutcome::Unsat);
}

#[test]
fn interval_regex_window_leaf_unsat() {
    // y ∈ (aaa)+ (lengths 3, 6, …) with 1 ≤ |y| ≤ 2: the leaf emptiness
    // product over regex × length-window refutes every leaf → Unsat.
    let p = WeProblem {
        equations: vec![eq(
            word(&[&[var(0)], &lit("a")]),
            word(&[&lit("a"), &[var(0)]]),
        )],
        num_vars: 2,
        memberships: vec![member(1, WeRegex::plus(WeRegex::lit("aaa")), true)],
        len_bounds: vec![bound(1, 1, Some(2))],
        ..Default::default()
    };
    assert_eq!(solve(&p), WeOutcome::Unsat);
}

#[test]
fn interval_contradictory_bounds_unsat() {
    // 2 ≤ |x| and |x| ≤ 1 (both faithful) contradict outright.
    let p = WeProblem {
        equations: vec![eq(
            word(&[&[var(0)], &lit("a")]),
            word(&[&lit("a"), &[var(0)]]),
        )],
        num_vars: 1,
        len_bounds: vec![bound(0, 2, None), bound(0, 0, Some(1))],
        ..Default::default()
    };
    assert_eq!(solve(&p), WeOutcome::Unsat);
}

#[test]
fn interval_propagation_pins_suffix() {
    // x = y·"a" with |x| ≤ 1: interval propagation forces |y| = 0, so the
    // only solution is y = "", x = "a".
    let p = WeProblem {
        equations: vec![eq(vec![var(0)], word(&[&[var(1)], &lit("a")]))],
        num_vars: 2,
        len_bounds: vec![bound(0, 0, Some(1))],
        ..Default::default()
    };
    match solve(&p) {
        WeOutcome::Sat(sols) => {
            for sol in &sols {
                assert!(sol.iter().any(|(v, val)| *v == 0 && val == "a"));
                assert!(sol.iter().any(|(v, val)| *v == 1 && val.is_empty()));
            }
        }
        other => panic!("expected Sat, got {other:?}"),
    }
}

#[test]
fn interval_bounds_never_flip_sat_to_unsat() {
    // Windows compatible with a solution must stay Sat (guards against
    // over-eager interval pruning).
    let p = WeProblem {
        equations: vec![eq(
            word(&[&[var(0)], &lit("ab")]),
            word(&[&lit("a"), &[var(1)]]),
        )],
        num_vars: 2,
        len_bounds: vec![bound(0, 1, Some(3)), bound(1, 2, Some(4))],
        ..Default::default()
    };
    // x·"ab" = "a"·y with |x| ∈ [1,3], |y| ∈ [2,4]: x = "a", y = "aab" works
    // (|x|=1, |y|=3), among others.
    assert!(matches!(solve(&p), WeOutcome::Sat(_)));
}

#[test]
fn boundary_char_disjoint_unsat() {
    // x·y = y·x with x ∈ (ab)+, y ∈ (ba)+: both sides are non-empty and
    // must share a first character, but σ(x·y) starts with 'a' and σ(y·x)
    // with 'b' → Unsat (z3 4.16 agrees).
    let p = WeProblem {
        equations: vec![eq(
            word(&[&[var(0)], &[var(1)]]),
            word(&[&[var(1)], &[var(0)]]),
        )],
        num_vars: 2,
        memberships: vec![
            member(0, WeRegex::plus(WeRegex::lit("ab")), true),
            member(1, WeRegex::plus(WeRegex::lit("ba")), true),
        ],
        ..Default::default()
    };
    assert_eq!(solve(&p), WeOutcome::Unsat);
}

#[test]
fn boundary_char_shared_stays_sat() {
    // Same shape but overlapping boundary characters: x = y = "ab" works.
    let p = WeProblem {
        equations: vec![eq(
            word(&[&[var(0)], &[var(1)]]),
            word(&[&[var(1)], &[var(0)]]),
        )],
        num_vars: 2,
        memberships: vec![
            member(0, WeRegex::plus(WeRegex::lit("ab")), true),
            member(1, WeRegex::plus(WeRegex::lit("ab")), true),
        ],
        ..Default::default()
    };
    assert!(matches!(solve(&p), WeOutcome::Sat(_)));
}

// ── Stage 3c: leaf length-composition witnesses + forced-root divisibility ──

#[test]
fn window_multivar_witness_sat() {
    // G3: x = y·z, y ∈ a+, z ∈ b+, 4 ≤ |x| ≤ 5 → SAT (e.g. y="a", z="bbb").
    let p = WeProblem {
        equations: vec![eq(word(&[&[var(0)]]), word(&[&[var(1)], &[var(2)]]))],
        num_vars: 3,
        len_bounds: vec![WeLenBound {
            var: 0,
            lo: 4,
            hi: Some(5),
        }],
        memberships: vec![
            member(1, WeRegex::plus(WeRegex::lit("a")), true),
            member(2, WeRegex::plus(WeRegex::lit("b")), true),
        ],
        ..Default::default()
    };
    assert!(matches!(solve(&p), WeOutcome::Sat(_)));
}

#[test]
fn commutation_root_divisibility_unsat() {
    // G4: x·y = y·x, x ∈ (ab)*, |x| ≥ 1, |y| = 3 → UNSAT: x nonempty in
    // (ab)* has primitive root "ab", so y ∈ (ab)* and 2 | |y|, but |y| = 3.
    let p = WeProblem {
        equations: vec![eq(
            word(&[&[var(0)], &[var(1)]]),
            word(&[&[var(1)], &[var(0)]]),
        )],
        num_vars: 2,
        exact_lens: vec![(1, 3)],
        len_bounds: vec![WeLenBound {
            var: 0,
            lo: 1,
            hi: None,
        }],
        memberships: vec![member(0, WeRegex::star(WeRegex::lit("ab")), true)],
        ..Default::default()
    };
    assert_eq!(solve(&p), WeOutcome::Unsat);
}

// ── Stage 3d: regex-derived length residues ─────────────────────────────

#[test]
fn regex_length_residue_parity_unsat() {
    // n7: x = y·z, y ∈ (aa)(aa)* (even, ≥2), z ∈ (bb)(bb)* (even, ≥2),
    // |x| = 5 → UNSAT: |y| + |z| is even.
    let p = WeProblem {
        equations: vec![eq(word(&[&[var(0)]]), word(&[&[var(1)], &[var(2)]]))],
        num_vars: 3,
        exact_lens: vec![(0, 5)],
        memberships: vec![
            member(1, WeRegex::plus(WeRegex::lit("aa")), true),
            member(2, WeRegex::plus(WeRegex::lit("bb")), true),
        ],
        ..Default::default()
    };
    assert_eq!(solve(&p), WeOutcome::Unsat);
}

#[test]
fn regex_length_residue_parity_sat_control() {
    // Same shape with |x| = 6 → SAT (y = "aaaa", z = "bb").
    let p = WeProblem {
        equations: vec![eq(word(&[&[var(0)]]), word(&[&[var(1)], &[var(2)]]))],
        num_vars: 3,
        exact_lens: vec![(0, 6)],
        memberships: vec![
            member(1, WeRegex::plus(WeRegex::lit("aa")), true),
            member(2, WeRegex::plus(WeRegex::lit("bb")), true),
        ],
        ..Default::default()
    };
    assert!(matches!(solve(&p), WeOutcome::Sat(_)));
}

#[test]
fn regex_length_residue_offset_prefix_unsat() {
    // y ∈ a(aa)* (odd), z ∈ (bb)* (even), x = y·z, |x| = 4 → UNSAT.
    let p = WeProblem {
        equations: vec![eq(word(&[&[var(0)]]), word(&[&[var(1)], &[var(2)]]))],
        num_vars: 3,
        exact_lens: vec![(0, 4)],
        memberships: vec![
            member(
                1,
                WeRegex::concat(vec![WeRegex::lit("a"), WeRegex::star(WeRegex::lit("aa"))]),
                true,
            ),
            member(2, WeRegex::star(WeRegex::lit("bb")), true),
        ],
        ..Default::default()
    };
    assert_eq!(solve(&p), WeOutcome::Unsat);
}

#[test]
fn regex_length_residue_union_stays_conservative() {
    // y ∈ (aa|aaa)* has NO single residue class (gcd(2,3) = 1): the
    // extractor must return nothing and |x| = 5 stays SAT (y="aaa", z="bb").
    let p = WeProblem {
        equations: vec![eq(word(&[&[var(0)]]), word(&[&[var(1)], &[var(2)]]))],
        num_vars: 3,
        exact_lens: vec![(0, 5)],
        memberships: vec![
            member(
                1,
                WeRegex::star(WeRegex::union(vec![
                    WeRegex::lit("aa"),
                    WeRegex::lit("aaa"),
                ])),
                true,
            ),
            member(2, WeRegex::star(WeRegex::lit("bb")), true),
        ],
        ..Default::default()
    };
    assert!(matches!(solve(&p), WeOutcome::Sat(_)));
}

#[test]
fn regex_length_residue_exact_len_clash_unsat() {
    // |y| = 3 directly contradicts y ∈ (aa)* even without equations
    // relating other variables.
    let p = WeProblem {
        equations: vec![eq(word(&[&[var(0)]]), word(&[&[var(1)]]))],
        num_vars: 2,
        exact_lens: vec![(1, 3)],
        memberships: vec![member(1, WeRegex::star(WeRegex::lit("aa")), true)],
        ..Default::default()
    };
    assert_eq!(solve(&p), WeOutcome::Unsat);
}

#[test]
fn lan_replace_all2_extended_fragment_unsat() {
    // Feasibility probe for QF_SLIA 20230403-webapp/lan-rep-all/lan_replace_all2:
    // the boolean-closure-extended fragment plus DERIVED length bounds
    // (from `len(x_2) + len(sink) < 50` propagated through the concat
    // length abstraction). V0=atkPtn V1=atk_sink V2=a1 V3=a2 V4=lit8
    // V5=lit10 V6=lit13 V9=x_9 V10=x_11 V11=x_12 V12=x_14 V13=sink
    // V14=x_7 V15=x_2.
    let l8 = lit("\\x20\\x20\\x20\\x20");
    let l10 = lit("\\x20\\x3d\\x20\\x27");
    let l13 = lit("\\x27\\x3b\\x5c\\x6e");
    let bound = |v: u32, lo: usize, hi: usize| WeLenBound {
        var: v,
        lo,
        hi: Some(hi),
    };
    let p = WeProblem {
        equations: vec![
            eq(word(&[&[var(0)]]), lit("vbscript:")),
            eq(
                word(&[&[var(1)]]),
                word(&[&[var(2)], &lit("vbscript:"), &[var(3)]]),
            ),
            eq(word(&[&[var(4)]]), l8.clone()),
            eq(word(&[&[var(5)]]), l10.clone()),
            eq(word(&[&[var(6)]]), l13.clone()),
            eq(word(&[&[var(9)]]), word(&[&[var(4)], &[var(14)]])),
            eq(word(&[&[var(10)]]), word(&[&[var(9)], &[var(5)]])),
            eq(word(&[&[var(11)]]), word(&[&[var(10)], &[var(15)]])),
            eq(word(&[&[var(12)]]), word(&[&[var(11)], &[var(6)]])),
            eq(word(&[&[var(13)]]), word(&[&[var(12)]])),
            eq(word(&[&[var(13)]]), word(&[&[var(1)]])),
        ],
        num_vars: 16,
        len_bounds: vec![
            bound(14, 0, 1),
            bound(15, 0, 1),
            bound(13, 48, 49),
            bound(9, 16, 17),
            bound(10, 32, 33),
            bound(11, 32, 33),
            bound(12, 48, 49),
            bound(2, 0, 40),
            bound(3, 0, 40),
        ],
        ..Default::default()
    };
    assert_eq!(solve(&p), WeOutcome::Unsat);
}
