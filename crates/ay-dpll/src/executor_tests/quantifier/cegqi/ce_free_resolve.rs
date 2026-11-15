// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// Textually included by `cegqi.rs` to keep the regression test FQN.
//
// (#quantifier-ce-free-resolve) Stage 4 of the quantifier-instantiation plan:
// a CEGQI-forall refutation the disambiguation apparatus cannot attribute is
// re-derived from the counterexample-free consequence set.
//
// The fixture is shaped after the measured corpus file
// (`UFLIA simplify2 javafe.ast.BranchStmt.002`): one entailed, triggerless
// arithmetic universal so CEGQI mints a counterexample lemma; more authored
// roots than `MAX_AUTHORED_ROOTS` (64) so the authored consequence replay
// declines; and a refutation that needs one E-matched instance of a
// triggered universal against the ground facts. In the campaign posture
// (`--z3-mode`, the proof cycle shed) the base tree publishes
// `unknown (incomplete quantifier-cegqi)` on it; z3 5.1.0 answers `unsat`.

/// `roots` ground facts `(> (f a_i) a_i)`, the CEGQI universal, a triggered
/// universal `f(y) <= g(y)`, and — when `contradict` — the fact `g(a_0) < a_0`
/// that closes the refutation through the instance at `a_0`.
fn ce_free_fixture(roots: usize, contradict: bool) -> String {
    let mut smt =
        String::from("(set-logic UFLIA)\n(declare-fun f (Int) Int)\n(declare-fun g (Int) Int)\n");
    for i in 0..roots {
        smt.push_str(&format!("(declare-const a{i} Int)\n"));
    }
    for i in 0..roots {
        smt.push_str(&format!("(assert (> (f a{i}) a{i}))\n"));
    }
    // Entailed, triggerless (no pattern is inferable that covers the binder
    // through an uninterpreted head at every occurrence), a CEGQI candidate.
    smt.push_str("(assert (forall ((x Int)) (or (= x 0) (>= (f x) 0))))\n");
    smt.push_str("(assert (forall ((y Int)) (! (<= (f y) (g y)) :pattern ((f y)))))\n");
    if contradict {
        smt.push_str("(assert (< (g a0) a0))\n");
    }
    smt.push_str("(check-sat)\n");
    smt
}

/// Solve in the campaign posture (proof cycle shed) — or, with `proofs`, in
/// the proof-producing posture — returning the verdict and the two stage-4
/// counters.
fn solve_ce_free_in(smt: &str, proofs: bool) -> (String, u64, u64) {
    solve_ce_free_within(smt, proofs, None)
}

/// As [`solve_ce_free_in`], under a solve deadline: the fixtures below are
/// the ones on which a probe that runs at the wrong point does not
/// terminate, so a regression must surface as a verdict, not as a hang.
fn solve_ce_free_within(
    smt: &str,
    proofs: bool,
    timeout: Option<std::time::Duration>,
) -> (String, u64, u64) {
    let commands = parse(smt).unwrap();
    let mut exec = Executor::new();
    exec.set_timeout(timeout);
    if proofs {
        exec.set_produce_proofs(true);
    } else {
        exec.set_competition_mode(true);
    }
    let outputs = exec.execute_all(&commands).unwrap();
    let verdict = outputs.last().cloned().unwrap_or_default();
    let stats = exec.statistics();
    (
        verdict,
        stats
            .get_int("quantifier.cegqi.ce_free_resolves")
            .unwrap_or(0),
        stats
            .get_int("quantifier.cegqi.ce_free_resolve_refutations")
            .unwrap_or(0),
    )
}

fn solve_ce_free(smt: &str) -> (String, u64, u64) {
    solve_ce_free_in(smt, false)
}

#[test]
fn ce_free_resolve_recovers_the_refutation_the_counterexample_lemma_masked() {
    let smt = ce_free_fixture(70, true);
    let (verdict, resolves, refutations) = solve_ce_free(&smt);
    assert_eq!(
        resolves, 1,
        "the fixture must reach the stage-4 re-solve exactly once (verdict={verdict})"
    );
    assert_eq!(refutations, 1, "the CE-free re-solve must refute");
    assert_eq!(verdict, "unsat");
}

#[test]
fn ce_free_resolve_kill_switch_restores_the_fail_closed_unknown() {
    let smt = ce_free_fixture(70, true);
    let guard = ay_core::misc_test_override::set(ay_core::MiscCliFlags {
        no_quantifier_ce_free_resolve: true,
        ..Default::default()
    });
    let (verdict, resolves, refutations) = solve_ce_free(&smt);
    drop(guard);
    assert_eq!(
        resolves, 0,
        "the switch must keep the re-solve from running"
    );
    assert_eq!(refutations, 0);
    assert_eq!(
        verdict, "unknown",
        "with the re-solve off the base tree's fail-closed verdict must be byte-identical"
    );
}

#[test]
fn ce_free_resolve_never_manufactures_unsat_on_a_satisfiable_fixture() {
    // Same roots and universals, no contradiction: `f := λx. x + 1`,
    // `g := λx. x + 1` is a model. The re-solve must not run at all — the
    // ground result is not a refutation — and whatever the existing SAT legs
    // decide, `unsat` is wrong.
    let smt = ce_free_fixture(70, false);
    let (verdict, resolves, refutations) = solve_ce_free(&smt);
    assert_eq!(refutations, 0);
    assert_ne!(verdict, "unsat", "resolves={resolves}");
}

#[test]
fn ce_free_resolve_does_not_fire_when_the_live_proof_already_certifies() {
    // Proof-producing posture, below the replay's root budget: the live strict
    // proof attributes the refutation itself (measured: `strict-proof`,
    // carcara `valid`, byte-identical to the base tree in all four postures)
    // and stage 4 must stay out of the way.
    let smt = ce_free_fixture(8, true);
    let (verdict, resolves, _) = solve_ce_free_in(&smt, true);
    assert_eq!(verdict, "unsat");
    assert_eq!(
        resolves, 0,
        "a refutation the disambiguation apparatus certifies must not be re-solved"
    );
}

/// The verifier's reproducer for the restore-don't-clear defect: a
/// satisfiable UFNIA problem on which CEGQI refutes the CE-augmented window,
/// the apparatus fails closed, and the `sat` is produced by the finite-table
/// certificate completing the ground witness the disambiguation had
/// installed in `last_model`. While the probe ran BEFORE that certificate, a
/// probe that cleared the model instead of restoring it exhausted the
/// certificate's solver-call budget from an empty base and published
/// `unknown` in both postures (build 9661); the base tree answers `sat`.
/// With the probe the last resort, the certificate runs first and decides
/// the query: `sat`, in both postures, and the probe is never reached.
#[test]
fn ce_free_resolve_that_does_not_refute_restores_the_predecessor_model() {
    let smt = include_str!(concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/tests/fixtures/quantifier/cegqi_ce_free_resolve_finite_table_sat.smt2"
    ));
    for proofs in [false, true] {
        let (verdict, resolves, refutations) = solve_ce_free_in(smt, proofs);
        assert_eq!(
            verdict, "sat",
            "the finite-table certificate decides this query (proofs={proofs}, \
             resolves={resolves})"
        );
        assert_eq!(
            resolves, 0,
            "the probe is the last resort; a query a SAT certificate decides never reaches \
             it (proofs={proofs})"
        );
        assert_eq!(refutations, 0);
    }
}

/// The starvation the last-resort placement closes (#quantifier-ce-free-resolve,
/// "Why last, and not merely after the CEGQI arms" in `ce_free_resolve.rs`):
/// two satisfiable problems whose counterexample-free vector the nonlinear
/// lane does not decide inside the deadline, and which `main` answers `sat`
/// through the constant-interpretation certificate (Phase 2.4 declines,
/// Phase 2.5c grants) in 4 s. With the probe hooked after the CEGQI arms but
/// BEFORE that certificate, the NRA shape (`nra_cube_sortpred`) spent the
/// whole deadline in the re-solve -- 16 / 56 / 116 s of `-T:20` / `60` /
/// `120` -- and published `unknown` at every deadline tried; the NIA shape
/// (`nia_mixed_sortpred`) published `unknown` at `-T:20` and `sat` at `-T:60`
/// after 27 s, 23 s of it the probe. z3 5.1.0: `sat` on both. Rows 13 and 14
/// of `scripts/z3_parity_reproducers.sh` (`benchmarks/smt/wrong-verdict/`).
#[test]
fn ce_free_resolve_is_the_last_resort_and_never_starves_a_sat_certificate() {
    let fixtures = [
        (
            "nra_cube_sortpred",
            include_str!(concat!(
                env!("CARGO_MANIFEST_DIR"),
                "/tests/fixtures/quantifier/cegqi_ce_free_resolve_last_resort_nra_cube_sortpred.smt2"
            )),
        ),
        (
            "nia_mixed_sortpred",
            include_str!(concat!(
                env!("CARGO_MANIFEST_DIR"),
                "/tests/fixtures/quantifier/cegqi_ce_free_resolve_last_resort_nia_mixed_sortpred.smt2"
            )),
        ),
    ];
    for (name, smt) in fixtures {
        for proofs in [false, true] {
            let (verdict, resolves, refutations) =
                solve_ce_free_within(smt, proofs, Some(std::time::Duration::from_secs(60)));
            assert_eq!(
                verdict, "sat",
                "{name}: the constant-interpretation certificate decides this query in \
                 seconds; a probe that runs before it spends the deadline (proofs={proofs}, \
                 resolves={resolves})"
            );
            assert_eq!(
                resolves, 0,
                "{name}: the probe is the last resort; a query a SAT certificate decides \
                 never reaches it (proofs={proofs})"
            );
            assert_eq!(refutations, 0, "{name}: proofs={proofs}");
        }
    }
}

/// The isolation window, exercised AT the last resort. On this satisfiable
/// problem nothing before the probe decides the query (`main` answers
/// `unknown` on it too), so the probe is reached and fires; inside its window
/// it does not refute and the fail-closed `unknown` stands. Without the
/// window the same probe refuted under the counterexample hypothesis --
/// `unsat`, wrong, in both postures (window-OFF measurement, 2026-09-16).
/// z3 5.1.0: `sat`. The three fixtures of the window test below no longer
/// reach the probe (a SAT certificate decides them first), which is why this
/// one exists.
#[test]
fn ce_free_resolve_window_holds_at_the_last_resort() {
    let smt = include_str!(concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/tests/fixtures/quantifier/cegqi_ce_free_resolve_window_nia_cube_twopreds.smt2"
    ));
    for proofs in [false, true] {
        let (verdict, resolves, refutations) =
            solve_ce_free_within(smt, proofs, Some(std::time::Duration::from_secs(60)));
        assert_ne!(
            verdict, "unsat",
            "the problem is satisfiable (z3 5.1.0 `sat`); a probe outside its window refutes \
             it under the counterexample hypothesis (proofs={proofs}, resolves={resolves})"
        );
        assert!(
            resolves >= 1,
            "nothing before the last resort decides this query, so the probe must be reached \
             (proofs={proofs}, verdict={verdict}); if a certificate now decides it, the \
             fixture has stopped exercising the window and this guard needs a new one"
        );
        assert_eq!(
            refutations, 0,
            "the CE-free vector is satisfiable; the probe must not refute (proofs={proofs})"
        );
    }
}

/// The wrong-`unsat` the window closes (#quantifier-ce-free-resolve, "The
/// window" in `ce_free_resolve.rs`): three satisfiable quantified problems
/// whose ground part routes to a lane that REUSES the persistent incremental
/// state (NIA, NRA), so a probe handed the correct counterexample-free vector
/// still solved it under the counterexample hypothesis the primary dispatch
/// had activated at scope depth 0 — `unsat` in both postures, 18/18, on the
/// tree before the window; `sat` from main, from the kill switch and from z3
/// 5.1.0. These are the `wrong-unsat` rows of `scripts/z3_parity_reproducers.sh`
/// (`benchmarks/smt/wrong-verdict/`), copied here so the library suite pins
/// them without the corpus. With the probe the last resort, a SAT
/// certificate decides each of these before the probe is reached, so they
/// pin the verdict and the absence of a refutation; the window itself is
/// exercised by `ce_free_resolve_window_holds_at_the_last_resort`.
fn ce_free_window_fixtures() -> [(&'static str, &'static str); 3] {
    [
        (
            "ufnia_sort",
            include_str!(concat!(
                env!("CARGO_MANIFEST_DIR"),
                "/tests/fixtures/quantifier/cegqi_ce_free_resolve_sat_quantified_ufnia_sort.smt2"
            )),
        ),
        (
            "ufnra_sort",
            include_str!(concat!(
                env!("CARGO_MANIFEST_DIR"),
                "/tests/fixtures/quantifier/cegqi_ce_free_resolve_sat_quantified_ufnra_sort.smt2"
            )),
        ),
        (
            "eu_two_preds",
            include_str!(concat!(
                env!("CARGO_MANIFEST_DIR"),
                "/tests/fixtures/quantifier/cegqi_ce_free_resolve_sat_quantified_eu_two_preds.smt2"
            )),
        ),
    ]
}

#[test]
fn ce_free_resolve_runs_its_lane_inside_its_own_isolation_window() {
    for (name, smt) in ce_free_window_fixtures() {
        for proofs in [false, true] {
            let (verdict, resolves, refutations) = solve_ce_free_in(smt, proofs);
            assert_eq!(
                verdict, "sat",
                "{name}: the problem is satisfiable (z3 5.1.0 `sat`); a probe that solves the \
                 CE-free vector under the predecessor's persistent SAT state refutes it under \
                 the counterexample hypothesis (proofs={proofs}, resolves={resolves}, \
                 refutations={refutations})"
            );
            assert_eq!(
                refutations, 0,
                "{name}: the CE-free vector is satisfiable; the probe must not refute \
                 (proofs={proofs}, resolves={resolves})"
            );
        }
    }
}
