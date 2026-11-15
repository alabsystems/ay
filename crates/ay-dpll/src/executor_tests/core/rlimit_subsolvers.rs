// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Deterministic `:rlimit` coverage for theory SAT sub-solvers.

use super::*;

fn checked_fp_stop_or_early_refutation(exec: &mut Executor, outputs: &[String], round: usize) {
    let conflicts = exec
        .statistics()
        .get_int("all_lanes.conflicts")
        .expect("the original check retains its cumulative conflict ledger");
    assert!(
        conflicts <= 1,
        "round {round}: original conflict allowance exceeded: {conflicts}"
    );
    match outputs.first().map(String::as_str) {
        Some("unknown") => {
            assert_eq!(
                outputs,
                ["unknown", "(:reason-unknown resourceout)"],
                "round {round}"
            );
            assert_eq!(exec.unknown_reason(), Some(UnknownReason::ResourceLimit));
        }
        Some("unsat") => {
            // A proved symbolic identity may finish before the first budgeted
            // conflict. Keep that improvement, but replay its actual proof.
            let proof = exec
                .last_proof()
                .cloned()
                .expect("early refutation has an actual proof");
            assert!(exec
                .check_proof_strict_with_datatypes(&proof)
                .unwrap()
                .is_complete());
            assert_eq!(exec.unknown_reason(), None);
        }
        _ => panic!("round {round}: expected a budget stop or checked refutation, got {outputs:?}"),
    }
}

#[test]
fn test_executor_rlimit_governs_bv_bitblast_subsolver() {
    // Regression (#8749 BV lane): `:rlimit` armed the MAIN pipeline CDCL
    // solves, but the BV lane's bit-blast SatSolver ran unbudgeted — a
    // divergent wide-multiply obligation burned wall clock at 100% CPU until
    // the deadline backstop, so its verdict was decided by machine load,
    // exactly the nondeterminism the conflict budget exists to kill.
    //
    // The reproducer must actually reach divergent bit-blast SEARCH, and most
    // "hard-looking" mul shapes never do: 64-bit mul identities (commutativity,
    // associativity, distributivity) fall to algebraic rewriting in <50ms,
    // full-width factoring (`bvmul x y` = N) wraps mod 2^64 so any odd x pairs
    // with y = x^-1*N (trivially SAT), and even genuine 32x32->64 SEMIPRIME
    // factoring is solved by ay in ~150ms. What diverges is the UNSAT twin:
    // x*y = P for a 62-bit PRIME P through a genuine zero-extended
    // 32x32->64 multiplier, with x,y > 1 — refuting it is a primality proof
    // inside the multiplier circuit (measured: 60s+ at 100% CPU with no
    // verdict on the pre-fix engine, `:rlimit 1` ignored). Under a 1-conflict
    // budget the BV sub-solve must instead stop with `resourceout` —
    // deterministically, identically on every run, and promptly (this test
    // burns wall clock for minutes if the budget is not threaded into the BV
    // bit-blast SAT sub-solver).
    let smt = "(set-logic QF_BV)\n\
               (set-option :rlimit 1)\n\
               (declare-const x (_ BitVec 32))\n\
               (declare-const y (_ BitVec 32))\n\
               (assert (= (bvmul ((_ zero_extend 32) x) ((_ zero_extend 32) y))\n\
                          #x2d5fca7bd3e96a43))\n\
               (assert (bvult #x00000001 x))\n\
               (assert (bvult #x00000001 y))\n\
               (check-sat)\n\
               (get-info :reason-unknown)\n";
    for round in 0..5 {
        let commands = parse(smt).unwrap();
        let mut exec = Executor::new();
        let outputs = exec.execute_all(&commands).unwrap();
        assert_eq!(
            outputs,
            vec!["unknown", "(:reason-unknown resourceout)"],
            "round {round}: BV bit-blast sub-solve must exhaust the :rlimit \
             conflict budget deterministically"
        );
        assert_eq!(exec.unknown_reason(), Some(UnknownReason::ResourceLimit));
    }
}

#[test]
fn test_executor_rlimit_governs_eager_persistent_lra_arm() {
    // P4a (T2): QF_LRA runs on the eager-persistent split-loop arm, which
    // armed no conflict or decision budget at all: its rounds were sliced by
    // per-iteration WALL windows, so `:rlimit` did not bound it and a
    // divergent query ran until the deadline backstop (`timeout`, decided by
    // machine load). The query is the pigeonhole principle for 12 pigeons
    // in 11 holes, posed over real positions: each pigeon sits at one of the
    // holes 1..11 and no two share one, so every refutation step is a
    // disequality conflict and resolution needs exponentially many of them.
    // Under a 1-conflict `:rlimit` the arm's first search must stop on the
    // count, as `resourceout`, deterministically and promptly; the 120 s
    // backstop only bounds this test on an arm that ignores the count.
    const PIGEONS: u32 = 12;
    const HOLES: u32 = 11;
    let mut smt =
        String::from("(set-logic QF_LRA)\n(set-option :rlimit 1)\n(set-option :timeout 120000)\n");
    for i in 1..=PIGEONS {
        smt.push_str(&format!("(declare-const x{i} Real)\n"));
    }
    for i in 1..=PIGEONS {
        let holes: Vec<String> = (1..=HOLES).map(|j| format!("(= x{i} {j}.0)")).collect();
        smt.push_str(&format!("(assert (or {}))\n", holes.join(" ")));
    }
    for i in 1..=PIGEONS {
        for k in (i + 1)..=PIGEONS {
            smt.push_str(&format!("(assert (not (= x{i} x{k})))\n"));
        }
    }
    smt.push_str("(check-sat)\n(get-info :reason-unknown)\n");
    let mut stop_points = Vec::new();
    for round in 0..3 {
        let commands = parse(&smt).unwrap();
        let mut exec = Executor::new();
        let outputs = exec.execute_all(&commands).unwrap();
        assert_eq!(
            outputs,
            vec!["unknown", "(:reason-unknown resourceout)"],
            "round {round}: the eager-persistent arm must exhaust the :rlimit conflict \
             budget, not run to the backstop"
        );
        assert_eq!(exec.unknown_reason(), Some(UnknownReason::ResourceLimit));
        let stats = exec.statistics();
        // Only the eager-persistent arm draws search allowances, so this pins
        // the route: on any other split-loop arm the statistic is absent.
        assert_eq!(
            stats.get_int("dpll.eager_persistent.searches"),
            Some(1),
            "round {round}: the query must run on the eager-persistent arm, whose one \
             search the count stops"
        );
        assert_eq!(
            stats.get_int("dpll.eager_persistent.slice_stops"),
            Some(0),
            "round {round}: iteration 0 has no slice; the allowance stopped it"
        );
        stop_points.push((stats.conflicts, stats.decisions));
    }
    assert!(
        stop_points.windows(2).all(|pair| pair[0] == pair[1]),
        "the count stops the arm at the same point every run: {stop_points:?}"
    );
}

#[test]
fn test_executor_rlimit_huge_budget_preserves_bv_unsat() {
    // Companion soundness guard for the BV `:rlimit` threading: a generous
    // budget must never perturb a normally-UNSAT BV query — the budget is an
    // exhaustion surface (Unknown/resourceout), NEVER a verdict. 8-bit
    // multiply commutativity refutation requires real bit-blast search yet
    // completes far inside a 1M-conflict budget.
    let smt = "(set-logic QF_BV)\n\
               (set-option :rlimit 1000000)\n\
               (declare-const a (_ BitVec 8))\n\
               (declare-const b (_ BitVec 8))\n\
               (assert (distinct (bvmul a b) (bvmul b a)))\n\
               (check-sat)\n";
    let commands = parse(smt).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();
    assert_eq!(outputs, vec!["unsat"]);

    // Proof lane twin: with `:produce-proofs true` the BV path bit-blasts
    // eagerly (no delayed ops) and takes the naked-solve site — the budget
    // must still be a no-interference bound there, the verdict must stay
    // `unsat`, and the proof must actually be produced (`get-proof` returns a
    // proof term, not an error).
    let smt_proof = "(set-logic QF_BV)\n\
                     (set-option :produce-proofs true)\n\
                     (set-option :rlimit 1000000)\n\
                     (declare-const a (_ BitVec 8))\n\
                     (declare-const b (_ BitVec 8))\n\
                     (assert (distinct (bvmul a b) (bvmul b a)))\n\
                     (check-sat)\n\
                     (get-proof)\n";
    let commands = parse(smt_proof).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();
    assert_eq!(outputs[0], "unsat");
    assert!(
        !outputs[1].contains("error") && !outputs[1].is_empty(),
        "huge budget must not suppress the UNSAT proof: {}",
        &outputs[1][..outputs[1].len().min(200)]
    );
}

#[test]
fn test_executor_rlimit_governs_fp_bitblast_subsolver() {
    // Regression (#8749, FP lane): `:rlimit` armed the MAIN pipeline CDCL
    // solves and (after the BV fix) the BV bit-blast sub-solves, but the FP
    // lane's bit-blast SatSolver still ran unbudgeted — same divergence class,
    // different theory. Float32 multiply commutativity refutation must push
    // `distinct` through two full 24-bit significand multipliers: measured on
    // the unbudgeted engine, 60s+ at 100% CPU with no verdict (wall-clock
    // decided). If search is needed, its budget must still report resourceout.
    // The independent exact commutativity schema can now finish before search;
    // that alternative is accepted only with a complete actual proof replay.
    let smt = "(set-option :produce-proofs true)\n\
               (set-logic QF_FP)\n\
               (set-option :rlimit 1)\n\
               (declare-const x (_ FloatingPoint 8 24))\n\
               (declare-const y (_ FloatingPoint 8 24))\n\
               (assert (distinct (fp.mul RNE x y) (fp.mul RNE y x)))\n\
               (check-sat)\n\
               (get-info :reason-unknown)\n";
    for round in 0..5 {
        let commands = parse(smt).unwrap();
        let mut exec = Executor::new();
        let outputs = exec.execute_all(&commands).unwrap();
        checked_fp_stop_or_early_refutation(&mut exec, &outputs, round);
    }
}

#[test]
fn test_executor_rlimit_governs_fp_to_real_refinement_chain() {
    // Regression (#8749, FP lane, `fp.to_real` two-phase path): the
    // refinement loop builds a FRESH SatSolver per iteration
    // (`solve_fp_sat_instance`), so the budget must bound the CHAIN total —
    // a per-solver budget would hand every iteration a fresh allowance.
    // The pure-FP side carries the divergent Float32 multiply-commutativity
    // refutation, so an unbudgeted chain burns wall clock; under `:rlimit 1`
    // search must retain the whole-chain allowance. A proved early identity
    // may avoid the chain entirely; replay that actual refutation rather than
    // freezing the historical resourceout outcome.
    let smt = "(set-option :produce-proofs true)\n\
               (set-logic QF_FPLRA)\n\
               (set-option :rlimit 1)\n\
               (declare-const x (_ FloatingPoint 8 24))\n\
               (declare-const y (_ FloatingPoint 8 24))\n\
               (assert (distinct (fp.mul RNE x y) (fp.mul RNE y x)))\n\
               (assert (= (fp.to_real x) (/ 3 2)))\n\
               (check-sat)\n\
               (get-info :reason-unknown)\n";
    for round in 0..5 {
        let commands = parse(smt).unwrap();
        let mut exec = Executor::new();
        let outputs = exec.execute_all(&commands).unwrap();
        checked_fp_stop_or_early_refutation(&mut exec, &outputs, round);
    }
}

#[test]
fn test_executor_rlimit_huge_budget_preserves_fp_unsat() {
    // Companion soundness guard for the FP `:rlimit` threading: a generous
    // budget must never perturb a normally-UNSAT FP query — the budget is an
    // exhaustion surface (Unknown/resourceout), NEVER a verdict. A small
    // format's multiply commutativity refutation requires real bit-blast
    // search yet completes far inside a 1M-conflict budget. (Float16 does
    // NOT: measured, its refutation honestly exhausts 1M conflicts — which is
    // budget semantics working, not a candidate for this guard.)
    let smt = "(set-logic QF_FP)\n\
               (set-option :rlimit 1000000)\n\
               (declare-const a (_ FloatingPoint 3 5))\n\
               (declare-const b (_ FloatingPoint 3 5))\n\
               (assert (distinct (fp.mul RNE a b) (fp.mul RNE b a)))\n\
               (check-sat)\n";
    let commands = parse(smt).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();
    assert_eq!(outputs, vec!["unsat"]);

    // Proof lane twin: the verdict must stay `unsat` under `:produce-proofs`
    // and the native proof must remain strict. Pinned Carcara has no FP sort
    // grammar; since D7 (2026-09-22) `get-proof` renders what the strict
    // checker accepted and the executor DISCLOSES the unsupported surface.
    let smt_proof = "(set-logic QF_FP)\n\
                     (set-option :produce-proofs true)\n\
                     (set-option :rlimit 1000000)\n\
                     (declare-const a (_ FloatingPoint 3 5))\n\
                     (declare-const b (_ FloatingPoint 3 5))\n\
                     (assert (distinct (fp.mul RNE a b) (fp.mul RNE b a)))\n\
                     (check-sat)\n\
                     (get-proof)\n";
    let commands = parse(smt_proof).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();
    assert_eq!(outputs[0], "unsat");
    assert!(
        !outputs[1].contains("UNVERIFIABLE PROOF")
            && !outputs[1].contains("error")
            && !outputs[1].is_empty(),
        "huge budget must not suppress the FP UNSAT proof: {}",
        &outputs[1][..outputs[1].len().min(200)]
    );
    let surface = exec
        .last_unsat_proof_carcara_surface()
        .expect("native FP proof after UNSAT");
    assert!(
        surface
            .unsupported_reason()
            .is_some_and(|reason| reason.contains("FloatingPoint")),
        "the FP sort must be disclosed as unsupported by pinned Carcara, got {surface}"
    );
    let proof = exec.last_proof().expect("native FP proof after UNSAT");
    let quality = ay_proof::check_proof_strict(proof, &exec.ctx.terms)
        .expect("the generous rlimit must preserve the strict native FP proof");
    assert!(quality.is_complete(), "{quality}");
}

#[test]
fn test_executor_rlimit_governs_enum_sat_bitblast_lane() {
    // Regression (#8749, EUF enum lane): the enum finite-domain SAT lane's
    // bit-blast SatSolver solve ran unbudgeted. Exhaustion there is
    // fail-closed twice over: the lane returns `Unknown` and FALLS THROUGH to
    // the general lane (never a verdict), and the general lane's own solves
    // are budget-governed, so the query surfaces `resourceout`
    // deterministically instead of letting the enum solve burn unbudgeted
    // wall clock. (Phase trace confirms this instance HITS the enum lane;
    // the plain Grötzsch graph is NOT usable here — its 3-coloring
    // refutation lands inside a 1-conflict budget on the in-process
    // configuration, and an answer found inside the allowance is KEPT by
    // the answer-before-budget ordering, so the test needs the strictly
    // harder Mycielskian.)
    let smt = mycielski_groetzsch_coloring_smt("(set-option :rlimit 1)\n");
    for round in 0..5 {
        let commands = parse(&smt).unwrap();
        let mut exec = Executor::new();
        let outputs = exec.execute_all(&commands).unwrap();
        assert_eq!(
            outputs,
            vec!["unknown", "(:reason-unknown resourceout)"],
            "round {round}: enum finite-domain SAT lane must respect the \
             :rlimit conflict budget deterministically"
        );
        // The BITE for the enum lane specifically: armed, the lane exhausts
        // its allowance and falls through (`fallback-unknown`). Neutered, the
        // lane solves unbudgeted and records its own verdict in this stat
        // (the final answer can still degrade to resourceout through the
        // budget-governed certification funnel, so the OUTPUT alone cannot
        // distinguish an armed lane from an unarmed one — this stat can).
        match exec.get_statistics().extra.get("solver.enum_sat_lane") {
            Some(crate::StatValue::String(s)) => assert_eq!(
                s, "fallback-unknown",
                "round {round}: the enum lane's own SAT solve must be the \
                 thing the budget stopped"
            ),
            other => panic!("round {round}: enum lane stat missing/wrong: {other:?}"),
        }
    }

    // Companion soundness guard: a generous budget must never perturb the
    // normally-UNSAT verdict (the budget is an exhaustion surface, never a
    // verdict), and the answer-before-budget ordering means a refutation the
    // lane completes inside its allowance is kept.
    let smt = mycielski_groetzsch_coloring_smt("(set-option :rlimit 1000000)\n");
    let commands = parse(&smt).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();
    assert_eq!(outputs[0], "unsat");
}

/// SMT text asserting a 4-coloring of the Mycielskian of the Grötzsch graph
/// (23 vertices, chromatic number 5) over a 4-constructor enum sort: UNSAT,
/// in-fragment for the enum finite-domain SAT lane (pure ground enum
/// disequalities — the vlsat3 coloring shape the lane exists for), and the
/// refutation needs real one-hot SAT search rather than unit propagation or
/// a single conflict. Shared by the deterministic-budget tests above.
fn mycielski_groetzsch_coloring_smt(options: &str) -> String {
    // Grötzsch graph = Mycielski of C5: outer cycle c0..c4, mirrors
    // g(5+i) ~ c_{i±1}, apex g10 ~ every mirror.
    let mut g_edges: Vec<(u32, u32)> = Vec::new();
    for i in 0..5u32 {
        g_edges.push((i, (i + 1) % 5));
        g_edges.push((5 + i, (i + 4) % 5));
        g_edges.push((5 + i, (i + 1) % 5));
        g_edges.push((10, 5 + i));
    }
    // Mycielskian: originals 0..10 keep their edges, mirror (v+11) is
    // adjacent to every neighbor of v, apex 22 is adjacent to every mirror.
    let mut edges = g_edges.clone();
    for &(a, b) in &g_edges {
        edges.push((a + 11, b));
        edges.push((b + 11, a));
    }
    for i in 0..11u32 {
        edges.push((22, 11 + i));
    }

    let mut smt = format!(
        "(set-logic QF_DT)\n{options}\
         (declare-datatypes ((Color 0)) (((C0) (C1) (C2) (C3))))\n"
    );
    for v in 0..23 {
        smt.push_str(&format!("(declare-const v{v} Color)\n"));
    }
    for (a, b) in edges {
        smt.push_str(&format!("(assert (distinct v{a} v{b}))\n"));
    }
    smt.push_str("(check-sat)\n(get-info :reason-unknown)\n");
    smt
}
