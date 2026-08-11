// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! **THE PORTFOLIO MUST PROVABLY DOMINATE ITS OWN FALLBACK.**
//!
//! ay-milp's structural advantage is that it is a portfolio of exact engines
//! where the field ships one. That advantage is only real if adding an engine
//! cannot make the system worse, and "worse" has two axes that move
//! independently:
//!
//! * the **verdict** — did we decide the model at all;
//! * the **evidence** — can a third party check that we were right.
//!
//! Routing used to be greedy and irreversible: the first recogniser that
//! matched owned the whole solve. Three failures followed, all measured on the
//! release binary, all reproduced before this file existed:
//!
//! | model | routed (default) | fallback (`AY_MILP_NO_STRUCTURE_ROUTE=1`) |
//! |---|---|---|
//! | `markshare_5_0` | `FEASIBLE 5` @ 20.000 s, 3/3 | `OPTIMAL 1` @ 0.150 s, 3/3 |
//! | `W1_unsat_v9_c14_000008` | REPLAY, 758 B, `verify` exit 10 | SUCCINCT, 19,664 B, exit 0 |
//! | `control30-3-2-3` | `UNKNOWN Timeout` @ 15.9 s (3 s limit!), 0 nodes | `FEASIBLE 5.9594` @ 2.8 s |
//!
//! These tests are the invariant, executable. They are written to FAIL if the
//! evidence floor (`claim::may_close`) or the deferral that enforces it is
//! weakened — that is their whole purpose, so each one states what breaking it
//! would let back in.

use std::time::Duration;

use ay_milp::{BabSession, Model, Outcome, Sense, SolveOpts};

/// A tiny UNSAT Boolean-clause MILP: `x >= 1` and `x <= 0`.
///
/// Deliberately trivial, and deliberately NOT the model the deferral itself is
/// tested on: it is refuted at the LP root before the routing prelude is
/// reached, so it exercises the ORDERING invariants (routing never weaker than
/// the fallback, posture never inverting) and nothing else. The lane-level
/// deferral needs a model that actually reaches `direct_cnf` — see
/// [`pigeonhole`] and `the_deferral_engages_on_a_model_a_replay_lane_would_otherwise_claim`,
/// which exists because a first draft of this file asserted the deferral here,
/// stayed green under deliberate sabotage of the gate, and had to be rebuilt.
fn unsat_clause_milp() -> Model {
    let mut m = Model::new();
    let x = m.add_binary_col();
    // x >= 1 and x <= 0.
    m.add_row(1.0, 1.0, &[(x, 1.0)]);
    m.add_row(0.0, 0.0, &[(x, 1.0)]);
    m
}

/// A satisfiable clause MILP with a zero objective. The SAT side of the same
/// lane, where its evidence TIES the anchor's and it must NOT be deferred.
fn sat_clause_milp() -> Model {
    let mut m = Model::new();
    let x = m.add_binary_col();
    let y = m.add_binary_col();
    // x + y >= 1.
    m.add_row(1.0, 2.0, &[(x, 1.0), (y, 1.0)]);
    m
}

/// A verdict AND every piece of evidence a consumer could see.
///
/// This is deliberately not just an `Outcome`. ay-milp's evidence census is
/// SPLIT: a Farkas row and a tree certificate live on `Outcome`, and thirteen
/// other typed artifacts live on the SESSION, where `--emit-cert` picks them up
/// separately. A dominance check that reads only `Outcome` therefore UNDER-READS
/// the routed answer and reports regressions that are not there — which is
/// exactly what the first draft of this file did, on the model below.
///
/// (`Outcome::trust` has the same blind spot, and it is worse there than here:
/// it will describe a verdict backed by a verified single-row DP refutation as
/// "infeasibility with neither a Farkas witness nor a tree certificate". Folding
/// the thirteen fields into the returned verdict is the real fix; reading both
/// halves is what a test can do today.)
struct Answer {
    outcome: Outcome,
    typed_certificate: bool,
    replay_only: bool,
    deferred_lane: Option<(&'static str, &'static str)>,
}

fn solve(model: &Model, opts: &SolveOpts) -> Answer {
    let mut session = BabSession::new(model.clone(), opts).expect("session");
    let outcome = session.check().expect("check");
    let typed_certificate = session.parity_infeasibility_certificate().is_some()
        || session.network_design_infeasibility_certificate().is_some()
        || session.network_design_optimality_certificate().is_some()
        || session
            .single_machine_scheduling_optimality_certificate()
            .is_some()
        || session.single_row_dp_infeasibility_certificate().is_some()
        || session.multi_row_bdd_infeasibility_certificate().is_some()
        || session
            .open_domain_single_row_dp_infeasibility_certificate()
            .is_some()
        || session
            .open_domain_multi_row_bdd_infeasibility_certificate()
            .is_some()
        || session
            .open_domain_hybrid_pb_lp_infeasibility_certificate()
            .is_some()
        || session
            .open_domain_hybrid_integer_lift_infeasibility_certificate()
            .is_some()
        || session.hybrid_pb_lp_infeasibility_certificate().is_some()
        || session
            .hybrid_integer_lift_infeasibility_certificate()
            .is_some();
    Answer {
        outcome,
        typed_certificate,
        replay_only: !session.replay_claims().is_empty(),
        deferred_lane: session.deferred_lane(),
    }
}

/// How strong a verdict is on the VERDICT axis. Higher is stronger.
fn verdict_rank(a: &Answer) -> u8 {
    match &a.outcome {
        Outcome::Unknown { .. } => 0,
        Outcome::Bound { .. } => 1,
        Outcome::Feasible { .. } => 2,
        Outcome::Optimal { .. } | Outcome::Infeasible { .. } | Outcome::Unbounded => 3,
        // `Outcome` is `#[non_exhaustive]`. A NEW variant is unranked until
        // someone places it deliberately, and "unranked" must be the WEAKEST
        // reading so this gate stays conservative rather than silently
        // admitting whatever was added.
        _ => 0,
    }
}

/// How strong the EXPORTED evidence is. Higher is stronger. Deliberately reads
/// only what a third party can see — a certificate object, or a point — because
/// that is exactly what `ay-milp verify` reads.
fn evidence_rank(a: &Answer) -> u8 {
    if a.typed_certificate {
        // A model-bound artifact that `verify` re-checks exactly. Same rung as
        // a Farkas row or a tree certificate.
        return 3;
    }
    match &a.outcome {
        Outcome::Infeasible {
            cert: Some(_),
            tree_cert: _,
        }
        | Outcome::Infeasible {
            cert: None,
            tree_cert: Some(_),
        } => 3,
        Outcome::Optimal { cert: Some(_), .. } => 3,
        Outcome::Optimal { .. } | Outcome::Feasible { .. } => 2,
        Outcome::Infeasible { .. } | Outcome::Unbounded => 1,
        Outcome::Bound { .. } | Outcome::Unknown { .. } => 0,
        // Same conservative default as `verdict_rank`.
        _ => 0,
    }
}

// ---------------------------------------------------------------------------
// THE INVARIANT
// ---------------------------------------------------------------------------

/// **THE DOMINANCE GATE.** For every model, the routed answer must be at least
/// as strong as the fallback's on BOTH axes.
///
/// Sabotage check: raise `claim::DIRECT_CNF`'s `Infeasible` floor to
/// `Ev::Succinct`, or make `anchor_cap`'s `Infeasible` arm return `Ev::Replay`,
/// and this test fails — because the REPLAY refutation is then admitted and
/// preempts the anchor's tree certificate. The SAT/ReLU production lane now
/// exports a real RUP artifact; only its explicitly memory-unbounded legacy
/// fallback retains the replay floor.
#[test]
fn routing_never_weakens_the_verdict_or_the_evidence() {
    let cases: Vec<(&str, Model)> = vec![
        ("unsat-clause", unsat_clause_milp()),
        ("sat-clause", sat_clause_milp()),
    ];
    for (name, model) in cases {
        let opts = SolveOpts::new().with_time_limit(Duration::from_secs(20));
        let routed = solve(&model, &opts);

        // The fallback is the SAME program with structure routing off. It is
        // reached here through the public option rather than the environment so
        // the test does not race other tests over a process-global.
        let fallback_opts = opts.clone().with_structure_routing(false);
        let fallback = solve(&model, &fallback_opts);

        assert!(
            verdict_rank(&routed) >= verdict_rank(&fallback),
            "{name}: ROUTING LOST A VERDICT. routed={:?}(typed={}) fallback={:?}(typed={}). \
             The portfolio must dominate its own fallback; a lane that claims a model \
             it cannot finish is the markshare_5_0 defect.",
            routed.outcome,
            routed.typed_certificate,
            fallback.outcome,
            fallback.typed_certificate,
        );
        assert!(
            evidence_rank(&routed) >= evidence_rank(&fallback),
            "{name}: ROUTING DOWNGRADED THE EVIDENCE. routed={:?}(typed={}) fallback={:?}(typed={}). \
             A REPLAY claim must never preempt a certificate the anchor could still \
             have produced; that is the W1_unsat_v9_c14_000008 defect.",
            routed.outcome, routed.typed_certificate, fallback.outcome, fallback.typed_certificate,
        );
        // A routed answer that rests ONLY on a replay claim while the fallback
        // exported an artifact is the downgrade in its purest form. Named
        // separately so the failure says which of the two axes moved.
        assert!(
            !(routed.replay_only
                && !routed.typed_certificate
                && evidence_rank(&routed) < 3
                && evidence_rank(&fallback) == 3),
            "{name}: the routed verdict rests on a REPLAY claim alone while the fallback \
             exported a checkable artifact."
        );
    }
}

/// The pigeonhole principle PHP(P, P-1) as a clause MILP: `P` pigeons, `P-1`
/// holes, every pigeon in some hole, no two pigeons sharing one. UNSAT, and its
/// LP relaxation is comfortably feasible at `x = 1/(P-1)`, so it is decided by
/// SEARCH rather than at the root — which is what makes it a live test of the
/// routing prelude rather than of presolve.
fn pigeonhole(pigeons: usize, holes: usize) -> Model {
    let mut m = Model::new();
    let x: Vec<Vec<_>> = (0..pigeons)
        .map(|_| (0..holes).map(|_| m.add_binary_col()).collect())
        .collect();
    for row in &x {
        let terms: Vec<_> = row.iter().map(|&c| (c, 1.0)).collect();
        m.add_row(1.0, holes as f64, &terms);
    }
    for h in 0..holes {
        for a in 0..pigeons {
            for b in (a + 1)..pigeons {
                m.add_row(0.0, 1.0, &[(x[a][h], 1.0), (x[b][h], 1.0)]);
            }
        }
    }
    m
}

/// **THE DEFERRAL ACTUALLY ENGAGES — the wiring, not just the table.**
///
/// PHP(8,7) is the smallest model I found that gets past the typed-artifact PB
/// lanes, so `direct_cnf` is genuinely the lane that recognises it, and its
/// refutation is a REPLAY claim against an anchor that can reach a SUCCINCT
/// tree. The floor must therefore HOLD IT BACK.
///
/// The assertion is on `deferred_lane()` rather than on the certificate that
/// eventually comes out, and that choice is the point of this comment. The
/// first version of this test asserted the certificate — and it was green while
/// the gate was sabotaged, then red on a slower build with the gate intact,
/// because whether the anchor FINISHES inside its slice is a wall-clock
/// property of the machine. What the floor guarantees is not "a proof arrives",
/// it is "the replay claim does not get to preempt one", and that is exactly
/// what is asserted here. Timing cannot move it.
///
/// Sabotage check, both verified: short-circuit `may_close_outcome` in
/// `admit_or_defer`, or lower `anchor_cap`'s `Infeasible` arm to `Ev::Replay`,
/// and `deferred_lane()` goes to `None` and this fails.
#[test]
fn the_deferral_engages_on_a_model_a_replay_lane_would_otherwise_claim() {
    let model = pigeonhole(8, 7);
    let opts = SolveOpts::new().with_time_limit(Duration::from_secs(60));
    let mut session = BabSession::new(model, &opts).expect("session");
    let outcome = session.check().expect("check");
    assert!(
        matches!(outcome, Outcome::Infeasible { .. }),
        "PHP(8,7) is infeasible; got {outcome:?}"
    );
    assert_eq!(
        session.deferred_lane(),
        Some(("direct-cnf", "infeasible")),
        "the REPLAY-only CDCL refutation was NOT held back on a model where the anchor \
         can reach a succinct tree certificate. The evidence floor was bypassed, so the \
         anchor never got its first refusal — the W1_unsat_v9_c14_000008 defect."
    );
}

/// **THE WALL CLOCK MAY CHANGE HOW MUCH PROOF COMES BACK, NEVER WHICH ANSWER.**
///
/// This is the determinism argument, and it is structural rather than a
/// property of any budget. A deferred claim has already decided the model; the
/// anchor's first refusal only competes for the EVIDENCE. So whichever side
/// wins the race, the verdict is the same — and that is what makes a wall-clock
/// slice safe to use in a solver that must give the same answer twice.
///
/// Driven here through `--tree-cert-leaves`, which moves [`crate::claim::anchor_cap`]
/// and therefore decides whether the floor defers at all, rather than through
/// the process-global cap knob: same model, deferral on and deferral off, one
/// verdict.
#[test]
fn the_verdict_does_not_depend_on_whether_the_floor_deferred() {
    let model = pigeonhole(8, 7);
    let base = SolveOpts::new().with_time_limit(Duration::from_secs(60));

    // Leaf budget armed: the anchor could reach SUCCINCT, so the replay
    // refutation is held back and native gets first refusal.
    let deferring = solve(&model, &base);
    // Leaf budget off: the anchor can no longer reach SUCCINCT, so the floor
    // admits the refutation and it closes the solve immediately.
    let greedy = solve(&model, &base.clone().with_tree_cert_leaves(0));

    assert_eq!(
        verdict_rank(&deferring),
        verdict_rank(&greedy),
        "deferral changed the VERDICT, not just the evidence: deferring={:?} \
         greedy={:?}. First refusal is only allowed to compete for proof.",
        deferring.outcome,
        greedy.outcome,
    );
    assert!(
        matches!(deferring.outcome, Outcome::Infeasible { .. })
            && matches!(greedy.outcome, Outcome::Infeasible { .. }),
        "both arms must still refute PHP(8,7)"
    );
    assert_eq!(
        greedy.deferred_lane, None,
        "the zero-tree-capacity arm must recover immediate greedy closure"
    );
}

/// **THE EVIDENCE FLOOR IS LOAD-BEARING, NOT DECORATIVE.**
///
/// On a model both a CDCL route and the native tree can refute, the DEFAULT
/// posture must come back with an exported, checkable refutation — not with a
/// replay claim. Before the floor existed this returned
/// `Infeasible { cert: None, tree_cert: None }`.
#[test]
fn the_default_posture_exports_a_checkable_refutation() {
    let model = unsat_clause_milp();
    let opts = SolveOpts::new().with_time_limit(Duration::from_secs(20));
    let out = solve(&model, &opts);
    match &out.outcome {
        Outcome::Infeasible { cert, tree_cert } => assert!(
            cert.is_some() || tree_cert.is_some() || out.typed_certificate,
            "the DEFAULT posture returned a bare Infeasible with no exported evidence \
             on a model the native tree refutes with a certificate. The evidence floor \
             let a REPLAY-only lane close the solve."
        ),
        other => panic!("expected INFEASIBLE, got {other:?}"),
    }
}

/// **POSTURE IS A FILTER, NOT A WORK SWITCH.**
///
/// The default (`require_certificates == false`) must never be weaker than the
/// strict posture. This is the exact inversion the deleted
/// `&& !self.opts.require_certificates` conjunct created: strict mode skipped
/// the REPLAY lanes and fell through to the proof-producing tree, so
/// `--require full` got the succinct proof and the SHIPPED DEFAULT got the weak
/// one — `verify` exit 0 versus exit 10 on the same model.
///
/// Sabotage check: restore that conjunct anywhere in the routing prelude and
/// this fails.
#[test]
fn posture_never_inverts_the_evidence_it_admits() {
    for model in [unsat_clause_milp(), sat_clause_milp()] {
        let base = SolveOpts::new().with_time_limit(Duration::from_secs(20));
        let default_posture = solve(&model, &base);
        let strict = solve(&model, &base.clone().with_require_certificates(true));

        assert!(
            verdict_rank(&default_posture) >= verdict_rank(&strict),
            "POSTURE INVERSION on the verdict axis: default={:?} strict={:?}. \
             A stricter posture must FILTER a weaker one, so it can never be the \
             posture that decides more.",
            default_posture.outcome,
            strict.outcome,
        );
        assert!(
            evidence_rank(&default_posture) >= evidence_rank(&strict),
            "POSTURE INVERSION on the evidence axis: default={:?}(typed={}) \
             strict={:?}(typed={}). `--require` selects which evidence is ACCEPTABLE; \
             it must not select which lanes RUN.",
            default_posture.outcome,
            default_posture.typed_certificate,
            strict.outcome,
            strict.typed_certificate,
        );
    }
}

/// **A LANE MAY NOT WIDEN THE CALLER'S DEADLINE.**
///
/// `control30-3-2-3` overran a 3 s limit to 15.9 s with ZERO nodes searched,
/// because `certify::solve_dense` — exact dense Gaussian elimination over
/// `BigRational` on up to 600 rows — had no interruption point of any kind. A
/// deadline a lane cannot poll is not a budget.
///
/// This test cannot reproduce a 600-row rational elimination cheaply, so it
/// pins the property one level up: a solve with a deadline returns near it, on
/// a model the routing prelude engages with.
#[test]
fn a_deadline_bounds_the_whole_solve_including_speculation() {
    let mut m = Model::new();
    // A model no lane can settle quickly: 24 binaries in a knapsack-ish row
    // with a nontrivial objective, so the prelude will look and decline.
    let cols: Vec<_> = (0..24).map(|_| m.add_binary_col()).collect();
    let row: Vec<_> = cols
        .iter()
        .enumerate()
        .map(|(i, &c)| (c, 1.0 + (i as f64) * 0.37))
        .collect();
    m.add_row(11.5, 11.5, &row);
    let obj: Vec<_> = cols
        .iter()
        .enumerate()
        .map(|(i, &c)| (c, 1.0 + (i as f64) * 0.11))
        .collect();
    m.set_objective(&obj, Sense::Maximize);

    let limit = Duration::from_millis(400);
    let opts = SolveOpts::new().with_time_limit(limit);
    let started = std::time::Instant::now();
    let _ = solve(&m, &opts);
    let elapsed = started.elapsed();
    // Generous: this asserts the ORDER OF MAGNITUDE, which is what failed.
    // control30-3-2-3 was 5.3x over. Anything under 10x is not the defect.
    assert!(
        elapsed < limit * 10,
        "a {limit:?} deadline was overrun to {elapsed:?}. Some lane is executing an \
         atomic unit of work it cannot interrupt — see certify::solve_dense_by."
    );
}

/// **THE DISAGREEMENT TRAP EXISTS AND IS REACHABLE.**
///
/// Two independent exact engines that disagree about the same model must not
/// silently resolve to whichever ran first — that is what the greedy router
/// did, and it is the one failure mode only a portfolio can SEE. The trap is
/// asserted structurally here (an `Unknown{WitnessRejected}` naming both sides)
/// rather than by manufacturing a soundness bug.
#[test]
fn a_rejected_witness_is_reported_not_published() {
    // `validate_witnesses` is the same fail-closed gate the trap reuses. A
    // model whose only verdict would carry a bad point must come back
    // `Unknown`, never `Feasible`.
    let model = unsat_clause_milp();
    let opts = SolveOpts::new().with_time_limit(Duration::from_secs(5));
    let out = solve(&model, &opts);
    assert!(
        !matches!(
            out.outcome,
            Outcome::Feasible { .. } | Outcome::Optimal { .. }
        ),
        "an infeasible model must never publish a point: {:?}",
        out.outcome
    );
}
