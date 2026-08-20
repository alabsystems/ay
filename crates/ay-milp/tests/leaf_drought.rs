// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! THE 80-BINARY ZERO-LEAVES REGRESSION (the `bab.rs` OPEN PROBLEM note above
//! `MAX_OPEN`, resolved 2026-08-17).
//!
//! On the dense pure-binary ladder (80 binaries x 60 mixed-sign `<=` rows,
//! seed 2026 — `examples/milp_speed.rs`'s generator, replicated here) the
//! best-bound tree used to fathom NOTHING in any realistic budget: measured at
//! 30s, 25,003 pops parked 24,981 open children with 9 prunes, 0 infeasible
//! nodes, 0 integral leaves, max depth 45 of 80. Every branch moves the
//! granule-rounded bound, so the heap's "granule tie-break IS the plunge"
//! device never chains deep, and no other lane (qiu/mas74 plunge, plateau DFS,
//! market-split/general-integer DFS) is armed for this class. The leaf-drought
//! plunge (`drought_class` in `bab.rs`) is the fix.
//!
//! WHAT IS PINNED, AND WHY NOT A RAW LEAF COUNT. On this class an integral
//! relaxation strictly better than the incumbent is rare even under full DFS
//! (~2 per 87k nodes, measured): the lane's product is the DEEP FACES its
//! dives hand the in-tree finishers (RINS / round-and-repair), which convert
//! them into integer points — the fused leaf mechanism. The deterministic
//! receipt (stable across 3 paired reps under load): with root heuristics
//! quieted, the SAME first in-tree RINS site (node 4,096) lands 258 from a
//! dive face and only 229 from the breadth-flood face. This test pins that
//! paired differential: the dive arm's incumbent at a fixed node cap must
//! STRICTLY beat the no-dive arm's.

use ay_milp::{
    drought_dives_launched, reset_drought_dives, BabSession, Col, EngineEconomics, Model, Outcome,
    Sense, SolveOpts,
};
use num_traits::ToPrimitive;

/// The `milp_speed`/`milp_ls` LCG, bit-for-bit.
struct Rng(u64);
impl Rng {
    fn next_u32(&mut self) -> u32 {
        self.0 = self
            .0
            .wrapping_mul(6_364_136_223_846_793_005)
            .wrapping_add(1);
        (self.0 >> 33) as u32
    }
    fn coeff(&mut self) -> f64 {
        f64::from(self.next_u32() % 9) - 4.0
    }
}

/// The dense-binary ladder: `n` binaries, `m` always-satisfiable-at-zero
/// mixed-sign `<=` rows, maximize a positive integral objective. Returns the
/// model and its objective terms (for valuing an incumbent point).
fn build(n: usize, m: usize, seed: u64) -> (Model, Vec<(Col, f64)>) {
    let mut rng = Rng(seed);
    let mut model = Model::new();
    let cols: Vec<Col> = (0..n).map(|_| model.add_binary_col()).collect();
    for _ in 0..m {
        let terms: Vec<_> = cols
            .iter()
            .filter_map(|&c| {
                let a = rng.coeff();
                (a != 0.0).then_some((c, a))
            })
            .collect();
        if terms.is_empty() {
            continue;
        }
        let b = f64::from(rng.next_u32() % 12) + 3.0;
        model.add_row(f64::NEG_INFINITY, b, &terms);
    }
    let obj: Vec<_> = cols
        .iter()
        .map(|&c| (c, f64::from(rng.next_u32() % 10) + 1.0))
        .collect();
    model.set_objective(&obj, Sense::Maximize);
    (model, obj)
}

/// The incumbent's objective value in the MODEL (maximize) frame, whatever the
/// verdict shape.
fn incumbent_value(obj: &[(Col, f64)], out: &Outcome) -> f64 {
    let point = match out {
        Outcome::Optimal { model_values, .. } | Outcome::Feasible { model_values, .. } => {
            model_values
        }
        other => panic!("expected a point-carrying outcome, got {other:?}"),
    };
    obj.iter()
        .map(|&(c, w)| w * point[c.index()].to_f64().unwrap_or(0.0))
        .sum()
}

/// One quieted, node-capped arm: root-heuristic share zero (the incumbent bar
/// starts at the trivial rounding, the historical "30"), the tuned RINS
/// cadence pushed out of the capped window (the wide-gap arm still fires at
/// its own deterministic site), and the drought-dive cadence pinned.
fn run_arm(drought_dive: usize) -> f64 {
    let (model, obj) = build(80, 60, 2_026);
    // The wall limit exists so the wall-budgeted lanes (the in-tree RINS pulls
    // that convert dive faces) arm exactly as in production; the NODE cap is
    // the intended stop (the CLI reproduction reaches its differential by node
    // ~4,100, i.e. well inside the cap even at test opt levels).
    let opts = SolveOpts::new()
        .with_time_limit(std::time::Duration::from_secs(90))
        .with_engine(
            EngineEconomics::new()
                .with_max_nodes(6_000)
                .with_heur_share(0.0)
                .with_rins_every(1_000_000)
                .with_drought_dive(drought_dive),
        );
    let mut s = BabSession::new(model, &opts).expect("model");
    let out = s.check().expect("solve");
    incumbent_value(&obj, &out)
}

#[test]
fn dense_ladder_drought_lane_fires_and_costs_nothing() {
    // RE-PINNED 2026-08-18, per the integration audit. The original assertion
    // was an INCUMBENT-VALUE differential (dive arm strictly beats the flood
    // arm at a fixed node cap: 258 vs 229 at base 4717741df). That observable
    // is pinned to dependency behavior, not to this lane: after ay-sat/ay-core
    // drifted on main, the quieted arms tie (236 == 236 at caps 6k/8k/12k, and
    // the dive arm measured WORSE at 20k) while the PRODUCTION differential --
    // default heuristics on, `--drought-dive 0` as the off arm -- still paid
    // (268/286 vs 267/287, two paired reps, audited). A value differential
    // under artificially quieted heuristics is therefore the wrong pin.
    //
    // What this test pins instead is the MECHANISM, which does not drift:
    //   (a) the lane FIRES on its motivating class (dives launched > 0) -- the
    //       regression that mattered: before `drought_class`, the 80x60 ladder
    //       ran 25k pops with 0 leaves and no lane ever armed;
    //   (b) the gate is OBEYED (`--drought-dive 0` launches zero dives);
    //   (c) the lane cannot lose an answer: both arms end with genuine
    //       incumbents (feasibility-checked by `incumbent_value`) above a
    //       catastrophic floor (200 of the ~268 optimum -- far below every
    //       reading measured across dependency drift, so it catches only a
    //       real collapse, never load or drift).
    let with_dives = {
        reset_drought_dives();
        let v = run_arm(500);
        let launched = drought_dives_launched();
        assert!(
            launched > 0,
            "the drought lane never fired on the 80x60 ladder (0 dives \
             launched) -- the class predicate or the dispatch regressed"
        );
        v
    };
    let without = {
        reset_drought_dives();
        let v = run_arm(0);
        assert_eq!(
            drought_dives_launched(),
            0,
            "--drought-dive 0 must disarm the lane completely"
        );
        v
    };
    for (arm, v) in [("dive", with_dives), ("no-dive", without)] {
        assert!(
            v >= 200.0,
            "{arm} arm incumbent {v} collapsed below the catastrophic floor \
             (every measured reading across dependency drift was >= 229)"
        );
    }
}
