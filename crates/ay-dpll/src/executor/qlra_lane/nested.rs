// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The lane's nested search (#qlra-nested-cegqi milestones M2/M3), default
//! ON; `--no-qlra-nested` turns it off.
//!
//! The search runs the Fig. 8 recursion (`cegqi::lra_nested::nested`) and
//! records its verdict as `qlra.shadow_verdict`. Its verdicts are HINTS:
//!
//! * a nested `unsat` publishes ONLY through its UNSAT expansion certificate
//!   (M3a, `nested_publish.rs`): tautological quantifier lemmas built from
//!   the instance log Γ, a strict ground refutation of the proxied set, and
//!   the unchanged strict installation boundary. Otherwise the lane declines
//!   and the legacy path runs with the pass rolled back;
//! * a nested `sat` reaches the public answer only through the SAT route: a
//!   model of the final main query is installed, the instance log is
//!   installed as untrusted expansion hints (`hints.rs`, M3b), and the
//!   quantified model gate must confirm every authored quantified conjunct —
//!   by its existing routes or by its confirm-only expansion route, a
//!   checked refutation of the negated conjunct's Herbrand expansion.

use super::super::Executor;
use super::{probe_oracle, LaneSearch};
use crate::cegqi::lra_nested::approx::NInstance;
use crate::cegqi::lra_nested::ntree::NestedTree;
use crate::cegqi::lra_nested::{self, QlraOutcome};
use ay_core::TermId;

/// A nested search's result: the outcome, the final main query (on `Sat`,
/// every model of it satisfies the roots), and the tree and instance log Γ
/// the UNSAT expansion certificate is built from. All of it HINTS.
#[derive(Clone)]
pub(in crate::executor) struct NestedSearch {
    pub(in crate::executor) outcome: QlraOutcome,
    pub(in crate::executor) main: Vec<TermId>,
    pub(in crate::executor) tree: NestedTree,
    pub(in crate::executor) gamma: Vec<Vec<NInstance>>,
    /// The final exact flags (for the session cache, `session.rs`).
    pub(in crate::executor) exact: Vec<bool>,
    /// An expansion certificate a pass whose strict obligation lacked the
    /// authored roots built and pre-checked, parked for the retry pass to
    /// install (`nested_publish.rs`). A hint like everything else here.
    pub(in crate::executor) deferred: Option<ay_core::Proof>,
}

fn stat_label(outcome: &QlraOutcome) -> &'static str {
    match outcome {
        QlraOutcome::Unsat => "unsat",
        QlraOutcome::Sat => "sat",
        QlraOutcome::Decline(_) => "decline",
    }
}

impl Executor {
    /// Build the nested tree and run the search. `None` when the tree
    /// builder declined the shape.
    pub(super) fn qlra_nested_search(&mut self, roots: &[TermId]) -> Option<LaneSearch> {
        self.last_statistics.set_int("qlra.nested", 1);
        // M4: a session cache bound to a retired store snapshot is cleared
        // here, before the builder could read a recycled id.
        let cached = self.qlra_lane.session.validate(&self.ctx.terms);
        let built = lra_nested::build_nested_tree_reusing(
            &mut self.ctx.terms,
            roots,
            cached.then_some(&self.qlra_lane.session),
        );
        let tree = match built {
            Ok(tree) => tree,
            Err(decline) => {
                self.last_statistics
                    .set_string("qlra.decline", format!("nested-shape-{decline:?}"));
                return None;
            }
        };
        let extra = &mut self.last_statistics;
        extra.set_int("qlra.nodes", tree.nodes.len() as u64);
        extra.set_int("qlra.max_depth", tree.max_depth() as u64);
        let seed = cached.then(|| self.qlra_lane.session.seed(&tree));
        let hits = seed.as_ref().map_or(0, |seed| seed.hits);
        self.last_statistics
            .set_int("qlra.session_hits", hits as u64);
        let deadline = self.qlra_lane_deadline();
        let run = {
            let mut host = probe_oracle::ExecutorQlraHost::with_route(
                self,
                deadline,
                probe_oracle::OracleRoute::DirectQfLra,
            );
            lra_nested::nested::solve_nested_seeded(
                &mut host,
                &tree,
                lra_nested::nested::NestedCaps::default(),
                seed.filter(|seed| seed.hits > 0),
            )
        };
        // A single probe polls the lane deadline only as coarsely as the LRA
        // solve does; record how far past it the search ran.
        let overshoot = ay_core::time::Instant::now().saturating_duration_since(deadline);
        let overshoot_ms = u64::try_from(overshoot.as_millis()).unwrap_or(u64::MAX);
        let extra = &mut self.last_statistics;
        extra.set_int("qlra.deadline_overshoot_ms", overshoot_ms);
        extra.set_int("qlra.rounds", run.stats.rounds as u64);
        extra.set_int("qlra.oracle_calls", run.stats.oracle_calls as u64);
        extra.set_int("qlra.instances", run.stats.instances as u64);
        extra.set_int("qlra.exact_nodes", run.stats.exact_nodes as u64);
        extra.set_int("qlra.approx_max", run.stats.approx_max as u64);
        extra.set_int("qlra.oracle_ms", run.stats.oracle_ms);
        extra.set_string("qlra.shadow_verdict", stat_label(&run.outcome));
        if let QlraOutcome::Decline(decline) = run.outcome {
            extra.set_string("qlra.decline", decline.label());
        }
        tracing::debug!(
            target: "ay::qlra",
            "nested: outcome={:?} rounds={} calls={} instances={} approx_max={} oracle_ms={} \
             exact={} nodes={} depth={} overshoot_ms={}",
            run.outcome,
            run.stats.rounds,
            run.stats.oracle_calls,
            run.stats.instances,
            run.stats.approx_max,
            run.stats.oracle_ms,
            run.stats.exact_nodes,
            tree.nodes.len(),
            tree.max_depth(),
            overshoot_ms,
        );
        Some(LaneSearch::Nested(Box::new(NestedSearch {
            outcome: run.outcome,
            main: run.main,
            tree,
            gamma: run.gamma,
            exact: run.exact,
            deferred: None,
        })))
    }
}
