// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Cold-clone node-relaxation probe used by the parallel-readiness guard.

use std::time::Instant;

use num_rational::BigRational;

use super::{exact_bound, safe_bound};
use crate::model::{Col, Model};
use crate::simplex::{FloatLp, SimplexStatus};

// ===========================================================================
// STAGE-0 COLD-CLONE READINESS PROOF-OF-CONCEPT (inert to the serial verdict path)
// ===========================================================================
//
// The parallel B&B plan (the development design notes
// plan.md) needs owned per-worker `FloatLp` clones. `NodeLpProbe` exposes the
// minimum surface `tests/parallel_ready.rs` needs to test COLD, independent node
// relaxations on owned clones. It deliberately does not model the production
// tree's warm bases, dynamic cut slots, or scheduling policy, so this is a
// feasibility guard rather than a proof of production parallel readiness. It is
// never called by `solve_milp`, `solve_milp_in`, the node driver, the cut loop,
// or the simplex hot loop, so it is dead code on every serial solve. The bound
// recipe below is `probe_child_full` (safe f64) + `exact_bound` (exact rational)
// verbatim — the two verdict-affecting per-node quantities.

/// The rigorous lower bounds of ONE node relaxation, as computed by
/// [`NodeLpProbe::solve_node_bound`]. `safe` and `exact` are the quantities the
/// cold-clone probe compares byte-for-byte across owned per-worker clones.
pub struct NodeBound {
    /// Neumaier–Shcherbina safe f64 lower bound (`safe_bound`): `+INFINITY` on a
    /// Farkas-proven-empty child, `None` when the box is open where the duals
    /// need it closed (no finite bound — the node cannot be pruned).
    pub safe: Option<f64>,
    /// The EXACT rational lower bound (`exact_bound`) on the snapped duals — the
    /// load-bearing quantity: it must be identical across a clone.
    pub exact: Option<BigRational>,
    /// `true` iff the relaxation LP priced out `Optimal`.
    pub optimal: bool,
    /// `true` iff the relaxation's box was proven empty (`PrimalInfeasible`).
    pub infeasible: bool,
}

/// A cloneable ROOT-relaxation LP engine — the Stage-0 parallel PoC handle.
///
/// `#[derive(Clone)]` delegates to `FloatLp::clone()`. Its custom cache wrappers
/// (`lu_cache`, `sx_cache`, `dse_cache`, and `probe_reuse`) clone empty, while
/// scalar `Cell` policy state is copied by value; none of that mutable state is
/// shared between clones. The `RefCell`/`Cell` interiors make `FloatLp` `!Sync`
/// (a `&FloatLp` cannot be shared) but leave it `Send` (an owned clone can be
/// moved into a thread): the property this cold-clone probe exercises.
#[derive(Clone)]
pub struct NodeLpProbe {
    pub(super) lp: FloatLp,
}

impl NodeLpProbe {
    /// Build a cold root-relaxation LP with the serial search's objective, sense,
    /// and classic cold-simplex policy. This intentionally omits presolve, root
    /// cuts, dynamic cut slots, and warm tree bases. `None` when the model cannot
    /// be lowered (zero columns or a NaN datum).
    pub fn from_model(model: &Model) -> Option<Self> {
        let objective: Vec<(u32, f64)> = (0..model.num_cols())
            .map(|j| (j as u32, model.obj_coeff(Col(j as u32))))
            .filter(|&(_, a)| a != 0.0)
            .collect();
        let mut lp = FloatLp::from_model(model, &objective, model.sense())?;
        lp.plain_cold = true;
        Some(Self { lp })
    }

    /// Structural column count `n` (excludes logicals).
    pub fn num_cols(&self) -> usize {
        self.lp.n
    }

    /// The root box `(lower, upper)` over ALL columns (structural then logical),
    /// so a caller can name structural-column fixings relative to it.
    pub fn root_box(&self) -> (Vec<f64>, Vec<f64>) {
        (self.lp.lower.clone(), self.lp.upper.clone())
    }

    /// A deterministic estimate of this engine's heap footprint (the per-worker
    /// clone cost the plan flags for wide instances). See `FloatLp::approx_bytes`.
    pub fn approx_bytes(&self) -> usize {
        self.lp.approx_bytes()
    }

    /// Solve the node relaxation on the box `root ⊕ fixings` — each
    /// `(j, lo, up)` overrides STRUCTURAL column `j`'s bounds — COLD (no warm
    /// basis), and return its rigorous safe + exact lower bounds. Mutates only
    /// THIS engine's own per-clone caches; that isolation is the property the
    /// PoC validates. The bound recipe is `probe_child_full` + `exact_bound`.
    pub fn solve_node_bound(
        &mut self,
        fixings: &[(usize, f64, f64)],
        deadline: Option<Instant>,
    ) -> NodeBound {
        let mut lower = self.lp.lower.clone();
        let mut upper = self.lp.upper.clone();
        for &(j, lo, up) in fixings {
            if j < self.lp.n {
                lower[j] = lo;
                upper[j] = up;
            }
        }
        let cand = self.lp.solve_bounded(&lower, &upper, None, deadline);
        let mut rc = vec![(0.0f64, 0.0f64); self.lp.n];
        let (safe, infeasible) = match cand.status {
            SimplexStatus::PrimalInfeasible => (Some(f64::INFINITY), true),
            SimplexStatus::Optimal => (
                safe_bound(&self.lp, &cand.duals, &lower, &upper, &mut rc),
                false,
            ),
            _ => (None, false),
        };
        let exact = exact_bound(&self.lp, &cand.duals, &lower, &upper);
        NodeBound {
            safe,
            exact,
            optimal: cand.status == SimplexStatus::Optimal,
            infeasible,
        }
    }
}
