// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! STRUCTURAL ELIMINATION: delete fixed columns and redundant rows.
//!
//! The rest of `presolve` only ever TIGHTENS — a bound moves, a coefficient is
//! rewritten — and never changes a model's row/column identity. This pass is
//! the exception in the same sense `substitute_singletons` is: it removes rows
//! and columns and therefore ships an explicit postsolve map.
//!
//! # What it removes, and why each removal preserves the optimum exactly
//!
//! Let `B*` be the bound-propagation fixpoint the shipped presolve emits
//! ([`super::tighten_bounds_opt`] with coefficient tightening OFF, so no row
//! coefficient changes and every kept row is the caller's row verbatim). `B*`
//! is IMPLIED by the caller's model, so `M = (R, B)` and `(R, B*)` have the
//! same feasible set.
//!
//! **Fixed column.** A column with `lb == ub == v` takes exactly one value in
//! every feasible point. Delete it, subtract `a_rj · v` from both sides of every
//! row it appears in, and add `c_j · v` to the reported objective. The map
//! `x ↦ (x restricted to survivors)` is a bijection between the feasible sets
//! that preserves the objective, so the optima are EQUAL.
//!
//! **Redundant row.** After the fixed columns are folded away, row `r` reads
//! `lb' ≤ Σ_{survivors} a_j x_j ≤ ub'`. If the survivors' declared boxes already
//! force the activity into `[lb', ub']`, then every point of `(R \ {r}, B*)`
//! satisfies `r`, so dropping it changes nothing:
//!
//! * `M ⊆ M'`: an `M`-feasible point satisfies every row and `B`, hence `B*`
//!   (propagation is valid), hence lies in `M' = (R \ {r}, B*)`.
//! * `M' ⊆ M`: a point of `M'` satisfies `B*`, and `B*` alone implies `r`; and
//!   `B*` implies `B`. So it lies in `M`.
//!
//! The second direction is the one that needs care, and it is why the reduced
//! model MUST carry `B*` and not the caller's looser box `B`: the redundancy
//! was established under `B*`, which was itself derived using row `r`. Emitting
//! `B` and dropping `r` would be circular and WRONG. (It is free to emit `B*`
//! anyway: `solve_milp_in` propagates to the same fixpoint on entry.)
//!
//! **Empty row.** A row all of whose columns were fixed is a constant; it is
//! either satisfied (drop it) or violated (the whole model is infeasible, and
//! this pass DECLINES rather than claim it — the caller's own presolve says so
//! with its own evidence).
//!
//! # Fail-closed obligations
//!
//! * inexact-coefficient or inexact-objective models are declined wholesale
//!   (`has_inexact_coeffs`, `has_inexact_objective_coeffs`), as `presolve.rs`
//!   does, because the reasoning reads the `f64` matrix as the truth;
//! * a model carrying a margin row is declined, as `binary_complement` does;
//! * every number written into the reduced model — the shifted row bounds
//!   above all — must come back from [`super::as_exact_f64`] as `Some`. A row
//!   whose shift is not exactly representable UN-FIXES every fixed column in it
//!   (a fixpoint, monotone downward, so it terminates), rather than declining
//!   the whole pass. An un-fixed column is simply kept: its bounds still pin it,
//!   so nothing is lost but the size reduction.
//! * `const_delta` rides an exact `BigRational` and is added at expansion time,
//!   never through the reduced model's `f64` objective offset — it need not be
//!   representable.
//!
//! # What it deliberately does NOT do
//!
//! No [`crate::cert_lift::ReducedFrame`]. The pass eliminates INTEGRAL columns
//! and re-boxes the survivors onto `B*`, so a reduced branching decision is not
//! a caller branching decision at the same integer cut. Tree certificates are
//! dropped and bought back by `harvest_tree_cert_by_resolve`.
//!
//! # MEASURED RESULT — NEGATIVE. This is why it is an arm, not a default.
//!
//! It was built to close the root-bound gap the 2026-08-04 campaign report
//! attributed to missing structural presolve. It cannot, and the reason is
//! structural rather than empirical: **a row the box already implies and a
//! column already pinned to a point each contribute exactly nothing to the LP
//! bound, so deleting them cannot move it.** Measured on `gen`, where the pass
//! removes 138 of 780 rows and 37 of 870 columns — the largest reduction on the
//! corpus — the pre-cut root bound differs between the two arms by exactly the
//! folded constant (53517.237241 vs 29286.585071, difference 24230.65217, which
//! is `const_delta` in the engine's scaled MIN frame). Zero bound movement.
//! Post-cut the two arms diverge by 1.2 against an integrality gap in the tens
//! of thousands, in both directions across instances — that is the cut loop
//! seeing a different matrix, not a stronger relaxation.
//!
//! What is left is THROUGHPUT, and the corpus does not pay for it either. Under
//! the mandated seeded control (`--emit-witness` then `--seed-solution`, both
//! arms handed the optimum, medians of interleaved runs) the node counts are
//! IDENTICAL on every instance where the pass fires — gt2 7/7, qnet1 1467/1467,
//! blend2 3824/3824, gen 9/9, dcmulti 765/765, khb05250 15/15, p0201 162/162 —
//! so the pass changes no search decision at all, and the wall difference is
//! pure per-node cost:
//!
//! ```text
//!               model             seeded OFF   seeded ON     delta
//!   gen         780r/870c -> 642r/833c   0.999s     0.825s    -0.174
//!   dcmulti     290r      -> 272r        1.499s     1.301s    -0.198
//!   blend2      274r/353c -> 186r/336c   0.983s     0.971s    -0.012
//!   khb05250    1350c     -> 1300c       0.707s     0.704s    -0.003
//!   gt2         29r       -> 28r         0.170s     0.175s    +0.005
//!   p0201       201c      -> 195c        1.138s     1.227s    +0.089
//!   qnet1       503r      -> 502r        5.923s     6.430s    +0.507  (2 reps, stable ratio)
//!   TOTAL WALL                          11.419s    11.633s    +0.214  WORSE
//! ```
//!
//! Note blend2: a 32% ROW REDUCTION buys 1.2% of wall. Row count is not what
//! this solver's time is denominated in.
//!
//! The UNSEEDED distribution looks like a 0.47s win (gt2 1.951 -> 0.389 at
//! 56670 -> 11010 nodes). It is not one: seeded, gt2 is 7 nodes in BOTH arms.
//! That entire swing was which incumbent the primal heuristic stumbled on, and
//! it is the fourth time this campaign has had to kill a claim that way.
//!
//! # WHERE THE SIZE PRIZE ACTUALLY IS, since this pass is not it
//!
//! Running AY on GUROBI's presolved qnet1 (503r/1541c -> 360r/1417c) is the
//! positive control for "would elimination pay", and it decomposes as follows —
//! interleaved, 2 reps, on a loaded box, so read the RATIOS not the absolutes:
//!
//! ```text
//!                    total     root work   nodes   ms per tree node
//!   qnet1 raw        13.6-15.7s  3.4-4.3s   850-874   11.9-13.1
//!   qnet1 Gurobi-pre  5.1-6.3s   1.3-1.5s   486        8.0-10.0
//! ```
//!
//! ~1.8x of the gap is a SMALLER TREE, ~1.4x is cheaper nodes, ~2.8x is cheaper
//! root work. The cheaper part comes from Gurobi SUBSTITUTING 124 columns out,
//! not from deleting what was already implied — and AY computes that same
//! 124-column reduction today and declines it (`bab.rs`, the
//! `has_inexact_objective_coeffs` branch, where the measurement is written up).
//!
//! The general lesson this pass paid for: **a reduction that removes only what
//! the LP could already derive removes no information, and therefore buys no
//! bound and — measurably — no wall.** The reductions that pay are the ones that
//! change what the relaxation can see.
//!
//! `markshare2` is excluded from the table as unmeasurable, not as neutral: its
//! seeded wall was 8.275/9.490 in one rep and 5.171/4.815 in the next — the
//! sign flips. The pass removes 7 of its 74 columns, which changes what the
//! lattice device downstream sees, and that lane's wall is not stable enough to
//! carry a claim either way.

use num_rational::BigRational;
use num_traits::Zero;

use crate::model::Col;

mod eliminate;
pub(crate) use eliminate::eliminate_structure;

#[cfg(test)]
mod tests;

/// One eliminated column: it was fixed, so its recovered value is a constant.
pub(crate) struct FixedRecovery {
    /// Original column index.
    pub(crate) col: usize,
    /// The value both of its bounds held.
    pub(crate) value: BigRational,
}

/// How to lift a solution of the structurally-reduced model back to the
/// caller's column space, and how to correct a reported objective value.
pub(crate) struct StructurePostsolve {
    pub(crate) n_orig: usize,
    /// Original column -> reduced column, `None` when eliminated.
    pub(crate) map: Vec<Option<Col>>,
    /// One entry per eliminated (fixed) column.
    pub(crate) recover: Vec<FixedRecovery>,
    /// Per REDUCED row, in emission order: which ORIGINAL row it is. Written in
    /// lockstep with `add_row`, never re-derived (see `presolve.rs:1939` for the
    /// bug that convention exists to prevent).
    ///
    /// NOTHING READS THIS YET, and it is kept deliberately rather than deleted.
    /// It is the row-frame record a certificate lift needs, and it can only be
    /// built correctly HERE, at emission time — re-deriving it later from the
    /// fate vector is exactly the drift `presolve.rs` documents. A lift added
    /// later must not have to re-introduce it.
    pub(crate) row_origin: Vec<usize>,
    /// The eliminated columns' folded objective contribution.
    pub(crate) const_delta: BigRational,
}

impl StructurePostsolve {
    pub(crate) fn const_delta(&self) -> &BigRational {
        &self.const_delta
    }

    /// Widen a reduced point to the caller's full column space.
    ///
    /// A single forward pass suffices and there is no dependency order to get
    /// wrong: every recovery is a CONSTANT, not a function of other columns.
    pub(crate) fn widen(&self, reduced: &[BigRational]) -> Vec<BigRational> {
        let mut full = vec![BigRational::zero(); self.n_orig];
        for (orig, slot) in self.map.iter().enumerate() {
            if let Some(nc) = slot {
                if let Some(v) = reduced.get(nc.index()) {
                    full[orig] = v.clone();
                }
            }
        }
        for rec in &self.recover {
            full[rec.col] = rec.value.clone();
        }
        full
    }
}

/// Cached trace predicate; see the live-read ratchet in `tests/env_ledger.rs`.
fn trace_enabled() -> bool {
    static ENABLED: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *ENABLED.get_or_init(|| crate::debug_flags::milp_debug_flags().trace)
}

/// Force this module's cached env accessor at solve entry, so a consumer that
/// rewrites its environment between window solves cannot race it. Called from
/// `bab::prime_env_all`.
pub(crate) fn prime_env() {
    let _ = trace_enabled();
}

/// Whether the pass is armed. DEFAULT OFF: measured net-negative on the corpus
/// under the seeded control (see the module header's MEASURED RESULT note), so
/// the shipped trajectory stays byte-identical and this stays an A/B arm.
///
/// DELIBERATELY NOT CACHED. It is an arm selector, and `tests/env_ledger.rs`
/// records why every arm selector must be a live read: a `OnceLock` latches the
/// first value a process sees, and a sweep whose second arm silently re-runs the
/// first records the wrong result as a finding.
pub(crate) fn struct_elim_enabled() -> bool {
    crate::tune::caller_flag(crate::tune::Knob::StructElim) == Some(true)
}
