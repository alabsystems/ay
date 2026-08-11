// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! DUAL FIXING BY LOCK COUNTING — the one reduction in this crate that is
//! allowed to cut off feasible points.
//!
//! # What it is
//!
//! For a column `j`, count over the rows that are still ALIVE how many of them
//! could be violated by moving `x_j` up (`uplocks`) and how many by moving it
//! down (`downlocks`). If nothing can be broken by pushing the column to one of
//! its own bounds, and the objective does not object, then push it there and
//! FIX it:
//!
//! ```text
//! c_j >= 0  and  downlocks[j] == 0  and  l_j finite   ->   x_j := l_j
//! c_j <= 0  and  uplocks[j]   == 0  and  u_j finite   ->   x_j := u_j
//! ```
//!
//! (Coefficients are read in the MINIMIZE frame; a `Maximize` model negates the
//! objective test.) This is SCIP's `dualfix` presolver / Achterberg–Bixby–Gu–
//! Rothberg–Weninger's "dual reductions" §4, and it is the single knob behind
//! Gurobi's `DualReductions` parameter on the ny W1 workload.
//!
//! # ⚠ WHY THIS MODULE IS NOT IN `presolve.rs`
//!
//! `presolve.rs`'s charter is stated in its own header: *"a derived bound that
//! is a hair too tight cuts off a feasible point, and if that point was the
//! optimum the solver now lies"*. Everything in that module is an IMPLIED
//! bound — it cuts off nothing.
//!
//! **This reduction cuts off feasible points on purpose.** It is not a valid
//! inequality; it is a WLOG argument. Measured on the ny W1 family: taking a
//! fixed binary `z_j := t` on a SAT instance and re-solving the ORIGINAL model
//! with `z_j := 1 - t` forced comes back SAT for 30 of 32 probes. Those points
//! exist in the caller's model and are gone from the reduced one. That is not a
//! bug in the rule — it is the rule.
//!
//! So it lives in its own module, with its own kill switch, and the call site
//! (`bab::expand_dualfix_outcome`) keeps the verdict, re-checks the witness
//! against the CALLER's model, and hands every certificate to the real verifier
//! against the CALLER's model before letting it out — which a proof that leaned
//! on a dual-fixed bound cannot survive. Declining evidence is the expected
//! outcome of that seal, not an error path.
//!
//! What the seal declines is then bought back rather than written off. On an
//! `Infeasible` verdict whose reduced-frame tree capture SURVIVED — a measured
//! statement that the refutation fits the caller's leaf budget — the call site
//! re-solves the caller's own model once and harvests THAT tree
//! (`bab::harvest_tree_cert_by_resolve`, the same decoupling commit `578b9c23a`
//! shipped for the kernel reformulation and duplicate-column dedup). Where the
//! capture had already poisoned, no tree exists to harvest in either frame and
//! the re-solve is declined instead of burning the reduction's whole gain to
//! return `None`. Measured effect on the ny W1 UNSAT captures: every instance
//! that carries an exit-0 certificate without this reduction still carries one
//! with it.
//!
//! # What it preserves, exactly
//!
//! Let `S` be the feasible set of the model as it stands at the start of a
//! round and `S'` the set after one fixing `x_j := l_j` (the down case; the up
//! case mirrors). Take any `x` in `S` and let `x'` be `x` with `x'_j := l_j`.
//!
//! * **Alive rows.** `downlocks[j] == 0` says every alive row containing `j`
//!   has, on the side that decreasing `x_j` moves toward, no finite bound at
//!   all. Still satisfied.
//! * **Deleted rows.** A row is deleted only when it is satisfied at EVERY
//!   point of the current box, and `x'` is in that box. Still satisfied.
//! * **Bounds / integrality.** `l_j <= l_j <= u_j`, and `l_j` is an integer
//!   (this module fixes integer columns at integer values only, see below).
//! * **Objective.** `c_j >= 0` and `x'_j <= x_j`, so `c·x' <= c·x`.
//!
//! Hence `S != {}  =>  S' != {}`, and `S' ⊆ S` gives the converse, so:
//!
//! | quantity | preserved? |
//! |---|---|
//! | SAT / UNSAT | YES, both directions |
//! | the optimal VALUE | YES (`inf S' == inf S`, including `-inf`) |
//! | a reduced-frame WITNESS, read in the caller's frame | YES, verbatim — `S' ⊆ S` |
//! | the feasible SET | **NO** |
//! | the optimal FACE / solution count / "a second solution" | **NO** |
//! | duals, reduced costs, Farkas multipliers, sensitivity | **NO** |
//! | a caller-supplied point checked against the reduced model | **NO** — never do this |
//!
//! # The INFEASIBLE-or-UNBOUNDED hazard, and why it cannot fire here
//!
//! `DualReductions=0` exists in Gurobi because these reductions can make
//! infeasible and unbounded indistinguishable. The mechanism is fixing at an
//! INFINITE bound: `c_j < 0`, `u_j = +inf`, no up-lock — the model is
//! unbounded-if-feasible, and a solver that "fixes" and answers INFEASIBLE has
//! conflated the two. [`dual_fix`] DECLINES whenever the target bound is
//! infinite, so the map `x -> x'` is always into the model's own box and the
//! equality `inf S' == inf S` holds with both sides possibly `-inf`. Unbounded
//! therefore transfers too.
//!
//! # Denominators
//!
//! This reduction creates NO new rational value. It copies one of a column's
//! own bounds onto the other side of the same column: no coefficient is
//! rewritten, no row is scaled, no pivot is taken, nothing is substituted or
//! aggregated. The model's rational data is byte-identical afterwards; exactly
//! two `f64` bound slots move per fixing.
//!
//! That is the structural reason it is safe on the ny W1 family, whose
//! constants carry float32 ULP fuzz (`-1.401298464324817e-45` = `-2^-149`,
//! `1.00000011920928955078125` = `1 + 2^-23`) with ~150-bit denominators.
//! Consuming another solver's PRESOLVED model on that family collapses this
//! crate's exact lane to 4.4 nodes/sec, because that presolve MULTIPLIES the
//! fuzzed constants together. This rule never multiplies two of them.
//!
//! It is belt-and-braces anyway: [`integral_f64`] refuses any target that is
//! not an integer exactly representable in `f64`, so the denominator bit-length
//! of every value this module writes is 1, by construction and not by luck.
//!
//! # Why the FIXPOINT is the deliverable, not the rule
//!
//! Applying the lock test to the raw ny matrix fires ZERO times: every binary
//! sits in two `<=` rows with opposite-signed coefficients and is two-sided as
//! read. The payload comes from the interleave:
//!
//! 1. exact bound propagation to fixpoint ([`crate::presolve::propagate`]),
//! 2. delete rows that have become REDUNDANT given the propagated box,
//! 3. recount locks over the survivors,
//! 4. fix, and go back to 1.
//!
//! On `W1_unsat_v30_c38` the clause neurons' post-activation `y` is forced to 0
//! by the specification rows, which makes `y - U z <= 0` redundant, which kills
//! `z`'s only down-lock. Step 2 is what makes step 4 bite; with it removed the
//! full loop still fires zero times.

use std::time::Instant;

use ay_lra::rational::Rational;
use num_traits::Zero;

use crate::model::{exact_small, Col, Model, Row, Sense};

/// How many outer (propagate, delete, count, fix) rounds to run.
///
/// Converges in 2 on every ny W1 instance measured; the cap is a budget guard,
/// and stopping early is always sound — it only forgoes fixings.
const MAX_ROUNDS: u32 = 8;

/// One dual fixing, recorded for postsolve, diagnostics and the certificate
/// frame.
#[derive(Debug, Clone, Copy, PartialEq)]
pub(crate) struct Fixing {
    /// The column index (`Col::index`).
    pub(crate) col: u32,
    /// `true` when the column was raised to its (propagated) UPPER bound —
    /// i.e. the LOWER side is the one the reduction tightened. `false` for the
    /// mirror case.
    pub(crate) to_upper: bool,
    /// The value fixed at. Always an integer exactly representable in `f64`.
    pub(crate) value: f64,
    /// Which round it fired in (0-based), for reading the cascade.
    pub(crate) round: u32,
}

/// What one [`dual_fix`] pass did.
#[derive(Debug, Clone, Default)]
pub(crate) struct DualFixLog {
    /// Every fixing applied, in the order they fired.
    pub(crate) fixings: Vec<Fixing>,
    /// Outer rounds actually run.
    pub(crate) rounds: u32,
    /// Integer columns whose box holds >= 2 values in the CALLER's model.
    pub(crate) free_ints_before: usize,
    /// Integer columns whose box still holds >= 2 values after propagation AND
    /// dual fixing — the number the `DualReductions` ablation compares.
    pub(crate) free_ints_after: usize,
    /// Integer columns still free after propagation ALONE (no fixing). The
    /// `DualReductions=0` arm, computed on the same pass so the attribution is
    /// a measurement rather than a second run.
    pub(crate) free_ints_prop_only: usize,
    /// Largest denominator bit-length written by this pass. 1 by construction
    /// (every target is an integer); reported so a future widening of
    /// [`integral_f64`] cannot silently break the guarantee.
    pub(crate) max_den_bits: u32,
}

/// An exact rational that is an integer `f64` can hold without rounding.
///
/// This is the DENOMINATOR GUARD and the `f64`-representability guard in one.
/// `Model` stores bounds as `f64`, so a target that is not exactly an `f64`
/// could only be written ROUNDED — and rounding a dual fixing in the wrong
/// direction would cut off the very point the WLOG argument promised to keep.
/// Refusing is free on the measured workload (every ny W1 target is 0 or 1) and
/// keeps the written denominator bit-length pinned at 1.
fn integral_f64(v: &Rational) -> Option<f64> {
    let i = v.to_i64()?;
    // Beyond 2^53 consecutive integers are no longer all `f64`-representable.
    if i.unsigned_abs() > (1u64 << 53) {
        return None;
    }
    #[allow(clippy::cast_precision_loss)]
    Some(i as f64)
}

/// Run dual fixing to fixpoint on `model`.
///
/// Returns `None` — meaning the caller's model is handed on BYTE-IDENTICAL —
/// whenever the pass is switched off, declines, or fixes nothing. Otherwise
/// returns a model that differs from `model` in COLUMN BOUNDS ONLY (each fixed
/// column's two bounds set to the same integer) plus the log of what it did.
///
/// The returned model is NOT equivalent to the caller's: see the module header.
/// Its verdict, its optimal value and its witnesses transfer; its evidence does
/// not.
pub(crate) fn dual_fix(model: &Model, deadline: Option<Instant>) -> Option<(Model, DualFixLog)> {
    // KILL SWITCH. `AY_MILP_NO_DUALFIX=1` restores the prior behaviour
    // byte-identically: this is the only entry point and it returns `None`.
    if crate::tune::on(crate::tune::Knob::NoDualfix) {
        return None;
    }
    // FAIL-CLOSED for inexact models, for the same reason
    // `presolve::tighten_bounds_opt` does: the propagation this rule sits on
    // reads the row `f64`s, and on a model whose true coefficients are rounded
    // proxies that reasoning is over the WRONG matrix. The lock SIGNS would be
    // read off the same rounded proxies.
    if model.has_inexact_coeffs() {
        return None;
    }
    // ⚠ THE MARGIN REFRAME IS A DIFFERENT QUESTION.
    //
    // `Model::mark_margin_row` turns an objective-≡0 FEASIBILITY model into a
    // margin OPTIMIZATION over the model MINUS that row. This reduction
    // preserves "is the whole system feasible"; it does NOT preserve
    // `max a·x  s.t. the other rows`, which is what the reframe then computes
    // and compares against the margin threshold. Counting locks WITH the margin
    // row present and then answering a question posed WITHOUT it is exactly the
    // shape of a silent wrong verdict. Decline.
    if model.margin_row().is_some() {
        return None;
    }
    let n = model.num_cols();
    let m = model.num_rows();
    if n == 0 || m == 0 {
        return None;
    }
    let integral: Vec<bool> = (0..n)
        .map(|j| model.col_kind(Col(j as u32)).is_integral())
        .collect();
    // The fixing guard below admits INTEGER columns only (see `integral_f64`),
    // so a continuous model can only ever fix nothing.
    if !integral.iter().any(|&b| b) {
        return None;
    }

    // Exact-rational working box. `None` on a side means OPEN, matching
    // `presolve::propagate`'s workspace convention.
    let mut lo: Vec<Option<Rational>> = Vec::with_capacity(n);
    let mut up: Vec<Option<Rational>> = Vec::with_capacity(n);
    for j in 0..n {
        let (l, u) = model.col_bounds(Col(j as u32));
        lo.push(exact_small(l));
        up.push(exact_small(u));
    }

    // Objective coefficients read in the MINIMIZE frame, so the sign tests
    // below are written once. `Maximize` negates.
    let minimize = model.sense() == Sense::Minimize;
    let cmin = |j: usize| -> f64 {
        let c = model.obj_coeff(Col(j as u32));
        if minimize {
            c
        } else {
            -c
        }
    };

    let free_ints_before = (0..n)
        .filter(|&j| {
            integral[j] && {
                let (l, u) = model.col_bounds(Col(j as u32));
                l.ceil() < u.floor()
            }
        })
        .count();

    let mut fixings: Vec<Fixing> = Vec::new();
    let mut rounds = 0u32;
    let mut free_ints_prop_only = free_ints_before;
    let expired = || deadline.is_some_and(|d| Instant::now() >= d);

    for round in 0..MAX_ROUNDS {
        if expired() {
            break;
        }
        // (1) EXACT BOUND PROPAGATION TO FIXPOINT.
        //
        // Reused verbatim from `presolve` rather than reimplemented: this is
        // the crate's audited exact propagator, with its outward rounding, its
        // integer floor/ceil and its at-most-one-infinite-contributor handling
        // already right. (Two independent reimplementations of this loop hit
        // the same silent bug — a row activity reused across the two branches
        // of an equality row derives INVALID, too-tight bounds — which is a
        // good reason not to write a third.)
        //
        // It is run into a COPY of the box: a `false` return leaves the
        // workspace half-updated, and the only state this pass is allowed to
        // keep in that case is what earlier rounds already proved.
        let mut plo = lo.clone();
        let mut pup = up.clone();
        if !crate::presolve::propagate(model, deadline, None, &integral, &mut plo, &mut pup, false)
        {
            // The box is empty. That is a sound INFEASIBLE — round 1 proves it
            // of the caller's own model, and a later round proves it of a
            // restriction that is nonempty only if the caller's is. But this
            // pass does not adjudicate verdicts: it stops, and ships whatever
            // earlier rounds fixed. The search (whose own root presolve runs
            // the identical propagation) reaches the same conclusion with its
            // certificate machinery armed.
            break;
        }
        lo = plo;
        up = pup;
        rounds = round + 1;
        if round == 0 {
            // THE `DualReductions=0` ARM, measured on this very pass: what
            // propagation ALONE leaves. Recorded before any fixing has fired.
            free_ints_prop_only = (0..n)
                .filter(|&j| integral[j] && !is_fixed(&lo[j], &up[j]))
                .count();
        }

        // (2) DELETE REDUNDANT ROWS and (3) RECOUNT LOCKS, in one pass over the
        // matrix. A row is REDUNDANT when it is satisfied at every point of the
        // current box — both its sides slack, or absent. Deletion is monotone
        // across rounds because the box only ever tightens, so a row deleted in
        // round k is still redundant in round k+1; it is recomputed anyway
        // because that costs one pass and assumes nothing.
        let mut uplocks = vec![0u32; n];
        let mut downlocks = vec![0u32; n];
        // ⚠ THE LOCK COUNT IS ONLY MEANINGFUL WHEN IT IS COMPLETE. Every other
        // budget cut in this pass is sound because it only WEAKENS the reduction
        // (a shorter propagation derives looser bounds, which deletes fewer rows,
        // which leaves more locks, which fixes less). This one is the opposite: a
        // sweep that stops at row 3,000 of 5,000 has seen fewer locks than exist,
        // and a column whose only lock lives in an unvisited row would look free.
        // That is a WRONG FIXING, not a missed one. So a truncated sweep
        // abandons the whole round rather than fixing off a partial count.
        let mut counted_every_row = true;
        for i in 0..m {
            if i % 256 == 0 && expired() {
                counted_every_row = false;
                break;
            }
            let (coeffs, rlb, rub) = model.row(Row(i as u32));
            let (rlb, rub) = (exact_small(rlb), exact_small(rub));
            if rlb.is_none() && rub.is_none() {
                continue; // free row: locks nothing, ever
            }
            let mut min_act = Rational::new(0, 1);
            let mut max_act = Rational::new(0, 1);
            let (mut min_inf, mut max_inf) = (0usize, 0usize);
            for &(c, a) in coeffs {
                let j = c as usize;
                let a = exact_small(a).expect("row coefficient is finite");
                if a.is_zero() {
                    continue;
                }
                let (at_min, at_max) = if a.is_positive() {
                    (&lo[j], &up[j])
                } else {
                    (&up[j], &lo[j])
                };
                match at_min {
                    Some(b) => min_act += a.clone() * b,
                    None => min_inf += 1,
                }
                match at_max {
                    Some(b) => max_act += a.clone() * b,
                    None => max_inf += 1,
                }
            }
            // An OPEN activity is not slack: `max_inf > 0` means the row's
            // upper side can be reached from inside the box, so it stays alive.
            let ub_slack = match &rub {
                None => true,
                Some(u) => max_inf == 0 && max_act <= *u,
            };
            let lb_slack = match &rlb {
                None => true,
                Some(l) => min_inf == 0 && min_act >= *l,
            };
            if ub_slack && lb_slack {
                continue; // DEAD: contributes no lock to anything
            }
            for &(c, a) in coeffs {
                let j = c as usize;
                let a = exact_small(a).expect("row coefficient is finite");
                if a.is_zero() {
                    continue;
                }
                // A column already pinned to a point imposes no lock on itself.
                if is_fixed(&lo[j], &up[j]) {
                    continue;
                }
                // Raising x_j raises this row's activity exactly when a_ij > 0,
                // so it can only ever violate a FINITE UPPER row bound; lowering
                // it can only ever violate a finite LOWER one. Both flip with the
                // coefficient's sign. An equality (or two-sided range) row has
                // both sides finite and therefore locks EVERY column it contains
                // in BOTH directions — which is also what makes the smt lane's
                // `>=`/`<=` PAIR lowering safe here with no special case, since a
                // column with the same-sign coefficient in both twins collects
                // one lock from each.
                let pos = a.is_positive();
                if rub.is_some() {
                    if pos {
                        uplocks[j] += 1;
                    } else {
                        downlocks[j] += 1;
                    }
                }
                if rlb.is_some() {
                    if pos {
                        downlocks[j] += 1;
                    } else {
                        uplocks[j] += 1;
                    }
                }
            }
        }

        // (4) FIX — only against a COMPLETE lock count; see above.
        if !counted_every_row {
            break;
        }
        let mut fired = 0usize;
        for j in 0..n {
            // GUARD: integer columns only. Measured cost on the ny W1 family:
            // zero (no continuous column is ever eligible there). What it buys
            // is that the written value is an integer, which is what makes the
            // `f64` write exact and the denominator guarantee structural. A
            // continuous column would be fixed at a PROPAGATION-DERIVED bound
            // — an arbitrary rational, on this family up to 150 denominator
            // bits — and that is the value a substituting implementation would
            // start compounding.
            if !integral[j] {
                continue;
            }
            if is_fixed(&lo[j], &up[j]) {
                continue;
            }
            let c = cmin(j);
            // Prefer the DOWN case when both apply (they both do under the
            // zero objective this workload has); the choice is arbitrary and
            // only has to be deterministic.
            let mut chosen: Option<(Rational, bool)> = None;
            if c >= 0.0 && downlocks[j] == 0 {
                // GUARD: never fire on an infinite target bound. This is
                // precisely Gurobi's INFEASIBLE-or-UNBOUNDED hazard; see the
                // module header.
                if let Some(v) = &lo[j] {
                    chosen = Some((v.clone(), false));
                }
            }
            if chosen.is_none() && c <= 0.0 && uplocks[j] == 0 {
                if let Some(v) = &up[j] {
                    chosen = Some((v.clone(), true));
                }
            }
            let Some((v, to_upper)) = chosen else {
                continue;
            };
            let Some(vf) = integral_f64(&v) else {
                continue;
            };
            // DEFENSIVE: the value must lie inside the box the caller declared.
            // Propagation only tightens, so this cannot fail — which is exactly
            // why it is cheap to assert rather than assume. A fixing outside the
            // caller's box would be a restriction the WLOG argument never made.
            let (l0, u0) = model.col_bounds(Col(j as u32));
            if !(l0 <= vf && vf <= u0) {
                continue;
            }
            if to_upper {
                lo[j] = Some(v);
            } else {
                up[j] = Some(v);
            }
            fixings.push(Fixing {
                col: j as u32,
                to_upper,
                value: vf,
                round,
            });
            fired += 1;
        }
        if fired == 0 {
            break;
        }
    }

    if fixings.is_empty() {
        return None;
    }

    // PIN THE BOUND; DO NOT SUBSTITUTE. Nothing but two `f64` slots per fixing
    // changes, so the reduced model's rational data — every row coefficient,
    // every row bound, the objective — is byte-identical to the caller's. That
    // is what keeps the postsolve trivial (the witness needs no map at all) and
    // the denominator footprint provably empty.
    let mut out = model.clone();
    for f in &fixings {
        out.set_col_bounds(Col(f.col), f.value, f.value);
    }

    let free_ints_after = (0..n)
        .filter(|&j| integral[j] && !is_fixed(&lo[j], &up[j]))
        .count();
    let log = DualFixLog {
        // Every value written is an integer, so the denominator is 1 and its
        // bit-length is 1. Computed, not asserted.
        max_den_bits: fixings
            .iter()
            .map(|f| {
                u32::try_from(
                    crate::model::exact(f.value)
                        .map_or(1u64, |r| r.denom().bits())
                        .max(1),
                )
                .unwrap_or(u32::MAX)
            })
            .max()
            .unwrap_or(1),
        fixings,
        rounds,
        free_ints_before,
        free_ints_after,
        free_ints_prop_only,
    };
    Some((out, log))
}

/// Is this column pinned to a single value?
fn is_fixed(l: &Option<Rational>, u: &Option<Rational>) -> bool {
    matches!((l, u), (Some(l), Some(u)) if l == u)
}

/// One-line census of what dual fixing would do to `model`, for `ay-milp diag
/// dualfix`. Measurement only — it runs the pass and throws the model away.
#[must_use]
pub(crate) fn diag_line(model: &Model, secs: f64) -> String {
    let deadline = Instant::now() + std::time::Duration::from_secs_f64(secs);
    // `gate` is the SHIPPED admission test (`bab::dualfix_gate`'s default arm),
    // reported separately because this diagnostic deliberately runs the rule
    // whether or not production would: `gate=off` says the model never reaches
    // `dual_fix` on default settings, so whatever the rest of the line says is a
    // measurement of the RULE, not of the engine.
    let gate = if model.objective_is_identically_zero() {
        "on"
    } else {
        "off"
    };
    match dual_fix(model, Some(deadline)) {
        None => format!(
            "DUALFIX gate={gate} rows={} cols={} fixings=0 DECLINED",
            model.num_rows(),
            model.num_cols()
        ),
        Some((_, log)) => {
            let to_upper = log.fixings.iter().filter(|f| f.to_upper).count();
            format!(
                "DUALFIX gate={gate} rows={} cols={} int_before={} int_prop_only={} \
                 int_after={} fixings={} to_upper={} to_lower={} rounds={} max_den_bits={}",
                model.num_rows(),
                model.num_cols(),
                log.free_ints_before,
                log.free_ints_prop_only,
                log.free_ints_after,
                log.fixings.len(),
                to_upper,
                log.fixings.len() - to_upper,
                log.rounds,
                log.max_den_bits,
            )
        }
    }
}

/// ADVERSARIAL BRUTE FORCE. Generate small integer models, run the
/// reduction, and enumerate BOTH boxes over the integer lattice to check the
/// two things it promises: the feasible set is nonempty in the reduced model
/// exactly when it is in the original, and the minimum is identical.
///
/// This is the check the repo's own history says is load-bearing: a widened
/// kernel gate once returned a worse-than-true `OPTIMAL`, passed 433 lib
/// tests and a 40-instance corpus run, and was caught only by a random-model
/// campaign. Returns `(models where the rule fired, columns actually
/// pinned)` so the caller can assert the campaign was not vacuous.
pub(crate) fn brute_force_campaign(samples: usize, seed: u64) -> (usize, usize) {
    let mut state = seed;
    let mut rng = move || {
        state ^= state << 13;
        state ^= state >> 7;
        state ^= state << 17;
        state
    };
    let mut fired = 0usize;
    let mut cut_points = 0usize;
    for _ in 0..samples {
        let ncol = 2 + (rng() % 4) as usize; // 2..5 integer columns
        let nrow = 1 + (rng() % 4) as usize; // 1..4 rows
        let mut m = Model::new();
        let mut cols = Vec::new();
        for _ in 0..ncol {
            // A lower bound that is not 0 catches "fixed at the DECLARED
            // bound instead of the PROPAGATED one", which is one of the two
            // silent traps in this rule.
            let lb = (rng() % 3) as f64 - 1.0; // -1..1
            let ub = lb + (rng() % 3) as f64; // width 0..2
            cols.push(m.add_int_col(lb, ub));
        }
        let mut obj = Vec::new();
        for &c in &cols {
            obj.push((c, (rng() % 5) as f64 - 2.0)); // -2..2
        }
        let sense = if rng() % 2 == 0 {
            Sense::Minimize
        } else {
            Sense::Maximize
        };
        m.set_objective(&obj, sense);
        for _ in 0..nrow {
            let mut coeffs = Vec::new();
            for &c in &cols {
                let a = (rng() % 5) as f64 - 2.0;
                if a != 0.0 {
                    coeffs.push((c, a));
                }
            }
            if coeffs.is_empty() {
                coeffs.push((cols[0], 1.0));
            }
            let rhs = (rng() % 7) as f64 - 3.0;
            let (lb, ub) = match rng() % 5 {
                0 => (f64::NEG_INFINITY, rhs),
                1 => (rhs, f64::INFINITY),
                2 => (rhs, rhs),
                3 => (rhs, rhs + (rng() % 3) as f64),
                // A FREE row: it locks nothing and must never be counted.
                _ => (f64::NEG_INFINITY, f64::INFINITY),
            };
            m.add_row(lb, ub, &coeffs);
        }
        let Some((red, log)) = dual_fix(&m, None) else {
            continue;
        };
        fired += 1;

        // Enumerate a model's whole integer box, in the MINIMIZE frame.
        let best = |mm: &Model| -> Option<i64> {
            let mut lows = Vec::new();
            let mut highs = Vec::new();
            for j in 0..ncol {
                let (l, u) = mm.col_bounds(cols[j]);
                lows.push(l as i64);
                highs.push(u as i64);
            }
            let mut idx = lows.clone();
            let mut best: Option<i64> = None;
            loop {
                let ok = (0..mm.num_rows()).all(|i| {
                    let (coeffs, lb, ub) = mm.row(Row(i as u32));
                    let act: i64 = coeffs
                        .iter()
                        .map(|&(c, a)| a as i64 * idx[c as usize])
                        .sum();
                    (lb.is_infinite() || act as f64 >= lb) && (ub.is_infinite() || act as f64 <= ub)
                });
                if ok {
                    let v: i64 = (0..ncol)
                        .map(|j| mm.obj_coeff(cols[j]) as i64 * idx[j])
                        .sum();
                    let v = if sense == Sense::Minimize { v } else { -v };
                    best = Some(best.map_or(v, |b: i64| b.min(v)));
                }
                let mut k = 0;
                loop {
                    if k == ncol {
                        return best;
                    }
                    idx[k] += 1;
                    if idx[k] <= highs[k] {
                        break;
                    }
                    idx[k] = lows[k];
                    k += 1;
                }
            }
        };
        let a = best(&m);
        let b = best(&red);
        assert_eq!(
            a, b,
            "DUAL FIXING CHANGED THE ANSWER.\n  fixings: {:?}\n  original min: {a:?}\n  \
             reduced  min: {b:?}",
            log.fixings
        );
        // The reduction must be a RESTRICTION, and it must really restrict —
        // otherwise the equality above proves nothing about the dangerous
        // case.
        for j in 0..ncol {
            let (l0, u0) = m.col_bounds(cols[j]);
            let (l1, u1) = red.col_bounds(cols[j]);
            assert!(l1 >= l0 && u1 <= u0, "the box must only ever tighten");
            assert!((l1 - u1).abs() < f64::EPSILON || l1 == l0 && u1 == u0);
            if l1 > l0 || u1 < u0 {
                cut_points += 1;
            }
        }
    }
    (fired, cut_points)
}

/// The `brute_force_campaign` at CAMPAIGN size — 300,000 models over 12 seeds.
///
/// This is the arm the dual-fix soundness claim leans on, and it is minutes of
/// brute force, so it is an `examples/` target rather than a `#[test]`. It was
/// previously a `#[test]` carrying `#[ignore]`, which `ay-quality-gate` forbids
/// and which meant it ran nowhere at all. The default-size arm
/// (`randomised_small_models_keep_their_verdict_and_their_optimum`, 6,000
/// models) still asserts the same property on every `cargo test`, so this is a
/// longer run of a checked property, not the only check.
///
/// Panics on a vacuous campaign, exactly as the test did, so a run that stops
/// exercising the rule fails loudly instead of printing a reassuring number.
///
/// Run: `cargo run --release -p ay-milp --example dualfix_campaign`
#[must_use]
pub fn diag_dualfix_campaign_at_scale() -> String {
    let mut fired = 0;
    let mut cut = 0;
    for seed in 0..12u64 {
        let (f, c) = brute_force_campaign(25_000, 0x9E37_79B9_7F4A_7C15 ^ (seed << 13 | 1));
        fired += f;
        cut += c;
    }
    assert!(fired > 30_000, "only {fired} models exercised the rule");
    assert!(cut > 30_000, "only {cut} columns pinned");
    format!("dualfix campaign: 300,000 models, {fired} fired, {cut} columns pinned")
}

#[cfg(test)]
mod tests {
    use super::*;
    use num_rational::BigRational;
    use num_traits::Zero;

    /// Serialise every test that touches the process environment.
    fn env_lock() -> std::sync::MutexGuard<'static, ()> {
        static L: std::sync::Mutex<()> = std::sync::Mutex::new(());
        L.lock().unwrap_or_else(std::sync::PoisonError::into_inner)
    }

    fn fixed_value(log: &DualFixLog, col: usize) -> Option<f64> {
        log.fixings
            .iter()
            .find(|f| f.col as usize == col)
            .map(|f| f.value)
    }

    /// The ny W1 "vestigial binary" shape, in miniature: `z` is a column
    /// SINGLETON with a NEGATIVE coefficient in a `<=` row, so raising it only
    /// ever relaxes the row. No up-lock, therefore `z := ub`.
    ///
    /// Note that no ordinary reduction reaches this: `z = 0` is perfectly
    /// feasible here (take `y = 0`). The fixing cuts that point off.
    #[test]
    fn a_singleton_column_with_no_up_lock_goes_to_its_upper_bound() {
        let _g = env_lock();
        let mut m = Model::new();
        let y = m.add_col(0.0, 1.0);
        let z = m.add_binary_col();
        // y - 5 z <= 0.
        m.add_row(f64::NEG_INFINITY, 0.0, &[(y, 1.0), (z, -5.0)]);
        let (red, log) = dual_fix(&m, None).expect("fires");
        assert_eq!(fixed_value(&log, z.index()), Some(1.0));
        assert_eq!(red.col_bounds(z), (1.0, 1.0));
        assert_eq!(log.max_den_bits, 1);
        // ⚠ THE POINT OF THE WHOLE MODULE: the cut-off point is FEASIBLE in
        // the caller's model. This is a dual reduction, not an implied one.
        let feasible_but_gone = [BigRational::zero(), BigRational::zero()];
        assert!(m.check_point(&feasible_but_gone).is_ok());
        assert!(red.check_point(&feasible_but_gone).is_err());
    }

    /// The mirror: a positive coefficient in a `<=` row is an up-lock and no
    /// down-lock, so the column goes to its LOWER bound.
    #[test]
    fn a_singleton_column_with_no_down_lock_goes_to_its_lower_bound() {
        let _g = env_lock();
        let mut m = Model::new();
        let y = m.add_col(0.0, 1.0);
        let z = m.add_int_col(0.0, 5.0);
        m.add_row(f64::NEG_INFINITY, 3.0, &[(y, 1.0), (z, 1.0)]);
        let (red, log) = dual_fix(&m, None).expect("fires");
        assert_eq!(fixed_value(&log, z.index()), Some(0.0));
        assert_eq!(red.col_bounds(z), (0.0, 0.0));
    }

    /// A column that is locked in BOTH directions survives. This is the ny W1
    /// unstable-ReLU shape: `+M` in one `<=` row and `-U` in another.
    #[test]
    fn a_two_sided_column_is_never_fixed() {
        let _g = env_lock();
        let mut m = Model::new();
        let y = m.add_col(0.0, 1.0);
        let z = m.add_binary_col();
        m.add_row(f64::NEG_INFINITY, 2.0, &[(y, 1.0), (z, 2.0)]);
        m.add_row(f64::NEG_INFINITY, 0.0, &[(y, 1.0), (z, -7.0)]);
        assert!(dual_fix(&m, None).is_none());
    }

    /// AN EQUALITY ROW LOCKS BOTH DIRECTIONS. This is also the smt lane's
    /// shape, where an equality is lowered as a `>=`/`<=` PAIR: a column with
    /// the same-sign coefficient in both twins is blocked in both directions by
    /// the sign test, exactly as the single two-sided row is.
    #[test]
    fn an_equality_row_blocks_both_directions() {
        let _g = env_lock();
        let mut m = Model::new();
        let y = m.add_col(0.0, 10.0);
        let z = m.add_int_col(0.0, 4.0);
        m.add_row(3.0, 3.0, &[(y, 1.0), (z, 1.0)]);
        assert!(dual_fix(&m, None).is_none());

        let mut split = Model::new();
        let y = split.add_col(0.0, 10.0);
        let z = split.add_int_col(0.0, 4.0);
        split.add_row(f64::NEG_INFINITY, 3.0, &[(y, 1.0), (z, 1.0)]);
        split.add_row(3.0, f64::INFINITY, &[(y, 1.0), (z, 1.0)]);
        assert!(dual_fix(&split, None).is_none());
    }

    /// THE HAZARD GUARD: no up-lock, negative cost, but the upper bound is
    /// `+inf`. This is the INFEASIBLE-or-UNBOUNDED case `DualReductions=0`
    /// exists for, and the rule must decline rather than "fix".
    #[test]
    fn an_infinite_target_bound_is_declined() {
        let _g = env_lock();
        let mut m = Model::new();
        let y = m.add_col(0.0, 1.0);
        let z = m.add_int_col(0.0, f64::INFINITY);
        m.add_row(f64::NEG_INFINITY, 0.0, &[(y, 1.0), (z, -5.0)]);
        m.set_objective(&[(z, -1.0)], Sense::Minimize);
        assert!(dual_fix(&m, None).is_none());
    }

    /// The objective sign test binds, and it binds in the model's own SENSE.
    #[test]
    fn the_objective_sign_test_is_read_in_the_models_sense() {
        let _g = env_lock();
        // Minimize with c_z = +1: pushing z UP costs, so the up-fix is refused
        // even though there is no up-lock.
        let build = |sense: Sense, c: f64| {
            let mut m = Model::new();
            let y = m.add_col(0.0, 1.0);
            let z = m.add_binary_col();
            m.add_row(f64::NEG_INFINITY, 0.0, &[(y, 1.0), (z, -5.0)]);
            m.set_objective(&[(z, c)], sense);
            m
        };
        assert!(dual_fix(&build(Sense::Minimize, 1.0), None).is_none());
        assert!(dual_fix(&build(Sense::Minimize, -1.0), None).is_some());
        // Maximizing the same coefficient flips which direction is free.
        assert!(dual_fix(&build(Sense::Maximize, 1.0), None).is_some());
        assert!(dual_fix(&build(Sense::Maximize, -1.0), None).is_none());
    }

    /// A CONTINUOUS column is never fixed, however dominated it is.
    #[test]
    fn continuous_columns_are_never_fixed() {
        let _g = env_lock();
        let mut m = Model::new();
        let y = m.add_col(0.0, 1.0);
        let w = m.add_col(0.0, 1.0);
        // Identical to the fixing case above but for `w`'s integrality.
        m.add_row(f64::NEG_INFINITY, 0.0, &[(y, 1.0), (w, -5.0)]);
        assert!(dual_fix(&m, None).is_none());
        let mut int = Model::new();
        let y = int.add_col(0.0, 1.0);
        let w = int.add_int_col(0.0, 1.0);
        int.add_row(f64::NEG_INFINITY, 0.0, &[(y, 1.0), (w, -5.0)]);
        assert!(dual_fix(&int, None).is_some());
    }

    /// THE CASCADE, which is the whole point: the rule fires ZERO times on the
    /// raw matrix and fires only because propagation forces `y = 0`, which
    /// makes `y - U z <= 0` REDUNDANT, which removes `z`'s last down-lock.
    /// This is the ny W1 clause-neuron gadget in miniature.
    #[test]
    fn the_cascade_needs_redundant_row_deletion_to_start() {
        let _g = env_lock();
        let mut m = Model::new();
        let y = m.add_col(0.0, 1.0);
        let s = m.add_col(1.0, 2.0);
        let z = m.add_binary_col();
        // y + s = 1 with s >= 1 forces y = 0.
        m.add_row(1.0, 1.0, &[(y, 1.0), (s, 1.0)]);
        // y - 3 z <= 0: an up-lock on nothing, a DOWN-lock on z (coefficient
        // -3 in a `<=` row). Once y is pinned at 0 the row is slack for every
        // z in [0, 1] and goes redundant, so the down-lock disappears.
        m.add_row(f64::NEG_INFINITY, 0.0, &[(y, 1.0), (z, -3.0)]);
        // y + 2 z <= 2: an up-lock on z. Also redundant once y = 0... which is
        // what makes z fixable at ALL, in either direction.
        m.add_row(f64::NEG_INFINITY, 2.0, &[(y, 1.0), (z, 2.0)]);
        let (_, log) = dual_fix(&m, None).expect("fires after the cascade");
        assert_eq!(log.fixings.len(), 1);
        assert_eq!(fixed_value(&log, z.index()), Some(0.0));
    }

    /// The reduction changes COLUMN BOUNDS AND NOTHING ELSE. Rows, objective
    /// and every rational constant come out byte-identical — the denominator
    /// argument in the module header rests on this.
    #[test]
    fn the_reduced_model_differs_only_in_column_bounds() {
        let _g = env_lock();
        let mut m = Model::new();
        let y = m.add_col(0.0, 1.0);
        let z = m.add_binary_col();
        m.add_row(f64::NEG_INFINITY, 0.0, &[(y, 1.0), (z, -5.0)]);
        let (red, log) = dual_fix(&m, None).expect("fires");
        assert_eq!(red.num_rows(), m.num_rows());
        assert_eq!(red.num_cols(), m.num_cols());
        for i in 0..m.num_rows() {
            let (ac, alb, aub) = m.row(Row(i as u32));
            let (bc, blb, bub) = red.row(Row(i as u32));
            assert_eq!(ac, bc);
            assert_eq!(alb.to_bits(), blb.to_bits());
            assert_eq!(aub.to_bits(), bub.to_bits());
        }
        for j in 0..m.num_cols() {
            let c = Col(j as u32);
            assert_eq!(m.obj_coeff(c).to_bits(), red.obj_coeff(c).to_bits());
            assert_eq!(m.col_kind(c), red.col_kind(c));
            if log.fixings.iter().all(|f| f.col as usize != j) {
                assert_eq!(m.col_bounds(c), red.col_bounds(c));
            }
        }
        assert_eq!(m.sense(), red.sense());
        assert_eq!(
            m.objective_offset().to_bits(),
            red.objective_offset().to_bits()
        );
    }

    /// The kill switch is exact: with it set the pass is not merely quiet, it
    /// never runs.
    #[test]
    fn the_kill_switch_disables_the_pass() {
        let _g = env_lock();
        let mut m = Model::new();
        let y = m.add_col(0.0, 1.0);
        let z = m.add_binary_col();
        m.add_row(f64::NEG_INFINITY, 0.0, &[(y, 1.0), (z, -5.0)]);
        assert!(dual_fix(&m, None).is_some());
        // SAFETY: single-threaded within the env lock held above.
        unsafe { std::env::set_var("AY_MILP_NO_DUALFIX", "1") };
        let off = dual_fix(&m, None);
        unsafe { std::env::remove_var("AY_MILP_NO_DUALFIX") };
        assert!(off.is_none());
    }

    /// A model whose true coefficients are only ROUNDED in the `f64` matrix is
    /// refused outright, exactly as `presolve` refuses it.
    #[test]
    fn an_inexact_model_is_refused() {
        let _g = env_lock();
        let mut m = Model::new();
        let y = m.add_col(0.0, 1.0);
        let z = m.add_binary_col();
        let r = m.add_row(f64::NEG_INFINITY, 0.0, &[(y, 1.0), (z, -5.0)]);
        assert!(dual_fix(&m, None).is_some());
        m.record_inexact_row_coeff(r, z.0, BigRational::new((-5i64).into(), 3i64.into()));
        assert!(dual_fix(&m, None).is_none());
    }

    /// A model with a MARGIN ROW is refused: the reframe asks a question this
    /// reduction does not preserve. See the decline in `dual_fix`.
    #[test]
    fn a_margin_model_is_refused() {
        let _g = env_lock();
        let mut m = Model::new();
        let y = m.add_col(0.0, 1.0);
        let z = m.add_binary_col();
        let r = m.add_row(f64::NEG_INFINITY, 0.0, &[(y, 1.0), (z, -5.0)]);
        assert!(dual_fix(&m, None).is_some());
        m.mark_margin_row(r)
            .expect("one-sided row in a 0-obj model");
        assert!(dual_fix(&m, None).is_none());
    }

    /// An already-expired deadline fixes NOTHING.
    ///
    /// Every budget cut in this pass has to be sound on its own. Most are
    /// trivially so because they only WEAKEN the reduction: a truncated
    /// propagation derives looser bounds, which deletes fewer rows, which leaves
    /// more locks, which fixes less. The LOCK SWEEP is the exception — a partial
    /// sweep UNDERCOUNTS locks, which is the direction that fixes a column that
    /// should not have been — so a truncated sweep abandons its round instead.
    #[test]
    fn an_expired_deadline_fixes_nothing() {
        let _g = env_lock();
        let mut m = Model::new();
        let y = m.add_col(0.0, 1.0);
        let z = m.add_binary_col();
        m.add_row(f64::NEG_INFINITY, 0.0, &[(y, 1.0), (z, -5.0)]);
        assert!(dual_fix(&m, None).is_some());
        let past = Instant::now()
            .checked_sub(std::time::Duration::from_secs(1))
            .expect("the process has been up for a second");
        assert!(dual_fix(&m, Some(past)).is_none());
    }

    #[test]
    fn randomised_small_models_keep_their_verdict_and_their_optimum() {
        let _g = env_lock();
        let (fired, cut) = brute_force_campaign(6_000, 0x2545_F491_4F6C_DD1D);
        assert!(
            fired > 500,
            "the rule barely fired ({fired}); test is vacuous"
        );
        assert!(cut > 500, "columns were barely pinned ({cut})");
    }

    /// END TO END, THROUGH THE REAL ENGINE. For each small objective-≡0 model
    /// the rule fires on, solve it BOTH ways — reduction on, reduction off — and
    /// assert the two contracts that matter to a caller:
    ///
    /// 1. **The verdict is the same.** SAT stays SAT, UNSAT stays UNSAT.
    /// 2. **Any certificate that comes back VERIFIES AGAINST THE CALLER'S OWN
    ///    MODEL.** This is the seal in `bab::expand_dualfix_outcome` under test:
    ///    a reduced-frame proof that leaned on a dual-fixed bound must be
    ///    declined, and the only way to be sure is to hand whatever survived to
    ///    the real verifier.
    /// 3. **NO TREE CERTIFICATE IS LOST.** Every model that ships a whole-tree
    ///    certificate with the reduction OFF ships one with it ON as well. This
    ///    is `bab::dualfix_should_harvest` and the re-solve behind it under
    ///    test, and it is a REGRESSION test in the literal sense: the reduction
    ///    shipped once without the harvest and silently dropped the artifact on
    ///    3 of 13 ny W1 instances that had one, including the largest
    ///    certificate in that corpus (`W1_unsat_v16_c39_000008`, 1,571,279 B).
    ///
    /// The second is the one that catches the wrong-answer class this reduction
    /// introduces. `verify` is the same code path a consumer runs on an exported
    /// `.ayc`, so a certificate that passes here is one they could re-check.
    #[test]
    fn a_dual_fixed_solve_keeps_its_verdict_and_never_ships_unverifiable_evidence() {
        let _g = env_lock();
        let mut state = 0xD1B5_4A32_D192_ED03u64;
        let mut rng = move || {
            state ^= state << 13;
            state ^= state >> 7;
            state ^= state << 17;
            state
        };
        // 30 s, not 5: these models are tiny and normally settle in milliseconds,
        // so the budget is not there to be spent — it is there to keep the CLOCK
        // out of the verdict comparison below on a loaded machine. Costs nothing
        // in the common case.
        let opts = crate::SolveOpts::new().with_time_limit(std::time::Duration::from_secs(30));
        let mut fired = 0usize;
        let mut infeasible = 0usize;
        let mut certs_kept = 0usize;
        let mut trees_harvested = 0usize;
        let mut undecided_asymmetry = 0usize;
        let mut seal_declines = 0usize;
        // 3,000 and not 600. MEASURED: the shape that makes the harvest
        // LOAD-BEARING — a reduced-frame tree the seal refuses against the
        // caller's model — occurs in roughly 4 of every 115 reduced trees on this
        // generator, so a 600-model run expects ZERO of them and the harvest
        // assertions below are then vacuous. That is not a guess: at 600 models
        // this test passed BYTE-IDENTICALLY with the harvest ripped out
        // (`24 trees kept` either way), which is exactly the hole the
        // `seal_declines` floor now closes.
        for _ in 0..3_000 {
            let ncol = 4 + (rng() % 3) as usize;
            // Deliberately OVER-constrained on average: the evidence lane only
            // exists on INFEASIBLE, so a generator that mostly produces feasible
            // models tests the half that was never in doubt.
            let nrow = 3 + (rng() % 3) as usize;
            let mut m = Model::new();
            let mut cols = Vec::new();
            for _ in 0..ncol {
                cols.push(m.add_int_col(0.0, (1 + rng() % 2) as f64));
            }
            // Objective IDENTICALLY ZERO — the shipped gate's class, and the ny
            // W1 shape.
            m.set_objective(&[], Sense::Minimize);
            for _ in 0..nrow {
                let mut coeffs = Vec::new();
                for &c in &cols {
                    let a = (rng() % 5) as f64 - 2.0;
                    if a != 0.0 {
                        coeffs.push((c, a));
                    }
                }
                if coeffs.is_empty() {
                    coeffs.push((cols[0], 1.0));
                }
                let rhs = (rng() % 5) as f64 - 2.0;
                let (lb, ub) = match rng() % 3 {
                    0 => (f64::NEG_INFINITY, rhs),
                    1 => (rhs, f64::INFINITY),
                    _ => (rhs, rhs),
                };
                m.add_row(lb, ub, &coeffs);
            }
            // HALF THE MODELS GET A CASE-SPLIT-ONLY GADGET on the first three
            // columns: `a + b + c = 3/2` has no integer solution, the LP
            // relaxation is perfectly happy at all-one-half, and BOUND
            // PROPAGATION CANNOT SEE IT either — each single-column residual
            // still admits an integer, so no floor/ceil ever contradicts. The
            // engine therefore has to BRANCH to know the model is infeasible,
            // which is what produces a TREE CERTIFICATE at all.
            //
            // Both halves of that matter. Without a gadget the generator is
            // ~99% feasible — the rule fires exactly when rows go redundant, and
            // a model with slack rows is usually satisfiable — so the evidence
            // lane never runs. The gadget locks only its own three columns (an
            // equality locks every column it contains in both directions); the
            // rest of the model stays dual-fixable.
            //
            // ⚠ IT MUST HAVE A FRACTIONAL RHS, and this is not a detail: the
            // obvious even-coefficient parity gadget `2a + 2b + 2c = 3` is
            // settled at the ROOT by the divisibility test, in ZERO nodes, so it
            // yields NO TREE and the harvest assertion below goes vacuous. That
            // is not hypothetical — it is what this test did before, and the
            // `trees_harvested` floor is what caught it. Kept in step with
            // `tree_cert.rs`'s `case_split_only_model`, which is the same shape.
            if rng() % 2 == 0 {
                m.add_row(1.5, 1.5, &[(cols[0], 1.0), (cols[1], 1.0), (cols[2], 1.0)]);
            }
            let Some((reduced, _)) = dual_fix(&m, None) else {
                continue;
            };
            fired += 1;
            let with = crate::bab::solve_milp(&m, &opts);
            // SAFETY: single-threaded within the env lock held above.
            unsafe { std::env::set_var("AY_MILP_NO_DUALFIX", "1") };
            let without = crate::bab::solve_milp(&m, &opts);
            // IS THE HARVEST LOAD-BEARING ON THIS MODEL? Solve the reduced frame
            // directly and ask the seal's own question of its tree: does it
            // verify against the CALLER's model? A `false` here is the exact
            // condition `bab::expand_dualfix_outcome` strips on and the only
            // condition under which the re-solve is the difference between an
            // artifact and none. Counted so the assertions above cannot go
            // quietly vacuous. (The kill switch stays set across this solve so it
            // does not re-enter the reduction on an already-reduced model.)
            let reduced_outcome = crate::bab::solve_milp(&reduced, &opts);
            unsafe { std::env::remove_var("AY_MILP_NO_DUALFIX") };
            if let crate::Outcome::Infeasible {
                tree_cert: Some(t), ..
            } = &reduced_outcome
            {
                if t.verify(&m).is_err() {
                    seal_declines += 1;
                }
            }

            let word = |o: &crate::Outcome| match o {
                crate::Outcome::Infeasible { .. } => "infeasible",
                crate::Outcome::Optimal { .. } | crate::Outcome::Feasible { .. } => "feasible",
                crate::Outcome::Unbounded => "unbounded",
                _ => "unknown",
            };
            // TWO DIFFERENT DECIDED VERDICTS IS THE WRONG-ANSWER CLASS, and it is
            // asserted without exception: infeasible against feasible is the
            // failure this reduction could actually introduce, and no budget can
            // excuse it.
            //
            // `unknown` is a different animal and is counted, not asserted.
            // `Outcome::Unknown` is FAIL-OPEN — "I did not settle every node" —
            // so an arm that returns it has claimed nothing and cannot be wrong.
            // It is reachable on either arm purely from the clock (the models are
            // tiny, but `SolverIncomplete` rides the same `incomplete` flag a
            // deadline sets), and asserting equality across it makes this test
            // fail under machine load for a reason that has nothing to do with
            // the rule. Observed once at a 5 s limit in a loaded full-suite run;
            // the budget below is now 30 s and the asymmetry is bounded rather
            // than ignored, so a SYSTEMATIC decidability regression still trips.
            if word(&with) != "unknown" && word(&without) != "unknown" {
                assert_eq!(
                    word(&with),
                    word(&without),
                    "DUAL FIXING CHANGED THE VERDICT.\n  with: {with:?}\n  without: {without:?}"
                );
            } else if word(&with) != word(&without) {
                undecided_asymmetry += 1;
            }
            // THE HARVEST UNDER TEST. The seal strips a reduced-frame tree
            // whenever it leaned on a dual-fixed bound, so without the re-solve
            // behind `bab::dualfix_should_harvest` this arm would simply be
            // missing the artifact the OFF arm hands over. Asserted per model
            // rather than in aggregate: a count would let one instance go dark
            // behind another that improved.
            // (An arm that ran out of budget is excluded for the reason above: it
            // has no tree because it has no verdict, which is not a loss.)
            if matches!(
                &without,
                crate::Outcome::Infeasible {
                    tree_cert: Some(_),
                    ..
                }
            ) && word(&with) != "unknown"
            {
                let crate::Outcome::Infeasible {
                    tree_cert: Some(t), ..
                } = &with
                else {
                    panic!(
                        "DUAL FIXING LOST A TREE CERTIFICATE the unreduced solve \
                         produced.\n  with: {with:?}\n  without: {without:?}"
                    );
                };
                t.verify(&m)
                    .expect("a harvested tree certificate must verify against the CALLER's model");
                trees_harvested += 1;
            }
            match &with {
                crate::Outcome::Infeasible { cert, tree_cert } => {
                    infeasible += 1;
                    if let Some(c) = cert {
                        c.verify(&m).expect(
                            "a shipped Farkas certificate must \
                             verify against the CALLER's model",
                        );
                        certs_kept += 1;
                    }
                    if let Some(t) = tree_cert {
                        t.verify(&m).expect(
                            "a shipped tree certificate must \
                             verify against the CALLER's model",
                        );
                        certs_kept += 1;
                    }
                }
                crate::Outcome::Optimal {
                    model_values, cert, ..
                } => {
                    m.check_point(model_values)
                        .expect("a shipped witness must satisfy the CALLER's model");
                    if let Some(c) = cert {
                        c.verify(&m).expect(
                            "a shipped optimality certificate must \
                             verify against the CALLER's model",
                        );
                        certs_kept += 1;
                    }
                }
                _ => {}
            }
        }
        assert!(
            fired > 30,
            "the rule barely fired ({fired}); test is vacuous"
        );
        assert!(
            infeasible > 5,
            "only {infeasible} infeasible verdicts; the evidence lane is untested"
        );
        // The harvest assertion above is vacuous unless the OFF arm actually
        // produced trees to lose, so pin that the lane ran.
        assert!(
            trees_harvested > 5,
            "only {trees_harvested} models had a tree certificate to keep; the \
             harvest assertion is vacuous"
        );
        // AND vacuous in the way that actually matters unless the SEAL DECLINED
        // at least once: a tree that survives `verify` against the caller's model
        // never needed buying back, so a population of only those would pass with
        // the harvest deleted. This floor is what makes the per-model assertion
        // above a real test of `harvest_tree_cert_by_resolve` rather than of the
        // seal's happy path.
        assert!(
            seal_declines > 0,
            "the seal never declined a reduced-frame tree in {fired} models, so \
             nothing here exercised the harvest at all"
        );
        // A HANDFUL of clock-driven `unknown` disagreements is expected on a
        // loaded machine; a systematic one is the reduction making models
        // materially harder to settle, which is a regression even though it is
        // not a wrong answer.
        assert!(
            undecided_asymmetry * 10 <= fired,
            "{undecided_asymmetry} of {fired} models were settled by one arm and \
             not the other; that is no longer clock noise"
        );
        // Not an assertion about HOW MANY survive the SEAL — that is an instance
        // property. Only that the lane is exercised rather than short-circuited.
        println!(
            "dualfix end-to-end: {fired} models, {infeasible} infeasible, \
             {certs_kept} certificates survived the seal, {trees_harvested} trees kept, \
             {seal_declines} of those bought back by the harvest, \
             {undecided_asymmetry} undecided on one arm only"
        );
    }
}
