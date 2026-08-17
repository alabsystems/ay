// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Bound propagation: read finite column bounds off the rows that imply them.
//!
//! # Why the search needs this to exist
//!
//! Every rigorous bound this crate computes is a weak-duality argument:
//!
//! ```text
//! c·z  =  yᵀ(Mz) + (c − Mᵀy)·z  =  d·z  ≥  Σ_j  min over the box of  d_j · z_j
//! ```
//!
//! and that last term is `−∞` the moment a single column is unbounded in the direction its
//! reduced cost points. One such column and the whole node has NO BOUND — it cannot be pruned,
//! and (because a bound-less node looks infinitely promising) it is explored FIRST.
//!
//! A binary model never shows this: every column is boxed in `[0, 1]`. Real models are full of
//! continuous columns declared `[0, ∞)` because the modeller never had to say otherwise, and on
//! them the effect is total — measured across MIPLIB, `blend2` had no bound on 11 of 12 nodes,
//! `rout` on 39 of 48, `dcmulti` on 1788 of 3263. The search was not searching.
//!
//! But those columns are not really unbounded. A row `Σ a_k x_k ≤ u` with every OTHER column
//! bounded below pins `x_j` from above, and that bound is IMPLIED — it cuts off no feasible
//! point, so imposing it is free. Deriving it is all this module does.
//!
//! # Why it is exact
//!
//! A derived bound that is a hair too tight cuts off a feasible point, and if that point was the
//! optimum the solver now lies. So the activities are accumulated in rationals — the model's
//! coefficients are exactly representable, so this is clean — and the derived bound is rounded
//! OUTWARD on its way back to `f64`. A bound that is a hair too loose costs a little search; a
//! bound that is a hair too tight costs correctness, and those are not the same mistake.

use num_rational::BigRational;
use num_traits::{One, Signed, ToPrimitive, Zero};

use crate::model::{exact, exact_small, Col, Model, Row};

pub(crate) mod binary_complement;
pub(crate) use binary_complement::{
    substitute_binary_complements, BinaryComplementPostsolve, BinaryComplementRowOrigin,
    BinaryComplementSide,
};
pub(crate) mod structure;
#[cfg(test)]
mod structure_adversary;
mod structure_attack;
pub(crate) use structure::{eliminate_structure, struct_elim_enabled, StructurePostsolve};
pub(crate) mod objective_singleton;
pub(crate) use objective_singleton::{
    substitute_objective_singletons, substitute_objective_singletons_with_deadline,
    ObjectiveSingletonPostsolve, ObjectiveSingletonRecovery, ObjectiveSingletonSide,
};

/// How many sweeps of propagation to run. Each sweep is one pass over the non-zeros; the
/// bounds tighten monotonically, so this converges. Past a handful of rounds the gains are
/// nil on every instance measured, and the cost is a pass over the whole matrix.
const ROUNDS: usize = 8;

/// A tightening smaller than this (relative) is not worth the pass it took to find.
const MIN_GAIN: f64 = 1e-7;

/// The result of propagating bounds.
pub(crate) enum Presolved {
    /// A model with (possibly) tighter column bounds.
    Tightened(Box<Model>),
    /// The bounds are contradictory: the model has no feasible point at all.
    Infeasible,
}

/// Tighten every column bound the rows imply a tighter one for.
///
/// `deadline` bounds the work: this runs in rationals over every non-zero, and on a model the
/// size of `nw04` (87,482 columns) eight unguarded sweeps of that is a minute of wall clock
/// spent before the search has looked at a single node. A caller's time limit is a limit on the
/// whole solve, not on the part of it that happens to be branch-and-bound.
pub(crate) fn tighten_bounds(model: &Model, deadline: Option<std::time::Instant>) -> Presolved {
    tighten_bounds_opt(model, deadline, true)
}

/// [`tighten_bounds`], with the second (coefficient-strengthening) phase made optional.
///
/// Root probing ([`crate::probe`]) fixes a binary and re-propagates purely to *detect
/// infeasibility and forced point-collapses*. Coefficient tightening rewrites feasible rows
/// but never collapses a column bound and never reports infeasibility, so on the probing
/// path it is pure cost and is skipped (`coef_tighten = false`). The bound-propagation lane
/// — the only part a probe reads — is byte-identical to the shipped presolve.
pub(crate) fn tighten_bounds_opt(
    model: &Model,
    deadline: Option<std::time::Instant>,
    coef_tighten: bool,
) -> Presolved {
    // FAIL-CLOSED for inexact models. Presolve derives tighter bounds (and
    // tightens row coefficients) by reading the row `f64`s; on a model whose
    // true coefficients are rounded proxies that reasoning is over the WRONG
    // matrix — a tightening could cut off a feasible point, and a coefficient
    // rewrite would desynchronise the exact-rational side-store (indexed by the
    // model's own rows) from the model. Skip it: the model (and its side-store)
    // stay pristine, and the search runs without presolve. Exact-coeff models
    // are unaffected.
    if model.has_inexact_coeffs() {
        // FORGONE COST. The comment above is a soundness argument and then asserts the
        // exclusion is free ("the search runs without presolve"). It never says what
        // that costs. Charge the quantity this module exists for: the OPEN bound sides
        // (presolve.rs, "The -inf in the box-minimum ... comes only from an OPEN
        // bound"). Cheaper than the `model.clone()` on the next line, and no rational
        // arithmetic runs on this branch by construction. A fully boxed inexact model
        // charges 0 while still being excluded wholesale — hits, not cost, is the
        // count of refused models.
        crate::sepstat::gate_charge(
            crate::sepstat::GATE_PRESOLVE_INEXACT,
            (0..model.num_cols())
                .map(|j| {
                    let (l, u) = model.col_bounds(Col(j as u32));
                    u64::from(!l.is_finite()) + u64::from(!u.is_finite())
                })
                .sum::<u64>(),
        );
        return Presolved::Tightened(Box::new(model.clone()));
    }
    // The arithmetic runs on the small-int-fast [`Rational`] (inline `i64/i64`,
    // exact big fallback): eight sweeps of allocating `BigRational` activity
    // sums were ~10% of a small instance's whole solve. Same numbers, same
    // derived bounds — every op is exact either way.
    use ay_lra::rational::Rational;
    let n = model.num_cols();
    let mut lo: Vec<Option<Rational>> = Vec::with_capacity(n);
    let mut up: Vec<Option<Rational>> = Vec::with_capacity(n);
    for j in 0..n {
        let (l, u) = model.col_bounds(Col(j as u32));
        lo.push(exact_small(l));
        up.push(exact_small(u));
    }
    let integral: Vec<bool> = (0..n)
        .map(|j| model.col_kind(Col(j as u32)).is_integral())
        .collect();

    // FLOAT SCOUT (advice lane; `--no-presolve-scout` kills it). The
    // OUTPUT of this function only ever differs from the input model through
    // (a) an integral column's bound moving, (b) an originally-OPEN bound
    // closing, or (c) infeasibility — a continuous column's already-finite
    // bound is deliberately discarded below. On the cifar100 w5 class the
    // exact sweeps cost 147s of an 18,692-row model's budget to derive 9,832
    // workspace bounds of which exactly ONE is output-visible (a single free
    // column closed off its defining row). The scout mirrors the sweep in f64
    // first and hands the exact lane a ROW PLAN:
    //   * no visible candidate anywhere -> the exact loop runs over zero rows
    //     (soundness: not tightening is always sound; the model ships
    //     byte-identical bounds);
    //   * visible candidates whose values a replay over just their rows
    //     reproduces -> the exact loop runs over exactly those rows (the
    //     applied bounds are still derived and admitted by the RATIONAL lane
    //     below — propagation over a row subset is valid propagation);
    //   * anything else (cascade-dependent visible values, suspected
    //     infeasibility, big visible row set, float overflow) -> None, the
    //     full exact lane runs exactly as it always has.
    // Floats ADVISE which rows are worth exact work; every applied bound is
    // still decided in exact rationals. A scout miss (float noise hiding a
    // just-past-threshold tightening) costs bound tightness, never
    // correctness.
    let trace = crate::debug_flags::milp_debug_flags().trace;
    let plan: Option<Vec<u32>> = if crate::tune::caller_flag(crate::tune::Knob::NoPresolveScout)
        != Some(true)
    {
        let _t_scout = std::time::Instant::now();
        let p = scout_plan(model, &integral, deadline);
        if trace {
            eprintln!(
                "--trace presolve: scout {} in {:.3}s",
                match &p {
                    None => "FULL LANE".to_string(),
                    Some(v) if v.is_empty() => "NOTHING VISIBLE (skip exact sweeps)".to_string(),
                    Some(v) => format!("RESTRICTED to {} rows", v.len()),
                },
                _t_scout.elapsed().as_secs_f64()
            );
        }
        p
    } else {
        None
    };

    if !propagate(
        model,
        deadline,
        plan.as_deref(),
        &integral,
        &mut lo,
        &mut up,
        trace,
    ) {
        return Presolved::Infeasible;
    }

    if crate::debug_flags::milp_debug_flags().trace {
        let mut newly_finite = 0;
        let mut biggest: f64 = 0.0;
        for j in 0..n {
            let (l0, u0) = model.col_bounds(Col(j as u32));
            if !l0.is_finite() && lo[j].is_some() || !u0.is_finite() && up[j].is_some() {
                newly_finite += 1;
            }
            for b in [lo[j].as_ref(), up[j].as_ref()].into_iter().flatten() {
                biggest = biggest.max(b.to_big().to_f64().unwrap_or(0.0).abs());
            }
        }
        eprintln!(
            "--trace presolve: {newly_finite} columns gained a finite bound; \
             largest bound magnitude {biggest:.3e}"
        );
    }

    let mut out = model.clone();
    for j in 0..n {
        // OUTWARD on the way back to f64: a lower bound rounds DOWN, an upper bound rounds UP.
        // A bound that is a hair too loose costs search. A bound that is a hair too tight can
        // cut off the optimum, and this whole crate exists so that cannot happen.
        let mut l = lo[j]
            .as_ref()
            .map_or(f64::NEG_INFINITY, |b| round_out(&b.to_big(), true));
        let mut u = up[j]
            .as_ref()
            .map_or(f64::INFINITY, |b| round_out(&b.to_big(), false));

        // An integer column takes every tightening; a continuous one only takes a bound that
        // was OPEN.
        //
        // The two are not the same kind of gain. Pulling an integer column from [0, 100] to
        // [0, 3] deletes 97 values the search would otherwise branch over -- that is real
        // domain reduction, and it is exact. Squeezing a CONTINUOUS column's already-finite
        // bound deletes no vertex the simplex was going to visit; it just moves the column onto
        // a new bound, which makes an already-degenerate LP more degenerate. Measured: doing it
        // anyway, blend2's root LP came back PRIMAL INFEASIBLE -- on a model that has an optimum
        // -- and the search fell through to the rational rim, which then spent the whole time
        // budget on a single node.
        //
        // The -inf in the box-minimum, which is what this module exists for, comes only from an
        // OPEN bound. Closing those is the part that pays.
        let (l0, u0) = model.col_bounds(Col(j as u32));
        if !integral[j] {
            if l0.is_finite() {
                l = l0;
            }
            if u0.is_finite() {
                u = u0;
            }
        }
        if l > u {
            return Presolved::Infeasible;
        }
        out.set_col_bounds(Col(j as u32), l, u);
    }

    // SECOND: with the box settled, strengthen the row coefficients themselves
    // (see `tighten_coefficients`). This must read the box `out` actually carries — not the
    // tighter rational bounds above — because its validity argument quantifies over exactly
    // the points the output model admits.
    if coef_tighten && !crate::tune::on(crate::tune::Knob::NoCoefTighten) {
        let _t_coef = std::time::Instant::now();
        let tightened = tighten_coefficients(&mut out, deadline);
        if trace {
            eprintln!(
                "--trace presolve: coef-tighten wall={:.3}s applied={tightened}",
                _t_coef.elapsed().as_secs_f64()
            );
        }
        // THIRD: the same rewrite with the rest of the row bounded CONDITIONAL on a binary's
        // value (see `tighten_coefficients_conditional`). It subsumes nothing above — it runs
        // after, on the already-tightened rows, and only pulls a right-hand side further down.
        //
        // DEFAULT ON (2026-07-26). The pass costs two exact propagations per probed binary and
        // whether that buys anything is an instance property, so it shipped opt-in — but
        // measured across the corpus at 60s/1T it is a strict improvement where it fires and
        // provably inert elsewhere: 12 of 13 deterministic instances are byte-identical in
        // objective AND node count with it on (blend2 5526, flugpl 2630, gen 11, gt2 272,
        // khb05250 13, mas76 722875, misc07 5236, mod010 1701, p0201 168, pk1 357727,
        // qnet1 372, air03 1), and dcmulti goes 1433 -> 899 nodes / 1.11s -> 0.76s at the same
        // proven optimum 188182.
        //
        // Soundness is the reason this can be a default rather than a gamble: the rewrite
        // lowers ONLY the relaxed level's right-hand side and leaves the other level
        // algebraically identical, so the feasible sets are EQUAL, not merely nested. Both
        // adversarial reviewers confirmed it independently.
        //
        // Its GENERAL form — tightening BOTH of the binary's levels — is strictly more valid
        // rewrites and a strictly stronger LP term by term, and was MEASURED NEGATIVE and
        // discarded: qnet1 372 -> 1518 nodes with root closure -52.5, mod010 1701 -> 1851,
        // gen 11 -> 22. It moved the pre-cut bound by exactly ZERO on qnet1 and mod010 while
        // moving the optimal basis, and a moved basis is a different Gomory tableau.
        // Strengthening a row the LP is not sitting on buys nothing and perturbs everything.
        //
        // `AY_MILP_NO_COND_TIGHTEN` restores the pre-2026-07-26 behaviour byte-identically;
        // `the cond-tighten knob` is kept as the explicit-on A/B arm.
        //
        // REVERTED TO OPT-IN (2026-07-29). The default-on justification above was measured and
        // was true when written: strict improvement where it fires, provably inert elsewhere.
        // It has since INVERTED. Thirty-four ay-milp commits landed afterwards, several of them
        // correctness fixes that legitimately move node counts ("the tree's claim was not
        // floored by the root's", "budget strong branching off THIS solve's work"), and under
        // their interaction the pass now COSTS the one instance it touches:
        //
        //   corpus A/B at 60s/1T, node counts, ON (was default) vs OFF
        //     dcmulti  2878  vs  917    <- 3.1x WORSE with it on, 1.184s vs 0.636s
        //     blend2, flugpl, gen, gt2, khb05250, misc07, mod010, p0201, pk1, qnet1
        //                              byte-identical, objectives preserved everywhere
        //
        // So it now helps nothing and harms one instance. The rewrite is still exactly sound --
        // it lowers only the relaxed level's right-hand side and leaves the other level
        // algebraically identical, so the feasible sets are EQUAL -- and the machinery, its
        // brute-force guard and its A/B arms all stay. Only the default moves back.
        //
        // THE TRANSFERABLE LESSON: a default justified as "inert everywhere except where it
        // wins" is only as durable as the interactions it was measured against. This one was
        // re-checked three days later and had flipped sign. Shipped defaults on this codebase
        // need periodic re-measurement, not just verification at merge time.
        // Both arms stay live: `the cond-tighten knob` opts in, `AY_MILP_NO_COND_TIGHTEN`
        // force-disables even if the opt-in is set, so a campaign script that sets the
        // kill switch keeps working exactly as it did while this was a default.
        if crate::tune::caller_flag(crate::tune::Knob::CondTighten) == Some(true)
        // B7: the AY_MILP_NO_COND_TIGHTEN off-switch is deleted (always enabled
        // when the opt-in above holds).
        {
            let _t_cond = std::time::Instant::now();
            let rewritten = tighten_coefficients_conditional(&mut out, deadline);
            if trace {
                eprintln!(
                    "--trace presolve: cond-tighten wall={:.3}s applied={rewritten}",
                    _t_cond.elapsed().as_secs_f64()
                );
            }
        }
    }

    Presolved::Tightened(Box::new(out))
}

/// THE exact bound-propagation sweep, over a caller-supplied workspace.
///
/// `lo`/`up` come in as the box the caller wants propagated from and go out as the fixpoint
/// the rows imply — `None` on a side means "still open". Returns `false` when the rows
/// PROVE the box empty (a column whose derived lower bound passes its upper).
///
/// Two callers, one primitive. [`tighten_bounds_opt`] propagates the model's declared box and
/// then applies its output policy. [`tighten_coefficients_conditional`] propagates the SAME
/// box with one binary pinned, and reads the workspace directly — the fixpoint, not the
/// policy-filtered model — because the bound it needs (a continuous column's conditional
/// ceiling) is exactly the kind the output policy deliberately discards.
///
/// `plan` restricts the sweep to a row subset (the float scout's advice); propagation over a
/// subset of the rows is still propagation, so a restriction costs tightness, never validity.
///
/// A THIRD caller, `crate::dualfix`, interleaves this with lock counting. It is the crate's
/// audited exact propagator and is reused rather than reimplemented deliberately: the outward
/// rounding, the integer floor/ceil and the at-most-one-infinite-contributor bookkeeping are
/// each a place a fresh implementation gets it subtly and silently wrong.
pub(crate) fn propagate(
    model: &Model,
    deadline: Option<std::time::Instant>,
    plan: Option<&[u32]>,
    integral: &[bool],
    lo: &mut [Option<ay_lra::rational::Rational>],
    up: &mut [Option<ay_lra::rational::Rational>],
    trace: bool,
) -> bool {
    use ay_lra::rational::Rational;
    let expired = || deadline.is_some_and(|d| std::time::Instant::now() >= d);
    // Round-level economics (`--trace`): where the presolve share
    // actually goes at the 7.5M-nnz scale — wall per sweep, rows reached
    // before the deadline, bounds moved. Diagnostic only.
    for round in 0..ROUNDS {
        let _t_round = std::time::Instant::now();
        let mut rows_done = 0usize;
        let mut moves = 0usize;
        let mut changed = false;
        if expired() {
            if trace {
                eprintln!("--trace presolve: round {round} skipped (deadline)");
            }
            break; // keep whatever has been derived so far -- it is all still valid
        }
        let row_count = plan.map_or(model.num_rows(), <[u32]>::len);
        for ri in 0..row_count {
            if ri % 256 == 0 && expired() {
                break;
            }
            rows_done = ri + 1;
            let r = plan.map_or(ri, |v| v[ri] as usize);
            let (coeffs, rlb, rub) = model.row(Row(r as u32));
            let (rlb, rub) = (exact_small(rlb), exact_small(rub));
            if rlb.is_none() && rub.is_none() {
                continue;
            }

            // The row's reachable activity range, with the count of columns that make it
            // infinite. One infinite column still lets us bound THAT column (all the others'
            // contributions are finite); two and the row says nothing about either.
            let mut min_act = Rational::new(0, 1);
            let mut max_act = Rational::new(0, 1);
            let (mut min_inf, mut max_inf) = (0usize, 0usize);
            for &(c, a) in coeffs {
                let (j, a) = (
                    c as usize,
                    exact_small(a).expect("row coefficient is finite"),
                );
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
            if min_inf > 1 && max_inf > 1 {
                continue; // this row implies nothing about anything
            }

            for &(c, a) in coeffs {
                let (j, a) = (
                    c as usize,
                    exact_small(a).expect("row coefficient is finite"),
                );
                if a.is_zero() {
                    continue;
                }
                let (at_min, at_max) = if a.is_positive() {
                    (&lo[j], &up[j])
                } else {
                    (&up[j], &lo[j])
                };
                // The rest of the row, with THIS column taken out.
                let rest_min = match (min_inf, at_min) {
                    (0, Some(b)) => Some(&min_act - &(a.clone() * b)),
                    (1, None) => Some(min_act.clone()), // j WAS the infinite one
                    _ => None,
                };
                let rest_max = match (max_inf, at_max) {
                    (0, Some(b)) => Some(&max_act - &(a.clone() * b)),
                    (1, None) => Some(max_act.clone()),
                    _ => None,
                };

                // a·x_j <= rub − (the least the rest can be)
                if let (Some(u), Some(rm)) = (&rub, &rest_min) {
                    let slack = u - rm;
                    let b = &slack / &a;
                    let moved = if a.is_positive() {
                        tighten(&mut up[j], b, false, integral[j])
                    } else {
                        tighten(&mut lo[j], b, true, integral[j])
                    };
                    moves += moved as usize;
                    changed |= moved;
                }
                // a·x_j >= rlb − (the most the rest can be)
                if let (Some(l), Some(rm)) = (&rlb, &rest_max) {
                    let slack = l - rm;
                    let b = &slack / &a;
                    let moved = if a.is_positive() {
                        tighten(&mut lo[j], b, true, integral[j])
                    } else {
                        tighten(&mut up[j], b, false, integral[j])
                    };
                    moves += moved as usize;
                    changed |= moved;
                }

                if let (Some(l), Some(u)) = (&lo[j], &up[j]) {
                    if l > u {
                        return false;
                    }
                }
            }
        }
        if trace {
            eprintln!(
                "--trace presolve: round {round} wall={:.3}s rows={rows_done}/{row_count} moves={moves}{}",
                _t_round.elapsed().as_secs_f64(),
                if expired() { " EXPIRED" } else { "" }
            );
        }
        if !changed {
            break;
        }
    }
    true
}

/// Float mirror of one `tighten_bounds` row visit, on the scout's f64
/// workspace. Applies with HALF the exact lane's `MIN_GAIN` (a scout that
/// tightens slightly more than the exact lane would OVER-detects visible
/// candidates — the safe direction; the exact lane never adopts scout values).
/// Returns whether any bound moved, whether a WATCH side moved (visible per
/// the output policy), or an infeasibility suspicion.
enum ScoutRow {
    Clean,
    Moved { watch: bool },
    Suspicious,
}

fn scout_row(
    model: &Model,
    r: usize,
    lo: &mut [f64],
    up: &mut [f64],
    integral: &[bool],
    watch_lo: &[bool],
    watch_up: &[bool],
) -> ScoutRow {
    // Mirror of `tighten`, in f64. `cur` open (±inf) adopts any finite bound;
    // else strict improvement past half the exact gain gate.
    fn apply(cur: &mut f64, b: f64, lower: bool, integral: bool) -> bool {
        if !b.is_finite() {
            return false; // float overflow: advise nothing (the exact lane cannot produce this)
        }
        let b = if integral {
            if lower {
                b.ceil()
            } else {
                b.floor()
            }
        } else {
            b
        };
        if cur.is_finite() {
            let better = if lower { b > *cur } else { b < *cur };
            if !better {
                return false;
            }
            if (b - *cur).abs() <= 0.5 * MIN_GAIN * cur.abs().max(1.0) {
                return false;
            }
        }
        *cur = b;
        true
    }

    let (coeffs, rlb, rub) = model.row(Row(r as u32));
    if !rlb.is_finite() && !rub.is_finite() {
        return ScoutRow::Clean;
    }
    let mut min_act = 0.0f64;
    let mut max_act = 0.0f64;
    let (mut min_inf, mut max_inf) = (0usize, 0usize);
    for &(c, a) in coeffs {
        let j = c as usize;
        // Sign split matches the exact lane's `a.is_positive()` (a == 0 lands
        // in the negative arm there too, and its INFINITE bounds still count).
        let (at_min, at_max) = if a > 0.0 {
            (lo[j], up[j])
        } else {
            (up[j], lo[j])
        };
        if at_min.is_finite() {
            min_act += a * at_min;
        } else {
            min_inf += 1;
        }
        if at_max.is_finite() {
            max_act += a * at_max;
        } else {
            max_inf += 1;
        }
    }
    if min_inf > 1 && max_inf > 1 {
        return ScoutRow::Clean;
    }
    if !min_act.is_finite() || !max_act.is_finite() {
        // f64 overflow in the activity itself: this row's advice is garbage —
        // let the caller fall back to the full exact lane.
        return ScoutRow::Suspicious;
    }
    let mut moved = false;
    let mut watch = false;
    for &(c, a) in coeffs {
        if a == 0.0 {
            continue;
        }
        let j = c as usize;
        let (at_min, at_max) = if a > 0.0 {
            (lo[j], up[j])
        } else {
            (up[j], lo[j])
        };
        let rest_min = if min_inf == 0 && at_min.is_finite() {
            Some(min_act - a * at_min)
        } else if min_inf == 1 && !at_min.is_finite() {
            Some(min_act)
        } else {
            None
        };
        let rest_max = if max_inf == 0 && at_max.is_finite() {
            Some(max_act - a * at_max)
        } else if max_inf == 1 && !at_max.is_finite() {
            Some(max_act)
        } else {
            None
        };
        if rub.is_finite() {
            if let Some(rm) = rest_min {
                let b = (rub - rm) / a;
                let m = if a > 0.0 {
                    apply(&mut up[j], b, false, integral[j]).then(|| watch_up[j])
                } else {
                    apply(&mut lo[j], b, true, integral[j]).then(|| watch_lo[j])
                };
                if let Some(w) = m {
                    moved = true;
                    watch |= w;
                }
            }
        }
        if rlb.is_finite() {
            if let Some(rm) = rest_max {
                let b = (rlb - rm) / a;
                let m = if a > 0.0 {
                    apply(&mut lo[j], b, true, integral[j]).then(|| watch_lo[j])
                } else {
                    apply(&mut up[j], b, false, integral[j]).then(|| watch_up[j])
                };
                if let Some(w) = m {
                    moved = true;
                    watch |= w;
                }
            }
        }
        // A MATERIAL crossing is an infeasibility the exact lane might prove:
        // hand the row set back and let it. (Degenerate lo == up pins and
        // ulp-level crossings are NOT suspicious — a missed presolve
        // infeasibility is found by the search, it is never wrong.)
        if lo[j].is_finite() && up[j].is_finite() && lo[j] > up[j] + 1e-7 * (1.0 + up[j].abs()) {
            return ScoutRow::Suspicious;
        }
    }
    if moved {
        ScoutRow::Moved { watch }
    } else {
        ScoutRow::Clean
    }
}

/// The scout pass over the whole model: run the `ROUNDS` cascade in f64, find
/// which rows produce OUTPUT-VISIBLE moves (integral columns; originally-open
/// sides), and check whether replaying ONLY those rows reproduces the visible
/// values. Returns `Some(rows)` (possibly empty = nothing visible anywhere)
/// as the exact lane's row plan, or `None` for the full lane.
fn scout_plan(
    model: &Model,
    integral: &[bool],
    deadline: Option<std::time::Instant>,
) -> Option<Vec<u32>> {
    let expired = || deadline.is_some_and(|d| std::time::Instant::now() >= d);
    let n = model.num_cols();
    let nrows = model.num_rows();
    let mut olo = Vec::with_capacity(n);
    let mut oup = Vec::with_capacity(n);
    for j in 0..n {
        let (l, u) = model.col_bounds(Col(j as u32));
        olo.push(l);
        oup.push(u);
    }
    // A side is WATCHED if a move on it can reach the output: integral columns
    // take every tightening; a continuous side only ever ships if it was OPEN.
    let watch_lo: Vec<bool> = (0..n).map(|j| integral[j] || !olo[j].is_finite()).collect();
    let watch_up: Vec<bool> = (0..n).map(|j| integral[j] || !oup[j].is_finite()).collect();

    // Phase 1: the full float cascade, recording rows that move watched sides.
    let mut lo = olo.clone();
    let mut up = oup.clone();
    let mut vseen = vec![false; nrows];
    let mut any_watch = false;
    for _round in 0..ROUNDS {
        if expired() {
            return None;
        }
        let mut changed = false;
        for r in 0..nrows {
            if r % 4096 == 0 && expired() {
                return None;
            }
            match scout_row(model, r, &mut lo, &mut up, integral, &watch_lo, &watch_up) {
                ScoutRow::Suspicious => return None,
                ScoutRow::Moved { watch } => {
                    changed = true;
                    if watch {
                        any_watch = true;
                        vseen[r] = true;
                    }
                }
                ScoutRow::Clean => {}
            }
        }
        if !changed {
            break;
        }
    }
    if !any_watch {
        return Some(Vec::new());
    }
    let vrows: Vec<u32> = (0..nrows as u32).filter(|&r| vseen[r as usize]).collect();
    if vrows.len() * 4 > nrows {
        return None; // restriction saves nothing worth the replay
    }

    // Phase 2: replay ONLY the visible rows and demand the watched values
    // agree — if a visible bound's VALUE depended on the wider cascade, the
    // restricted exact lane would ship a (valid but) looser bound than the
    // full lane always has; fall back instead.
    let mut rlo = olo;
    let mut rup = oup;
    for _round in 0..ROUNDS {
        if expired() {
            return None;
        }
        let mut changed = false;
        for &r in &vrows {
            match scout_row(
                model, r as usize, &mut rlo, &mut rup, integral, &watch_lo, &watch_up,
            ) {
                ScoutRow::Suspicious => return None,
                ScoutRow::Moved { .. } => changed = true,
                ScoutRow::Clean => {}
            }
        }
        if !changed {
            break;
        }
    }
    let agree = |a: f64, b: f64| -> bool {
        if a.is_finite() && b.is_finite() {
            (a - b).abs() <= MIN_GAIN * a.abs().max(1.0)
        } else {
            a == b // same infinity (or both open)
        }
    };
    for j in 0..n {
        if (watch_lo[j] && !agree(lo[j], rlo[j])) || (watch_up[j] && !agree(up[j], rup[j])) {
            return None;
        }
    }
    Some(vrows)
}

/// How many strengthening sweeps to run over each row. Within one row every application
/// shifts the redundancy slack the NEXT coefficient sees, so a second look pays (the classic
/// `5x + 3y <= 6  ->  x + y <= 1` needs the second visit to `x`... it gets it within one pass
/// here because the sweep updates its activity bound as it goes; the extra rounds mop up the
/// order-dependent remainder). Gains vanish after a couple of rounds on everything measured.
const COEF_ROUNDS: usize = 4;

/// Coefficient tightening (Crowder–Johnson–Padberg "coefficient improvement" /
/// Savelsbergh "coefficient reduction"), on one-sided rows, over integral columns.
///
/// # The rule, and why it is exact
///
/// Work in the `<=` frame: a row `Σ_k a_k x_k <= b` whose OTHER side is infinite (a `>=` row
/// is negated into this frame; an equality or range row is untouchable — its two sides share
/// the coefficients, and a change valid for one side changes the other). Take a column `x_j`
/// that is INTEGRAL, with `a_j > 0`, and let
///
/// ```text
/// ū  = floor(u_j)                       the top integer level x_j can reach in the box
/// U' = Σ_{k≠j} max over the box of a_k x_k     (must be finite, as must u_j)
/// d  = b − a_j·(ū−1) − U'               the row's slack at the level BELOW the top
/// ```
///
/// If `0 < d < a_j`, replace `a_j ← a_j − d` and `b ← b − d·ū`. Validity: for each integer
/// value `x_j = ū − t` the row constrains the rest of the columns, and the replacement
/// preserves that constraint CASE BY CASE.
///
/// * `t = 0`: the new bound on the rest is `(b − d·ū) − (a_j − d)·ū = b − a_j·ū` — identical
///   to the old row's. Nothing gained, nothing lost.
/// * `t = 1`: the new bound is `b − a_j·(ū−1) − d = U'` — vacuous, since the rest can never
///   exceed `U'` inside the box. The OLD bound at this level was `U' + d ≥ U'` — also vacuous.
/// * `t ≥ 2`: new bound `U' + (t−1)·(a_j − d)`, old bound `U' + d + (t−1)·a_j`; both `≥ U'`
///   (this is where `d < a_j` is needed), so both vacuous.
///
/// So every point of the box with `x_j` INTEGER satisfies the new row iff it satisfies the
/// old one: the integer feasible set is preserved EXACTLY, in both directions — incumbents
/// transfer forward, witnesses transfer back, and every dual bound computed against the
/// tightened rows is a bound for the original model. Fractional `x_j` (which only the LP
/// relaxation visits) is where the new row is strictly stronger — that is the point.
///
/// For `a_j < 0` the mirror applies at the BOTTOM integer level `l̄ = ceil(l_j)`:
/// `d = b − a_j·(l̄+1) − U'`, and if `0 < d < −a_j`, replace `a_j ← a_j + d`, `b ← b + d·l̄`.
/// (Same case analysis at `x_j = l̄ + t`.)
///
/// `d ≥ |a_j|` means the row cannot be violated inside the box at all; it is left alone
/// rather than dropped (dropping would renumber rows).
///
/// # Exactness discipline
///
/// All arithmetic is in rationals over the dyadics the f64 model data denotes, and a
/// replacement is applied ONLY if both the new coefficient and the new bound convert to f64
/// EXACTLY (round-trip). No rounding direction is safe here — a coefficient a hair low or a
/// bound a hair high admits integer points the original excluded; the opposite hair excludes
/// points it admitted — so inexact replacements are skipped, not rounded. Skipping any subset
/// of applications is sound: each one's validity argument reads only the CURRENT row and the
/// box.
///
/// Returns how many coefficients were tightened; a model with nothing to tighten is untouched.
pub(crate) fn tighten_coefficients(
    model: &mut Model,
    deadline: Option<std::time::Instant>,
) -> usize {
    let expired = || deadline.is_some_and(|d| std::time::Instant::now() >= d);
    let n = model.num_cols();
    let mut lo: Vec<Option<BigRational>> = Vec::with_capacity(n);
    let mut up: Vec<Option<BigRational>> = Vec::with_capacity(n);
    for j in 0..n {
        let (l, u) = model.col_bounds(Col(j as u32));
        lo.push(exact(l));
        up.push(exact(u));
    }
    let integral: Vec<bool> = (0..n)
        .map(|j| model.col_kind(Col(j as u32)).is_integral())
        .collect();
    let one = BigRational::one();
    let min_gain = exact(MIN_GAIN).expect("MIN_GAIN is finite");
    let mut applied = 0usize;

    for r in 0..model.num_rows() {
        if r % 64 == 0 && expired() {
            break; // everything applied so far is valid on its own
        }
        let (rlb, rub) = {
            let row = &model.rows[r];
            (row.lb, row.ub)
        };
        // Only a ONE-SIDED row may be touched; `flip` says the finite side is the lower one.
        let flip = match (rlb.is_finite(), rub.is_finite()) {
            (false, true) => false,
            (true, false) => true,
            _ => continue,
        };
        let signed = |a: f64| if flip { -a } else { a };
        let mut b_hat = exact(signed(if flip { rlb } else { rub })).expect("finite side");
        // The row's coefficients in the `<=` frame, index-aligned with the model's row.
        let mut coeffs: Vec<(usize, BigRational)> = model.rows[r]
            .coeffs
            .iter()
            .map(|&(c, a)| (c as usize, exact(signed(a)).expect("finite coefficient")))
            .collect();

        'row: for _ in 0..COEF_ROUNDS {
            // Max reachable activity of the whole row. One unbounded term and the rule is
            // inapplicable to every column here: a candidate needs the REST finite and its
            // own bound (which is its own max-activity term) finite.
            let mut total_max = BigRational::zero();
            for (c, a) in &coeffs {
                let bound = if a.is_positive() { &up[*c] } else { &lo[*c] };
                match bound {
                    Some(b) => total_max += a * b,
                    None => break 'row,
                }
            }
            let mut changed = false;
            for i in 0..coeffs.len() {
                let (c, a) = (coeffs[i].0, coeffs[i].1.clone());
                if !integral[c] || a.is_zero() {
                    continue;
                }
                // The box bound the activity sum used for this column, the integer level the
                // row binds at, and the adjacent level the slack is measured at.
                let (own_bound, level, level_adj) = if a.is_positive() {
                    let u = up[c].as_ref().expect("finite: total_max exists");
                    let ubar = u.floor();
                    let adj = &ubar - &one;
                    (u, ubar, adj)
                } else {
                    let l = lo[c].as_ref().expect("finite: total_max exists");
                    let lbar = l.ceil();
                    let adj = &lbar + &one;
                    (l, lbar, adj)
                };
                let rest_max = &total_max - &a * own_bound;
                let d = &b_hat - &a * &level_adj - &rest_max;
                // Material on both sides: `d` big enough to be worth a changed model, and
                // `|a| − d` big enough that the surviving coefficient is not numerical dust
                // (this also enforces `d < |a|` strictly; `d ≥ |a|` is the redundant-row
                // case, which is left alone).
                let scale = {
                    let abs = a.abs();
                    if abs > one {
                        abs
                    } else {
                        one.clone()
                    }
                };
                let floor_gain = &min_gain * &scale;
                if d <= floor_gain || a.abs() - &d <= floor_gain {
                    continue;
                }
                let a_new = if a.is_positive() { &a - &d } else { &a + &d };
                let b_new = if a.is_positive() {
                    &b_hat - &d * &level
                } else {
                    &b_hat + &d * &level
                };
                // Fail closed: apply only if BOTH survive the trip back to f64 exactly.
                let (Some(af), Some(bf)) = (as_exact_f64(&a_new), as_exact_f64(&b_new)) else {
                    continue;
                };
                if crate::debug_flags::milp_debug_flags().coef_tighten_debug {
                    eprintln!(
                        "COEF_TIGHTEN row {r} col {c}: a {} -> {af} | rhs {} -> {bf} (level {level}, d {d})",
                        signed(model.rows[r].coeffs[i].1),
                        signed(if flip { model.rows[r].lb } else { model.rows[r].ub }),
                    );
                }
                total_max += (&a_new - &a) * own_bound;
                coeffs[i].1 = a_new;
                b_hat = b_new;
                model.rows[r].coeffs[i].1 = signed(af);
                if flip {
                    model.rows[r].lb = signed(bf);
                } else {
                    model.rows[r].ub = signed(bf);
                }
                applied += 1;
                changed = true;
            }
            if !changed {
                break;
            }
        }
    }
    applied
}

/// The deterministic work budgets for [`tighten_coefficients_conditional`], in units of
/// `matrix passes · nnz`: `COND_WORK_BUDGET` caps the EXACT rational propagations, and
/// `COND_SCOUT_BUDGET` caps the f64 mirrors that decide which candidates earn one.
///
/// Both are counted rather than timed. A wall-clock share would make the pass's OUTPUT — which
/// rows it rewrites — depend on how loaded the host is, and a measurement that moves with the
/// machine is not a measurement. The deadline is still honoured, but as a safety valve, not as
/// the thing that decides.
///
/// The exact budget at 2M is every side every MIPLIB-easy model needs (dcmulti wants 30 sides
/// against 1,315 nnz = 39k) with three orders of magnitude of headroom, and it is a hard
/// ceiling on the worst case: a model whose rationals have grown big denominators pays roughly
/// a second for 2M row visits, and then stops. The scout budget is ten times larger because a
/// float pass is roughly two orders of magnitude cheaper than a rational one; it exists so that
/// "cheap, times a hundred thousand binaries" cannot quietly become a time limit.
const COND_WORK_BUDGET: usize = 2_000_000;
const COND_SCOUT_BUDGET: usize = 20_000_000;

/// CONDITIONAL coefficient tightening: [`tighten_coefficients`]'s rule with the rest of the row
/// bounded *given the binary's value* instead of over the whole box. This is the big-M / VUB
/// reduction, and it is the one Gurobi has and the unconditional rule provably cannot get.
///
/// # Why the unconditional rule is not enough
///
/// dcmulti row 26 is `−600·D111 + Z1121 ≤ 0` — a variable upper bound, `Z1121 ≤ 600·D111`.
/// Base propagation proves `Z1121 ≤ 350`, so [`tighten_coefficients`] rewrites the big-M
/// 600 -> 350 and stops: 350 is the most `Z1121` can be *anywhere in the box*. But the only
/// point of that coefficient is the case `D111 = 1`, and CONDITIONAL on `D111 = 1` two other
/// rows force `Z1111 ≥ 180` and `Z1111 + Z1121 ≤ 350`, so `Z1121 ≤ 170`. The valid big-M is
/// 170. No amount of unconditional propagation finds it — the bound does not exist until the
/// binary is pinned. Gurobi tightens exactly this row to 170, and this pass reproduces that
/// number: dcmulti's pre-cut root LP moves 184,034.38 -> 184,136.65 and its tree 1,433 -> 899
/// nodes.
///
/// # The rule, and why it is exact
///
/// Work in the `<=` frame, on a ONE-SIDED row `a·y + Σ_k a_k x_k ≤ b` with `y` a binary whose
/// box is exactly `[0,1]` (a `>=` row is negated into this frame; an equality or range row is
/// untouchable — its two sides share the coefficients). Over the feasible set the row says
/// exactly two things:
///
/// ```text
/// y = 0:   rest ≤ b            y = 1:   rest ≤ b − a
/// ```
///
/// One of those two levels is the one `y` RELAXES — the level the big-M pays for: `y = 1` when
/// `a < 0`, `y = 0` when `a > 0`. Let `R` be a valid upper bound on `rest` CONDITIONAL on `y`
/// taking that value — here, the fixpoint of the SAME exact propagation with `y` pinned — and
/// let `d` be the slack it leaves:
///
/// ```text
/// a < 0:   d = (b − a) − R      apply  a ← a + d                (b unchanged)
/// a > 0:   d =  b      − R      apply  a ← a − d,  b ← b − d
/// ```
///
/// applied only when `0 < d < |a|`, so the coefficient shrinks toward zero and never crosses
/// it. This is [`tighten_coefficients`]'s rule at `ū = 1` / `l̄ = 0` with the box activity `U'`
/// replaced by the conditional `R`, and the validity argument is two lines rather than that
/// rule's case analysis, because a binary has only two levels:
///
/// * **Nothing is cut off.** The rewrite touches ONE level's right-hand side and lowers it to
///   `R`. Every feasible point at that level has `rest ≤ R` — that is what the conditional
///   bound says — so every feasible point still satisfies the row. The OTHER level's
///   right-hand side is algebraically unchanged (`a<0`: `b` itself; `a>0`: `b − a`, and both
///   move by `d`), so points there are untouched.
/// * **Nothing is let in.** A point of the new model's box has `y ∈ {0,1}`, and the new row's
///   right-hand side at each of those two values is `≤` the old row's, so the new row implies
///   the old one pointwise.
///
/// Because the two feasible sets are EQUAL, a conditional bound derived from the pre-rewrite
/// model stays valid for the post-rewrite one: applications compose, and rewriting one row
/// never invalidates a bound another row's rewrite is about to use.
///
/// The LP relaxation is strictly stronger where it matters: for `y ∈ [0,1]` the new row reads
/// `rest ≤ b'(1−y) + (b'−a')·y`, a term-by-term tightening of the old `b(1−y) + (b−a)y`.
///
/// # What is deliberately NOT done, and the measurement that decided it
///
/// The rule generalises: tighten BOTH levels (`b' = min(b, R_0)`, `b'−a' = min(b−a, R_1)`),
/// which also licenses `|a|` to GROW and the coefficient to reach zero. That version was
/// implemented and measured on the 17-instance corpus, and it is NET NEGATIVE:
///
/// ```text
///            nodes            root bound_cut       what it rewrote
///   dcmulti  1433 ->  899     +105.2              the VUB big-Ms (this rule)
///   qnet1     372 -> 1518      −52.5              a 546 -> 672 coefficient GROWTH
///   mod010   1701 -> 1851       0.0               16 -> 20 growth on a covering row
///   gen        11 ->   22       0.0               −45 -> 0, coefficient erased
/// ```
///
/// The extra rewrites are valid and they do strengthen the LP term-by-term, but on qnet1 and
/// mod010 they moved the pre-cut bound by exactly ZERO while moving the optimal basis — and a
/// moved basis is a different Gomory tableau, which cost qnet1 a cut and 52 points of root
/// closure. Strengthening a row the LP was not sitting on buys nothing and perturbs everything.
/// So the shipped rule is the big-M direction only: `|a|` shrinks or nothing happens.
///
/// # Scope, and why it is not the whole matrix
///
/// A candidate row must have a non-binary column in its rest. `|a|` is a BIG-M only when it
/// pays for a continuous or general-integer quantity; on a pure 0/1 row it is a knapsack
/// coefficient, the conditional analysis there is implication structure, and that is
/// [`crate::probe`]'s business (cliques and forced fixings), not a coefficient rewrite. The
/// filter is also what makes the pass affordable: it takes the pure-binary instances
/// (mas74, mas76, pk1, p0201, misc07) to zero candidates and therefore zero cost.
///
/// # Exactness discipline
///
/// Identical to [`tighten_coefficients`]: the conditional bounds are exact rationals read off
/// the propagation WORKSPACE, not off an output model — the output policy discards a continuous
/// column's finite bound, which is precisely the bound this pass exists to use — and a rewrite
/// is applied only when both the new coefficient and the new right-hand side convert to `f64`
/// EXACTLY. Skipping any subset of rewrites is sound; each one's validity reads only its own
/// row and one conditional fixpoint.
///
/// A probe side that comes back INFEASIBLE means the binary is forced. That is real domain
/// reduction, but it is [`crate::probe`]'s product, not this pass's: such a binary is skipped.
///
/// Returns how many coefficients were rewritten.
pub(crate) fn tighten_coefficients_conditional(
    model: &mut Model,
    deadline: Option<std::time::Instant>,
) -> usize {
    use ay_lra::rational::Rational;
    if model.has_inexact_coeffs() {
        return 0;
    }
    let expired = || deadline.is_some_and(|d| std::time::Instant::now() >= d);
    let n = model.num_cols();
    let nr = model.num_rows();
    let integral: Vec<bool> = (0..n)
        .map(|j| model.col_kind(Col(j as u32)).is_integral())
        .collect();
    // A column that is NOT a 0/1 box: the quantity a big-M can be paying for.
    let wide: Vec<bool> = (0..n)
        .map(|j| model.col_bounds(Col(j as u32)) != (0.0, 1.0))
        .collect();

    // ROW ELIGIBILITY, fixed up front: one-sided (so the coefficients are not shared with a
    // second side) and carrying at least one non-0/1 column (see "Scope" above). `Some(flip)`
    // says the finite side is the LOWER one, i.e. the row is negated into the `<=` frame.
    // Sidedness and support are never changed by this pass, so this survives the rewrites.
    let flip_of: Vec<Option<bool>> = (0..nr)
        .map(|r| {
            let row = &model.rows[r];
            if row.coeffs.len() < 2 || !row.coeffs.iter().any(|&(c, _)| wide[c as usize]) {
                return None;
            }
            match (row.lb.is_finite(), row.ub.is_finite()) {
                (false, true) => Some(false),
                (true, false) => Some(true),
                _ => None,
            }
        })
        .collect();

    // CANDIDATES: free binaries (box exactly `[0,1]`, integral kind — a general integer boxed
    // to `[0,1]` is a binary) in at least one eligible row, in column order. `need` records
    // WHICH level each one is probed at: only the level its coefficient relaxes is ever read,
    // so a binary that only ever appears with one sign costs one propagation, not two.
    let mut rows_of: Vec<Vec<u32>> = vec![Vec::new(); n];
    let mut need = vec![[false; 2]; n];
    for r in 0..nr {
        let Some(flip) = flip_of[r] else { continue };
        for &(c, a) in &model.rows[r].coeffs {
            let j = c as usize;
            if !integral[j] || wide[j] || a == 0.0 {
                continue;
            }
            rows_of[j].push(r as u32);
            need[j][usize::from((if flip { -a } else { a }) < 0.0)] = true;
        }
    }
    let nnz: usize = model
        .rows
        .iter()
        .map(|r| r.coeffs.len())
        .sum::<usize>()
        .max(1);
    let mut budget = COND_WORK_BUDGET / nnz;
    let mut scout_budget = COND_SCOUT_BUDGET / nnz;
    let one = BigRational::one();
    let min_gain = exact(MIN_GAIN).expect("MIN_GAIN is finite");
    let debug = crate::debug_flags::milp_debug_flags().coef_tighten_debug;
    let mut applied = 0usize;

    // FLOAT SCOUT (advice lane, same bargain as `scout_plan`'s). A candidate costs an exact
    // rational propagation over the whole matrix, and on every instance measured OUTSIDE the
    // fixed-charge family every one of those propagations comes back with nothing: qnet1 spent
    // 0.84s over 1,288 binaries for zero rewrites, mas74 1.07s for zero. So the probe is
    // mirrored in f64 first and the exact lane runs only for a candidate the mirror says has a
    // material, in-range `d` somewhere. Floats ADVISE which binaries are worth exact work; every
    // applied rewrite is still decided in exact rationals. A scout miss (float noise hiding a
    // just-past-threshold `d`) costs a tightening, never correctness — not tightening is always
    // sound.
    let scout = crate::tune::caller_flag(crate::tune::Knob::NoCondScout) != Some(true);
    let (mut flo, mut fup) = (vec![0.0f64; n], vec![0.0f64; n]);
    for j in 0..n {
        let (l, u) = model.col_bounds(Col(j as u32));
        flo[j] = l;
        fup[j] = u;
    }
    let nowatch = vec![false; n];

    // The box every probe starts from, built once (empty until a candidate needs it).
    let mut base: Option<(Vec<Option<Rational>>, Vec<Option<Rational>>)> = None;

    for y in 0..n {
        if rows_of[y].is_empty() {
            continue;
        }
        let sides = usize::from(need[y][0]) + usize::from(need[y][1]);
        if sides > budget || expired() {
            break; // everything applied so far is valid on its own
        }
        if scout {
            if scout_budget == 0 {
                break; // the advice lane is spent; skipping candidates is always sound
            }
            scout_budget -= 1;
            if !cond_scout_worth_it(
                model,
                y,
                &need[y],
                &rows_of[y],
                &flip_of,
                &flo,
                &fup,
                &integral,
                &nowatch,
            ) {
                continue;
            }
        }
        budget -= sides;
        let (base_lo, base_up) = base.get_or_insert_with(|| {
            let mut lo = Vec::with_capacity(n);
            let mut up = Vec::with_capacity(n);
            for j in 0..n {
                let (l, u) = model.col_bounds(Col(j as u32));
                lo.push(exact_small(l));
                up.push(exact_small(u));
            }
            (lo, up)
        });
        // The probe, on the model AS IT STANDS (earlier rewrites preserved its feasible set
        // exactly, so a fixpoint derived now is valid for the original model too).
        let mut fix = [None, None];
        for (v, slot) in fix.iter_mut().enumerate() {
            if !need[y][v] {
                continue;
            }
            let (mut lo, mut up) = (base_lo.clone(), base_up.clone());
            lo[y] = Some(Rational::new(v as i64, 1));
            up[y] = Some(Rational::new(v as i64, 1));
            if propagate(model, deadline, None, &integral, &mut lo, &mut up, false) {
                *slot = Some((lo, up));
            }
            // Propagation infeasible under this fixing = the binary is FORCED, which is
            // `crate::probe`'s product; `slot` stays `None` and every row of `y` is skipped.
        }

        for ri in 0..rows_of[y].len() {
            let r = rows_of[y][ri] as usize;
            let flip = flip_of[r].expect("eligible row");
            let signed = |a: f64| if flip { -a } else { a };
            let Some(i) = model.rows[r]
                .coeffs
                .iter()
                .position(|&(c, _)| c as usize == y)
            else {
                continue;
            };
            let a = exact(signed(model.rows[r].coeffs[i].1)).expect("finite coefficient");
            if a.is_zero() {
                continue;
            }
            let b_hat = exact(signed(if flip {
                model.rows[r].lb
            } else {
                model.rows[r].ub
            }))
            .expect("finite side");
            // The level `y` RELAXES: `y = 1` when the coefficient is negative, `y = 0` when it
            // is positive. That level's right-hand side is the big-M this pass shrinks.
            let level = usize::from(a.is_negative());
            let Some((lo, up)) = fix[level].as_ref() else {
                continue;
            };

            // The most the REST of the row can reach under that fixpoint. `None` if any needed
            // bound is still open — the rule wants a real ceiling, not a guess.
            let mut rest = BigRational::zero();
            let mut open = false;
            for (k, &(c, av)) in model.rows[r].coeffs.iter().enumerate() {
                if k == i {
                    continue;
                }
                let av = exact(signed(av)).expect("finite coefficient");
                if av.is_zero() {
                    continue;
                }
                let side = if av.is_positive() {
                    up[c as usize].as_ref()
                } else {
                    lo[c as usize].as_ref()
                };
                match side {
                    Some(b) => rest += av * b.to_big(),
                    None => {
                        open = true;
                        break;
                    }
                }
            }
            if open {
                continue;
            }

            // The slack the conditional ceiling leaves at the relaxed level.
            let d = if level == 1 {
                (&b_hat - &a) - &rest
            } else {
                &b_hat - &rest
            };
            // Material on both sides, exactly as `tighten_coefficients` gates it: `d` big
            // enough to be worth a changed model, and `|a| − d` big enough that the surviving
            // coefficient is not numerical dust (which also enforces `d < |a|` strictly;
            // `d ≥ |a|` says the row is redundant at this level, and it is left alone).
            let scale = {
                let abs = a.abs();
                if abs > one {
                    abs
                } else {
                    one.clone()
                }
            };
            let floor_gain = &min_gain * &scale;
            if d <= floor_gain || a.abs() - &d <= floor_gain {
                continue;
            }
            let (a_new, b_new) = if level == 1 {
                (&a + &d, b_hat.clone())
            } else {
                (&a - &d, &b_hat - &d)
            };
            // Fail closed: apply only if BOTH survive the trip back to f64 exactly.
            let (Some(af), Some(bf)) = (as_exact_f64(&a_new), as_exact_f64(&b_new)) else {
                continue;
            };
            if debug {
                eprintln!(
                    "COND_TIGHTEN row {r} col {y}: a {} -> {af} | rhs {} -> {bf} (y={level}, d {d})",
                    signed(model.rows[r].coeffs[i].1),
                    signed(if flip {
                        model.rows[r].lb
                    } else {
                        model.rows[r].ub
                    }),
                );
            }
            model.rows[r].coeffs[i].1 = signed(af);
            if flip {
                model.rows[r].lb = signed(bf);
            } else {
                model.rows[r].ub = signed(bf);
            }
            applied += 1;
        }
    }
    applied
}

/// Float mirror of one candidate binary's probe, for [`tighten_coefficients_conditional`].
///
/// Runs the same pin-and-propagate cascade in `f64` (through [`scout_row`], which applies with
/// HALF the exact lane's gain gate and therefore over-tightens — the safe direction for a
/// scout: a smaller `R` means a bigger `d`, so a borderline candidate is OVER-detected and
/// merely costs exact work) and reports whether any eligible row of `y` would then show a
/// material, in-range `d`. `true` means "spend the exact propagation"; `false` skips the
/// candidate, which costs at most a tightening and never correctness.
///
/// The threshold is deliberately half the exact gate and the range test is one-sided-loose, so
/// float noise around either end of `0 < d < |a|` resolves toward running the exact lane.
#[allow(clippy::too_many_arguments)]
fn cond_scout_worth_it(
    model: &Model,
    y: usize,
    need: &[bool; 2],
    rows: &[u32],
    flip_of: &[Option<bool>],
    base_lo: &[f64],
    base_up: &[f64],
    integral: &[bool],
    nowatch: &[bool],
) -> bool {
    for level in 0..2 {
        if !need[level] {
            continue;
        }
        let (mut lo, mut up) = (base_lo.to_vec(), base_up.to_vec());
        lo[y] = level as f64;
        up[y] = level as f64;
        let mut suspicious = false;
        for _ in 0..ROUNDS {
            let mut changed = false;
            for r in 0..model.num_rows() {
                match scout_row(model, r, &mut lo, &mut up, integral, nowatch, nowatch) {
                    // A float-suspected infeasibility (the pin may FORCE the binary) is handed
                    // to the exact lane rather than judged here.
                    ScoutRow::Suspicious => {
                        suspicious = true;
                        break;
                    }
                    ScoutRow::Moved { .. } => changed = true,
                    ScoutRow::Clean => {}
                }
            }
            if suspicious {
                return true;
            }
            if !changed {
                break;
            }
        }
        for &r in rows {
            let r = r as usize;
            let Some(flip) = flip_of[r] else { continue };
            let signed = |a: f64| if flip { -a } else { a };
            let (coeffs, rlb, rub) = model.row(Row(r as u32));
            let Some(a) = coeffs
                .iter()
                .find(|&&(c, _)| c as usize == y)
                .map(|&(_, a)| signed(a))
            else {
                continue;
            };
            if (a < 0.0) != (level == 1) || a == 0.0 {
                continue; // this row reads the OTHER level
            }
            let b = signed(if flip { rlb } else { rub });
            let mut rest = 0.0f64;
            let mut open = false;
            for &(c, av) in coeffs {
                if c as usize == y {
                    continue;
                }
                let av = signed(av);
                let side = if av > 0.0 {
                    up[c as usize]
                } else {
                    lo[c as usize]
                };
                if !side.is_finite() {
                    open = true;
                    break;
                }
                rest += av * side;
            }
            if open || !rest.is_finite() {
                continue;
            }
            let d = if level == 1 { b - a - rest } else { b - rest };
            let gate = 0.5 * MIN_GAIN * a.abs().max(1.0);
            if d > gate && a.abs() - d > gate {
                return true;
            }
        }
    }
    false
}

/// The f64 that denotes `v` exactly, if one exists. Anything else — too many mantissa bits,
/// out of range — is `None`: the caller must skip, not round.
pub(crate) fn as_exact_f64(v: &BigRational) -> Option<f64> {
    let f = v.to_f64()?;
    if !f.is_finite() {
        return None;
    }
    (BigRational::from_float(f).as_ref() == Some(v)).then_some(f)
}

/// Apply one derived bound, if it is genuinely tighter. Returns whether it moved.
///
/// `lower` says which side this is; `integral` licenses the round to an integer, which for an
/// integer column is not an approximation but a consequence — `x >= 7/2` and `x` an integer
/// together say `x >= 4`.
fn tighten(
    cur: &mut Option<ay_lra::rational::Rational>,
    b: ay_lra::rational::Rational,
    lower: bool,
    integral: bool,
) -> bool {
    use ay_lra::rational::Rational;
    let b = if integral {
        // `Rational::ceil`/`floor` return the integer; wrap it back up. Exact,
        // like the `BigRational` path this replaced.
        if lower {
            Rational::from_integer(b.ceil())
        } else {
            Rational::from_integer(b.floor())
        }
    } else {
        b
    };
    match cur {
        None => {
            *cur = Some(b);
            true
        }
        Some(c) => {
            let better = if lower { b > *c } else { b < *c };
            if !better {
                return false;
            }
            // Ignore a tightening too small to pay for itself -- and, more to the point, too
            // small to be anything but the tail of a float coefficient.
            // (`to_big().to_f64()`, not `approx_f64`: bit-identical to the
            // `BigRational` comparison this code has always made.)
            let gain = (&b - c).abs();
            let scale = std::cmp::max(c.abs(), Rational::new(1, 1));
            let worth = gain.to_big().to_f64().unwrap_or(0.0)
                > MIN_GAIN * scale.to_big().to_f64().unwrap_or(1.0);
            if worth {
                *cur = Some(b);
                true
            } else {
                false
            }
        }
    }
}

/// A rational to an `f64` that is certainly on the outside of it.
fn round_out(v: &BigRational, down: bool) -> f64 {
    let Some(f) = v.to_f64() else {
        return if down {
            f64::NEG_INFINITY
        } else {
            f64::INFINITY
        };
    };
    if !f.is_finite() {
        return f;
    }
    // `to_f64` rounds to nearest, which may land INSIDE the true bound. One ulp outward is
    // always safe and costs nothing.
    let back = BigRational::from_float(f).expect("finite");
    if down {
        if back <= *v {
            f
        } else {
            next_toward(f, f64::NEG_INFINITY)
        }
    } else if back >= *v {
        f
    } else {
        next_toward(f, f64::INFINITY)
    }
}

fn next_toward(f: f64, to: f64) -> f64 {
    if f == to {
        return f;
    }
    let bits = f.to_bits();
    let up = to > f;
    let next = if f == 0.0 {
        if up {
            1
        } else {
            (1u64 << 63) | 1
        }
    } else if (f > 0.0) == up {
        bits + 1
    } else {
        bits - 1
    };
    f64::from_bits(next)
}

// ---------------------------------------------------------------------------
// STRUCTURAL REDUCTION: free / implied-free singleton-column substitution.
//
// The rest of this module TIGHTENS bounds and coefficients; it never changes a
// model's row/column identity, which is why its output is consumed
// transparently by a search and a certificate machinery that both re-derive in
// the caller's frame. This section is the one exception: it removes a column
// AND a row, and so it comes with an explicit postsolve map (`SingletonPostsolve`)
// that lifts a reduced-model solution back to the caller's column space. It is
// used exactly like the duplicate-column presolve in `bab.rs` (build a reduced
// model + map, solve, expand the outcome, fail-closed on any tree certificate).
// ---------------------------------------------------------------------------

use crate::model::ColKind;

/// The recovery rule for one eliminated singleton column: its value is a linear
/// function of the SURVIVING columns of its defining (equality) row.
///
/// `x = (b − Σ_k a_k · z_k) / a`, where the `z_k` are the surviving columns,
/// indexed by their ORIGINAL column number (they are all populated in the
/// widened vector before any recovery runs, because an eliminated column has
/// degree 1 — it appears in no other column's defining row).
pub(crate) struct Recover {
    /// Original column index of the eliminated variable `x`.
    pub(crate) col: usize,
    /// The ORIGINAL row index of `x`'s defining equality.
    ///
    /// The recovery rule itself does not need it — `widen` reads `a`, `b` and
    /// `rest`. The CERTIFICATE lift does: the deleted/rebounded equality is the
    /// only original fact that carries a coefficient on `col`, so lifting a
    /// reduced certificate has to be able to name the row the verifier will
    /// price (see [`crate::cert_lift`]).
    pub(crate) row: usize,
    /// `x`'s coefficient in its defining row (nonzero, exact).
    pub(crate) a: BigRational,
    /// The defining row's right-hand side `b` (it is an equality).
    pub(crate) b: BigRational,
    /// `(original survivor column, its coefficient a_k)` for every other column
    /// of the defining row.
    pub(crate) rest: Vec<(usize, BigRational)>,
}

/// Which original row a surviving REDUCED row is.
///
/// `substitute_singletons` emits reduced rows in original order, skipping the
/// dropped ones, so a reduced row handle is not an original row handle. A
/// certificate proved against the reduced model cites reduced rows; the lift
/// needs this to say which original fact each one IS.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum SingletonRowOrigin {
    /// The reduced row is original row `.0`, verbatim: same coefficients over
    /// the surviving columns (an eliminated column has degree 1, so it appears
    /// in no row but its own defining one) and the same two bounds.
    Kept(usize),
    /// The reduced row is the FORCING RANGE that replaced original equality row
    /// `orig` when the eliminated column was not implied-free. `recover` indexes
    /// [`SingletonPostsolve::recover`], which holds the eliminated column and
    /// its exact coefficient in `orig`.
    Rebound {
        /// The original equality row this range came from.
        orig: usize,
        /// Index into [`SingletonPostsolve::recover`].
        recover: usize,
    },
}

/// What becomes of the defining row of an eliminated singleton.
enum RowFate {
    /// The row is copied unchanged (no singleton eliminated from it).
    Keep,
    /// `x` was implied-free: recovering it lands inside its box for every
    /// feasible survivor assignment, so the row is redundant and dropped.
    Drop,
    /// `x` was NOT implied-free: the row survives as a forcing inequality over
    /// the survivors, `lb ≤ Σ a_k z_k ≤ ub`, encoding `x ∈ [lo, up]`.
    Rebound(f64, f64),
}

/// How to lift a solution of the singleton-reduced model back to the caller's
/// full column space, and how to correct a reported objective value.
pub(crate) struct SingletonPostsolve {
    pub(crate) n_orig: usize,
    /// Original column -> reduced column, or `None` if the column was eliminated.
    pub(crate) map: Vec<Option<Col>>,
    /// One entry per eliminated column.
    pub(crate) recover: Vec<Recover>,
    /// One entry per REDUCED row, in reduced row order: which original row it
    /// is and how. Written as the reduced rows are emitted.
    pub(crate) row_origin: Vec<SingletonRowOrigin>,
    /// The constant the eliminated columns' objective contributions fold into.
    /// It is NOT carried in the reduced model's `f64` offset (it need not be
    /// representable): it is added to the reported value at expansion time,
    /// where the value is an exact `BigRational`.
    pub(crate) const_delta: BigRational,
}

impl SingletonPostsolve {
    /// The constant to add to a reduced-model objective value / dual bound to
    /// recover the caller-frame value.
    pub(crate) fn const_delta(&self) -> &BigRational {
        &self.const_delta
    }

    /// Widen a reduced-model point (length = reduced column count) to the
    /// caller's full column space, recovering each eliminated column exactly.
    pub(crate) fn widen(&self, reduced: &[BigRational]) -> Vec<BigRational> {
        let mut full = vec![BigRational::zero(); self.n_orig];
        for (orig, slot) in self.map.iter().enumerate() {
            if let Some(nc) = slot {
                if let Some(v) = reduced.get(nc.index()) {
                    full[orig] = v.clone();
                }
            }
        }
        // Every recovery references SURVIVORS only (already filled above), so a
        // single pass suffices — no dependency ordering among eliminations.
        for rec in &self.recover {
            let mut s = rec.b.clone();
            for (k, ak) in &rec.rest {
                s -= ak * &full[*k];
            }
            full[rec.col] = &s / &rec.a;
        }
        full
    }
}

/// Substitute out continuous singleton columns on equality rows, deleting one
/// column and either deleting or rebounding its defining row.
///
/// # The rule, and why it preserves the exact optimum
///
/// A column `x` that is CONTINUOUS and appears in exactly ONE row `r`, where
/// `r` is an equality `a·x + Σ_k a_k z_k = b` (`a ≠ 0`), is UNIQUELY determined
/// by the others: `x = (b − Σ_k a_k z_k) / a`. Delete `x`; when its declared
/// box is implied by the survivors' boxes, delete `r` as redundant. Otherwise
/// replace `r` by the equivalent range on the survivors that enforces `x`'s
/// lower and upper bounds. Fold `x`'s objective contribution
/// `c_x·x = (c_x/a)·b − Σ_k (c_x·a_k/a)·z_k` into the surviving objective (the
/// linear part onto the `z_k`, the constant into `const_delta`).
///
/// * **Forward** (original → reduced): drop `x`; the surviving rows never
///   mention it (degree 1). Drop an implied-free defining row, or replace it by
///   the range obtained by substituting `x`'s box. The folded objective equals
///   the original at the surviving columns, so feasible maps to feasible at
///   equal cost.
/// * **Backward** (reduced → original): recover `x` by the formula. It satisfies
///   row `r` by construction. Its box follows either from the implied-free test
///   or from the retained forcing range. All other rows are unchanged and
///   independent of `x`.
///
/// The two feasible sets are therefore in exact objective-preserving
/// correspondence: the optima are EQUAL, and every witness lifts by `widen`.
///
/// # Guards (all fail-closed — a skipped column is always sound)
///
/// * inexact-coefficient models are declined wholesale (the reasoning reads the
///   `f64` matrix as exact, as the rest of presolve does);
/// * a row is a candidate only if it has EXACTLY ONE eligible degree-1 column,
///   so deleting it cannot orphan a second one;
/// * a non-implied-free box is translated to a forcing range only when both
///   finite sides convert back to `f64` exactly;
/// * the objective fold is applied only if every changed survivor coefficient
///   converts back to `f64` EXACTLY (the constant rides an exact `BigRational`,
///   so it is unconstrained).
///
/// Returns `None` when nothing is eliminated (the caller then solves the
/// original model untouched).
pub(crate) fn substitute_singletons(model: &Model) -> Option<(Model, SingletonPostsolve)> {
    if model.has_inexact_coeffs() {
        return None;
    }
    let n = model.num_cols();
    let nr = model.num_rows();

    // Column degree: how many rows each column appears in.
    let mut deg = vec![0u32; n];
    for r in 0..nr {
        let (coeffs, _, _) = model.row(Row(r as u32));
        for &(c, _) in coeffs {
            deg[c as usize] += 1;
        }
    }

    if crate::debug_flags::milp_debug_flags().trace {
        let cont = (0..n)
            .filter(|&j| model.col_kind(Col(j as u32)) == ColKind::Continuous)
            .count();
        let cont_deg1 = (0..n)
            .filter(|&j| model.col_kind(Col(j as u32)) == ColKind::Continuous && deg[j] == 1)
            .count();
        let eq_rows = (0..nr)
            .filter(|&r| {
                let (_, lb, ub) = model.row(Row(r as u32));
                lb.is_finite() && ub.is_finite() && lb == ub
            })
            .count();
        // Degree-1 continuous columns whose single row is an equality.
        let mut singleton_in_eq = 0;
        for r in 0..nr {
            let (coeffs, lb, ub) = model.row(Row(r as u32));
            if !(lb.is_finite() && ub.is_finite() && lb == ub) {
                continue;
            }
            for &(c, _) in coeffs {
                if deg[c as usize] == 1 && model.col_kind(Col(c)) == ColKind::Continuous {
                    singleton_in_eq += 1;
                }
            }
        }
        eprintln!(
            "--trace singleton-sub: cols={n} cont={cont} cont_deg1={cont_deg1} eq_rows={eq_rows}/{nr} cont_singletons_in_eq={singleton_in_eq}"
        );
    }

    // Objective as exact rationals; folded in place as columns are eliminated.
    let mut obj: Vec<BigRational> = (0..n)
        .map(|j| exact(model.obj_coeff(Col(j as u32))).expect("finite objective coefficient"))
        .collect();
    let mut const_delta = BigRational::zero();
    let mut eliminated = vec![false; n];
    let mut recover: Vec<Recover> = Vec::new();
    // Original row -> its `recover` entry, for the rows that eliminated a column.
    let mut recover_of_row: Vec<Option<usize>> = vec![None; nr];
    let mut row_fate: Vec<RowFate> = (0..nr).map(|_| RowFate::Keep).collect();
    let diag = crate::debug_flags::milp_debug_flags().trace;
    let (mut sk_multi, mut sk_range, mut sk_obj, mut n_drop, mut n_rebound) = (0, 0, 0, 0, 0);

    // Cached exact box bounds (None == infinite).
    let bound = |j: usize| -> (Option<BigRational>, Option<BigRational>) {
        let (l, u) = model.col_bounds(Col(j as u32));
        (exact(l), exact(u))
    };

    for r in 0..nr {
        let (coeffs, rlb, rub) = model.row(Row(r as u32));
        // Equality rows only: a range or one-sided row does not pin `x`.
        if !(rlb.is_finite() && rub.is_finite() && rlb == rub) {
            continue;
        }
        // The eligible degree-1 continuous columns of this row.
        let mut eligible = coeffs.iter().map(|&(c, _)| c as usize).filter(|&c| {
            deg[c] == 1 && !eliminated[c] && model.col_kind(Col(c as u32)) == ColKind::Continuous
        });
        let Some(x) = eligible.next() else {
            continue;
        };
        if eligible.next().is_some() {
            // Two degree-1 columns here: eliminating one orphans the other
            // (it would appear in no row). Leave the whole row alone.
            sk_multi += 1;
            continue;
        }
        let a = coeffs
            .iter()
            .find(|&&(c, _)| c as usize == x)
            .map(|&(_, a)| a)
            .expect("x is in this row");
        if a == 0.0 {
            continue;
        }
        let a = exact(a).expect("finite");
        let b = exact(rlb).expect("finite equality rhs");
        let a_pos = a.is_positive();

        // The rest of the row's reachable activity range over the current boxes.
        // `None` on a side means it is infinite (an open survivor bound in the
        // direction that side reads).
        let mut rest_min = Some(BigRational::zero());
        let mut rest_max = Some(BigRational::zero());
        let mut rest: Vec<(usize, BigRational)> =
            Vec::with_capacity(coeffs.len().saturating_sub(1));
        for &(c, ak) in coeffs {
            let c = c as usize;
            if c == x {
                continue;
            }
            let ak = exact(ak).expect("finite");
            let (lo_k, up_k) = bound(c);
            let (at_min, at_max) = if ak.is_positive() {
                (&lo_k, &up_k)
            } else {
                (&up_k, &lo_k)
            };
            rest_min = match (rest_min, at_min) {
                (Some(s), Some(bk)) => Some(s + &ak * bk),
                _ => None,
            };
            rest_max = match (rest_max, at_max) {
                (Some(s), Some(bk)) => Some(s + &ak * bk),
                _ => None,
            };
            rest.push((c, ak));
        }

        // Implied bounds on x = (b − rest)/a, and the IMPLIED-FREE test against
        // x's declared box. `a > 0`: x_ub uses rest_min, x_lb uses rest_max.
        let (decl_lo, decl_up) = bound(x);
        let implied_ub = if a_pos { &rest_min } else { &rest_max };
        let implied_lb = if a_pos { &rest_max } else { &rest_min };
        // Upper side free: x's declared upper is +inf, or the implied upper
        // exists and does not exceed it.
        let upper_free = match &decl_up {
            None => true,
            Some(u) => implied_ub
                .as_ref()
                .is_some_and(|rest_side| &(&(&b - rest_side) / &a) <= u),
        };
        let lower_free = match &decl_lo {
            None => true,
            Some(l) => implied_lb
                .as_ref()
                .is_some_and(|rest_side| &(&(&b - rest_side) / &a) >= l),
        };
        let implied_free = upper_free && lower_free;

        // When NOT implied-free, `x`'s box `[lo, up]` must still be enforced.
        // Substitute `a·x = b − Σ a_k z_k` into `lo ≤ x ≤ up`: the equality row
        // becomes a forcing inequality on the survivors,
        //   a > 0:  b − a·up  ≤  Σ a_k z_k  ≤  b − a·lo
        //   a < 0:  b − a·lo  ≤  Σ a_k z_k  ≤  b − a·up
        // (an infinite `x`-bound leaves the corresponding row side infinite).
        // The bounds must convert to f64 EXACTLY or the reduction is declined
        // for this column (fail closed). Implied-free rows skip this — they are
        // redundant and simply dropped.
        let fate = if implied_free {
            RowFate::Drop
        } else {
            let (nlb_r, nub_r) = if a_pos {
                (
                    decl_up.as_ref().map(|u| &b - &(&a * u)),
                    decl_lo.as_ref().map(|l| &b - &(&a * l)),
                )
            } else {
                (
                    decl_lo.as_ref().map(|l| &b - &(&a * l)),
                    decl_up.as_ref().map(|u| &b - &(&a * u)),
                )
            };
            let to_f = |o: &Option<BigRational>, inf: f64| match o {
                None => Some(inf),
                Some(v) => as_exact_f64(v),
            };
            let (Some(nlb_f), Some(nub_f)) =
                (to_f(&nlb_r, f64::NEG_INFINITY), to_f(&nub_r, f64::INFINITY))
            else {
                sk_range += 1;
                continue; // range bound not exactly f64-representable: decline
            };
            RowFate::Rebound(nlb_f, nub_f)
        };

        // Objective fold, exact-f64 fail-closed. c_x·x = (c_x/a)·b − Σ (c_x·a_k/a)·z_k.
        let cx = obj[x].clone();
        if !cx.is_zero() {
            // Tentative new coefficients for the survivors; commit only if ALL
            // convert back to f64 exactly (else the reduced objective would be a
            // rounded proxy and could hide the true optimum).
            let mut updates: Vec<(usize, BigRational)> = Vec::with_capacity(rest.len());
            let mut ok = true;
            for (c, ak) in &rest {
                let new_c = &obj[*c] - &(&cx * ak) / &a;
                if as_exact_f64(&new_c).is_none() {
                    ok = false;
                    break;
                }
                updates.push((*c, new_c));
            }
            if !ok {
                sk_obj += 1;
                continue;
            }
            for (c, new_c) in updates {
                obj[c] = new_c;
            }
            const_delta += &(&cx * &b) / &a;
            obj[x] = BigRational::zero();
        }

        match fate {
            RowFate::Drop => n_drop += 1,
            RowFate::Rebound(..) => n_rebound += 1,
            RowFate::Keep => {}
        }
        eliminated[x] = true;
        row_fate[r] = fate;
        recover_of_row[r] = Some(recover.len());
        recover.push(Recover {
            col: x,
            row: r,
            a,
            b,
            rest,
        });
    }

    if diag {
        eprintln!(
            "--trace singleton-sub: eliminated={} (drop={n_drop} rebound={n_rebound}) skipped: multi_deg1={sk_multi} range_inexact={sk_range} obj_inexact={sk_obj}",
            recover.len()
        );
    }

    if recover.is_empty() {
        return None;
    }

    // Build the reduced model: surviving columns in original order, surviving
    // rows remapped (dropped or reboundd per `row_fate`), the folded objective
    // (exact f64), the ORIGINAL offset (the eliminated constant rides
    // `const_delta`, applied at expansion).
    let mut out = Model::new();
    out.inherit_ft_adoption_solve_latch(model);
    let mut map: Vec<Option<Col>> = vec![None; n];
    for j in 0..n {
        if eliminated[j] {
            continue;
        }
        let col = Col(j as u32);
        let (lb, ub) = model.col_bounds(col);
        let nc = match model.col_kind(col) {
            ColKind::Continuous => out.add_col(lb, ub),
            ColKind::Binary => out.add_binary_col(),
            ColKind::Integer => out.add_int_col(lb, ub),
        };
        out.cols[nc.index()].lb = lb;
        out.cols[nc.index()].ub = ub;
        map[j] = Some(nc);
    }
    // Reduced rows are emitted in original order with the dropped ones skipped,
    // so `row_origin` is built HERE, in lockstep with `add_row`, rather than
    // re-derived later from `row_fate` — a re-derivation could drift from the
    // emission order and a certificate lift would then cite the wrong row.
    let mut row_origin: Vec<SingletonRowOrigin> = Vec::with_capacity(nr);
    for r in 0..nr {
        let (lb, ub, origin) = match row_fate[r] {
            RowFate::Drop => continue,
            RowFate::Keep => {
                let (_, lb, ub) = model.row(Row(r as u32));
                (lb, ub, SingletonRowOrigin::Kept(r))
            }
            RowFate::Rebound(lb, ub) => (
                lb,
                ub,
                SingletonRowOrigin::Rebound {
                    orig: r,
                    recover: recover_of_row[r]?,
                },
            ),
        };
        let (coeffs, _, _) = model.row(Row(r as u32));
        let mapped: Vec<(Col, f64)> = coeffs
            .iter()
            .filter_map(|&(c, a)| map[c as usize].map(|nc| (nc, a)))
            .collect();
        out.add_row(lb, ub, &mapped);
        debug_assert_eq!(
            row_origin.len() + 1,
            out.num_rows(),
            "row_origin must be indexed by REDUCED row"
        );
        row_origin.push(origin);
    }
    let obj_terms: Vec<(Col, f64)> = (0..n)
        .filter_map(|j| {
            map[j].and_then(|nc| {
                let f = as_exact_f64(&obj[j]).expect("survivor objective is exact by construction");
                (f != 0.0).then_some((nc, f))
            })
        })
        .collect();
    out.set_objective(&obj_terms, model.sense());
    out.set_objective_offset(model.objective_offset());

    if crate::debug_flags::milp_debug_flags().trace {
        let onz: usize = (0..nr).map(|r| model.row(Row(r as u32)).0.len()).sum();
        let rnz: usize = (0..out.num_rows())
            .map(|r| out.row(Row(r as u32)).0.len())
            .sum();
        eprintln!(
            "--trace singleton-sub: eliminated {} col ({n_drop} row-drop, {n_rebound} row-rebound); model {}r/{}c/{}nnz -> {}r/{}c/{}nnz",
            recover.len(),
            nr,
            n,
            onz,
            out.num_rows(),
            out.num_cols(),
            rnz,
        );
    }

    let post = SingletonPostsolve {
        n_orig: n,
        map,
        recover,
        row_origin,
        const_delta,
    };
    Some((out, post))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::model::Sense;

    mod scout_skip;

    /// The case the whole module is for: a column the modeller left open above, which a row
    /// pins anyway.
    #[test]
    fn a_row_gives_an_unbounded_column_a_finite_upper_bound() {
        let mut m = Model::new();
        let x = m.add_col(0.0, f64::INFINITY);
        let y = m.add_col(0.0, 10.0);
        // 2x + y <= 30, y >= 0  =>  x <= 15
        m.add_row(f64::NEG_INFINITY, 30.0, &[(x, 2.0), (y, 1.0)]);
        m.set_objective(&[(x, 1.0)], Sense::Maximize);

        let Presolved::Tightened(out) = tighten_bounds(&m, None) else {
            panic!("the model is feasible");
        };
        let (lo, up) = out.col_bounds(x);
        assert_eq!(lo, 0.0);
        assert!(
            (up - 15.0).abs() < 1e-9,
            "x should be pinned at 15, got {up}"
        );
    }

    /// An integer column may be rounded to the integer the bound admits -- that is a
    /// consequence of integrality, not an approximation of it.
    #[test]
    fn an_integer_column_rounds_to_the_integer_the_bound_admits() {
        let mut m = Model::new();
        let x = m.add_int_col(0.0, 100.0);
        // 2x <= 7  =>  x <= 3.5  =>  x <= 3
        m.add_row(f64::NEG_INFINITY, 7.0, &[(x, 2.0)]);
        m.set_objective(&[(x, 1.0)], Sense::Maximize);

        let Presolved::Tightened(out) = tighten_bounds(&m, None) else {
            panic!("the model is feasible");
        };
        assert_eq!(out.col_bounds(x).1, 3.0);
    }

    #[test]
    fn contradictory_bounds_are_reported_as_infeasible() {
        let mut m = Model::new();
        let x = m.add_col(5.0, 10.0);
        m.add_row(f64::NEG_INFINITY, 4.0, &[(x, 1.0)]); // x <= 4 and x >= 5
        assert!(matches!(tighten_bounds(&m, None), Presolved::Infeasible));
    }

    /// The Crowder–Johnson–Padberg classic: `5x + 3y <= 6` over binaries tightens to
    /// `2x + 2y <= 2` (the same integer set as `x + y <= 1`, with a strictly stronger
    /// LP relaxation than the original).
    #[test]
    fn classic_binary_knapsack_coefficients_tighten() {
        let mut m = Model::new();
        let x = m.add_binary_col();
        let y = m.add_binary_col();
        m.add_row(f64::NEG_INFINITY, 6.0, &[(x, 5.0), (y, 3.0)]);
        m.set_objective(&[(x, 1.0), (y, 1.0)], Sense::Maximize);

        let n = tighten_coefficients(&mut m, None);
        assert_eq!(n, 2, "both coefficients should move");
        let (coeffs, lb, ub) = m.row(Row(0));
        assert_eq!(coeffs, &[(0, 2.0), (1, 2.0)]);
        assert_eq!(ub, 2.0);
        assert_eq!(lb, f64::NEG_INFINITY);
    }

    /// The `>=` mirror: `5x + 3y >= 4` over binaries tightens to `4x + 3y >= 4`
    /// (x = 1 alone already meets the bound, so its coefficient carries slack).
    #[test]
    fn ge_rows_tighten_through_the_negated_frame() {
        let mut m = Model::new();
        let x = m.add_binary_col();
        let y = m.add_binary_col();
        m.add_row(4.0, f64::INFINITY, &[(x, 5.0), (y, 3.0)]);

        let n = tighten_coefficients(&mut m, None);
        assert_eq!(n, 1);
        let (coeffs, lb, ub) = m.row(Row(0));
        assert_eq!(coeffs, &[(0, 4.0), (1, 3.0)]);
        assert_eq!(lb, 4.0);
        assert_eq!(ub, f64::INFINITY);
    }

    /// The general-integer form binds at the TOP LEVEL, not at 1:
    /// `4x + 3y <= 10`, `x` integer in `[0, 2]`, `y` binary, tightens to `x + y <= 2`.
    #[test]
    fn general_integer_columns_tighten_at_their_top_level() {
        let mut m = Model::new();
        let x = m.add_int_col(0.0, 2.0);
        let y = m.add_binary_col();
        m.add_row(f64::NEG_INFINITY, 10.0, &[(x, 4.0), (y, 3.0)]);

        let n = tighten_coefficients(&mut m, None);
        assert_eq!(n, 2);
        let (coeffs, _, ub) = m.row(Row(0));
        assert_eq!(coeffs, &[(0, 1.0), (1, 1.0)]);
        assert_eq!(ub, 2.0);
    }

    /// Rows that are equalities, ranges, or that involve a continuous column's coefficient
    /// are exactly the ones the rule must NOT touch — and a model with nothing to tighten
    /// comes back bit-identical.
    #[test]
    fn untouchable_rows_are_untouched() {
        let mut m = Model::new();
        let x = m.add_binary_col();
        let y = m.add_col(0.0, 1.0); // continuous
        let z = m.add_binary_col();
        m.add_row(6.0, 6.0, &[(x, 5.0), (y, 3.0)]); // equality: shared coefficients
        m.add_row(0.0, 6.0, &[(x, 5.0), (z, 3.0)]); // range: shared coefficients
        m.add_row(f64::NEG_INFINITY, 6.0, &[(y, 5.0)]); // continuous column: rule unproven
        m.add_row(f64::NEG_INFINITY, 1.0, &[(x, 1.0), (z, 1.0)]); // already as tight as it gets
        let before = m.clone();

        let n = tighten_coefficients(&mut m, None);
        assert_eq!(n, 0);
        for r in 0..m.num_rows() {
            let (ca, la, ua) = m.row(Row(r as u32));
            let (cb, lb, ub) = before.row(Row(r as u32));
            assert_eq!(ca, cb);
            assert_eq!(la.to_bits(), lb.to_bits());
            assert_eq!(ua.to_bits(), ub.to_bits());
        }
    }

    /// The load-bearing property, checked exhaustively: coefficient tightening preserves the
    /// integer feasible set EXACTLY — nothing cut off, nothing let in — on random one- and
    /// two-sided rows over small integer boxes.
    #[test]
    fn coefficient_tightening_preserves_the_integer_set_exactly() {
        let mut seed = 123_456_789u64;
        let mut rnd = || {
            seed = seed.wrapping_mul(6_364_136_223_846_793_005).wrapping_add(1);
            (seed >> 33) as i64
        };
        for _ in 0..300 {
            let mut m = Model::new();
            let cols: Vec<_> = (0..4).map(|_| m.add_int_col(0.0, 3.0)).collect();
            for _ in 0..3 {
                let terms: Vec<_> = cols
                    .iter()
                    .map(|&c| (c, (rnd() % 11 - 5) as f64))
                    .filter(|&(_, a)| a != 0.0)
                    .collect();
                if terms.is_empty() {
                    continue;
                }
                let b = (rnd() % 19 - 4) as f64;
                if rnd() % 2 == 0 {
                    m.add_row(f64::NEG_INFINITY, b, &terms);
                } else {
                    m.add_row(b, f64::INFINITY, &terms);
                }
            }
            let mut t = m.clone();
            tighten_coefficients(&mut t, None);
            for a in 0..4 {
                for b in 0..4 {
                    for c in 0..4 {
                        for d in 0..4 {
                            let p: Vec<BigRational> = [a, b, c, d]
                                .iter()
                                .map(|&v| BigRational::from_integer(v.into()))
                                .collect();
                            assert_eq!(
                                m.check_point(&p).is_ok(),
                                t.check_point(&p).is_ok(),
                                "integer point {p:?} changed feasibility"
                            );
                        }
                    }
                }
            }
        }
    }

    /// THE dcmulti SHAPE, end to end: the conditional rule must reach the number Gurobi
    /// reaches, and it must take TWO hops to get there.
    ///
    /// ```text
    ///   180·D − Z1111        ≤ 0      (D = 1 forces Z1111 ≥ 180)
    ///   Z1111 + Z1121 − X    = 0      (X ≤ 350 caps the pair)
    ///  −600·D + Z1121        ≤ 0      (the big-M this test is about)
    /// ```
    ///
    /// Base propagation proves `Z1121 ≤ 350` and the UNCONDITIONAL rule takes 600 -> 350 —
    /// that much is [`tighten_coefficients`]'s job and is asserted here so the test fails if
    /// the conditional pass is silently doing the unconditional pass's work. Conditional on
    /// `D = 1` the first two rows give `Z1121 ≤ 350 − 180 = 170`, which no unconditional
    /// reasoning can see, and the big-M is 170.
    #[test]
    fn the_vub_big_m_falls_to_its_conditional_ceiling() {
        let mut m = Model::new();
        let d = m.add_binary_col();
        let z1 = m.add_col(0.0, f64::INFINITY);
        let z2 = m.add_col(0.0, f64::INFINITY);
        let x = m.add_col(0.0, 350.0);
        m.add_row(f64::NEG_INFINITY, 0.0, &[(d, 180.0), (z1, -1.0)]);
        m.add_row(0.0, 0.0, &[(z1, 1.0), (z2, 1.0), (x, -1.0)]);
        let vub = m.num_rows();
        m.add_row(f64::NEG_INFINITY, 0.0, &[(d, -600.0), (z2, 1.0)]);

        let Presolved::Tightened(mut out) = tighten_bounds(&m, None) else {
            panic!("feasible");
        };
        let big_m = |mm: &Model| {
            let (coeffs, _, _) = mm.row(Row(vub as u32));
            coeffs
                .iter()
                .find(|&&(c, _)| c == d.0)
                .map(|&(_, a)| a)
                .expect("D is in the VUB row")
        };
        // The conditional pass was default-on briefly (2026-07-26) and REVERTED to opt-in on
        // 2026-07-29 after it measured 3.1x WORSE on dcmulti under later changes. So the
        // pipeline again stops at the unconditional rule, and the staged progression is the
        // thing to pin: the unconditional rule reaches -350, and the conditional pass -- which
        // is still exactly sound, just no longer a default -- takes it to Gurobi's -170.
        assert_eq!(big_m(&out), -350.0, "unconditional rule reaches 350");
        assert_eq!(
            tighten_coefficients_conditional(&mut out, None),
            1,
            "the conditional pass rewrites exactly the one VUB row"
        );
        assert_eq!(big_m(&out), -170.0, "conditional rule reaches Gurobi's 170");

        // And it cut nothing off: every point the ORIGINAL admits, on a grid dense enough to
        // straddle both big-Ms, survives.
        for di in 0..2 {
            for zi in 0..36 {
                for xi in 0..36 {
                    let (z2v, xv) = (zi as f64 * 10.0, xi as f64 * 10.0);
                    let z1v = xv - z2v;
                    let p: Vec<BigRational> = [f64::from(di), z1v, z2v, xv]
                        .iter()
                        .map(|&v| BigRational::from_float(v).expect("finite"))
                        .collect();
                    if m.check_point(&p).is_ok() {
                        assert!(
                            out.check_point(&p).is_ok(),
                            "conditional rule cut off {p:?}"
                        );
                    }
                }
            }
        }
    }

    /// THE LOAD-BEARING PROPERTY for the conditional rule, checked EXHAUSTIVELY: it preserves
    /// the feasible set exactly — nothing cut off, nothing let in.
    ///
    /// Every column is integral, so the lattice enumerated below IS the feasible set and there
    /// is no sampling gap: any rewrite that moved a single point in either direction fails.
    /// (Two general integers give the rule the non-0/1 column its eligibility filter wants.)
    #[test]
    fn conditional_tightening_preserves_the_integer_set_exactly() {
        let mut seed = 0x5eed_1234_abcd_0001u64;
        let mut rnd = || {
            seed = seed.wrapping_mul(6_364_136_223_846_793_005).wrapping_add(1);
            (seed >> 33) as i64
        };
        let mut rewrites = 0usize;
        for _ in 0..400 {
            let mut m = Model::new();
            let bins: Vec<_> = (0..3).map(|_| m.add_binary_col()).collect();
            let gis: Vec<_> = (0..2).map(|_| m.add_int_col(0.0, 3.0)).collect();
            let cols: Vec<_> = bins.iter().chain(gis.iter()).copied().collect();
            for _ in 0..3 {
                let terms: Vec<_> = cols
                    .iter()
                    .map(|&c| (c, (rnd() % 13 - 6) as f64))
                    .filter(|&(_, a)| a != 0.0)
                    .collect();
                if terms.len() < 2 {
                    continue;
                }
                let b = (rnd() % 17 - 5) as f64;
                if rnd() % 2 == 0 {
                    m.add_row(f64::NEG_INFINITY, b, &terms);
                } else {
                    m.add_row(b, f64::INFINITY, &terms);
                }
            }
            let mut t = m.clone();
            rewrites += tighten_coefficients_conditional(&mut t, None);
            for mask in 0..8u32 {
                for g0 in 0..4 {
                    for g1 in 0..4 {
                        let p: Vec<BigRational> = [
                            i64::from((mask >> 2) & 1),
                            i64::from((mask >> 1) & 1),
                            i64::from(mask & 1),
                            g0,
                            g1,
                        ]
                        .iter()
                        .map(|&v| BigRational::from_integer(v.into()))
                        .collect();
                        assert_eq!(
                            m.check_point(&p).is_ok(),
                            t.check_point(&p).is_ok(),
                            "conditional rewrite changed the feasibility of {p:?}"
                        );
                    }
                }
            }
        }
        // A guard that never fires is not a guard: the sweep must actually exercise the rule.
        assert!(rewrites > 0, "no conditional rewrite was exercised");
    }

    /// The same property with a CONTINUOUS column in the mix — the shape the pass exists for.
    /// The continuous column is sampled rather than enumerated, so this is the weaker of the
    /// two guards; it is here because the exhaustive one cannot reach a mixed model.
    #[test]
    fn conditional_tightening_is_sound_with_a_continuous_column() {
        let mut seed = 0xfeed_face_0bad_cafeu64;
        let mut rnd = || {
            seed = seed.wrapping_mul(6_364_136_223_846_793_005).wrapping_add(1);
            (seed >> 33) as i64
        };
        let mut rewrites = 0usize;
        for _ in 0..400 {
            let mut m = Model::new();
            let b0 = m.add_binary_col();
            let b1 = m.add_binary_col();
            let gi = m.add_int_col(0.0, 3.0);
            let cont = m.add_col(0.0, 4.0);
            let cols = [b0, b1, gi, cont];
            for _ in 0..3 {
                let terms: Vec<_> = cols
                    .iter()
                    .map(|&c| (c, (rnd() % 11 - 5) as f64))
                    .filter(|&(_, a)| a != 0.0)
                    .collect();
                if terms.len() < 2 {
                    continue;
                }
                let rhs = (rnd() % 15 - 4) as f64;
                if rnd() % 2 == 0 {
                    m.add_row(f64::NEG_INFINITY, rhs, &terms);
                } else {
                    m.add_row(rhs, f64::INFINITY, &terms);
                }
            }
            let mut t = m.clone();
            rewrites += tighten_coefficients_conditional(&mut t, None);
            for a in 0..2 {
                for b in 0..2 {
                    for g in 0..4 {
                        for cv in 0..17 {
                            let p: Vec<BigRational> = vec![
                                BigRational::from_integer(a.into()),
                                BigRational::from_integer(b.into()),
                                BigRational::from_integer(g.into()),
                                BigRational::from_float(f64::from(cv) * 0.25).expect("finite"),
                            ];
                            assert_eq!(
                                m.check_point(&p).is_ok(),
                                t.check_point(&p).is_ok(),
                                "conditional rewrite changed the feasibility of {p:?}"
                            );
                        }
                    }
                }
            }
        }
        assert!(rewrites > 0, "no conditional rewrite was exercised");
    }

    /// The rows the conditional rule must not touch — equalities and ranges (their two sides
    /// share the coefficients) and rows with no non-0/1 column (a knapsack coefficient is not
    /// a big-M) — come back bit-identical.
    #[test]
    fn conditional_tightening_leaves_untouchable_rows_alone() {
        let mut m = Model::new();
        let y = m.add_binary_col();
        let z = m.add_binary_col();
        let x = m.add_col(0.0, 3.0);
        m.add_row(6.0, 6.0, &[(y, -9.0), (x, 1.0)]); // equality
        m.add_row(-9.0, 6.0, &[(y, -9.0), (x, 1.0)]); // range
        m.add_row(f64::NEG_INFINITY, 0.0, &[(y, -9.0), (z, 1.0)]); // pure 0/1: not a big-M
        m.add_row(f64::NEG_INFINITY, 3.0, &[(z, 1.0)]); // single term
        let before = m.clone();
        assert_eq!(tighten_coefficients_conditional(&mut m, None), 0);
        for r in 0..m.num_rows() {
            let (ca, la, ua) = m.row(Row(r as u32));
            let (cb, lb, ub) = before.row(Row(r as u32));
            assert_eq!(ca, cb);
            assert_eq!(la.to_bits(), lb.to_bits());
            assert_eq!(ua.to_bits(), ub.to_bits());
        }
    }

    /// The float scout only ADVISES. Whatever it skips, the rewrites it does let through must
    /// be a subset of what the exact lane alone would apply — and on the shape the pass exists
    /// for it must let the rewrite through at all.
    #[test]
    fn the_scout_is_advice_and_never_invents_a_rewrite() {
        let mut seed = 0x0123_4567_89ab_cdefu64;
        let mut rnd = || {
            seed = seed.wrapping_mul(6_364_136_223_846_793_005).wrapping_add(1);
            (seed >> 33) as i64
        };
        for _ in 0..200 {
            let mut m = Model::new();
            let b0 = m.add_binary_col();
            let b1 = m.add_binary_col();
            let gi = m.add_int_col(0.0, 3.0);
            for _ in 0..3 {
                let terms: Vec<_> = [b0, b1, gi]
                    .iter()
                    .map(|&c| (c, (rnd() % 11 - 5) as f64))
                    .filter(|&(_, a)| a != 0.0)
                    .collect();
                if terms.len() < 2 {
                    continue;
                }
                m.add_row(f64::NEG_INFINITY, (rnd() % 13 - 4) as f64, &terms);
            }
            // The scout path (default) against the exact-only path, on the same input.
            let (mut scouted, mut exact_only) = (m.clone(), m.clone());
            let n_scouted = tighten_coefficients_conditional(&mut scouted, None);
            // SAFETY: single-threaded test, and the name is read only inside the call below.
            unsafe { std::env::set_var("the no-cond-scout knob", "1") };
            let n_exact = tighten_coefficients_conditional(&mut exact_only, None);
            unsafe { std::env::remove_var("the no-cond-scout knob") };
            assert!(
                n_scouted <= n_exact,
                "the scout let through {n_scouted} rewrites the exact lane would not have made \
                 ({n_exact})"
            );
            for r in 0..m.num_rows() {
                let (cs, ls, us) = scouted.row(Row(r as u32));
                let (co, lo_, uo) = m.row(Row(r as u32));
                let (ce, le, ue) = exact_only.row(Row(r as u32));
                // A scouted row is either untouched or exactly what the exact lane produced.
                let untouched =
                    cs == co && ls.to_bits() == lo_.to_bits() && us.to_bits() == uo.to_bits();
                let agreed =
                    cs == ce && ls.to_bits() == le.to_bits() && us.to_bits() == ue.to_bits();
                assert!(untouched || agreed, "scouted row {r} matches neither arm");
            }
        }
    }

    /// Tightening must never cut off a feasible point. Random rows, random boxes: every point
    /// the ORIGINAL model admits must still be admitted after propagation.
    #[test]
    fn propagation_never_cuts_off_a_feasible_point() {
        let mut seed = 987_654_321u64;
        let mut rnd = || {
            seed = seed.wrapping_mul(6_364_136_223_846_793_005).wrapping_add(1);
            (seed >> 33) as i64
        };
        for _ in 0..200 {
            let mut m = Model::new();
            let cols: Vec<_> = (0..4).map(|_| m.add_int_col(0.0, 6.0)).collect();
            for _ in 0..3 {
                let terms: Vec<_> = cols
                    .iter()
                    .map(|&c| (c, (rnd() % 7 - 3) as f64))
                    .filter(|&(_, a)| a != 0.0)
                    .collect();
                if terms.is_empty() {
                    continue;
                }
                m.add_row(f64::NEG_INFINITY, (rnd() % 15) as f64, &terms);
            }
            let Presolved::Tightened(out) = tighten_bounds(&m, None) else {
                continue; // proven empty: nothing to preserve
            };
            // Every integer point of the box the ORIGINAL model calls feasible.
            for a in 0..7 {
                for b in 0..7 {
                    for c in 0..7 {
                        for d in 0..7 {
                            let p: Vec<BigRational> = [a, b, c, d]
                                .iter()
                                .map(|&v| BigRational::from_integer(v.into()))
                                .collect();
                            if m.check_point(&p).is_ok() {
                                assert!(
                                    out.check_point(&p).is_ok(),
                                    "propagation cut off a feasible point {p:?}"
                                );
                            }
                        }
                    }
                }
            }
        }
    }

    /// SCOUT GUARD: a binary fixing that exists ONLY through an intermediate
    /// continuous tightening (which itself never ships — finite continuous
    /// bounds are discarded at output). The scout's restricted replay cannot
    /// reproduce the visible value from the visible row alone, so it must
    /// fall back to the full exact lane — and the binary must still be fixed.
    #[test]
    fn scout_falls_back_on_cascade_dependent_visible_moves() {
        let mut m = Model::new();
        let y = m.add_int_col(0.0, 1.0);
        let x = m.add_col(0.0, 100.0);
        // x <= 3 (workspace-only: x's finite continuous bound never ships).
        m.add_row(f64::NEG_INFINITY, 3.0, &[(x, 1.0)]);
        // 2y - x <= -2: with x <= 3 this says 2y <= 1, so y (integer) <= 0.
        // With only x's ORIGINAL ub 100 it says 2y <= 98 — no move. The
        // visible fix is real only through the cascade.
        m.add_row(f64::NEG_INFINITY, -2.0, &[(y, 2.0), (x, -1.0)]);
        m.set_objective(&[(y, 1.0)], Sense::Maximize);
        let Presolved::Tightened(out) = tighten_bounds(&m, None) else {
            panic!("the model is feasible");
        };
        let (_, yu) = out.col_bounds(y);
        assert_eq!(yu, 0.0, "the cascade-dependent binary fix must survive");
        // The discarded continuous bound really is discarded (output policy).
        let (_, xu) = out.col_bounds(x);
        assert_eq!(xu, 100.0);
    }

    // --- Free / implied-free singleton-column substitution --------------------

    /// The obvious clean case: a FREE continuous column that appears in exactly
    /// one equality row is substituted out, deleting the column and dropping the
    /// (now redundant) row; the eliminated value is recovered exactly by `widen`.
    #[test]
    fn free_singleton_is_dropped_and_recovered_exactly() {
        let mut m = Model::new();
        let z = m.add_int_col(0.0, 5.0);
        let x = m.add_col(f64::NEG_INFINITY, f64::INFINITY); // free continuous singleton
                                                             // x + 2 z = 7  =>  x = 7 - 2 z, x is free so this is IMPLIED-FREE.
        m.add_row(7.0, 7.0, &[(x, 1.0), (z, 2.0)]);
        m.set_objective(&[(x, 3.0), (z, 1.0)], Sense::Minimize);

        let (reduced, post) = substitute_singletons(&m).expect("x is an eligible singleton");
        assert_eq!(reduced.num_cols(), 1, "x removed");
        assert_eq!(reduced.num_rows(), 0, "the redundant equality dropped");

        // Reduced objective: 3x + z = 3(7-2z) + z = 21 - 5z; const_delta = 21,
        // the surviving linear coefficient on z is -5.
        assert_eq!(post.const_delta(), &BigRational::from_integer(21.into()));
        assert_eq!(reduced.obj_coeff(Col(0)), -5.0);

        // widen a reduced point z = 2  =>  full (z=2, x=7-4=3).
        let full = post.widen(&[BigRational::from_integer(2.into())]);
        assert_eq!(full.len(), 2);
        assert_eq!(full[0], BigRational::from_integer(2.into())); // z
        assert_eq!(full[1], BigRational::from_integer(3.into())); // x = 7 - 2*2
        assert!(m.check_point(&full).is_ok(), "recovered point is feasible");
    }

    /// A BOUNDED singleton is not implied-free: its box must still be enforced,
    /// so the equality becomes a forcing inequality over the survivors. The
    /// column is still removed and recovered exactly.
    #[test]
    fn bounded_singleton_becomes_a_forcing_inequality() {
        let mut m = Model::new();
        let z = m.add_int_col(0.0, 10.0);
        let x = m.add_col(0.0, 4.0); // bounded continuous singleton
                                     // x + z = 10  =>  x = 10 - z, and x in [0,4]  =>  z in [6,10].
        m.add_row(10.0, 10.0, &[(x, 1.0), (z, 1.0)]);
        m.set_objective(&[(z, 1.0)], Sense::Minimize);

        let (reduced, post) = substitute_singletons(&m).expect("eligible");
        assert_eq!(reduced.num_cols(), 1);
        assert_eq!(
            reduced.num_rows(),
            1,
            "row survives as a forcing inequality"
        );
        // The forcing row on z: a>0, [b - a*up, b - a*lo] = [10-4, 10-0] = [6, 10].
        let (coeffs, lb, ub) = reduced.row(Row(0));
        assert_eq!(coeffs, &[(0, 1.0)]);
        assert_eq!(lb, 6.0);
        assert_eq!(ub, 10.0);

        // z = 6 recovers x = 4 (at its upper bound); feasible.
        let full = post.widen(&[BigRational::from_integer(6.into())]);
        assert_eq!(full[1], BigRational::from_integer(4.into()));
        assert!(m.check_point(&full).is_ok());
        // z = 5 would recover x = 5 > 4 — and the forcing inequality (z >= 6)
        // correctly forbids it in the reduced model.
        let bad = m.check_point(&[
            BigRational::from_integer(5.into()),
            BigRational::from_integer(5.into()),
        ]);
        assert!(bad.is_err(), "x=5 violates x<=4 in the original too");
    }

    /// A row with TWO degree-1 continuous columns must be left alone: eliminating
    /// one would orphan the other (leave it in no row at all).
    #[test]
    fn a_row_with_two_singletons_is_left_alone() {
        let mut m = Model::new();
        let x = m.add_col(f64::NEG_INFINITY, f64::INFINITY);
        let y = m.add_col(f64::NEG_INFINITY, f64::INFINITY);
        m.add_row(5.0, 5.0, &[(x, 1.0), (y, 1.0)]); // both x and y are singletons here
        m.set_objective(&[(x, 1.0), (y, 1.0)], Sense::Minimize);
        assert!(
            substitute_singletons(&m).is_none(),
            "two singletons in one row: no safe elimination"
        );
    }

    /// An objective fold that does not land back on an exact f64 is declined
    /// (fail-closed): the reduced objective must never be a rounded proxy.
    #[test]
    fn inexact_objective_fold_is_declined() {
        let mut m = Model::new();
        let z = m.add_int_col(0.0, 10.0);
        let x = m.add_col(f64::NEG_INFINITY, f64::INFINITY);
        // 3 x + z = 1  =>  x = (1 - z)/3.  Objective 1·x folds z's coefficient by
        // -1/3, which is not representable in f64 — so x must NOT be eliminated.
        m.add_row(1.0, 1.0, &[(x, 3.0), (z, 1.0)]);
        m.set_objective(&[(x, 1.0)], Sense::Minimize);
        assert!(
            substitute_singletons(&m).is_none(),
            "an inexact objective fold must be declined"
        );
    }

    /// A zero-objective singleton has nothing to fold, so it is always eligible
    /// (the exactness guard is vacuous) regardless of coefficients.
    #[test]
    fn zero_objective_singleton_folds_with_no_exactness_risk() {
        let mut m = Model::new();
        let z = m.add_int_col(0.0, 10.0);
        let x = m.add_col(f64::NEG_INFINITY, f64::INFINITY);
        // 3 x + z = 1, but x has NO objective — the /3 never touches the objective.
        m.add_row(1.0, 1.0, &[(x, 3.0), (z, 1.0)]);
        m.set_objective(&[(z, 1.0)], Sense::Minimize);
        let (reduced, post) = substitute_singletons(&m).expect("eligible, no objective fold");
        assert_eq!(reduced.num_cols(), 1);
        assert!(post.const_delta().is_zero());
    }

    /// The load-bearing property, checked by brute force: substitution preserves
    /// the EXACT optimum. Random models with a continuous singleton in an equality
    /// row (plus survivor-only side rows) are minimized two ways — directly, and
    /// through `substitute_singletons` (+ `const_delta`, + `widen` re-check) — and
    /// the optima must match. Non-vacuous: the reduction is asserted to fire.
    #[test]
    fn singleton_substitution_preserves_the_optimum() {
        let mut seed = 0x51_9101_2026u64;
        let mut rnd = || {
            seed = seed.wrapping_mul(6_364_136_223_846_793_005).wrapping_add(1);
            (seed >> 33) as i64
        };
        let mut fired = 0usize;
        for _case in 0..400 {
            let k = 3usize; // integer survivor columns
            let mut m = Model::new();
            let survivors: Vec<Col> = (0..k).map(|_| m.add_int_col(0.0, 4.0)).collect();
            // The continuous singleton: half the time free, half bounded.
            let (xlo, xup) = if rnd() % 2 == 0 {
                (f64::NEG_INFINITY, f64::INFINITY)
            } else {
                (0.0, (2 + rnd().rem_euclid(6)) as f64)
            };
            let x = m.add_col(xlo, xup);
            // Equality row: a·x + Σ a_k z_k = b, a ∈ {±1, ±2}. Keep a ∈ {±1} most
            // of the time so the objective fold is usually exact (a=±2 halves).
            let a = [1.0, -1.0, 1.0, 2.0][(rnd().rem_euclid(4)) as usize];
            let mut terms = vec![(x, a)];
            for &z in &survivors {
                let c = rnd().rem_euclid(5) - 2;
                if c != 0 {
                    terms.push((z, c as f64));
                }
            }
            let b = (rnd().rem_euclid(9) - 2) as f64;
            m.add_row(b, b, &terms);
            // A survivor-only side inequality, so x stays a genuine singleton.
            let sterms: Vec<(Col, f64)> = survivors
                .iter()
                .map(|&z| (z, (rnd().rem_euclid(5) - 2) as f64))
                .filter(|&(_, c)| c != 0.0)
                .collect();
            if !sterms.is_empty() {
                m.add_row(f64::NEG_INFINITY, (rnd().rem_euclid(10)) as f64, &sterms);
            }
            // Objective over survivors and (sometimes) x.
            let mut obj: Vec<(Col, f64)> = survivors
                .iter()
                .map(|&z| (z, (rnd().rem_euclid(7) - 3) as f64))
                .collect();
            if rnd() % 2 == 0 {
                obj.push((x, (rnd().rem_euclid(5) - 2) as f64));
            }
            m.set_objective(&obj, Sense::Minimize);

            let Some((reduced, post)) = substitute_singletons(&m) else {
                continue;
            };
            fired += 1;

            // Brute-force the ORIGINAL optimum over integer survivor assignments;
            // x is pinned by the equality and must land in its box.
            let val = |model: &Model, p: &[BigRational]| -> BigRational {
                let mut v = exact(model.objective_offset()).unwrap();
                for (j, pj) in p.iter().enumerate() {
                    v += exact(model.obj_coeff(Col(j as u32))).unwrap() * pj;
                }
                v
            };
            let mut best_orig: Option<BigRational> = None;
            let mut best_reduced: Option<BigRational> = None;
            let ra = exact(a).unwrap();
            let rb = exact(b).unwrap();
            let rest: Vec<(usize, BigRational)> = terms
                .iter()
                .filter(|&&(c, _)| c != x)
                .map(|&(c, ak)| (c.index(), exact(ak).unwrap()))
                .collect();
            for code in 0..5i64.pow(k as u32) {
                let zi: Vec<i64> = (0..k).map(|t| (code / 5i64.pow(t as u32)) % 5).collect();
                // x = (b - Σ a_k z_k)/a.
                let mut s = rb.clone();
                for (c, ak) in &rest {
                    s -= ak * BigRational::from_integer(zi[*c].into());
                }
                let xval = &s / &ra;
                // Full original point.
                let mut full = vec![BigRational::zero(); m.num_cols()];
                for (t, &z) in survivors.iter().enumerate() {
                    full[z.index()] = BigRational::from_integer(zi[t].into());
                }
                full[x.index()] = xval.clone();
                if m.check_point(&full).is_ok() {
                    let v = val(&m, &full);
                    best_orig = Some(best_orig.map_or(v.clone(), |cur| cur.min(v)));
                }
                // Reduced point: survivors in reduced order.
                let mut rp = vec![BigRational::zero(); reduced.num_cols()];
                for (t, &z) in survivors.iter().enumerate() {
                    if let Some(nc) = post.map[z.index()] {
                        rp[nc.index()] = BigRational::from_integer(zi[t].into());
                    }
                }
                if reduced.check_point(&rp).is_ok() {
                    let v = val(&reduced, &rp) + post.const_delta();
                    best_reduced = Some(best_reduced.map_or(v.clone(), |cur| cur.min(v.clone())));
                    // The widened reduced point must be feasible in the original
                    // and attain exactly the same value.
                    let w = post.widen(&rp);
                    assert!(
                        m.check_point(&w).is_ok(),
                        "widened reduced point infeasible in the original"
                    );
                    assert_eq!(val(&m, &w), v, "widened value mismatch");
                }
            }
            assert_eq!(
                best_orig, best_reduced,
                "substitution changed the optimum (case seed {seed:#x})"
            );
        }
        assert!(fired > 50, "test is vacuous: only {fired} cases fired");
    }
}
