// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Deep continuous-elimination chain aggregation for c-MIR.

use super::*;

// ---------------------------------------------------------------------------------------------
// DEEP CONTINUOUS-ELIMINATION ("CHAIN") AGGREGATION — a NETWORK WALK feeding the existing cMIR.
// ---------------------------------------------------------------------------------------------

/// A base row wider than this is not worth walking, and a row narrower than
/// [`CHAIN_AGG_MIN_BASE_NNZ`] is already inside the single-row and 3-step families' reach.
const CHAIN_AGG_MIN_BASE_NNZ: usize = 24;
/// How many cancellable continuous columns a base row must carry before the walk is worth
/// starting. Below this the 3-step `separate_mir_agg` already covers the whole chain.
const CHAIN_AGG_MIN_TARGETS: usize = 8;
/// Belt-and-braces stop. The walk is ALREADY bounded: every accepted step removes exactly one
/// negative-coefficient continuous column and (by the progress rule) creates none, so it
/// terminates in at most `#targets` steps.
const CHAIN_AGG_MAX_DEPTH: usize = 1024;
/// How many base rows one call may walk.
const CHAIN_AGG_MAX_BASES: usize = 32;

/// Trace predicate for this family, `OnceLock`-cached ON PURPOSE. `tests/env_ledger.rs`'s
/// live-read ratchet asks for exactly this shape — the structure-recognition lanes routed nine
/// bare `--trace` predicates through module-local caches for the same reason — and a
/// DIAGNOSTIC switch, unlike an arm selector, is never flipped mid-process by a test.
fn chain_trace() -> bool {
    static ON: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *ON.get_or_init(|| crate::debug_flags::milp_debug_flags().trace)
}

/// A two-column partner row in one fixed orientation, ready to be added with a positive
/// multiplier: `sgn·row <= sgn·rhs`, `cols` its two ORIENTED coefficients.
struct ChainRow {
    row: u32,
    rhs: BigRational,
    cols: [(usize, BigRational); 2],
}

/// DEEP CONTINUOUS-ELIMINATION AGGREGATION — the c-MIR half `separate_mir_agg` structurally
/// cannot reach, on the fixed-charge network shape.
///
/// # ⚠ MEASURED NEGATIVE ON ITS ONLY TARGET. OPT-IN (`with_chain_agg(true)`), DEFAULT-OFF.
///
/// It does everything it was built to do and the bound does not move. Recorded here in full so
/// nobody builds it a second time.
///
/// The walk reaches the aggregate exactly as designed: all four of qiu's capacity rows complete
/// their 66-step chain and land on `Σ_{66 arcs} x_j <= 48` (`agg_nnz=66, b=48`), and the c-MIR of
/// that row is violated by **0.261715** — the number the design note predicted, to five decimals.
/// Then both of the things that decide the family go against it:
///
/// ```text
///   SELECTION   cut nnz 77, violation 0.261715, EFFICACY 0.000742
///               against `default_root_cut_eff_floor` = 1e-3 (bab.rs:5947).
///               It is DERIVED AND DISCARDED. The 66 continuous columns carry ±1, but the VUB
///               substitution drags in the switch binaries at their arc capacities (up to 22.23),
///               so ‖a‖ ≈ 353 and a violation of a quarter of a unit is a depth of 7e-4.
///
///   BOUND       forcing it in with `--cut-eff-floor`, qiu's root LP is
///               -7278.428478 at round 0, 1, 2 AND 3 — bit-identical, `gain=0`.
///               The class then DRIES UP: round 3 separates zero. So three rows is everything
///               this family will ever have to say at qiu's root, and it is worth 0.000.
///               In the shipped root-cut posture (`diag root-closure`, presolve off) the whole
///               loop closes `gain=0.84823507968` with 4 cuts; admitting the two chain cuts
///               takes it to 6 cuts and `gain=0.84823507968` — the SAME 11 digits, against the
///               798.77 Gurobi parity needs.
///
///   WALL        admitted (floor 5e-4) vs the shipped default, 3 runs each, serial and idle:
///                 admitted  28.278 / 28.135 / 28.243 s   4116 nodes, all three
///                 default   25.803 / 25.887 / 25.847 s   4116 nodes, all three
///               +2.37 s (+9.2%) on a BYTE-IDENTICAL tree. The exact "denser root row paid at
///               every node" failure `MAX_CUT_NNZ=300` already recorded on this instance.
/// ```
///
/// The mechanism is dual degeneracy, not a weak cut: the cut IS violated and IS tight after the
/// re-solve, and the LP simply walks to another vertex of the same optimal face. qiu's root gap
/// is not a chain-aggregation gap, and this closes that lead.
///
/// Kept in the tree because it is correct, tested and cheap — it is the only aggregator here that
/// can reach depth 66 — but it must be asked for.
///
/// # Why the existing aggregator cannot get here, measured rather than argued
///
/// `separate_mir_agg` is a PAIRWISE, three-step, greedy walk: it cancels the ONE column whose
/// bound substitution costs the rounding most, with one θ, and stops after `MIR_AGG_STEPS = 3`.
/// On qiu (fixed-charge network flow, 1192x840, 48 binary + 792 continuous) that is three of the
/// wrong thing:
///
/// * its base-row gate is `any column fractional and integral`, and qiu's four capacity rows
///   (`c661..c664`, 198 nonzeros each) contain **no integer column at all** — the binaries enter
///   only later, through the VUB substitution inside `mir_build_subs`. So the capacity rows are
///   never even considered;
/// * and the depth is 3 where the answer needs 66. Aggregation depths 1, 2, 4, 8, 16, 32 and 50
///   are ALL still negative on qiu. **It is a cliff, not a gradient**: only the COMPLETE chain
///   flips the sign.
///
/// # The walk
///
/// A capacity row is `Σ_{p∈P} x_p − Σ_{n∈N} x_n <= b`. Every `x_n` is linked to some `x_p` by a
/// chain row `x_n − x_p <= 0`, and adding that row with multiplier 1 cancels **both** columns at
/// once. Doing it for all 66 of `c661`'s negative columns leaves the clean single-node set
/// `Σ_{66 arcs} x_j <= 48`, which is where c-MIR finally bites (δ = 0.26, violation 0.2617).
///
/// So this separator does not SEARCH: it walks the structure. From a wide `<=` row, repeatedly
///
/// 1. pick a **continuous column with a negative coefficient** — on a `<=` row over columns at
///    their lower bound such a term is pure slack: it lets the row be satisfied for free and the
///    MIR rounding gets nothing from it;
/// 2. find a two-column partner row that cancels it with a **positive** multiplier `λ` (an
///    equality takes any `λ`; a one-sided row must keep its `<=` sense, so `λ > 0`);
/// 3. accept the step **only if the partner's other column ends up with a non-negative
///    coefficient**. This is the load-bearing rule and it does three jobs at once. It makes the
///    walk provably TERMINATING: the cancelled column's coefficient becomes exactly zero, the
///    partner's cannot go negative, and a two-column partner touches nothing else — so the count
///    of negative continuous columns strictly decreases every step. It means the aggregate never
///    GROWS, so no fill is ever added and the density cap the pool applies is never approached.
///    And it is what picks the right partner when a column has several: on qiu each negative
///    column has TWO chain rows (`x49 − x313 <= 0` and `x49 − x577 <= 0`, verified), and once an
///    earlier step has zeroed `x313` the rule refuses the partner that would push it back
///    negative and takes the other one. Nothing here is hard-coded to a row shape.
///
/// The result is MIR'd ONCE, at the end, by the existing [`mir_from_row`] — the intermediate
/// depths are measured dry on the only shape this fires on, and MIR-ing 66 intermediates per base
/// row would be 66x the cost for cuts the delta search has already been shown to reject.
///
/// # Validity
///
/// Nothing new is claimed. Each step adds `λ · (oriented partner row <= oriented rhs)` with
/// `λ > 0` (or any `λ` for an equality) to a `<=` aggregate, in exact `BigRational`, which is the
/// same non-negative-combination argument `separate_mir_agg` rests on; the finished aggregate is
/// then handed verbatim to `mir_from_row`, which owns every rounding decision and every
/// soundness guard. This function derives no coefficient of its own.
///
/// # Gate
///
/// OPT-IN: `with_chain_agg(true)`. Off, this is one `var_os` per round and the default corpus is
/// bit-identical (verified: every objective, status and node count unchanged over 19 instances).
///
/// On, `CHAIN_AGG_MIN_BASE_NNZ` / `CHAIN_AGG_MIN_TARGETS` keep it off narrow rows, and the walk
/// must **complete** — a base row that still has a negative continuous column when the walk
/// stalls is dropped, not MIR'd, because a partial chain is exactly the depth-1..50 regime
/// already measured negative. Over the 19-instance corpus the walk starts on exactly THREE
/// models (qiu 4 base rows, khb05250 224, blend2 8) and derives a cut on ONE (qiu).
struct ChainIndex {
    rows: Vec<ChainRow>,
    by_col: Vec<Vec<u32>>,
}

struct OrientedBase<'a> {
    row: usize,
    coeffs: &'a [(u32, f64)],
    sign: f64,
    rhs: f64,
}

fn build_chain_index(model: &Model, n_rows: usize) -> Option<ChainIndex> {
    let mut rows = Vec::new();
    for row in 0..n_rows {
        let (coeffs, lb, ub) = model.row(Row(row as u32));
        if coeffs.len() != 2 {
            continue;
        }
        for (sign, rhs_raw) in [(1.0, ub), (-1.0, lb)] {
            if !rhs_raw.is_finite() {
                continue;
            }
            let (Some(a0), Some(a1), Some(rhs)) = (
                exact(sign * coeffs[0].1),
                exact(sign * coeffs[1].1),
                exact(sign * rhs_raw),
            ) else {
                continue;
            };
            if !a0.is_zero() && !a1.is_zero() {
                rows.push(ChainRow {
                    row: row as u32,
                    rhs,
                    cols: [(coeffs[0].0 as usize, a0), (coeffs[1].0 as usize, a1)],
                });
            }
        }
    }
    if rows.len() < CHAIN_AGG_MIN_TARGETS {
        return None;
    }
    let mut by_col = vec![Vec::new(); model.num_cols()];
    for (index, chain) in rows.iter().enumerate() {
        for &(column, _) in &chain.cols {
            by_col[column].push(index as u32);
        }
    }
    Some(ChainIndex { rows, by_col })
}

fn is_chain_target(model: &Model, column: usize, coefficient: &BigRational) -> bool {
    !model.col_kind(Col(column as u32)).is_integral() && coefficient < &BigRational::zero()
}

fn orient_chain_base(
    model: &Model,
    base: &OrientedBase<'_>,
) -> Option<(
    std::collections::BTreeMap<usize, BigRational>,
    BigRational,
    usize,
)> {
    let mut terms = std::collections::BTreeMap::new();
    for &(column, coefficient) in base.coeffs {
        let value = exact(base.sign * coefficient)?;
        if !value.is_zero() {
            *terms
                .entry(column as usize)
                .or_insert_with(BigRational::zero) += value;
        }
    }
    let rhs = exact(base.sign * base.rhs)?;
    let targets = terms
        .iter()
        .filter(|&(&column, coefficient)| is_chain_target(model, column, coefficient))
        .count();
    (targets >= CHAIN_AGG_MIN_TARGETS).then_some((terms, rhs, targets))
}

fn walk_chain(
    model: &Model,
    index: &ChainIndex,
    terms: &mut std::collections::BTreeMap<usize, BigRational>,
    rhs: &mut BigRational,
) -> (bool, std::collections::HashSet<u32>) {
    let mut used = std::collections::HashSet::new();
    for _ in 0..CHAIN_AGG_MAX_DEPTH {
        let Some(column) = terms
            .iter()
            .find(|&(&column, coefficient)| is_chain_target(model, column, coefficient))
            .map(|(&column, _)| column)
        else {
            return (true, used);
        };
        let coefficient = terms[&column].clone();
        let chosen = index.by_col[column].iter().find_map(|&chain_index| {
            let chain = &index.rows[chain_index as usize];
            if used.contains(&chain.row) {
                return None;
            }
            let (pivot, other) = if chain.cols[0].0 == column {
                (&chain.cols[0].1, &chain.cols[1])
            } else {
                (&chain.cols[1].1, &chain.cols[0])
            };
            let multiplier = -&coefficient / pivot;
            if multiplier <= BigRational::zero() {
                return None;
            }
            let current = terms
                .get(&other.0)
                .cloned()
                .unwrap_or_else(BigRational::zero);
            (current + &multiplier * &other.1 >= BigRational::zero())
                .then_some((multiplier, chain_index as usize))
        });
        let Some((multiplier, chain_index)) = chosen else {
            return (false, used);
        };
        let chain = &index.rows[chain_index];
        for &(column, ref coefficient) in &chain.cols {
            *terms.entry(column).or_insert_with(BigRational::zero) += &multiplier * coefficient;
        }
        *rhs += &multiplier * &chain.rhs;
        terms.retain(|_, value| !value.is_zero());
        used.insert(chain.row);
    }
    (true, used)
}

fn chain_cut_for_base(
    model: &Model,
    x: &[f64],
    base: OrientedBase<'_>,
    index: &ChainIndex,
    vubs: &Vubs,
) -> (bool, Option<Cut>) {
    let Some((mut terms, mut rhs, targets)) = orient_chain_base(model, &base) else {
        return (false, None);
    };
    let (complete, used) = walk_chain(model, index, &mut terms, &mut rhs);
    if chain_trace() {
        let activity = terms
            .iter()
            .map(|(&column, coefficient)| {
                to_f64(coefficient) * x.get(column).copied().unwrap_or(0.0)
            })
            .sum::<f64>();
        eprintln!(
            "--trace     chain row={} sgn={} base_nnz={} targets={targets} \
             steps={} complete={complete} agg_nnz={} b={:.6} act={activity:.6}",
            base.row,
            base.sign,
            base.coeffs.len(),
            used.len(),
            terms.len(),
            to_f64(&rhs),
        );
    }
    if !complete || used.is_empty() || terms.is_empty() {
        return (true, None);
    }
    let terms = terms.into_iter().collect::<Vec<_>>();
    let cut = mir_from_row(model, x, &terms, &rhs, vubs);
    if chain_trace() {
        if let Some(cut) = &cut {
            eprintln!(
                "--trace       -> cut nnz={} viol={:.6} eff={:.6}",
                cut.coeffs.len(),
                violation(cut, x),
                efficacy(cut, x)
            );
        } else {
            eprintln!("--trace       -> mir_from_row: NONE (aggregate yields no cut)");
        }
    }
    (true, cut)
}

fn collect_chain_candidates(
    model: &Model,
    x: &[f64],
    n_rows: usize,
    index: &ChainIndex,
    vubs: &Vubs,
) -> (Vec<Cut>, usize) {
    let mut candidates = Vec::new();
    let mut bases = 0;
    for row in 0..n_rows {
        if bases >= CHAIN_AGG_MAX_BASES || sep_wall_expired() {
            break;
        }
        let (coeffs, lb, ub) = model.row(Row(row as u32));
        if coeffs.len() < CHAIN_AGG_MIN_BASE_NNZ {
            continue;
        }
        for (sign, rhs) in [(1.0, ub), (-1.0, lb)] {
            if !rhs.is_finite() {
                continue;
            }
            let (eligible, cut) = chain_cut_for_base(
                model,
                x,
                OrientedBase {
                    row,
                    coeffs,
                    sign,
                    rhs,
                },
                index,
                vubs,
            );
            bases += usize::from(eligible);
            if let Some(cut) = cut {
                candidates.push(cut);
            }
        }
    }
    (candidates, bases)
}

pub(crate) fn separate_mir_chain_agg(
    model: &Model,
    x: &[f64],
    n_rows: usize,
    budget: usize,
) -> Vec<Cut> {
    if budget == 0
        || crate::tune::caller_flag(crate::tune::Knob::ChainAgg) != Some(true)
        || mir_family_inert(model)
    {
        return Vec::new();
    }
    let n_rows = n_rows.min(model.num_rows());
    let has_wide_row = (0..n_rows).any(|row| {
        let (coeffs, lb, ub) = model.row(Row(row as u32));
        coeffs.len() >= CHAIN_AGG_MIN_BASE_NNZ && (lb.is_finite() || ub.is_finite())
    });
    if !has_wide_row {
        return Vec::new();
    }
    let Some(index) = build_chain_index(model, n_rows) else {
        return Vec::new();
    };
    // Reuse the shared VUB recognizer so its kill switch still covers this family.
    let vubs = node_vubs(model);
    let (mut candidates, bases) = collect_chain_candidates(model, x, n_rows, &index, &vubs);
    candidates.sort_by(|left, right| {
        efficacy(right, x)
            .partial_cmp(&efficacy(left, x))
            .unwrap_or(std::cmp::Ordering::Equal)
    });
    if chain_trace() {
        eprintln!(
            "--trace   mir_chain_agg: {} candidates from {bases} base rows, best efficacy {:.6}, kept {}",
            candidates.len(),
            candidates.first().map(|cut| efficacy(cut, x)).unwrap_or(0.0),
            candidates.len().min(budget)
        );
    }
    candidates.truncate(budget);
    candidates
}
