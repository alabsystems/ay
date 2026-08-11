// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Meet-in-the-middle exact solver for small ALL-EQUALITY 0/1 systems — the
//! market-split (Cornuéjols–Dawande) feasibility family and any structurally
//! identical small instance.
//!
//! # Why this exists
//!
//! The market-split OPT-LIN instances (`market-split_C_N_K`) are a system of
//! `C` linear equalities `A x = b` over `N` binary variables, wrapped in a
//! trivial objective (`min: +1 x1`, with `x1` forced to 0 by a `-1 x1 >= 0`
//! bound). They are constructed to be pathological for LP/branch-and-bound AND
//! for stochastic local search: the feasible set is the exact intersection of
//! `C` equality hyperplanes with the hypercube — a needle that neither the
//! complete CDCL/SAT engines nor the from-scratch SLS arms reach within the
//! competition budget, so every arm returns UNKNOWN (no incumbent, no verdict).
//!
//! When the whole instance is small (few FREE variables after unit fixings),
//! meet-in-the-middle subset-sum is an *exact* decision procedure: split the
//! free variables in half, enumerate each half's `A`-image, and match halves
//! whose images sum to `b`. This finds the minimum-objective feasible point (or
//! proves infeasibility) exactly.
//!
//! # Soundness
//!
//! The recognizer accepts ONLY when EVERY constraint is consumed as either a
//! single-variable bound (a fixing or a trivially-true/false row) or an exact
//! linear equality (an `Eq` row, or a complementary pair of `Ge` rows
//! `a·x >= b` and `-a·x >= -b`). Under that guarantee the set of assignments the
//! meet-in-the-middle search enumerates is EXACTLY the instance's feasible set,
//! so its minimum is the true optimum and "no match" is a true infeasibility.
//! Independent belts and suspenders:
//! * the optimum witness is re-verified against ALL original constraints via
//!   the caller's `sanitize`/VIG gate before it is emitted (on any mismatch the
//!   solver declines rather than emit — a recognizer bug can only cost the
//!   incumbent, never fabricate one);
//! * the UNSAT verdict — which has no witness to re-verify — is emitted only
//!   when two variable splits BOTH find no feasible point; on any disagreement
//!   the solver declines. NOTE (soundness scope, per review): a single split is
//!   already exhaustive (`mitm_min` matches every left subset against the full
//!   right-half image map, so its feasibility answer is split-INDEPENDENT), and
//!   the second pass permutes the columns of the SAME reduced `EqSystem`.
//!   The two-split agreement therefore only guards against a variable-grouping-
//!   sensitive ENUMERATION bug — it does NOT independently re-check the
//!   recognizer/reduction, so UNSAT soundness ultimately rests on the recognizer
//!   consuming EVERY constraint (enumerated set == true feasible set), which the
//!   randomized brute-force differential tests pin.
//!
//! Any instance that does not match the recognizer (a lone inequality, a
//! non-linear term, a negated literal, or too many free variables) declines in
//! O(constraints), leaving the normal portfolio untouched.

use crate::output::{PbSolution, PbStatus};
use crate::types::{PbConstraint, PbInstance, PbObjective, PbRel};
use std::collections::HashMap;

/// Maximum number of FREE (non-fixed) variables the meet-in-the-middle search
/// will enumerate. `n` free vars ⇒ `2^ceil(n/2)` assignments per half; 52 ⇒
/// `2^26` ≈ 67M per half. The hash-side allocation for the larger counts is
/// bounded at runtime by [`mitm_rmap_fits_memory`], which DECLINES (falls back
/// to CDCL, soundly) when the projection would breach the process memory
/// budget — so this ceiling admits the `6_50` target (50 free ⇒ ~14 GB on a
/// generous-memory host) without risking OOM on a tight one. The `8_70`
/// members (70 free) remain above the ceiling. The historical `<=42`-free-var
/// targets (`4_30` ⇒ 30, `5_40` ⇒ 40) project to well under a gigabyte and are
/// never gated.
const MITM_MAX_FREE_VARS: usize = 52;

/// Fast pre-filter on the DECLARED variable count so oversized instances bail in
/// O(1) before the O(constraints) structural pass. A generous margin over
/// [`MITM_MAX_FREE_VARS`] (fixings shrink the free set below the declared count).
const MITM_MAX_DECLARED_VARS: u32 = 96;

/// How often (in enumerated subsets) to poll the caller stop signal.
const STOP_POLL_MASK: u64 = (1 << 16) - 1;

/// Outcome of the structural recognizer.
enum Recognized {
    /// A single-variable row (or a pair of conflicting fixings) is unsatisfiable
    /// on its own — the whole instance is infeasible.
    TriviallyUnsat,
    /// A small all-equality system ready for meet-in-the-middle.
    System(EqSystem),
}

/// A recognized all-equality system reduced to its FREE variables.
struct EqSystem {
    /// Fixed variables: `fixed[v] = Some(bit)` when variable `v` (0-based) is
    /// forced, else `None`. Length == `num_vars`.
    fixed: Vec<Option<bool>>,
    /// Free variable indices (0-based), the meet-in-the-middle search domain.
    free_vars: Vec<u32>,
    /// One row per equality; `coeffs[k]` is aligned to `free_vars`, and `rhs[k]`
    /// already has the fixed-variable contributions folded out.
    eq_coeffs: Vec<Vec<i128>>,
    eq_rhs: Vec<i128>,
    /// Objective coefficient of each free variable (aligned to `free_vars`).
    obj_coeff: Vec<i128>,
    /// Objective contribution of the fixed variables (a constant).
    obj_const: i128,
}

/// Attempts to solve `instance` exactly via meet-in-the-middle over a small
/// all-equality system. See the module docs for the soundness argument.
///
/// Returns `Some(OptimumFound)` (re-verified witness) or `Some(Unsatisfiable)`
/// (two-split agreement) when recognized and decided; `None` when the instance
/// is not recognized, exceeds the size budget, or the deadline/interrupt fires.
pub(crate) fn try_market_split_exact(
    instance: &PbInstance,
    objective: &PbObjective,
    should_stop: &dyn Fn() -> bool,
    on_improve: &mut dyn FnMut(i128, &[bool]),
) -> Option<PbSolution> {
    if instance.num_vars == 0 || instance.num_vars > MITM_MAX_DECLARED_VARS {
        return None;
    }
    if should_stop() {
        return None;
    }

    let system = match recognize(instance, objective)? {
        Recognized::TriviallyUnsat => {
            // A single-variable row proved infeasibility with no search needed.
            return Some(unsat_solution());
        }
        Recognized::System(system) => system,
    };

    if system.free_vars.len() > MITM_MAX_FREE_VARS {
        return None;
    }

    // Primary split (contiguous halves of the free-var order).
    let n = system.free_vars.len();
    let split_a = n / 2;
    match mitm_min(&system, split_a, should_stop)? {
        MitmResult::Optimum(free_bits, obj_value) => {
            let assignment = materialize(instance, &system, &free_bits);
            // Belt and suspenders: re-verify against EVERY original constraint
            // and recompute the objective exactly. On any mismatch, decline
            // (never emit an unverified verdict).
            let (assignment, actual_obj) = sanitize(&assignment, obj_value, instance, objective)?;
            on_improve(actual_obj, &assignment);
            Some(PbSolution {
                status: PbStatus::OptimumFound,
                assignment,
                objective: Some(actual_obj),
            })
        }
        MitmResult::Infeasible => {
            // UNSAT has no witness to re-verify: require a SECOND, independently
            // partitioned, exhaustive pass to agree before claiming infeasibility.
            // The second pass interleaves the free-variable order (even indices
            // then odd) so the two halves group STRUCTURALLY different variables,
            // while staying BALANCED (split at n/2) — an unbalanced split would
            // blow the larger half up to 2^(n-k).
            let order_b = interleaved_system(&system);
            match mitm_min(&order_b, order_b.free_vars.len() / 2, should_stop)? {
                MitmResult::Infeasible => Some(unsat_solution()),
                // Disagreement ⇒ a bug in one pass; do NOT risk a wrong UNSAT.
                MitmResult::Optimum(_, _) => None,
            }
        }
    }
}

/// The recognizer: fold single-variable rows into fixings, pair `Ge` rows into
/// equalities, and reduce to a free-variable [`EqSystem`]. Declines (`None`) on
/// any row that is neither a single-variable bound nor part of an equality, on
/// non-linear or negated-literal terms, and on an unpaired multi-variable `Ge`.
fn recognize(instance: &PbInstance, objective: &PbObjective) -> Option<Recognized> {
    let num_vars = usize::try_from(instance.num_vars).ok()?;

    // Normalize every constraint to (var -> coeff, rel, rhs) over positive
    // literals. Decline on any non-linear or negated literal (market-split has
    // neither; keeping this strict removes a whole class of sign-handling bugs).
    let mut single: Vec<(u32, i128, PbRel, i128)> = Vec::new();
    let mut multi_eq: Vec<(Vec<(u32, i128)>, i128)> = Vec::new();
    // Multi-variable `Ge` rows awaiting a complementary partner.
    let mut multi_ge: Vec<(Vec<(u32, i128)>, i128)> = Vec::new();

    for con in &instance.constraints {
        let terms = normalize_linear_row(con)?;
        // Decline (never index-panic) on a variable beyond the declared
        // `num_vars`: a header-undercount OPB (`#variable=` less than the max
        // referenced var) is trusted verbatim by the parser, and the
        // constraint-side index derivations below (`fixed[idx]`, `is_free[idx]`)
        // are otherwise unchecked. The objective loop already guards this;
        // mirror it here so a malformed instance declines instead of crashing.
        for &(var, _) in &terms {
            if usize::try_from(var).ok()? >= num_vars {
                return None;
            }
        }
        match terms.len() {
            0 => {
                // Empty LHS: 0 rel rhs. Trivially decidable.
                let holds = match con.rel {
                    PbRel::Ge => 0 >= con.rhs,
                    PbRel::Eq => 0 == con.rhs,
                };
                if !holds {
                    return Some(Recognized::TriviallyUnsat);
                }
            }
            1 => single.push((terms[0].0, terms[0].1, con.rel, con.rhs)),
            _ => match con.rel {
                PbRel::Eq => multi_eq.push((terms, con.rhs)),
                PbRel::Ge => multi_ge.push((terms, con.rhs)),
            },
        }
    }

    // Fold single-variable rows into fixings by evaluating both 0/1 values.
    let mut fixed: Vec<Option<bool>> = vec![None; num_vars];
    for (var, coeff, rel, rhs) in single {
        // Evaluate the row at both binary values: LHS is 0 at x=0, `coeff` at x=1.
        let sat0 = row_holds(0, rel, rhs);
        let sat1 = row_holds(coeff, rel, rhs);
        let forced = match (sat0, sat1) {
            (false, false) => return Some(Recognized::TriviallyUnsat),
            (true, false) => Some(false),
            (false, true) => Some(true),
            (true, true) => None, // trivially satisfied; no fixing
        };
        if let Some(bit) = forced {
            let idx = usize::try_from(var).ok()?;
            match fixed[idx] {
                Some(prev) if prev != bit => return Some(Recognized::TriviallyUnsat),
                _ => fixed[idx] = Some(bit),
            }
        }
    }

    // Pair multi-variable `Ge` rows into equalities. Two rows form the equality
    // `a·x = b` iff one is the exact elementwise negation of the other (coeffs
    // and rhs both negated).
    let mut used = vec![false; multi_ge.len()];
    for i in 0..multi_ge.len() {
        if used[i] {
            continue;
        }
        let (ref terms_i, rhs_i) = multi_ge[i];
        let mut paired = false;
        for j in (i + 1)..multi_ge.len() {
            if used[j] {
                continue;
            }
            let (ref terms_j, rhs_j) = multi_ge[j];
            if rhs_j == -rhs_i && is_negation(terms_i, terms_j) {
                multi_eq.push((terms_i.clone(), rhs_i));
                used[i] = true;
                used[j] = true;
                paired = true;
                break;
            }
        }
        if !paired {
            // A lone multi-variable inequality cannot be handled exactly by
            // this equality-only search: decline.
            return None;
        }
    }

    // Collect the free variables: every variable appearing (nonzero) in an
    // equality and not fixed. Objective-only and constraint-free variables are
    // set to their minimizing value below (they do not constrain feasibility).
    let mut is_free = vec![false; num_vars];
    for (terms, _rhs) in &multi_eq {
        for &(var, coeff) in terms {
            let idx = usize::try_from(var).ok()?;
            if coeff != 0 && fixed[idx].is_none() {
                is_free[idx] = true;
            }
        }
    }
    let free_vars: Vec<u32> = (0..num_vars)
        .filter(|&i| is_free[i])
        .map(|i| i as u32)
        .collect();
    if free_vars.is_empty() {
        // No free variables: the system is either fully fixed or empty. Let the
        // normal (also cheap) portfolio path handle these degenerate shapes.
        return None;
    }
    if free_vars.len() > MITM_MAX_FREE_VARS {
        return None;
    }

    // Position of each free var within `free_vars` (for aligning coeff vectors).
    let mut pos = vec![usize::MAX; num_vars];
    for (p, &v) in free_vars.iter().enumerate() {
        pos[v as usize] = p;
    }

    // Coalesce the objective to a per-variable coefficient (declining on any
    // non-linear or negated term), so each variable is categorized exactly once.
    let mut obj_by_var: HashMap<usize, i128> = HashMap::new();
    for term in &objective.terms {
        if term.lits.len() != 1 {
            return None;
        }
        let lit = term.lits[0];
        if lit.negated {
            return None;
        }
        let idx = usize::try_from(lit.var.checked_sub(1)?).ok()?;
        if idx >= num_vars {
            return None;
        }
        let e = obj_by_var.entry(idx).or_insert(0);
        *e = e.checked_add(term.coeff)?;
    }

    // Objective: coefficient per free var; constant from fixed + objective-only.
    let mut obj_coeff = vec![0i128; free_vars.len()];
    let mut obj_const = 0i128;
    for (idx, coeff) in obj_by_var {
        if let Some(bit) = fixed[idx] {
            if bit {
                obj_const = obj_const.checked_add(coeff)?;
            }
        } else if pos[idx] != usize::MAX {
            obj_coeff[pos[idx]] = obj_coeff[pos[idx]].checked_add(coeff)?;
        } else {
            // Objective-only variable (not in any equality, not fixed): FIX it to
            // its minimizing value so `materialize` and `obj_const` stay
            // consistent. Negative coeff ⇒ 1 (and subtract into the constant),
            // else 0.
            if coeff < 0 {
                fixed[idx] = Some(true);
                obj_const = obj_const.checked_add(coeff)?;
            } else {
                fixed[idx] = Some(false);
            }
        }
    }

    // Build equality coeff vectors over free vars, folding fixed contributions
    // into the rhs.
    let mut eq_coeffs: Vec<Vec<i128>> = Vec::with_capacity(multi_eq.len());
    let mut eq_rhs: Vec<i128> = Vec::with_capacity(multi_eq.len());
    for (terms, rhs) in &multi_eq {
        let mut row = vec![0i128; free_vars.len()];
        let mut r = *rhs;
        for &(var, coeff) in terms {
            let idx = usize::try_from(var).ok()?;
            if let Some(bit) = fixed[idx] {
                if bit {
                    r = r.checked_sub(coeff)?;
                }
            } else if pos[idx] != usize::MAX {
                row[pos[idx]] = row[pos[idx]].checked_add(coeff)?;
            } else {
                // A variable in an equality that is neither fixed nor free
                // cannot happen (we marked it free above); guard defensively.
                return None;
            }
        }
        eq_coeffs.push(row);
        eq_rhs.push(r);
    }

    Some(Recognized::System(EqSystem {
        fixed,
        free_vars,
        eq_coeffs,
        eq_rhs,
        obj_coeff,
        obj_const,
    }))
}

/// Normalizes a linear constraint to `(var, coeff)` pairs over positive
/// literals, coalescing repeated variables. Returns `None` on any non-linear
/// term (`lits.len() != 1`) or negated literal.
fn normalize_linear_row(con: &PbConstraint) -> Option<Vec<(u32, i128)>> {
    // Use a small map keyed by var to coalesce duplicates deterministically.
    let mut acc: HashMap<u32, i128> = HashMap::new();
    for term in &con.terms {
        if term.lits.len() != 1 {
            return None;
        }
        let lit = term.lits[0];
        if lit.negated {
            return None;
        }
        let var = lit.var.checked_sub(1)?; // 0-based
        let e = acc.entry(var).or_insert(0);
        *e = e.checked_add(term.coeff)?;
    }
    let mut out: Vec<(u32, i128)> = acc.into_iter().filter(|&(_, c)| c != 0).collect();
    out.sort_unstable_by_key(|&(v, _)| v);
    Some(out)
}

/// Whether the row with LHS value `lhs` satisfies `rel rhs`.
fn row_holds(lhs: i128, rel: PbRel, rhs: i128) -> bool {
    match rel {
        PbRel::Ge => lhs >= rhs,
        PbRel::Eq => lhs == rhs,
    }
}

/// Whether two normalized rows are exact elementwise negations (same variables,
/// opposite coefficients).
fn is_negation(a: &[(u32, i128)], b: &[(u32, i128)]) -> bool {
    if a.len() != b.len() {
        return false;
    }
    a.iter()
        .zip(b.iter())
        .all(|(&(va, ca), &(vb, cb))| va == vb && ca == -cb)
}

/// Result of one meet-in-the-middle pass.
enum MitmResult {
    /// A minimum-objective feasible point: free-variable bits + objective value.
    Optimum(Vec<bool>, i128),
    /// No feasible point exists (exhaustive).
    Infeasible,
}

/// Runs meet-in-the-middle over `system.free_vars`, splitting at index `split`
/// (left = `free_vars[..split]`, right = the rest). Returns the minimum-objective
/// feasible assignment (as free-var bits) or `Infeasible`. Returns `None` only
/// if the caller stop signal fires mid-search.
/// Whether the meet-in-the-middle hash map for a half of `stored_bits` free
/// variables (over `m` equality rows) is projected to fit within the process
/// memory budget with headroom.
///
/// The map holds up to `2^stored_bits` entries; each entry is modelled as
/// `m * 24 + 128` bytes — an `m`-component `Vec<i128>` key plus the
/// `(i128, u64)` value and hash-bucket/load-factor overhead (calibrated against
/// a measured ~415 B/entry at `m = 13`). We admit the allocation only if the
/// projection stays under 60% of the *remaining* budget
/// (`limit - current_rss`, or physical RAM when no limit is set), leaving room
/// for the sweep side and the rest of the solver. Returns `true` when no limit
/// is set AND physical RAM is unknown (the conservative pre-existing behaviour
/// for the small free-var counts, which project to well under a gigabyte).
fn mitm_rmap_fits_memory(stored_bits: usize, m: usize) -> bool {
    let entry_bytes: u128 = (m as u128) * 24 + 128;
    // `stored_bits` is bounded by MITM_MAX_FREE_VARS (<= ~26 for the stored
    // half); clamp the shift defensively so it can never overflow.
    let entries: u128 = 1u128 << stored_bits.min(100);
    let projected = entries.saturating_mul(entry_bytes);

    let limit = ay_sys::get_process_memory_limit();
    let budget: u128 = if limit > 0 {
        limit as u128
    } else {
        let phys = ay_sys::physical_memory_bytes();
        if phys == 0 {
            // No limit and unknown RAM: keep the historical behaviour (the small
            // targets project to < 1 GB); only refuse an obviously huge map.
            return projected < (4u128 << 30);
        }
        phys as u128
    };
    let available = budget.saturating_sub(ay_sys::current_rss_bytes() as u128);
    projected <= available / 100 * 60
}

fn mitm_min(system: &EqSystem, split: usize, should_stop: &dyn Fn() -> bool) -> Option<MitmResult> {
    let n = system.free_vars.len();
    let split = split.clamp(0, n);
    let left: Vec<usize> = (0..split).collect();
    let right: Vec<usize> = (split..n).collect();
    let m = system.eq_coeffs.len();

    // Memory guard. The RIGHT-half hash map holds up to `2^right_bits` entries,
    // each roughly a `Vec<i128>` key of `m` components plus an `(i128, u64)`
    // value and bucket overhead. For the larger free-var counts the raised
    // [`MITM_MAX_FREE_VARS`] now admits, building it can run to many GB — so
    // PROJECT the peak against the process memory budget and DECLINE (fall back
    // to the CDCL portfolio) rather than risk an OOM kill of the entire solve.
    // Declining is sound: the exhaustive search simply does not run here; the
    // reported optimum/UNSAT is unaffected because none is emitted. Small
    // instances (the historical <=42-free-var targets) project to well under a
    // gigabyte and are never gated, so there is no regression.
    if !mitm_rmap_fits_memory(right.len(), m) {
        return None;
    }

    // Build the RIGHT-half hash map: image vector -> (min objective, subset mask).
    // Keyed by the m-dimensional A-image; value keeps the min-objective witness.
    let mut rmap: HashMap<Vec<i128>, (i128, u64)> = HashMap::new();
    enumerate_subsets(&right, m, system, should_stop, |image, obj, mask| {
        rmap.entry(image.to_vec())
            .and_modify(|slot| {
                if obj < slot.0 {
                    *slot = (obj, mask);
                }
            })
            .or_insert((obj, mask));
    })?;

    // Sweep the LEFT half, matching each image against `b - image` in `rmap`.
    let mut best: Option<(i128, u64, u64)> = None; // (obj, left_mask, right_mask)
    enumerate_subsets(&left, m, system, should_stop, |image, obj, mask| {
        // need_k = rhs_k - left_image_k
        let mut need = Vec::with_capacity(m);
        for k in 0..m {
            need.push(system.eq_rhs[k] - image[k]);
        }
        if let Some(&(robj, rmask)) = rmap.get(&need) {
            let total = obj + robj + system.obj_const;
            if best.is_none_or(|(b, _, _)| total < b) {
                best = Some((total, mask, rmask));
            }
        }
    })?;

    match best {
        None => Some(MitmResult::Infeasible),
        Some((obj, left_mask, right_mask)) => {
            // Reconstruct free-var bit vector (aligned to `system.free_vars`).
            let mut bits = vec![false; n];
            for (t, &fi) in left.iter().enumerate() {
                if (left_mask >> t) & 1 == 1 {
                    bits[fi] = true;
                }
            }
            for (t, &fi) in right.iter().enumerate() {
                if (right_mask >> t) & 1 == 1 {
                    bits[fi] = true;
                }
            }
            Some(MitmResult::Optimum(bits, obj))
        }
    }
}

/// Enumerates all `2^half.len()` subsets of the given free-var half in Gray-code
/// order, invoking `visit(image, obj, mask)` for each: `image` is the running
/// m-dimensional A-image, `obj` the running objective contribution, and `mask`
/// the subset membership (bit `t` set ⇒ `half[t]` selected). Returns `None` if
/// the caller stop signal fires.
fn enumerate_subsets(
    half: &[usize],
    m: usize,
    system: &EqSystem,
    should_stop: &dyn Fn() -> bool,
    mut visit: impl FnMut(&[i128], i128, u64),
) -> Option<()> {
    let h = half.len();
    debug_assert!(h < 64);
    let total: u64 = 1u64 << h;
    let mut cur = vec![0i128; m];
    let mut cur_obj = 0i128;
    let mut prev_mask = 0u64;
    for i in 0..total {
        if i & STOP_POLL_MASK == 0 && should_stop() {
            return None;
        }
        let mask = i ^ (i >> 1); // Gray code
        if i > 0 {
            let diff = mask ^ prev_mask; // exactly one bit
            let t = diff.trailing_zeros() as usize;
            let fi = half[t];
            if mask & diff != 0 {
                // bit t now set: add this variable's contribution
                for k in 0..m {
                    cur[k] += system.eq_coeffs[k][fi];
                }
                cur_obj += system.obj_coeff[fi];
            } else {
                for k in 0..m {
                    cur[k] -= system.eq_coeffs[k][fi];
                }
                cur_obj -= system.obj_coeff[fi];
            }
            prev_mask = mask;
        }
        visit(&cur, cur_obj, mask);
    }
    Some(())
}

/// Returns a copy of `system` with the free-variable order INTERLEAVED — even
/// original indices first, then odd — so that a balanced (n/2) split groups a
/// structurally different set of variables into each half than the contiguous
/// split does. Used only to corroborate an UNSAT verdict; the search remains
/// exhaustive and its feasibility answer is split-independent.
fn interleaved_system(system: &EqSystem) -> EqSystem {
    let n = system.free_vars.len();
    // New order: [v0, v2, v4, ..., v1, v3, v5, ...].
    let order: Vec<usize> = (0..n).step_by(2).chain((1..n).step_by(2)).collect();
    let free_vars = order.iter().map(|&i| system.free_vars[i]).collect();
    let obj_coeff = order.iter().map(|&i| system.obj_coeff[i]).collect();
    let eq_coeffs = system
        .eq_coeffs
        .iter()
        .map(|row| order.iter().map(|&i| row[i]).collect())
        .collect();
    EqSystem {
        fixed: system.fixed.clone(),
        free_vars,
        eq_coeffs,
        eq_rhs: system.eq_rhs.clone(),
        obj_coeff,
        obj_const: system.obj_const,
    }
}

/// Builds the full-width assignment (indexed by `var - 1`) from the fixed
/// variables and the meet-in-the-middle free-variable bits. Unmentioned
/// variables default to `false`.
fn materialize(instance: &PbInstance, system: &EqSystem, free_bits: &[bool]) -> Vec<bool> {
    let num_vars = instance.num_vars as usize;
    let mut assignment = vec![false; num_vars];
    for (v, slot) in system.fixed.iter().enumerate() {
        if let Some(bit) = slot {
            assignment[v] = *bit;
        }
    }
    for (t, &v) in system.free_vars.iter().enumerate() {
        assignment[v as usize] = free_bits[t];
    }
    assignment
}

/// Re-verifies `assignment` against ALL original constraints and recomputes the
/// exact objective (the caller's soundness gate). Returns the (width-normalized)
/// assignment and its exact objective, or `None` on any constraint violation /
/// objective overflow.
fn sanitize(
    assignment: &[bool],
    claimed_obj: i128,
    instance: &PbInstance,
    objective: &PbObjective,
) -> Option<(Vec<bool>, i128)> {
    // Width-normalize (materialize already produces `num_vars` width, but guard
    // defensively) before the VIG re-verification.
    let target = usize::try_from(instance.num_vars).ok()?;
    let mut assignment = assignment.to_vec();
    assignment.resize(target, false);
    assignment.truncate(target);
    if !crate::eval::verify_all_constraints(&instance.constraints, &assignment) {
        return None;
    }
    let actual = crate::solver::eval_objective_exact(objective, &assignment).ok()?;
    // The claimed objective must match the exact recompute (a divergence means a
    // recognizer/aggregation bug — decline rather than emit).
    if actual != claimed_obj {
        return None;
    }
    Some((assignment, actual))
}

fn unsat_solution() -> PbSolution {
    PbSolution {
        status: PbStatus::Unsatisfiable,
        assignment: Vec::new(),
        objective: None,
    }
}

#[cfg(test)]
mod tests;
