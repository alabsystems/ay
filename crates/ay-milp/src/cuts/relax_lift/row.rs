// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! One-row exact relax-and-lift construction.

use super::*;

/// How a column enters the view `Σ w_j·v_j ≤ c`.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum RlView {
    /// `v_j = x_j − l_j`, `w_j = a_j > 0`.
    Shift,
    /// `v_j = u_j − x_j`, `w_j = −a_j > 0`.
    Complement,
}

/// The most a set of UNIT-value items of ascending weights is worth inside capacity `c`, exact in
/// `BigRational`. `prefix[i] = Σ_{<i} w`, so this is a binary search: the answer is the largest `i`
/// with `prefix[i] ≤ c`. `None` means `c < 0` — no capacity at all, so the state is infeasible and
/// bounds nothing (the same convention `max_cardinality` uses).
fn rl_max_cardinality(prefix: &[BigRational], c: &BigRational) -> Option<usize> {
    if c.is_negative() {
        return None;
    }
    // prefix[0] == 0 <= c always, so the answer is at least 0.
    let (mut lo, mut hi) = (0usize, prefix.len() - 1);
    while lo < hi {
        let mid = (lo + hi + 1) / 2;
        if prefix[mid] <= *c {
            lo = mid;
        } else {
            hi = mid - 1;
        }
    }
    Some(lo)
}

/// One already-lifted general integer: `(view index, weight, range U, reference t*, γ)`.
pub(super) type RlLifted = (usize, BigRational, i64, i64, BigRational);

/// One non-negative bounded view of an original column.
struct Item {
    col: u32,
    view: RlView,
    w: BigRational,
    vstar: f64,
}

/// The classified row and its exact lifted-state size.
struct ClassifiedRow {
    bins: Vec<Item>,
    gens: Vec<(Item, i64)>,
    capacity: BigRational,
    lift_space: u128,
}

/// The violated binary face cover and the data used by the lifting oracle.
struct FaceCover {
    cover: Vec<usize>,
    prefix: Vec<BigRational>,
    rho: BigRational,
    tstar: Vec<i64>,
    residual: BigRational,
}

/// `Φ_L(budget)` — see [`separate_relax_lift`]. `None` when the state is infeasible for every
/// multiplicity vector (so it constrains nothing).
pub(super) fn rl_phi(
    prefix: &[BigRational],
    lifted: &[RlLifted],
    budget: &BigRational,
) -> Option<BigRational> {
    let mut best: Option<BigRational> = None;
    let mut idx = vec![0i64; lifted.len()];
    loop {
        let mut used = BigRational::zero();
        let mut val = BigRational::zero();
        for (t, l) in idx.iter().zip(lifted) {
            used += &l.1 * BigRational::from_integer((*t).into());
            val += &l.4 * BigRational::from_integer((*t - l.3).into());
        }
        if let Some(n) = rl_max_cardinality(prefix, &(budget - &used)) {
            let v = val + BigRational::from_integer((n as i64).into());
            if best.as_ref().is_none_or(|b| v > *b) {
                best = Some(v);
            }
        }
        let mut k = 0;
        while k < lifted.len() {
            idx[k] += 1;
            if idx[k] <= lifted[k].2 {
                break;
            }
            idx[k] = 0;
            k += 1;
        }
        if k == lifted.len() {
            break;
        }
    }
    best
}

/// Orient, bound-check, and classify the row without claiming integrality for a fractional-bound
/// displacement.
fn classify_row(
    model: &Model,
    x: &[f64],
    coeffs: &[(u32, f64)],
    ub: f64,
    negated: bool,
) -> Option<ClassifiedRow> {
    let mut bins = Vec::new();
    let mut gens = Vec::new();
    let mut capacity = exact(ub)?;
    for &(col, a0) in coeffs {
        let a = if negated { -a0 } else { a0 };
        if a == 0.0 {
            continue;
        }
        let (lo, up) = model.col_bounds(Col(col));
        let ae = exact(a)?;
        let (view, bnd) = if a > 0.0 {
            if !lo.is_finite() {
                return None;
            }
            (RlView::Shift, lo)
        } else {
            if !up.is_finite() {
                return None;
            }
            (RlView::Complement, up)
        };
        capacity -= &ae * exact(bnd)?;
        let w = if view == RlView::Shift { ae } else { -ae };
        debug_assert!(w > BigRational::zero());
        let vstar = match view {
            RlView::Shift => x.get(col as usize).copied().unwrap_or(0.0) - bnd,
            RlView::Complement => bnd - x.get(col as usize).copied().unwrap_or(0.0),
        };
        let item = Item {
            col,
            view,
            w,
            vstar: vstar.max(0.0),
        };

        // A displacement is integral only when both column kind and finite bounds are integral.
        let integral_kind = model.col_kind(Col(col)).is_integral();
        let bounds_integral = {
            let (loe, upe) = (exact(lo), exact(up));
            matches!((&loe, &upe), (Some(l), Some(u)) if l.is_integer() && u.is_integer())
        };
        if !integral_kind || !bounds_integral || !lo.is_finite() || !up.is_finite() || lo < 0.0 {
            continue;
        }
        let ru = match i64::try_from((exact(up)? - exact(lo)?).to_integer()) {
            Ok(v) => v,
            Err(_) => continue,
        };
        if ru == 1 {
            bins.push(item);
        } else if (2..=RL_MAX_GEN_RANGE).contains(&ru) && gens.len() < RL_MAX_GENS {
            gens.push((item, ru));
        }
    }
    if bins.len() < 2 {
        return None;
    }
    let lift_space = gens
        .iter()
        .try_fold(1u128, |acc, (_, u)| acc.checked_mul(*u as u128 + 1))
        .unwrap_or(u128::MAX);
    (lift_space <= RL_LIFT_SPACE_CAP).then_some(ClassifiedRow {
        bins,
        gens,
        capacity,
        lift_space,
    })
}

/// Fix general integers at the LP face and select the exact violated binary cover.
fn select_face_cover(row: &ClassifiedRow) -> Option<FaceCover> {
    let mut tstar = Vec::with_capacity(row.gens.len());
    let mut residual = row.capacity.clone();
    for (it, u) in &row.gens {
        let t = (it.vstar.floor() as i64).clamp(0, *u);
        residual -= &it.w * BigRational::from_integer(t.into());
        tstar.push(t);
    }
    if residual.is_negative() {
        return None;
    }

    let mut order: Vec<usize> = (0..row.bins.len()).collect();
    order.sort_by(|&p, &q| {
        let wp = to_f64(&row.bins[p].w).max(1e-12);
        let wq = to_f64(&row.bins[q].w).max(1e-12);
        let rp = (1.0 - row.bins[p].vstar.min(1.0)) / wp;
        let rq = (1.0 - row.bins[q].vstar.min(1.0)) / wq;
        rp.partial_cmp(&rq)
            .unwrap_or(std::cmp::Ordering::Equal)
            .then_with(|| row.bins[p].col.cmp(&row.bins[q].col))
    });
    let mut cover = Vec::new();
    let mut cw = BigRational::zero();
    for &i in &order {
        if cover.len() >= RL_MAX_COVER {
            break;
        }
        cover.push(i);
        cw += &row.bins[i].w;
        if cw > residual {
            break;
        }
    }
    if cw <= residual || cover.len() < 2 {
        return None;
    }
    let rho = BigRational::from_integer(((cover.len() - 1) as i64).into());
    let lhs0: f64 = cover.iter().map(|&i| row.bins[i].vstar.min(1.0)).sum();
    if lhs0 <= to_f64(&rho) + min_violation() {
        return None;
    }
    let mut sorted_w: Vec<_> = cover.iter().map(|&i| row.bins[i].w.clone()).collect();
    sorted_w.sort();
    let mut prefix = Vec::with_capacity(sorted_w.len() + 1);
    prefix.push(BigRational::zero());
    for w in sorted_w {
        let next = prefix[prefix.len() - 1].clone() + w;
        prefix.push(next);
    }
    Some(FaceCover {
        cover,
        prefix,
        rho,
        tstar,
        residual,
    })
}

/// Sequentially lift the general integers in deterministic heaviest-first order.
fn lift_generals(row: &ClassifiedRow, face: &FaceCover) -> Option<Vec<RlLifted>> {
    let mut order: Vec<usize> = (0..row.gens.len()).collect();
    order.sort_by(|&p, &q| {
        row.gens[q]
            .0
            .w
            .cmp(&row.gens[p].0.w)
            .then_with(|| row.gens[p].0.col.cmp(&row.gens[q].0.col))
    });
    let mut budget = face.residual.clone();
    let mut lifted = Vec::new();
    let mut work = 0u64;
    for gi in order {
        let (it, u) = &row.gens[gi];
        let t_star = face.tstar[gi];
        let mut upper = None;
        let mut lower = None;
        for t in 0..=*u {
            if t == t_star {
                continue;
            }
            work += row.lift_space as u64;
            if work > RL_WORK_CAP {
                return None;
            }
            let z = BigRational::from_integer((t - t_star).into());
            let Some(phi) = rl_phi(&face.prefix, &lifted, &(&budget - &it.w * &z)) else {
                continue;
            };
            let bound = (&face.rho - phi) / &z;
            if t > t_star {
                upper = Some(match upper {
                    Some(g) if g < bound => g,
                    _ => bound,
                });
            } else {
                lower = Some(match lower {
                    Some(g) if g > bound => g,
                    _ => bound,
                });
            }
        }
        let gamma = match (&upper, &lower) {
            (Some(u), _) => u.clone(),
            (None, Some(l)) if l.is_negative() => BigRational::zero(),
            (None, Some(l)) => l.clone(),
            (None, None) => BigRational::zero(),
        };
        if lower.as_ref().is_some_and(|l| gamma < *l) {
            return None;
        }
        budget += &it.w * BigRational::from_integer(t_star.into());
        lifted.push((gi, it.w.clone(), *u, t_star, gamma));
    }
    Some(lifted)
}

fn push_view_term(
    model: &Model,
    terms: &mut std::collections::BTreeMap<usize, BigRational>,
    rhs: &mut BigRational,
    item: &Item,
    coefficient: &BigRational,
) -> Option<()> {
    let (lo, up) = model.col_bounds(Col(item.col));
    match item.view {
        RlView::Shift => {
            *terms
                .entry(item.col as usize)
                .or_insert_with(BigRational::zero) += coefficient;
            *rhs += coefficient * exact(lo)?;
        }
        RlView::Complement => {
            *terms
                .entry(item.col as usize)
                .or_insert_with(BigRational::zero) -= coefficient;
            *rhs -= coefficient * exact(up)?;
        }
    }
    Some(())
}

/// Un-complement the lifted face inequality back to the model's columns.
fn emit_relax_lift_cut(
    model: &Model,
    x: &[f64],
    row: &ClassifiedRow,
    face: &FaceCover,
    lifted: &[RlLifted],
) -> Option<Cut> {
    let mut terms = std::collections::BTreeMap::new();
    let mut rhs = face.rho.clone();
    let one = BigRational::one();
    for &i in &face.cover {
        push_view_term(model, &mut terms, &mut rhs, &row.bins[i], &one)?;
    }
    for item in lifted {
        if item.4.is_zero() {
            continue;
        }
        rhs += &item.4 * BigRational::from_integer(item.3.into());
        push_view_term(model, &mut terms, &mut rhs, &row.gens[item.0].0, &item.4)?;
    }
    let cut = emit_le_cut(model, &terms, &rhs)?;
    clears_min_violation(&cut, x).then_some(cut)
}

/// One relax-and-lift cut from one oriented row. `negated` means the caller handed us the `≥` side
/// as `Σ (−a)·x ≤ −lb`, so every coefficient read out of `coeffs` must have its sign flipped.
pub(super) fn relax_lift_from_row(
    model: &Model,
    x: &[f64],
    coeffs: &[(u32, f64)],
    ub: f64,
    negated: bool,
) -> Option<Cut> {
    let row = classify_row(model, x, coeffs, ub, negated)?;
    let face = select_face_cover(&row)?;
    let lifted = lift_generals(&row, &face)?;
    emit_relax_lift_cut(model, x, &row, &face, &lifted)
}
