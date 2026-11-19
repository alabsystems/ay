// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Small-dimensional upper hull for the maximum of four affine functions.
//! Convexity bounds its value at every box point by a convex combination of
//! corner heights. Thus its concave envelope is piecewise affine, and a
//! supporting upper facet contains d+1 affinely independent lifted corners.

use super::{fixed_slope, maximum, Column};

fn sign(vertex: usize, axis: usize) -> f64 {
    if vertex & (1 << axis) == 0 {
        -1.0
    } else {
        1.0
    }
}

// Solve slope·(v-v0) = h(v)-h(v0) for one choice of d+1 corners.
// The matrix contains only 0 and ±2. Singular choices do not define a facet.
fn through(mask: usize, dim: usize, height: &[f64; 8]) -> Option<[f64; 3]> {
    let base = mask.trailing_zeros() as usize;
    let mut vertices = mask & (mask - 1);
    let mut rows = [[0.0; 4]; 3];
    for row in &mut rows[..dim] {
        let v = vertices.trailing_zeros() as usize;
        vertices &= vertices - 1;
        for (j, cell) in row[..dim].iter_mut().enumerate() {
            *cell = sign(v, j) - sign(base, j);
        }
        row[dim] = height[v] - height[base];
    }
    for k in 0..dim {
        let pivot = (k..dim).find(|&i| rows[i][k] != 0.0)?;
        rows.swap(k, pivot);
        let divisor = rows[k][k];
        for cell in &mut rows[k][k..=dim] {
            *cell /= divisor;
        }
        let normalized = rows[k];
        for (i, row) in rows[..dim].iter_mut().enumerate() {
            if i != k {
                let factor = row[k];
                for j in k..=dim {
                    row[j] -= factor * normalized[j];
                }
            }
        }
    }
    let slopes = std::array::from_fn(|j| rows[j][dim]);
    slopes[..dim]
        .iter()
        .all(|s| s.is_finite())
        .then_some(slopes)
}

pub(super) fn slopes(mut offsets: [f64; 4], columns: &[Column], point: &[f64]) -> Option<Vec<f64>> {
    let mut free = [0; 3];
    let mut dim = 0;
    for (j, col) in columns.iter().enumerate() {
        if let Some(s) = fixed_slope(col, point[col.index]) {
            for (h, a) in offsets.iter_mut().zip(col.arms) {
                *h += (a - s).abs();
            }
        } else {
            *free.get_mut(dim)? = j;
            dim += 1;
        }
    }
    if dim == 0 || !offsets.iter().all(|h| h.is_finite()) {
        return None;
    }
    let corners = 1_usize << dim;
    let mut heights = [0.0; 8];
    for (v, h) in heights[..corners].iter_mut().enumerate() {
        let mut values = offsets;
        for (j, &idx) in free[..dim].iter().enumerate() {
            for (val, a) in values.iter_mut().zip(columns[idx].arms) {
                *val += sign(v, j) * a;
            }
        }
        if !values.iter().all(|h| h.is_finite()) {
            return None;
        }
        *h = maximum(values);
    }
    let mut lowest = f64::INFINITY;
    let mut best = None;
    for mask in 1_usize..1 << corners {
        if mask.count_ones() as usize != dim + 1 {
            continue;
        }
        let Some(candidate) = through(mask, dim, &heights) else {
            continue;
        };
        // Lift every slope to its valid intercept on this face; this also
        // handles a plane that passes below one of the unselected corners.
        let mut support = offsets;
        let mut at_point = 0.0;
        for (j, &idx) in free[..dim].iter().enumerate() {
            let col = &columns[idx];
            at_point += point[col.index] * candidate[j];
            for (cost, a) in support.iter_mut().zip(col.arms) {
                *cost += (a - candidate[j]).abs();
            }
        }
        let value = maximum(support) + at_point;
        if value.is_finite() && value < lowest {
            lowest = value;
            best = Some(candidate);
        }
    }
    let best = best?;
    let mut saved = best[..dim].iter().copied();
    columns
        .iter()
        .map(|col| fixed_slope(col, point[col.index]).or_else(|| saved.next()))
        .collect()
}
