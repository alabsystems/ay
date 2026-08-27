// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Diagnostic incumbent loading and exact continuous completion.

use std::path::Path;

use super::*;

pub(super) enum LoadResult {
    Accepted(Vec<BigRational>, BigRational),
    CompletionFailed,
    Infeasible,
}

pub(super) fn load(
    model: &Model,
    opts: &SolveOpts,
    shared_binary_prefix: &[Col],
    path: &Path,
) -> Option<LoadResult> {
    if !shared_binary_prefix.is_empty() {
        return None;
    }
    let text = std::fs::read_to_string(path).ok()?;
    let n = model.num_cols();
    // Float dumps cannot satisfy exact continuous equalities reliably. Pin the
    // integer columns only, then re-derive the continuous completion.
    let mut fixed = model.clone();
    for line in text.lines() {
        let mut fields = line.split_whitespace();
        if let (Some(j), Some(v)) = (fields.next(), fields.next()) {
            if let (Ok(j), Ok(v)) = (j.parse::<usize>(), v.parse::<f64>()) {
                if j < n {
                    let col = Col(j as u32);
                    if model.col_kind(col).is_integral() {
                        fixed.fix_col(col, v.round());
                    }
                }
            }
        }
    }
    let done = solve_milp_in(&fixed, opts, SearchMode::FULL, None, &[], &[], &[]);
    let point = match done {
        Outcome::Optimal { model_values, .. } | Outcome::Feasible { model_values, .. }
            if model_values.len() == n =>
        {
            model_values
        }
        _ => return Some(LoadResult::CompletionFailed),
    };
    if model.check_point(&point).is_err() {
        return Some(LoadResult::Infeasible);
    }
    let mut value = BigRational::zero();
    for (j, point_value) in point.iter().enumerate() {
        let coefficient = model.obj_coeff(Col(j as u32));
        if coefficient != 0.0 {
            value += exact(coefficient)? * point_value;
        }
    }
    if matches!(model.sense(), Sense::Maximize) {
        value = -value;
    }
    Some(LoadResult::Accepted(point, value))
}
