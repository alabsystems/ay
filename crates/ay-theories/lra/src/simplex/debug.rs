// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use std::fmt::Write as _;

use super::*;

impl LraSolver {
    fn debug_format_var(&self, var: u32) -> String {
        match self.var_to_term.get(&var).copied() {
            Some(term) => format!("v{var} term={term:?} ast={:?}", self.terms().get(term)),
            None => format!("v{var} term=<anonymous>"),
        }
    }

    fn debug_format_bound(&self, label: &str, bound: &crate::Bound) -> String {
        let mut rendered = format!(
            "{label}={}{}",
            bound.value,
            if bound.strict { " (strict)" } else { "" }
        );
        if bound.reasons.is_empty() {
            rendered.push_str(" reasons=[]");
            return rendered;
        }
        rendered.push_str(" reasons=[");
        for (idx, ((reason, value), scale)) in bound
            .reasons
            .iter()
            .zip(&bound.reason_values)
            .zip(
                bound
                    .reason_scales
                    .iter()
                    .map(Some)
                    .chain(std::iter::repeat(None)),
            )
            .take(bound.reasons.len())
            .enumerate()
        {
            if idx > 0 {
                rendered.push_str(", ");
            }
            if reason.is_sentinel() {
                let _ = write!(rendered, "{reason:?}:{value} ast=<sentinel>");
            } else {
                let _ = write!(
                    rendered,
                    "{reason:?}:{value} ast={:?}",
                    self.terms().get(*reason)
                );
            }
            if let Some(scale) = scale {
                let _ = write!(rendered, " scale={scale}");
            }
        }
        rendered.push(']');
        rendered
    }

    fn debug_format_row(&self, row: &TableauRow) -> String {
        let mut rendered = format!(
            "{} := {}",
            self.debug_format_var(row.basic_var),
            row.constant
        );
        for &(var, ref coeff) in &row.coeffs {
            let _ = write!(rendered, " + ({coeff})*{}", self.debug_format_var(var));
        }
        rendered
    }

    pub(super) fn debug_log_contradictory_bounds(
        &self,
        var: u32,
        lower: &crate::Bound,
        upper: &crate::Bound,
    ) {
        safe_eprintln!(
            "[LRA] contradictory bounds precheck on {}",
            self.debug_format_var(var)
        );
        safe_eprintln!("[LRA]   {}", self.debug_format_bound("lower", lower));
        safe_eprintln!("[LRA]   {}", self.debug_format_bound("upper", upper));
    }

    pub(crate) fn debug_log_row_lower_precheck(
        &self,
        row: &TableauRow,
        implied_lower: &Rational,
        lower_strict: bool,
        upper: &crate::Bound,
    ) {
        safe_eprintln!(
            "[LRA] row-strict lower precheck on {}: implied_lower={}{} vs upper={}{}",
            self.debug_format_var(row.basic_var),
            implied_lower,
            if lower_strict { " (strict)" } else { "" },
            upper.value,
            if upper.strict { " (strict)" } else { "" }
        );
        safe_eprintln!("[LRA]   row: {}", self.debug_format_row(row));
        safe_eprintln!("[LRA]   {}", self.debug_format_bound("upper", upper));
    }

    pub(crate) fn debug_log_row_upper_precheck(
        &self,
        row: &TableauRow,
        implied_upper: &Rational,
        upper_strict: bool,
        lower: &crate::Bound,
    ) {
        safe_eprintln!(
            "[LRA] row-strict upper precheck on {}: implied_upper={}{} vs lower={}{}",
            self.debug_format_var(row.basic_var),
            implied_upper,
            if upper_strict { " (strict)" } else { "" },
            lower.value,
            if lower.strict { " (strict)" } else { "" }
        );
        safe_eprintln!("[LRA]   row: {}", self.debug_format_row(row));
        safe_eprintln!("[LRA]   {}", self.debug_format_bound("lower", lower));
    }

    /// Mix a u32 variable ID into a 64-bit hash value (#6221 Finding 1).
    /// Uses splitmix64-style avalanche to ensure XOR-based set hashing
    /// has good collision resistance.
    #[inline]
    pub(super) fn mix_u32(v: u32) -> u64 {
        let mut x = u64::from(v).wrapping_mul(0x9e37_79b9_7f4a_7c15);
        x ^= x >> 30;
        x = x.wrapping_mul(0xbf58_476d_1ce4_e5b9);
        x ^= x >> 27;
        x = x.wrapping_mul(0x94d0_49bb_1331_11eb);
        x ^= x >> 31;
        x
    }

    #[cfg(debug_assertions)]
    pub(super) fn debug_assert_tableau_consistency(&self, context: &str) {
        for (row_idx, row) in self.rows.iter().enumerate() {
            debug_assert!(
                (row.basic_var as usize) < self.vars.len(),
                "BUG: {context}: basic var {} out of range (vars={})",
                row.basic_var,
                self.vars.len()
            );
            debug_assert_eq!(
                self.vars[row.basic_var as usize].status,
                Some(VarStatus::Basic(row_idx)),
                "BUG: {context}: basic var {} status mismatch for row {}",
                row.basic_var,
                row_idx
            );
            for &(var, ref coeff) in &row.coeffs {
                debug_assert!(
                    (var as usize) < self.vars.len(),
                    "BUG: {context}: row {} references out-of-range var {} (vars={})",
                    row_idx,
                    var,
                    self.vars.len()
                );
                debug_assert!(
                    !coeff.is_zero(),
                    "BUG: {context}: row {row_idx} contains explicit zero coefficient for var {var}"
                );
                debug_assert_ne!(
                    var, row.basic_var,
                    "BUG: {context}: row {} includes its basic var {} in coefficient list",
                    row_idx, row.basic_var
                );
                // Cross-row check (#5946): coefficient variables must not be basic
                // in any other row. If they are, the row was constructed without
                // substituting basic variables — a violation of the tableau invariant.
                debug_assert!(
                    !matches!(self.vars[var as usize].status, Some(VarStatus::Basic(_))),
                    "BUG: {context}: row {row_idx} coefficient var {var} is basic (status={:?})",
                    self.vars[var as usize].status
                );
            }
        }
    }

    #[cfg(debug_assertions)]
    pub(super) fn debug_assert_col_index_consistency(&self, context: &str) {
        // For each row, every coefficient variable should appear in col_index
        for (row_idx, row) in self.rows.iter().enumerate() {
            for &(var, _) in &row.coeffs {
                let vi = var as usize;
                debug_assert!(
                    vi < self.col_index.len()
                        && self.col_index[vi].iter().any(|e| e.row_idx == row_idx),
                    "BUG: {context}: var {var} in row {row_idx} but not in col_index"
                );
            }
        }
        // For each col_index entry, the row should actually contain the variable
        for (var, entries) in self.col_index.iter().enumerate() {
            for entry in entries {
                debug_assert!(
                    entry.row_idx < self.rows.len(),
                    "BUG: {context}: col_index[{var}] references out-of-bounds row {}",
                    entry.row_idx
                );
                let has_var = self.rows[entry.row_idx]
                    .coeffs
                    .binary_search_by_key(&(var as u32), |(v, _)| *v)
                    .is_ok();
                debug_assert!(
                    has_var,
                    "BUG: {context}: col_index[{var}] references row {} but row doesn't contain var",
                    entry.row_idx
                );
                // row_pos validation relaxed (#8003 TL87): after eliminating
                // update_col_index_positions_for_row for dense LP performance,
                // row_pos may be stale for surviving entries whose positions shifted
                // due to removals. Consumers (update_nonbasic, pivot) already have
                // O(log w) binary-search fallbacks for stale positions.
            }
        }
    }
}
