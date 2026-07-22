// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Model-based bound inference and term-level analysis for SmtContext.
//!
//! Companion to `bounds.rs` which contains expression-level (ChcExpr) analysis.
//! This module operates on ay_core term IDs and SAT model assignments.

use super::context::SmtContext;
use super::types::DiseqGuardKind;
use ay_core::term::{Constant, TermData};
use ay_core::{Sort, TermId};
use num_bigint::BigInt;
use num_traits::ToPrimitive;

impl SmtContext {
    /// i128-lockstep: widened from i64 so large (e.g. u64::MAX) type-range
    /// constants participate in bound inference; beyond-i128 stays fail-closed.
    pub(super) fn term_const_i128_if_int(&self, term: TermId) -> Option<i128> {
        match self.terms.get(term) {
            // #3827: return None on overflow instead of saturating to wrong value
            TermData::Const(Constant::Int(n)) => n.to_i128(),
            TermData::Const(Constant::Rational(r)) => {
                if r.0.denom() == &BigInt::from(1) {
                    r.0.numer().to_i128()
                } else {
                    None
                }
            }
            _ => None,
        }
    }

    /// Infer a conservative inclusive integer interval `[lb, ub]` for `variable` from the current
    /// SAT assignment over atomic comparisons.
    ///
    /// This is used to prune infeasible branches for disequality splits (common for `mod` remainders
    /// where bounds like `0 <= r < 2` make `r != 0` deterministically imply `r > 0`).
    pub(super) fn infer_int_bounds_from_sat_model<'a, I>(
        &self,
        variable: TermId,
        model: &[bool],
        var_to_term: I,
    ) -> (Option<i128>, Option<i128>)
    where
        I: IntoIterator<Item = (&'a u32, &'a TermId)>,
    {
        if self.terms.sort(variable) != &Sort::Int {
            return (None, None);
        }

        let mut lower: Option<i128> = None;
        let mut upper: Option<i128> = None;

        for (&var_idx, &term_id) in var_to_term {
            let sat_var = ay_sat::Variable::new(var_idx - 1);
            let Some(&assigned) = model.get(sat_var.index()) else {
                continue;
            };

            let TermData::App(sym, args) = self.terms.get(term_id) else {
                continue;
            };
            if args.len() != 2 {
                continue;
            }

            let op = sym.name();

            // We only extract bounds from atoms where one side is exactly `variable`
            // and the other side is an (integer) constant.
            let (var_on_left, c) = if args[0] == variable {
                let Some(c) = self.term_const_i128_if_int(args[1]) else {
                    continue;
                };
                (true, c)
            } else if args[1] == variable {
                let Some(c) = self.term_const_i128_if_int(args[0]) else {
                    continue;
                };
                (false, c)
            } else {
                continue;
            };

            // Convert atom + assignment into an implied inclusive bound on `variable`.
            // Handle `variable < c` as `variable <= c-1` for Int, etc.
            let mut apply_lower = |v: i128| {
                lower = Some(lower.map_or(v, |cur| cur.max(v)));
            };
            let mut apply_upper = |v: i128| {
                upper = Some(upper.map_or(v, |cur| cur.min(v)));
            };

            match (op, var_on_left, assigned) {
                // variable < c
                ("<", true, true) => {
                    if let Some(v) = c.checked_sub(1) {
                        apply_upper(v);
                    }
                }
                ("<", true, false) => apply_lower(c),
                // c < variable
                ("<", false, true) => {
                    if let Some(v) = c.checked_add(1) {
                        apply_lower(v);
                    }
                }
                ("<", false, false) => apply_upper(c),

                // variable <= c
                ("<=", true, true) => apply_upper(c),
                ("<=", true, false) => {
                    if let Some(v) = c.checked_add(1) {
                        apply_lower(v);
                    }
                }
                // c <= variable
                ("<=", false, true) => apply_lower(c),
                ("<=", false, false) => {
                    if let Some(v) = c.checked_sub(1) {
                        apply_upper(v);
                    }
                }

                // variable > c
                (">", true, true) => {
                    if let Some(v) = c.checked_add(1) {
                        apply_lower(v);
                    }
                }
                (">", true, false) => apply_upper(c),
                // c > variable
                (">", false, true) => {
                    if let Some(v) = c.checked_sub(1) {
                        apply_upper(v);
                    }
                }
                (">", false, false) => apply_lower(c),

                // variable >= c
                (">=", true, true) => apply_lower(c),
                (">=", true, false) => {
                    if let Some(v) = c.checked_sub(1) {
                        apply_upper(v);
                    }
                }
                // c >= variable
                (">=", false, true) => apply_upper(c),
                (">=", false, false) => {
                    if let Some(v) = c.checked_add(1) {
                        apply_lower(v);
                    }
                }

                // variable = c (only use when true)
                ("=", true, true) => {
                    apply_lower(c);
                    apply_upper(c);
                }
                ("=", false, true) => {
                    apply_lower(c);
                    apply_upper(c);
                }

                _ => {}
            }
        }

        (lower, upper)
    }

    pub(super) fn const_as_big_rational(&self, term: TermId) -> Option<num_rational::BigRational> {
        match self.terms.get(term) {
            TermData::Const(Constant::Int(n)) => Some(num_rational::BigRational::from(n.clone())),
            TermData::Const(Constant::Rational(r)) => Some(r.0.clone()),
            _ => None,
        }
    }

    pub(super) fn find_diseq_guard_atom<'a, I>(
        &self,
        split_variable: TermId,
        excluded_value: &num_rational::BigRational,
        model: &[bool],
        var_to_term: I,
    ) -> Option<(TermId, DiseqGuardKind)>
    where
        I: IntoIterator<Item = (&'a u32, &'a TermId)>,
    {
        for (&var_idx, &term_id) in var_to_term {
            let sat_var = ay_sat::Variable::new(var_idx - 1);
            let Some(&assigned) = model.get(sat_var.index()) else {
                continue;
            };

            let TermData::App(sym, args) = self.terms.get(term_id) else {
                continue;
            };
            if args.len() != 2 {
                continue;
            }

            let sym_name = sym.name();
            if sym_name != "=" && sym_name != "distinct" {
                continue;
            }

            let matches = |a: TermId, b: TermId| -> bool {
                if a != split_variable {
                    return false;
                }
                let Some(c) = self.const_as_big_rational(b) else {
                    return false;
                };
                &c == excluded_value
            };

            let arg0 = args[0];
            let arg1 = args[1];
            let is_match = matches(arg0, arg1) || matches(arg1, arg0);
            if !is_match {
                continue;
            }

            // Only treat this atom as the guard if it currently asserts the disequality:
            // - (distinct x c) asserted true
            // - (= x c) asserted false
            if sym_name == "distinct" && assigned {
                return Some((term_id, DiseqGuardKind::Distinct));
            }
            if sym_name == "=" && !assigned {
                return Some((term_id, DiseqGuardKind::Eq));
            }
        }
        None
    }
}
