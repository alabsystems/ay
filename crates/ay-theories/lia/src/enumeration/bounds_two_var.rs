// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Two free variable bound computation for direct enumeration.
//!
//! Computes bounds on two free variables by building linear constraints from
//! inequalities and iteratively tightening via cross-variable propagation.
//! Extracted from `bounds.rs` to keep each file under 500 lines.

use super::*;

impl LiaSolver<'_> {
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn compute_two_free_var_bounds(
        &self,
        free_vars: &[usize],
        substitutions: &[SubstitutionTriple<usize, BigRational>],
        idx_to_term: &[TermId],
        term_to_idx: &HashMap<TermId, usize>,
        lower: &mut [Option<BigInt>],
        upper: &mut [Option<BigInt>],
        debug: bool,
    ) {
        #[derive(Clone, Debug)]
        struct Constraint {
            op: IneqOp,
            constant: BigRational,
            c0: BigRational,
            c1: BigRational,
        }

        let fv0 = free_vars[0];
        let fv1 = free_vars[1];
        let mut constraints: Vec<Constraint> = Vec::new();

        for &(literal, value) in &self.assertion_view().inequalities {
            let TermData::App(Symbol::Named(name), args) = self.terms.get(literal) else {
                continue;
            };

            if args.len() != 2 {
                continue;
            }

            #[allow(clippy::match_same_arms)]
            let op = match (name.as_str(), value) {
                (">=", true) => IneqOp::Ge,
                (">=", false) => IneqOp::Lt,
                ("<=", true) => IneqOp::Le,
                ("<=", false) => IneqOp::Gt,
                (">", true) => IneqOp::Gt,
                (">", false) => IneqOp::Le,
                ("<", true) => IneqOp::Lt,
                ("<", false) => IneqOp::Ge,
                _ => continue,
            };

            let (constant_part, coeffs) = self.substitute_and_simplify_multi(
                args[0],
                args[1],
                substitutions,
                free_vars,
                term_to_idx,
            );

            if coeffs[0].is_zero() && coeffs[1].is_zero() {
                continue;
            }

            constraints.push(Constraint {
                op,
                constant: constant_part,
                c0: coeffs[0].clone(),
                c1: coeffs[1].clone(),
            });
        }

        for (pivot_col, pivot_coeffs, pivot_constant) in substitutions {
            if *pivot_col >= idx_to_term.len() {
                continue;
            }
            let pivot_term = idx_to_term[*pivot_col];

            let (pivot_lb, pivot_ub) = match self.lra.get_bounds_ref(pivot_term) {
                Some((lb, ub)) => (lb.map(|b| b.value.clone()), ub.map(|b| b.value.clone())),
                None => (None, None),
            };

            let mut c0 = BigRational::zero();
            let mut c1 = BigRational::zero();
            for (fc, c) in pivot_coeffs {
                if *fc == fv0 {
                    c0 = c.clone();
                } else if *fc == fv1 {
                    c1 = c.clone();
                }
            }
            if c0.is_zero() && c1.is_zero() {
                continue;
            }

            if let Some(lb) = pivot_lb {
                constraints.push(Constraint {
                    op: IneqOp::Ge,
                    constant: pivot_constant - &lb,
                    c0: c0.clone(),
                    c1: c1.clone(),
                });
            }

            if let Some(ub) = pivot_ub {
                constraints.push(Constraint {
                    op: IneqOp::Le,
                    constant: pivot_constant - &ub,
                    c0,
                    c1,
                });
            }
        }

        let mut changed = true;
        let mut iterations = 0usize;
        while changed && iterations < 20 {
            changed = false;
            iterations += 1;

            let [t0_lower, t1_lower] = lower else {
                unreachable!("free_vars.len()==2 implies lower.len()==2");
            };
            let [t0_upper, t1_upper] = upper else {
                unreachable!("free_vars.len()==2 implies upper.len()==2");
            };

            for c in &constraints {
                changed |= Self::tighten_two_var_bound(
                    c.op,
                    &c.constant,
                    &c.c0,
                    &c.c1,
                    t1_lower.as_ref(),
                    t1_upper.as_ref(),
                    t0_lower,
                    t0_upper,
                );
                changed |= Self::tighten_two_var_bound(
                    c.op,
                    &c.constant,
                    &c.c1,
                    &c.c0,
                    t0_lower.as_ref(),
                    t0_upper.as_ref(),
                    t1_lower,
                    t1_upper,
                );
            }
        }

        if debug {
            safe_eprintln!(
                "[ENUM] 2D bound propagation iterations: {}, bounds t0=[{:?},{:?}] t1=[{:?},{:?}] ({} constraints)",
                iterations,
                lower[0],
                upper[0],
                lower[1],
                upper[1],
                constraints.len()
            );
        }
    }

    /// Tighten bounds on one free variable using bounds on another.
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn tighten_two_var_bound(
        op: IneqOp,
        constant: &BigRational,
        a: &BigRational,
        b: &BigRational,
        other_lower: Option<&BigInt>,
        other_upper: Option<&BigInt>,
        this_lower: &mut Option<BigInt>,
        this_upper: &mut Option<BigInt>,
    ) -> bool {
        #[derive(Clone, Copy, Debug)]
        enum BoundKind {
            LowerInclusive,
            LowerStrict,
            UpperInclusive,
            UpperStrict,
        }

        let (bound_kind, use_min_over_other) = match op {
            IneqOp::Ge => {
                if a.is_positive() {
                    (BoundKind::LowerInclusive, true)
                } else if a.is_negative() {
                    (BoundKind::UpperInclusive, false)
                } else {
                    return false;
                }
            }
            IneqOp::Gt => {
                if a.is_positive() {
                    (BoundKind::LowerStrict, true)
                } else if a.is_negative() {
                    (BoundKind::UpperStrict, false)
                } else {
                    return false;
                }
            }
            IneqOp::Le => {
                if a.is_positive() {
                    (BoundKind::UpperInclusive, false)
                } else if a.is_negative() {
                    (BoundKind::LowerInclusive, true)
                } else {
                    return false;
                }
            }
            IneqOp::Lt => {
                if a.is_positive() {
                    (BoundKind::UpperStrict, false)
                } else if a.is_negative() {
                    (BoundKind::LowerStrict, true)
                } else {
                    return false;
                }
            }
        };

        let (rhs_min, rhs_max) = if b.is_zero() {
            let rhs = -constant.clone();
            (rhs.clone(), rhs)
        } else {
            let (Some(ol), Some(ou)) = (other_lower, other_upper) else {
                return false;
            };

            let ol = BigRational::from(ol.clone());
            let ou = BigRational::from(ou.clone());

            let rhs_l = -constant - b * &ol;
            let rhs_u = -constant - b * &ou;
            if rhs_l <= rhs_u {
                (rhs_l, rhs_u)
            } else {
                (rhs_u, rhs_l)
            }
        };

        let min_over_other = if a.is_positive() {
            &rhs_min / a
        } else {
            &rhs_max / a
        };
        let max_over_other = if a.is_positive() {
            &rhs_max / a
        } else {
            &rhs_min / a
        };
        let bound = if use_min_over_other {
            min_over_other
        } else {
            max_over_other
        };

        let mut changed = false;
        match bound_kind {
            BoundKind::LowerInclusive => {
                let new_lb = Self::ceil_bigint(&bound);
                let next = match this_lower.as_ref() {
                    Some(cur) => cur.clone().max(new_lb),
                    None => new_lb,
                };
                if this_lower.as_ref() != Some(&next) {
                    *this_lower = Some(next);
                    changed = true;
                }
            }
            BoundKind::LowerStrict => {
                let mut new_lb = Self::ceil_bigint(&bound);
                if Self::is_integer(&bound) {
                    new_lb += BigInt::one();
                }
                let next = match this_lower.as_ref() {
                    Some(cur) => cur.clone().max(new_lb),
                    None => new_lb,
                };
                if this_lower.as_ref() != Some(&next) {
                    *this_lower = Some(next);
                    changed = true;
                }
            }
            BoundKind::UpperInclusive => {
                let new_ub = Self::floor_bigint(&bound);
                let next = match this_upper.as_ref() {
                    Some(cur) => cur.clone().min(new_ub),
                    None => new_ub,
                };
                if this_upper.as_ref() != Some(&next) {
                    *this_upper = Some(next);
                    changed = true;
                }
            }
            BoundKind::UpperStrict => {
                let mut new_ub = Self::floor_bigint(&bound);
                if Self::is_integer(&bound) {
                    new_ub -= BigInt::one();
                }
                let next = match this_upper.as_ref() {
                    Some(cur) => cur.clone().min(new_ub),
                    None => new_ub,
                };
                if this_upper.as_ref() != Some(&next) {
                    *this_upper = Some(next);
                    changed = true;
                }
            }
        }

        changed
    }
}
