// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

impl LiaSolver<'_> {
    /// Compute bounds on free variables by substituting into inequalities.
    pub(crate) fn compute_free_var_bounds(
        &self,
        free_vars: &[usize],
        substitutions: &[SubstitutionTriple<usize, BigRational>],
        idx_to_term: &[TermId],
        term_to_idx: &HashMap<TermId, usize>,
        debug: bool,
    ) -> (Vec<Option<BigInt>>, Vec<Option<BigInt>>) {
        let mut lower: Vec<Option<BigInt>> = vec![None; free_vars.len()];
        let mut upper: Vec<Option<BigInt>> = vec![None; free_vars.len()];

        for (i, &free_col) in free_vars.iter().enumerate() {
            if free_col < idx_to_term.len() {
                let term_id = idx_to_term[free_col];
                if let Some((lb, ub)) = self.lra.get_bounds_ref(term_id) {
                    if let Some(lb) = lb {
                        lower[i] = Some(Self::ceil_bigint(&lb.value.to_big()));
                    }
                    if let Some(ub) = ub {
                        upper[i] = Some(Self::floor_bigint(&ub.value.to_big()));
                    }
                }
            }
        }

        for (pivot_col, coeffs, constant) in substitutions {
            if *pivot_col >= idx_to_term.len() {
                continue;
            }
            let pivot_term = idx_to_term[*pivot_col];

            let (pivot_lb, pivot_ub) = match self.lra.get_bounds_ref(pivot_term) {
                Some((lb, ub)) => (lb.map(|b| b.value_big()), ub.map(|b| b.value_big())),
                None => (None, None),
            };

            if coeffs.len() == 1 && free_vars.len() == 1 {
                let (fc, coeff) = &coeffs[0];
                if *fc != free_vars[0] {
                    continue;
                }
                let i = 0;

                if coeff.is_positive() {
                    if let Some(ref lb) = pivot_lb {
                        let bound_int = Self::ceil_bigint(&((lb - constant) / coeff));
                        if debug {
                            safe_eprintln!(
                                "[ENUM] From pivot x{} >= {}: t >= {}",
                                pivot_col,
                                lb,
                                bound_int
                            );
                        }
                        lower[i] = Some(match &lower[i] {
                            Some(l) => l.clone().max(bound_int),
                            None => bound_int,
                        });
                    }
                    if let Some(ref ub) = pivot_ub {
                        let bound_int = Self::floor_bigint(&((ub - constant) / coeff));
                        if debug {
                            safe_eprintln!(
                                "[ENUM] From pivot x{} <= {}: t <= {}",
                                pivot_col,
                                ub,
                                bound_int
                            );
                        }
                        upper[i] = Some(match &upper[i] {
                            Some(u) => u.clone().min(bound_int),
                            None => bound_int,
                        });
                    }
                } else if coeff.is_negative() {
                    if let Some(ref lb) = pivot_lb {
                        let bound_int = Self::floor_bigint(&((lb - constant) / coeff));
                        if debug {
                            safe_eprintln!(
                                "[ENUM] From pivot x{} >= {} (neg coeff): t <= {}",
                                pivot_col,
                                lb,
                                bound_int
                            );
                        }
                        upper[i] = Some(match &upper[i] {
                            Some(u) => u.clone().min(bound_int),
                            None => bound_int,
                        });
                    }
                    if let Some(ref ub) = pivot_ub {
                        let bound_int = Self::ceil_bigint(&((ub - constant) / coeff));
                        if debug {
                            safe_eprintln!(
                                "[ENUM] From pivot x{} <= {} (neg coeff): t >= {}",
                                pivot_col,
                                ub,
                                bound_int
                            );
                        }
                        lower[i] = Some(match &lower[i] {
                            Some(l) => l.clone().max(bound_int),
                            None => bound_int,
                        });
                    }
                }
            }
        }

        if free_vars.len() == 1 {
            self.compute_single_free_var_bounds(
                free_vars[0],
                substitutions,
                term_to_idx,
                idx_to_term,
                &mut lower,
                &mut upper,
                debug,
            );
        } else if free_vars.len() == 2 {
            self.compute_two_free_var_bounds(
                free_vars,
                substitutions,
                idx_to_term,
                term_to_idx,
                &mut lower,
                &mut upper,
                debug,
            );
        }

        (lower, upper)
    }

    /// Substitute pivot variables into an inequality and simplify for 2 free vars.
    pub(crate) fn substitute_and_simplify_multi(
        &self,
        lhs: TermId,
        rhs: TermId,
        substitutions: &[SubstitutionTriple<usize, BigRational>],
        free_cols: &[usize],
        term_to_idx: &HashMap<TermId, usize>,
    ) -> (BigRational, [BigRational; 2]) {
        assert_eq!(
            free_cols.len(),
            2,
            "BUG: substitute_and_simplify_multi requires exactly 2 free columns"
        );
        let free_col0 = free_cols[0];
        let free_col1 = free_cols[1];

        let mut var_coeffs: HashMap<usize, BigRational> = HashMap::default();
        let mut constant = BigRational::zero();

        self.collect_rational_terms(
            lhs,
            &BigRational::one(),
            &mut var_coeffs,
            &mut constant,
            term_to_idx,
        );
        self.collect_rational_terms(
            rhs,
            &-BigRational::one(),
            &mut var_coeffs,
            &mut constant,
            term_to_idx,
        );

        let mut final_constant = constant;
        let mut free_coeffs = [BigRational::zero(), BigRational::zero()];
        free_coeffs[0] = var_coeffs.remove(&free_col0).unwrap_or_default();
        free_coeffs[1] = var_coeffs.remove(&free_col1).unwrap_or_default();

        for (pivot_col, pivot_coeffs, pivot_constant) in substitutions {
            if let Some(pivot_coeff) = var_coeffs.remove(pivot_col) {
                final_constant = &final_constant + &pivot_coeff * pivot_constant;
                for (fc, c) in pivot_coeffs {
                    if *fc == free_col0 {
                        free_coeffs[0] = &free_coeffs[0] + &pivot_coeff * c;
                    } else if *fc == free_col1 {
                        free_coeffs[1] = &free_coeffs[1] + &pivot_coeff * c;
                    }
                }
            }
        }

        (final_constant, free_coeffs)
    }

    /// Substitute pivot variable expressions into an inequality and simplify.
    pub(crate) fn substitute_and_simplify(
        &self,
        lhs: TermId,
        rhs: TermId,
        substitutions: &[SubstitutionTriple<usize, BigRational>],
        free_col: usize,
        term_to_idx: &HashMap<TermId, usize>,
        _idx_to_term: &[TermId],
    ) -> (BigRational, BigRational) {
        let mut var_coeffs: HashMap<usize, BigRational> = HashMap::default();
        let mut constant = BigRational::zero();

        self.collect_rational_terms(
            lhs,
            &BigRational::one(),
            &mut var_coeffs,
            &mut constant,
            term_to_idx,
        );
        self.collect_rational_terms(
            rhs,
            &-BigRational::one(),
            &mut var_coeffs,
            &mut constant,
            term_to_idx,
        );

        let mut final_constant = constant;
        let mut free_coeff = var_coeffs.remove(&free_col).unwrap_or_default();

        for (pivot_col, pivot_coeffs, pivot_constant) in substitutions {
            if let Some(pivot_coeff) = var_coeffs.remove(pivot_col) {
                final_constant = &final_constant + &pivot_coeff * pivot_constant;
                for (fc, c) in pivot_coeffs {
                    if *fc == free_col {
                        free_coeff = &free_coeff + &pivot_coeff * c;
                    }
                }
            }
        }

        (final_constant, free_coeff)
    }

    /// Collect linear terms with rational coefficients.
    pub(crate) fn collect_rational_terms(
        &self,
        term: TermId,
        scale: &BigRational,
        coeffs: &mut HashMap<usize, BigRational>,
        constant: &mut BigRational,
        term_to_idx: &HashMap<TermId, usize>,
    ) {
        let resolve_var = |t: TermId| term_to_idx.get(&t).copied();
        let convert_const = |c: &Constant| -> Option<BigRational> {
            match c {
                Constant::Int(n) => Some(BigRational::from(n.clone())),
                Constant::Rational(r) => Some(r.0.clone()),
                _ => None,
            }
        };
        let terms = self.terms;
        let extract_mul_const = |t: TermId| -> Option<BigRational> {
            fn extract_from(terms: &TermStore, t: TermId) -> Option<BigRational> {
                match terms.get(t) {
                    TermData::Const(Constant::Int(n)) => Some(BigRational::from(n.clone())),
                    TermData::Const(Constant::Rational(r)) => Some(r.0.clone()),
                    TermData::App(Symbol::Named(name), args) if name == "-" && args.len() == 1 => {
                        extract_from(terms, args[0]).map(|n| -n)
                    }
                    _ => None,
                }
            }
            extract_from(terms, t)
        };

        crate::linear_collect::collect_linear_terms(
            self.terms,
            term,
            scale,
            coeffs,
            constant,
            &resolve_var,
            &convert_const,
            &extract_mul_const,
            true,
            false,
        );
    }
}
