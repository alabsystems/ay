// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Single free variable bound computation for direct enumeration.
//!
//! Extracts bounds from inequality constraints when there is exactly one free
//! variable after Gaussian elimination. Extracted from `bounds.rs` to keep
//! each file under 500 lines.

use super::*;

impl LiaSolver<'_> {
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn compute_single_free_var_bounds(
        &self,
        free_col: usize,
        substitutions: &[SubstitutionTriple<usize, BigRational>],
        term_to_idx: &HashMap<TermId, usize>,
        idx_to_term: &[TermId],
        lower: &mut [Option<BigInt>],
        upper: &mut [Option<BigInt>],
        debug: bool,
    ) {
        for &(literal, value) in &self.assertion_view().inequalities {
            let TermData::App(Symbol::Named(name), args) = self.terms.get(literal) else {
                continue;
            };

            if args.len() != 2 {
                continue;
            }

            #[allow(clippy::match_same_arms)]
            let op = match (name.as_str(), value) {
                (">=", true) => ">=",
                (">=", false) => "<",
                ("<=", true) => "<=",
                ("<=", false) => ">",
                (">", true) => ">",
                (">", false) => "<=",
                ("<", true) => "<",
                ("<", false) => ">=",
                _ => continue,
            };

            let (constant_part, free_coeff) = self.substitute_and_simplify(
                args[0],
                args[1],
                substitutions,
                free_col,
                term_to_idx,
                idx_to_term,
            );

            if free_coeff.is_zero() {
                continue;
            }

            match op {
                ">=" => {
                    if free_coeff.is_positive() {
                        let bound_int = Self::ceil_bigint(&(-&constant_part / &free_coeff));
                        if debug {
                            safe_eprintln!("[ENUM] From >= inequality: t >= {}", bound_int);
                        }
                        lower[0] = Some(match &lower[0] {
                            Some(l) => l.clone().max(bound_int),
                            None => bound_int,
                        });
                    } else {
                        let bound_int = Self::floor_bigint(&(-&constant_part / &free_coeff));
                        if debug {
                            safe_eprintln!("[ENUM] From >= inequality (neg): t <= {}", bound_int);
                        }
                        upper[0] = Some(match &upper[0] {
                            Some(u) => u.clone().min(bound_int),
                            None => bound_int,
                        });
                    }
                }
                "<=" => {
                    if free_coeff.is_positive() {
                        let bound_int = Self::floor_bigint(&(-&constant_part / &free_coeff));
                        if debug {
                            safe_eprintln!("[ENUM] From <= inequality: t <= {}", bound_int);
                        }
                        upper[0] = Some(match &upper[0] {
                            Some(u) => u.clone().min(bound_int),
                            None => bound_int,
                        });
                    } else {
                        let bound_int = Self::ceil_bigint(&(-&constant_part / &free_coeff));
                        if debug {
                            safe_eprintln!("[ENUM] From <= inequality (neg): t >= {}", bound_int);
                        }
                        lower[0] = Some(match &lower[0] {
                            Some(l) => l.clone().max(bound_int),
                            None => bound_int,
                        });
                    }
                }
                ">" => {
                    if free_coeff.is_positive() {
                        let bound = -&constant_part / &free_coeff;
                        let mut adjusted = Self::ceil_bigint(&bound);
                        if Self::is_integer(&bound) {
                            adjusted += BigInt::one();
                        }
                        if debug {
                            safe_eprintln!("[ENUM] From > inequality: t >= {}", adjusted);
                        }
                        lower[0] = Some(match &lower[0] {
                            Some(l) => l.clone().max(adjusted),
                            None => adjusted,
                        });
                    } else {
                        let bound = -&constant_part / &free_coeff;
                        let mut adjusted = Self::floor_bigint(&bound);
                        if Self::is_integer(&bound) {
                            adjusted -= BigInt::one();
                        }
                        if debug {
                            safe_eprintln!("[ENUM] From > inequality (neg): t <= {}", adjusted);
                        }
                        upper[0] = Some(match &upper[0] {
                            Some(u) => u.clone().min(adjusted),
                            None => adjusted,
                        });
                    }
                }
                "<" => {
                    if free_coeff.is_positive() {
                        let bound = -&constant_part / &free_coeff;
                        let mut adjusted = Self::floor_bigint(&bound);
                        if Self::is_integer(&bound) {
                            adjusted -= BigInt::one();
                        }
                        if debug {
                            safe_eprintln!("[ENUM] From < inequality: t <= {}", adjusted);
                        }
                        upper[0] = Some(match &upper[0] {
                            Some(u) => u.clone().min(adjusted),
                            None => adjusted,
                        });
                    } else {
                        let bound = -&constant_part / &free_coeff;
                        let mut adjusted = Self::ceil_bigint(&bound);
                        if Self::is_integer(&bound) {
                            adjusted += BigInt::one();
                        }
                        if debug {
                            safe_eprintln!("[ENUM] From < inequality (neg): t >= {}", adjusted);
                        }
                        lower[0] = Some(match &lower[0] {
                            Some(l) => l.clone().max(adjusted),
                            None => adjusted,
                        });
                    }
                }
                _ => {}
            }
        }
    }
}
