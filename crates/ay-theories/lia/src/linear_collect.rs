// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Generic linear term collector for LIA.
//!
//! Unifies three near-identical term-tree walkers (#4817):
//! - `parsing.rs:collect_linear_terms_with_vars` (BigInt, TermId keys)
//! - `cuts.rs:collect_hnf_terms` (BigInt, usize keys via term_to_idx)
//! - `enumeration.rs:collect_rational_terms` (BigRational, usize keys via term_to_idx)

use std::hash::Hash;
use std::ops::{AddAssign, Mul, Neg};

use num_traits::Zero;

// #8529: Use deterministic hash maps in all builds.
use ay_core::kani_compat::DetHashMap as HashMap;

use ay_core::term::{Constant, Symbol, TermData, TermId, TermStore};

/// Walk a term tree collecting linear coefficients and a constant.
///
/// Parameters:
/// - `terms`: Term store for structural analysis
/// - `term`: Root term to collect from
/// - `scale`: Current coefficient scale factor
/// - `coeffs`: Output: variable key → accumulated coefficient
/// - `constant`: Output: accumulated constant term
/// - `resolve_var`: Maps a term to its coefficient key (None = not a variable)
/// - `convert_const`: Extracts a numeric value from a `Constant` node
/// - `extract_mul_const`: Extracts a constant factor from a term (for `*` handling)
/// - `pre_resolve`: If true, call `resolve_var` before structural matching
///   (for AUFLIA where mapped terms override structure)
/// - `fallback_as_var`: If true, treat unrecognized terms as opaque variables
#[allow(clippy::too_many_arguments)]
pub(crate) fn collect_linear_terms<N, K>(
    terms: &TermStore,
    term: TermId,
    scale: &N,
    coeffs: &mut HashMap<K, N>,
    constant: &mut N,
    resolve_var: &impl Fn(TermId) -> Option<K>,
    convert_const: &impl Fn(&Constant) -> Option<N>,
    extract_mul_const: &impl Fn(TermId) -> Option<N>,
    pre_resolve: bool,
    fallback_as_var: bool,
) where
    N: Clone + Zero + AddAssign + Mul<Output = N> + Neg<Output = N>,
    K: Hash + Eq + Ord,
{
    // Pre-match resolution: if the term is a known variable, accumulate
    // and return immediately. This handles AUFLIA where UF applications
    // like (f x) are linearized as atomic variables regardless of structure.
    if pre_resolve {
        if let Some(key) = resolve_var(term) {
            *coeffs.entry(key).or_insert_with(N::zero) += scale.clone();
            return;
        }
    }

    match terms.get(term) {
        TermData::Const(c) => {
            if let Some(val) = convert_const(c) {
                *constant += scale.clone() * val;
            }
        }
        TermData::Var(_, _) => {
            if let Some(key) = resolve_var(term) {
                *coeffs.entry(key).or_insert_with(N::zero) += scale.clone();
            }
        }
        TermData::App(Symbol::Named(name), args) => match name.as_str() {
            "+" => {
                for &arg in args {
                    collect_linear_terms(
                        terms,
                        arg,
                        scale,
                        coeffs,
                        constant,
                        resolve_var,
                        convert_const,
                        extract_mul_const,
                        pre_resolve,
                        fallback_as_var,
                    );
                }
            }
            "-" if args.len() == 1 => {
                let neg_scale = -scale.clone();
                collect_linear_terms(
                    terms,
                    args[0],
                    &neg_scale,
                    coeffs,
                    constant,
                    resolve_var,
                    convert_const,
                    extract_mul_const,
                    pre_resolve,
                    fallback_as_var,
                );
            }
            "-" if args.len() >= 2 => {
                collect_linear_terms(
                    terms,
                    args[0],
                    scale,
                    coeffs,
                    constant,
                    resolve_var,
                    convert_const,
                    extract_mul_const,
                    pre_resolve,
                    fallback_as_var,
                );
                let neg_scale = -scale.clone();
                for &arg in &args[1..] {
                    collect_linear_terms(
                        terms,
                        arg,
                        &neg_scale,
                        coeffs,
                        constant,
                        resolve_var,
                        convert_const,
                        extract_mul_const,
                        pre_resolve,
                        fallback_as_var,
                    );
                }
            }
            "*" => {
                let mut const_factor: Option<N> = None;
                let mut var_args = Vec::new();

                for &arg in args {
                    if let Some(c) = extract_mul_const(arg) {
                        const_factor = Some(match const_factor {
                            Some(f) => f * c,
                            None => c,
                        });
                    } else {
                        var_args.push(arg);
                    }
                }

                let new_scale = match const_factor {
                    Some(f) => scale.clone() * f,
                    None => scale.clone(),
                };

                if var_args.is_empty() {
                    *constant += new_scale;
                } else if var_args.len() == 1 {
                    collect_linear_terms(
                        terms,
                        var_args[0],
                        &new_scale,
                        coeffs,
                        constant,
                        resolve_var,
                        convert_const,
                        extract_mul_const,
                        pre_resolve,
                        fallback_as_var,
                    );
                } else if fallback_as_var {
                    // Non-linear: treat entire * term as opaque variable.
                    // Use original scale (not new_scale) since the const
                    // factors are part of the opaque term's semantics.
                    if let Some(key) = resolve_var(term) {
                        *coeffs.entry(key).or_insert_with(N::zero) += scale.clone();
                    }
                }
                // else: non-linear term silently ignored (HNF/enumeration mode)
            }
            _ => {
                if fallback_as_var {
                    if let Some(key) = resolve_var(term) {
                        *coeffs.entry(key).or_insert_with(N::zero) += scale.clone();
                    }
                }
            }
        },
        _ => {
            if fallback_as_var {
                if let Some(key) = resolve_var(term) {
                    *coeffs.entry(key).or_insert_with(N::zero) += scale.clone();
                }
            }
        }
    }
}
