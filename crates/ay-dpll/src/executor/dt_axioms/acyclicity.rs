// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Depth-function acyclicity encoding via rank functions
//! (Barrett, Shikanian, Tinelli 2007).
//!
//! Extracted from `dt_axioms.rs` as part of the code-health module split.

// #8529: Use deterministic hash sets in all builds.
use ay_core::kani_compat::DetHashSet as HashSet;
use ay_core::term::Symbol;
use ay_core::{Sort, TermData, TermId};
use num_bigint::BigInt;

use crate::executor::Executor;

impl Executor {
    /// Generate acyclicity depth axioms for DT+arithmetic paths (#1764).
    ///
    /// For inductive datatypes, terms cannot be cyclic (e.g., `x = cons(n, x)` is UNSAT).
    /// This function encodes acyclicity by introducing a depth function for each datatype
    /// and adding strict decrease constraints for datatype-typed constructor arguments:
    ///
    /// For each constructor application `t = C(a_0, ..., a_n)` where `t` has datatype sort D
    /// and argument `a_i` has datatype sort E (including D), we assert:
    /// `depth_D(t) > depth_E(a_i)` (Real depth) or `depth_D(t) >= depth_E(a_i) + 1` (Int depth).
    ///
    /// Any equality cycle implies a strict inequality cycle (d > d), which is impossible.
    ///
    /// The `depth_sort` parameter determines the arithmetic sort for depth functions:
    /// - `Sort::Int` for AUFLIA paths
    /// - `Sort::Real` for AUFLRA paths
    ///
    /// NOTE: Due to limitations in AY's LIA solver (#51), indirect cycles (x = cons(a, y),
    /// y = cons(b, x)) may not be detected. The depth axioms are generated correctly,
    /// but the solver may return SAT or unknown for transitivity-requiring constraints.
    ///
    /// Reference: Barrett, Shikanian, Tinelli (2007), Section 4 - acyclicity via rank functions.
    pub(in crate::executor) fn dt_acyclicity_depth_axioms(
        &mut self,
        depth_sort: Sort,
    ) -> Vec<TermId> {
        self.dt_acyclicity_depth_axioms_up_to(depth_sort, self.ctx.terms.len())
    }

    /// Like [`dt_acyclicity_depth_axioms`], but only scan constructor terms with
    /// `TermId < scan_limit`. Callers that run AFTER selector-axiom generation
    /// pass the PRE-selector term-store length so depth axioms are generated
    /// only for genuine ASSERTED constructor structure and not for the synthetic
    /// `(C (sel0 X) (sel1 X) …)` artifacts the recursive selector unfolding
    /// produces — depth constraints over those artifacts are unsound in theory
    /// combination and yield spurious cycles (#dt-array-acyc wrong-unsat).
    pub(in crate::executor) fn dt_acyclicity_depth_axioms_up_to(
        &mut self,
        depth_sort: Sort,
        scan_limit: usize,
    ) -> Vec<TermId> {
        let mut extra: Vec<TermId> = Vec::new();
        let mut seen: HashSet<TermId> = HashSet::default();

        // Build map: datatype name -> depth function symbol name
        // We use a deterministic naming scheme: __ay_dt_depth_<dt_name>
        let datatype_names: Vec<String> = self
            .ctx
            .datatype_iter()
            .map(|(name, _)| name.to_string())
            .collect();

        if datatype_names.is_empty() {
            return extra;
        }

        // Create a set of datatype names for fast lookup
        let dt_name_set: HashSet<&str> = datatype_names.iter().map(String::as_str).collect();

        // Collect asserted equalities for depth congruence axioms.
        // When `x = C(args)` is asserted, we need `depth(x) = depth(C(args))` to
        // propagate depth constraints through variable indirection (#1764).
        let base_assertions: HashSet<TermId> = self.ctx.assertions.iter().copied().collect();

        // Scan the term store for constructor applications, up to `scan_limit`.
        // The scan window deliberately EXCLUDES synthetic constructor terms the
        // recursive selector unfolding creates (those have TermId >= scan_limit
        // when the caller passes the pre-selector-axiom length) — see the doc
        // comment. Asserted-constructor structure (incl. occurs-check terms) is
        // always below the limit, so genuine direct/indirect cycles are kept.
        let term_len = scan_limit.min(self.ctx.terms.len());
        let one_int = if depth_sort == Sort::Int {
            Some(self.ctx.terms.mk_int(BigInt::from(1)))
        } else {
            None
        };

        for idx in 0..term_len {
            let term = TermId::new(idx as u32);

            // Check if this is a constructor application
            let (ctor_name, args) = match self.ctx.terms.get(term) {
                TermData::App(Symbol::Named(name), args) if !args.is_empty() => {
                    (name.clone(), args.clone())
                }
                _ => continue,
            };

            // Check if this symbol is a constructor
            let Some((dt_name, _ctor_name)) = self.ctx.is_constructor(&ctor_name) else {
                continue;
            };

            // Get depth function name for this datatype
            let depth_fn_name = format!("__ay_dt_depth_{dt_name}");

            // Build depth(C(args)) term
            let depth_term = self.ctx.terms.mk_app(
                Symbol::named(&depth_fn_name),
                vec![term],
                depth_sort.clone(),
            );

            // For each argument, check if it has a datatype sort and add depth constraint
            for arg in &args {
                let arg_sort = self.ctx.terms.sort(*arg);

                // Check if argument sort is a datatype (stored as Uninterpreted in ay)
                let arg_dt_name = match arg_sort {
                    Sort::Uninterpreted(name) if dt_name_set.contains(name.as_str()) => {
                        name.clone()
                    }
                    Sort::Datatype(dt) if dt_name_set.contains(dt.name.as_str()) => dt.name.clone(),
                    _ => continue,
                };

                // Get depth function for argument's datatype
                let arg_depth_fn_name = format!("__ay_dt_depth_{arg_dt_name}");

                // Build depth(arg) term
                let arg_depth_term = self.ctx.terms.mk_app(
                    Symbol::named(&arg_depth_fn_name),
                    vec![*arg],
                    depth_sort.clone(),
                );

                if depth_sort == Sort::Int {
                    // For Int depth, avoid strict inequalities by using:
                    //   depth(C(args)) >= depth(arg) + 1
                    //
                    // This is equivalent to `>` for integer-valued depth functions, and avoids
                    // strict-bound handling in the underlying LRA relaxation (#1776).
                    let rhs = self
                        .ctx
                        .terms
                        .mk_add(vec![arg_depth_term, one_int.expect("one_int initialized")]);
                    let ge_term = self.ctx.terms.mk_ge(depth_term, rhs);
                    if seen.insert(ge_term) {
                        extra.push(ge_term);
                    }
                } else {
                    // Build: depth(C(args)) > depth(arg)
                    let gt_term = self.ctx.terms.mk_app(
                        Symbol::named(">"),
                        vec![depth_term, arg_depth_term],
                        Sort::Bool,
                    );

                    if seen.insert(gt_term) {
                        extra.push(gt_term);
                    }
                }
            }
        }

        // Second pass: Add depth congruence axioms for asserted equalities.
        // When `x = C(args)` is asserted directly, we add `depth(x) = depth(C(args))`
        // to help the arithmetic solver propagate depth constraints through variables.
        // This is needed because the AUFLIA solver may not automatically apply EUF
        // congruence to our newly-introduced depth functions.
        for idx in 0..term_len {
            let term = TermId::new(idx as u32);

            // Only process equalities that are directly asserted
            if !base_assertions.contains(&term) {
                continue;
            }

            // Check if this is an equality between a variable and a constructor
            let (eq_lhs, eq_rhs) = match self.ctx.terms.get(term) {
                TermData::App(Symbol::Named(name), args) if name == "=" && args.len() == 2 => {
                    (args[0], args[1])
                }
                _ => continue,
            };

            // Try both orderings: x = C(args) or C(args) = x
            for (var_term, ctor_term) in [(eq_lhs, eq_rhs), (eq_rhs, eq_lhs)] {
                // Check if ctor_term is a constructor application
                let (ctor_name, _ctor_args) = match self.ctx.terms.get(ctor_term) {
                    TermData::App(Symbol::Named(name), args) if !args.is_empty() => {
                        (name.clone(), args.clone())
                    }
                    _ => continue,
                };

                // Check if it's a constructor
                let Some((dt_name, _)) = self.ctx.is_constructor(&ctor_name) else {
                    continue;
                };

                // Get depth function name
                let depth_fn_name = format!("__ay_dt_depth_{dt_name}");

                // Build depth(var_term) and depth(ctor_term)
                let depth_var = self.ctx.terms.mk_app(
                    Symbol::named(&depth_fn_name),
                    vec![var_term],
                    depth_sort.clone(),
                );
                let depth_ctor = self.ctx.terms.mk_app(
                    Symbol::named(&depth_fn_name),
                    vec![ctor_term],
                    depth_sort.clone(),
                );

                // Build: depth(var) = depth(ctor)
                let depth_eq = self.ctx.terms.mk_eq(depth_var, depth_ctor);

                if seen.insert(depth_eq) {
                    extra.push(depth_eq);
                }

                // Only process the first matching ordering
                break;
            }
        }

        extra
    }
}
