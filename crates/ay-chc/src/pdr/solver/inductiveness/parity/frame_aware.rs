// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Frame-aware algebraic offset parity analysis.
//!
//! Uses frame[1] equality lemmas, parity lemmas, and transition constraints
//! to algebraically evaluate the parity of offset expressions without SMT
//! queries. Includes CRT (Chinese Remainder Theorem) decomposition for
//! composite moduli and divisibility extraction from constraints.

use super::super::super::PdrSolver;
use crate::{ChcExpr, ChcOp, PredicateId};

impl PdrSolver {
    /// Frame-aware algebraic parity check for offset expressions.
    ///
    /// When `post_def` defines `post = pre + sum(other_vars)`, uses frame[1]
    /// equality lemmas (v1 = v2 → v1 + v2 = 2*v1, always even) and parity
    /// lemmas (v mod k = c) to algebraically evaluate the offset's parity.
    ///
    /// This avoids relying on the SMT solver for mod queries, which often
    /// returns Unknown within the 100ms timeout for mod 2. (#1362)
    fn frame_aware_offset_parity_check(
        &self,
        predicate: PredicateId,
        post_def: &ChcExpr,
        pre_var_name: &str,
        body_args: &[ChcExpr],
        k: i128,
    ) -> bool {
        // Extract sum terms from post_def
        let terms = Self::extract_sum_terms(post_def);

        // Separate pre_var from other terms
        let other_terms: Vec<&ChcExpr> = terms
            .iter()
            .filter(|t| !matches!(t, ChcExpr::Var(v) if v.name == pre_var_name))
            .collect();

        if other_terms.is_empty() {
            return true; // post = pre, identity
        }

        // Build maps from body variable names to canonical variable indices,
        // and collect frame[1] equality and parity information.
        let canonical_vars = match self.canonical_vars(predicate) {
            Some(v) => v,
            None => return false,
        };

        // Map: body_var_name → canonical_var_index
        let mut body_to_canon: ay_core::kani_compat::DetHashMap<String, usize> = Default::default();
        for (ci, body_arg) in body_args.iter().enumerate() {
            if let ChcExpr::Var(v) = body_arg {
                body_to_canon.insert(v.name.clone(), ci);
            }
        }

        // Collect frame[1] equalities: sets of canonical indices that are equal
        let mut equal_to: ay_core::kani_compat::DetHashMap<usize, usize> = Default::default();
        // Collect frame[1] parities: canonical_index → known remainder mod k
        let mut known_parity: ay_core::kani_compat::DetHashMap<usize, i128> = Default::default();

        if self.frames.len() > 1 {
            for lemma in self.frames[1]
                .lemmas
                .iter()
                .filter(|l| l.predicate == predicate)
            {
                // Check for equality: __p_ai = __p_aj
                if let ChcExpr::Op(ChcOp::Eq, args) = &lemma.formula {
                    if args.len() == 2 {
                        if let (ChcExpr::Var(v1), ChcExpr::Var(v2)) =
                            (args[0].as_ref(), args[1].as_ref())
                        {
                            let i1 = canonical_vars.iter().position(|v| v.name == v1.name);
                            let i2 = canonical_vars.iter().position(|v| v.name == v2.name);
                            if let (Some(i1), Some(i2)) = (i1, i2) {
                                equal_to.insert(i1, i2);
                                equal_to.insert(i2, i1);
                            }
                        }
                    }
                }
                // Check for parity: (mod __p_ai k) = c
                if let ChcExpr::Op(ChcOp::Eq, args) = &lemma.formula {
                    if args.len() == 2 {
                        if let (ChcExpr::Op(ChcOp::Mod, mod_args), ChcExpr::Int(c)) =
                            (args[0].as_ref(), args[1].as_ref())
                        {
                            if mod_args.len() == 2 {
                                if let (ChcExpr::Var(v), ChcExpr::Int(m)) =
                                    (mod_args[0].as_ref(), mod_args[1].as_ref())
                                {
                                    if *m == k {
                                        if let Some(ci) =
                                            canonical_vars.iter().position(|cv| cv.name == v.name)
                                        {
                                            known_parity.insert(ci, *c);
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }

        // Now evaluate the parity of the sum of other_terms.
        // Strategy: pair equal variables (their sum is 2*v, always even),
        // then check remaining terms via parity lemmas.
        let mut remaining_parity_sum: i128 = 0;
        let mut used: ay_core::kani_compat::DetHashSet<usize> = Default::default();
        let mut all_resolved = true;

        // First pass: identify canonical indices for each term
        let mut term_indices: Vec<Option<usize>> = Vec::new();
        for term in &other_terms {
            match term {
                ChcExpr::Var(v) => {
                    term_indices.push(body_to_canon.get(&v.name).copied());
                }
                ChcExpr::Int(c) => {
                    remaining_parity_sum += c.rem_euclid(k);
                    term_indices.push(None); // handled as constant
                }
                _ => {
                    all_resolved = false;
                    break;
                }
            }
        }

        if !all_resolved {
            return false;
        }

        // Second pass: pair equal variables
        for (i, idx_opt) in term_indices.iter().enumerate() {
            let ci = match idx_opt {
                Some(ci) => *ci,
                None => continue, // constant, already handled
            };
            if used.contains(&i) {
                continue;
            }
            // Look for another term with an equal canonical index
            if let Some(&partner_ci) = equal_to.get(&ci) {
                // Find another term that maps to partner_ci
                for (j, other_idx_opt) in term_indices.iter().enumerate() {
                    if j <= i || used.contains(&j) {
                        continue;
                    }
                    if *other_idx_opt == Some(partner_ci) {
                        // ci and partner_ci are equal: sum = 2*v, contributes 0 mod 2
                        // More generally for mod k: parity(v + v) = 2*parity(v)
                        // For k=2 this is always 0
                        if k == 2 {
                            used.insert(i);
                            used.insert(j);
                        } else if let Some(&p) = known_parity.get(&ci) {
                            remaining_parity_sum += (2 * p).rem_euclid(k);
                            used.insert(i);
                            used.insert(j);
                        }
                        break;
                    }
                }
            }
        }

        // Third pass: resolve remaining terms via parity lemmas
        for (i, idx_opt) in term_indices.iter().enumerate() {
            if used.contains(&i) {
                continue;
            }
            let ci = match idx_opt {
                Some(ci) => *ci,
                None => continue, // constant, already handled
            };
            if let Some(&p) = known_parity.get(&ci) {
                remaining_parity_sum += p;
                used.insert(i);
            } else {
                all_resolved = false;
                break;
            }
        }

        if !all_resolved {
            return false;
        }

        remaining_parity_sum.rem_euclid(k) == 0
    }

    /// Frame-aware algebraic parity check, extended with constraint parity extraction.
    ///
    /// Like `frame_aware_offset_parity_check`, but also extracts parity information
    /// from the transition constraint (mod-pre-eliminated forms like `V = k*q + r`
    /// where `r = 0`). Uses CRT for composite moduli: if frame says `V mod 2 = 0`
    /// and constraint says `V mod 3 = 0`, deduces `V mod 6 = 0`.
    pub(super) fn frame_aware_offset_parity_check_with_constraint(
        &self,
        predicate: PredicateId,
        post_def: &ChcExpr,
        pre_var_name: &str,
        body_args: &[ChcExpr],
        k: i128,
        constraint: Option<&ChcExpr>,
    ) -> bool {
        // Try the basic frame-only check first
        if self.frame_aware_offset_parity_check(predicate, post_def, pre_var_name, body_args, k) {
            return true;
        }

        // Extract sum terms and identify offset variables
        let terms = Self::extract_sum_terms(post_def);
        let other_terms: Vec<&ChcExpr> = terms
            .iter()
            .filter(|t| !matches!(t, ChcExpr::Var(v) if v.name == pre_var_name))
            .collect();

        if other_terms.is_empty() {
            return true;
        }

        // All offset terms must be variables for CRT analysis
        let offset_var_names: Vec<&str> = other_terms
            .iter()
            .filter_map(|t| match t {
                ChcExpr::Var(v) => Some(v.name.as_str()),
                ChcExpr::Int(c) if c.rem_euclid(k) == 0 => None, // constant 0 mod k
                _ => None,
            })
            .collect();

        // Check for non-zero constant offsets
        for t in &other_terms {
            if let ChcExpr::Int(c) = t {
                if c.rem_euclid(k) != 0 {
                    return false;
                }
            } else if !matches!(t, ChcExpr::Var(_)) {
                return false;
            }
        }

        // Extract constraint parity info for offset variables
        let constraint_divisors = constraint
            .map(Self::extract_constraint_divisors)
            .unwrap_or_default();

        // For each offset variable, check if it's divisible by k using CRT:
        // check each prime factor separately against frame lemmas + constraint
        let canonical_vars = match self.canonical_vars(predicate) {
            Some(v) => v,
            None => return false,
        };

        let mut body_to_canon: ay_core::kani_compat::DetHashMap<&str, usize> = Default::default();
        for (ci, body_arg) in body_args.iter().enumerate() {
            if let ChcExpr::Var(v) = body_arg {
                body_to_canon.insert(v.name.as_str(), ci);
            }
        }

        // Collect all frame parity info (any modulus, not just k)
        let mut frame_parities: ay_core::kani_compat::DetHashMap<(usize, i128), i128> =
            Default::default();
        if self.frames.len() > 1 {
            for lemma in self.frames[1]
                .lemmas
                .iter()
                .filter(|l| l.predicate == predicate)
            {
                if let ChcExpr::Op(ChcOp::Eq, args) = &lemma.formula {
                    if args.len() == 2 {
                        if let (ChcExpr::Op(ChcOp::Mod, mod_args), ChcExpr::Int(c)) =
                            (args[0].as_ref(), args[1].as_ref())
                        {
                            if mod_args.len() == 2 {
                                if let (ChcExpr::Var(v), ChcExpr::Int(m)) =
                                    (mod_args[0].as_ref(), mod_args[1].as_ref())
                                {
                                    if let Some(ci) =
                                        canonical_vars.iter().position(|cv| cv.name == v.name)
                                    {
                                        frame_parities.insert((ci, *m), *c);
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }

        // Exact offset evaluation from the transition guard plus substituted
        // frame bounds. This handles bounded-exit loops after frame retry
        // learns a tight upper bound, e.g. B >= 16 from the clause and
        // B <= 16 from frame[1] imply B = 16, so the offset is 0 mod 16.
        if let Some(offset_mod_k) = self.resolve_offset_sum_mod_k_from_context(
            predicate,
            &other_terms,
            body_args,
            k,
            constraint,
            &body_to_canon,
            &frame_parities,
        ) {
            return offset_mod_k == 0;
        }

        // For composite moduli, try CRT: check if all prime factors have parity 0
        // using a combination of frame lemmas and constraint parity.
        let factors = Self::prime_factors(k);
        if factors.len() <= 1 {
            return false; // Prime modulus or prime-power without exact-value help
        }

        // For each offset variable, verify mod k = 0 via CRT over prime factors
        for var_name in &offset_var_names {
            let ci = match body_to_canon.get(var_name) {
                Some(&ci) => ci,
                None => return false,
            };

            for &p in &factors {
                // Check frame lemma for this variable mod p
                let frame_ok = frame_parities.get(&(ci, p)).map_or(false, |&c| c == 0);

                if frame_ok {
                    continue;
                }

                // Check constraint divisors for this variable
                let constraint_ok = constraint_divisors
                    .get(*var_name)
                    .map_or(false, |divs| divs.iter().any(|&d| d % p == 0));

                if !constraint_ok {
                    return false;
                }
            }
        }

        true
    }

    /// Try to evaluate the offset sum exactly using the transition constraint
    /// plus substituted frame[1] lemmas.
    ///
    /// This complements parity-only reasoning for bounded exits. If the guard
    /// and frame imply `B = 16`, we can use the exact value even when the frame
    /// only knows `B mod 2 = 0`.
    fn resolve_offset_sum_mod_k_from_context(
        &self,
        predicate: PredicateId,
        other_terms: &[&ChcExpr],
        body_args: &[ChcExpr],
        k: i128,
        constraint: Option<&ChcExpr>,
        body_to_canon: &ay_core::kani_compat::DetHashMap<&str, usize>,
        frame_parities: &ay_core::kani_compat::DetHashMap<(usize, i128), i128>,
    ) -> Option<i128> {
        let canonical_vars = self.canonical_vars(predicate)?;

        let mut context_parts: Vec<ChcExpr> = Vec::new();
        if let Some(c) = constraint {
            context_parts.push(c.clone());
        }
        if self.frames.len() > 1 {
            for lemma in self.frames[1]
                .lemmas
                .iter()
                .filter(|l| l.predicate == predicate)
            {
                context_parts.push(Self::substitute_canonical_vars(
                    &lemma.formula,
                    canonical_vars,
                    body_args,
                ));
            }
        }
        let context = ChcExpr::and_all(context_parts);

        let mut total = 0i128;
        for term in other_terms {
            match term {
                ChcExpr::Int(c) => {
                    total = (total + c.rem_euclid(k)).rem_euclid(k);
                }
                ChcExpr::Var(v) => {
                    if let Some(exact) = Self::resolve_exact_value_in_context(&context, &v.name) {
                        total = (total + exact.rem_euclid(k)).rem_euclid(k);
                        continue;
                    }

                    let ci = *body_to_canon.get(v.name.as_str())?;
                    let parity = *frame_parities.get(&(ci, k))?;
                    total = (total + parity).rem_euclid(k);
                }
                _ => return None,
            }
        }

        Some(total.rem_euclid(k))
    }

    /// Resolve an exact integer value for `var_name` from a conjunction of
    /// transition constraints and substituted frame lemmas.
    fn resolve_exact_value_in_context(context: &ChcExpr, var_name: &str) -> Option<i128> {
        if let Some(value) = Self::find_constant_value_in_constraint(context, var_name) {
            return Some(value);
        }

        let lower = Self::tightest_lower_bound_in_context(context, var_name);
        let upper = Self::tightest_upper_bound_in_context(context, var_name);
        match (lower, upper) {
            (Some(lb), Some(ub)) if lb == ub => Some(lb),
            _ => None,
        }
    }

    fn tightest_lower_bound_in_context(context: &ChcExpr, var_name: &str) -> Option<i128> {
        crate::expr::maybe_grow_expr_stack(|| match context {
            ChcExpr::Op(ChcOp::And, args) => args
                .iter()
                .filter_map(|arg| Self::tightest_lower_bound_in_context(arg, var_name))
                .max(),
            ChcExpr::Op(ChcOp::Eq, args) if args.len() == 2 => {
                match (args[0].as_ref(), args[1].as_ref()) {
                    (ChcExpr::Var(v), ChcExpr::Int(n)) | (ChcExpr::Int(n), ChcExpr::Var(v))
                        if v.name == var_name =>
                    {
                        Some(*n)
                    }
                    _ => None,
                }
            }
            ChcExpr::Op(ChcOp::Ge, args) if args.len() == 2 => {
                match (args[0].as_ref(), args[1].as_ref()) {
                    (ChcExpr::Var(v), ChcExpr::Int(n)) if v.name == var_name => Some(*n),
                    _ => None,
                }
            }
            ChcExpr::Op(ChcOp::Gt, args) if args.len() == 2 => {
                match (args[0].as_ref(), args[1].as_ref()) {
                    (ChcExpr::Var(v), ChcExpr::Int(n)) if v.name == var_name => {
                        Some(n.saturating_add(1))
                    }
                    _ => None,
                }
            }
            ChcExpr::Op(ChcOp::Le, args) if args.len() == 2 => {
                match (args[0].as_ref(), args[1].as_ref()) {
                    (ChcExpr::Int(n), ChcExpr::Var(v)) if v.name == var_name => Some(*n),
                    _ => None,
                }
            }
            ChcExpr::Op(ChcOp::Lt, args) if args.len() == 2 => {
                match (args[0].as_ref(), args[1].as_ref()) {
                    (ChcExpr::Int(n), ChcExpr::Var(v)) if v.name == var_name => {
                        Some(n.saturating_add(1))
                    }
                    _ => None,
                }
            }
            ChcExpr::Op(ChcOp::Not, args) if args.len() == 1 => match args[0].as_ref() {
                ChcExpr::Op(ChcOp::Le, inner) if inner.len() == 2 => {
                    match (inner[0].as_ref(), inner[1].as_ref()) {
                        (ChcExpr::Var(v), ChcExpr::Int(n)) if v.name == var_name => {
                            Some(n.saturating_add(1))
                        }
                        _ => None,
                    }
                }
                ChcExpr::Op(ChcOp::Lt, inner) if inner.len() == 2 => {
                    match (inner[0].as_ref(), inner[1].as_ref()) {
                        (ChcExpr::Var(v), ChcExpr::Int(n)) if v.name == var_name => Some(*n),
                        _ => None,
                    }
                }
                ChcExpr::Op(ChcOp::Ge, inner) if inner.len() == 2 => {
                    match (inner[0].as_ref(), inner[1].as_ref()) {
                        (ChcExpr::Int(n), ChcExpr::Var(v)) if v.name == var_name => {
                            Some(n.saturating_add(1))
                        }
                        _ => None,
                    }
                }
                ChcExpr::Op(ChcOp::Gt, inner) if inner.len() == 2 => {
                    match (inner[0].as_ref(), inner[1].as_ref()) {
                        (ChcExpr::Int(n), ChcExpr::Var(v)) if v.name == var_name => Some(*n),
                        _ => None,
                    }
                }
                _ => None,
            },
            _ => None,
        })
    }

    fn tightest_upper_bound_in_context(context: &ChcExpr, var_name: &str) -> Option<i128> {
        crate::expr::maybe_grow_expr_stack(|| match context {
            ChcExpr::Op(ChcOp::And, args) => args
                .iter()
                .filter_map(|arg| Self::tightest_upper_bound_in_context(arg, var_name))
                .min(),
            ChcExpr::Op(ChcOp::Eq, args) if args.len() == 2 => {
                match (args[0].as_ref(), args[1].as_ref()) {
                    (ChcExpr::Var(v), ChcExpr::Int(n)) | (ChcExpr::Int(n), ChcExpr::Var(v))
                        if v.name == var_name =>
                    {
                        Some(*n)
                    }
                    _ => None,
                }
            }
            ChcExpr::Op(ChcOp::Le, args) if args.len() == 2 => {
                match (args[0].as_ref(), args[1].as_ref()) {
                    (ChcExpr::Var(v), ChcExpr::Int(n)) if v.name == var_name => Some(*n),
                    _ => None,
                }
            }
            ChcExpr::Op(ChcOp::Lt, args) if args.len() == 2 => {
                match (args[0].as_ref(), args[1].as_ref()) {
                    (ChcExpr::Var(v), ChcExpr::Int(n)) if v.name == var_name => {
                        Some(n.saturating_sub(1))
                    }
                    _ => None,
                }
            }
            ChcExpr::Op(ChcOp::Ge, args) if args.len() == 2 => {
                match (args[0].as_ref(), args[1].as_ref()) {
                    (ChcExpr::Int(n), ChcExpr::Var(v)) if v.name == var_name => Some(*n),
                    _ => None,
                }
            }
            ChcExpr::Op(ChcOp::Gt, args) if args.len() == 2 => {
                match (args[0].as_ref(), args[1].as_ref()) {
                    (ChcExpr::Int(n), ChcExpr::Var(v)) if v.name == var_name => {
                        Some(n.saturating_sub(1))
                    }
                    _ => None,
                }
            }
            ChcExpr::Op(ChcOp::Not, args) if args.len() == 1 => match args[0].as_ref() {
                ChcExpr::Op(ChcOp::Ge, inner) if inner.len() == 2 => {
                    match (inner[0].as_ref(), inner[1].as_ref()) {
                        (ChcExpr::Var(v), ChcExpr::Int(n)) if v.name == var_name => {
                            Some(n.saturating_sub(1))
                        }
                        _ => None,
                    }
                }
                ChcExpr::Op(ChcOp::Gt, inner) if inner.len() == 2 => {
                    match (inner[0].as_ref(), inner[1].as_ref()) {
                        (ChcExpr::Var(v), ChcExpr::Int(n)) if v.name == var_name => Some(*n),
                        _ => None,
                    }
                }
                ChcExpr::Op(ChcOp::Le, inner) if inner.len() == 2 => {
                    match (inner[0].as_ref(), inner[1].as_ref()) {
                        (ChcExpr::Int(n), ChcExpr::Var(v)) if v.name == var_name => {
                            Some(n.saturating_sub(1))
                        }
                        _ => None,
                    }
                }
                ChcExpr::Op(ChcOp::Lt, inner) if inner.len() == 2 => {
                    match (inner[0].as_ref(), inner[1].as_ref()) {
                        (ChcExpr::Int(n), ChcExpr::Var(v)) if v.name == var_name => Some(*n),
                        _ => None,
                    }
                }
                _ => None,
            },
            _ => None,
        })
    }

    /// Extract divisibility information from a mod-pre-eliminated constraint.
    /// Returns a map: variable_name → list of known divisors.
    /// Recognizes patterns like: `V = k * q + r` where `r = 0` → V divisible by k.
    fn extract_constraint_divisors(
        constraint: &ChcExpr,
    ) -> ay_core::kani_compat::DetHashMap<String, Vec<i128>> {
        let mut result: ay_core::kani_compat::DetHashMap<String, Vec<i128>> = Default::default();
        // Collect all equalities: var = expr and var = 0
        let mut var_defs: Vec<(String, ChcExpr)> = Vec::new();
        let mut zero_vars: ay_core::kani_compat::DetHashSet<String> = Default::default();
        Self::collect_constraint_equalities(constraint, &mut var_defs, &mut zero_vars);

        // Look for pattern: V = k * Q + R where R is in zero_vars
        // This means V = k * Q, so V is divisible by k.
        for (var_name, expr) in &var_defs {
            if let ChcExpr::Op(ChcOp::Add, args) = expr {
                if args.len() == 2 {
                    // Check k * Q + R pattern
                    if let (ChcExpr::Op(ChcOp::Mul, mul_args), ChcExpr::Var(r)) =
                        (args[0].as_ref(), args[1].as_ref())
                    {
                        if zero_vars.contains(&r.name) {
                            if let Some(k) = Self::extract_mul_constant(mul_args) {
                                result.entry(var_name.clone()).or_default().push(k.abs());
                            }
                        }
                    }
                    // Check R + k * Q pattern
                    if let (ChcExpr::Var(r), ChcExpr::Op(ChcOp::Mul, mul_args)) =
                        (args[0].as_ref(), args[1].as_ref())
                    {
                        if zero_vars.contains(&r.name) {
                            if let Some(k) = Self::extract_mul_constant(mul_args) {
                                result.entry(var_name.clone()).or_default().push(k.abs());
                            }
                        }
                    }
                }
                // Direct k * Q pattern (no remainder term)
                if args.len() == 2 {
                    if let ChcExpr::Op(ChcOp::Mul, mul_args) = expr {
                        if let Some(k) = Self::extract_mul_constant(mul_args) {
                            result.entry(var_name.clone()).or_default().push(k.abs());
                        }
                    }
                }
            }
            // Direct k * Q pattern at top level
            if let ChcExpr::Op(ChcOp::Mul, mul_args) = expr {
                if let Some(k) = Self::extract_mul_constant(mul_args) {
                    result.entry(var_name.clone()).or_default().push(k.abs());
                }
            }
        }

        result
    }

    /// Collect equalities (var = expr) and zero-valued variables from constraint.
    fn collect_constraint_equalities(
        constraint: &ChcExpr,
        var_defs: &mut Vec<(String, ChcExpr)>,
        zero_vars: &mut ay_core::kani_compat::DetHashSet<String>,
    ) {
        match constraint {
            ChcExpr::Op(ChcOp::And, args) => {
                for arg in args {
                    Self::collect_constraint_equalities(arg, var_defs, zero_vars);
                }
            }
            ChcExpr::Op(ChcOp::Eq, args) if args.len() == 2 => {
                match (args[0].as_ref(), args[1].as_ref()) {
                    (ChcExpr::Var(v), ChcExpr::Int(0)) | (ChcExpr::Int(0), ChcExpr::Var(v)) => {
                        zero_vars.insert(v.name.clone());
                    }
                    (ChcExpr::Var(v), expr) => {
                        var_defs.push((v.name.clone(), expr.clone()));
                    }
                    (expr, ChcExpr::Var(v)) => {
                        var_defs.push((v.name.clone(), expr.clone()));
                    }
                    _ => {}
                }
            }
            _ => {}
        }
    }

    /// Extract constant multiplier from a Mul expression like [Int(k), Var(q)].
    fn extract_mul_constant(args: &[std::sync::Arc<ChcExpr>]) -> Option<i128> {
        if args.len() == 2 {
            if let ChcExpr::Int(k) = args[0].as_ref() {
                return Some(*k);
            }
            if let ChcExpr::Int(k) = args[1].as_ref() {
                return Some(*k);
            }
        }
        None
    }

    /// Return prime factors of n (with multiplicity 1 each).
    fn prime_factors(n: i128) -> Vec<i128> {
        let mut n = n.abs();
        let mut factors = Vec::new();
        let mut d = 2i128;
        while d * d <= n {
            if n % d == 0 {
                factors.push(d);
                while n % d == 0 {
                    n /= d;
                }
            }
            d += 1;
        }
        if n > 1 {
            factors.push(n);
        }
        factors
    }
}
