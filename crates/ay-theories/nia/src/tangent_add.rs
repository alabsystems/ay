// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Linearization constraints for NIA solver: McCormick envelopes + tangent planes
//!
//! ## McCormick Envelopes (binary monomials with known bounds)
//!
//! For m = x*y with x in [xL, xU], y in [yL, yU], the tightest convex
//! relaxation is the McCormick envelope (McCormick, 1976):
//!
//!   Lower: m >= xL*y + x*yL - xL*yL   (tangent at (xL, yL))
//!          m >= xU*y + x*yU - xU*yU   (tangent at (xU, yU))
//!   Upper: m <= xU*y + x*yL - xU*yL   (tangent at (xU, yL))
//!          m <= xL*y + x*yU - xL*yU   (tangent at (xL, yU))
//!
//! These are globally valid over the box [xL,xU] x [yL,yU].
//!
//! ## Tangent hyperplanes (higher-degree monomials)
//!
//! For m = x1*x2*...*xn at model point (v1,...,vn):
//!   T(x1,...,xn) = sum_i (prod_{j!=i} vj) * xi - (n-1) * prod_i vi
//!
//! Based on Z3's `nla_tangent_lemmas.cpp`.

use num_rational::BigRational;
use num_traits::{One, Zero};

use super::*;

impl NiaSolver<'_> {
    /// Add a single McCormick bound: m - a*y - b*x [cmp] -a*b
    ///
    /// `vars`: (m_var, x_var, y_var) -- LRA variable indices for the monomial.
    ///
    /// `reasons` are the asserted atoms justifying the two variable bounds the
    /// envelope was built from (#nia-mccormick-reasons). The McCormick
    /// inequality is a valid theorem *conditional on those bounds*, so the cut
    /// must carry them: a reason-less cut is only justified by its
    /// `source_term` sentinel (the monomial term, which is not a boolean
    /// atom), and the LRA justification audit rightly retracts such bounds as
    /// unjustified ("reason atoms not asserted"), silently discarding the
    /// envelope and leaving box-bounded UNSAT goals (e.g. `0 <= x <= c1 &&
    /// 0 <= z <= c2 && x*z > c1*c2`) at `unknown`. With the real reasons the
    /// cut survives the audit and any LIA/LRA Farkas conflict it joins
    /// explains itself with exactly those literals — a valid conflict clause.
    /// When a used bound carries no reason atoms (empty `reasons`), we fall
    /// back to the historical sentinel path unchanged.
    fn add_mccormick_bound(
        &mut self,
        m: TermId,
        vars: (u32, u32, u32),
        a_val: &BigRational,
        b_val: &BigRational,
        is_lower: bool,
        reasons: Vec<(TermId, bool)>,
    ) {
        let (m_var, x_var, y_var) = vars;
        let coeffs = vec![
            (m_var, BigRational::one()),
            (y_var, -a_val.clone()),
            (x_var, -b_val.clone()),
        ];
        let bound = -(a_val * b_val);
        self.lia.lra_solver_mut().add_gomory_cut(
            &GomoryCut {
                coeffs,
                bound,
                is_lower,
                reasons,
                source_term: None,
            },
            m,
        );
    }

    /// Add McCormick envelope constraints for a binary monomial m = x*y.
    ///
    /// Uses bounds from the LRA solver to generate globally valid linear
    /// relaxations. Returns the number of constraints added.
    pub(crate) fn add_mccormick_constraints(&mut self, mon: &Monomial) -> usize {
        if !mon.is_binary() {
            return 0;
        }

        let Some(x) = mon.x() else { return 0 };
        let Some(y) = mon.y() else { return 0 };
        let m = mon.aux_var;

        let (x_lb, x_ub) = match self.lia.lra_solver().get_bounds(x) {
            Some((lb, ub)) => (lb, ub),
            None => return 0,
        };
        let (y_lb, y_ub) = match self.lia.lra_solver().get_bounds(y) {
            Some((lb, ub)) => (lb, ub),
            None => return 0,
        };

        let lra = self.lia.lra_solver_mut();
        let vars = (
            lra.ensure_var_registered(m),
            lra.ensure_var_registered(x),
            lra.ensure_var_registered(y),
        );

        // Joint justification of an envelope built from bounds `a` and `b`
        // (#nia-mccormick-reasons): the union of both bounds' reason atoms
        // with their asserted polarities. Empty when EITHER bound carries no
        // reason atoms — conditioning the cut on only one side's reasons
        // would claim the other bound holds unconditionally, which we cannot
        // check here, so we keep the historical sentinel path in that case.
        let joint_reasons = |a: &ay_lra::Bound, b: &ay_lra::Bound| -> Vec<(TermId, bool)> {
            if a.reasons.is_empty() || b.reasons.is_empty() {
                return Vec::new();
            }
            let mut reasons: Vec<(TermId, bool)> = a
                .reasons
                .iter()
                .copied()
                .zip(a.reason_values.iter().copied())
                .chain(
                    b.reasons
                        .iter()
                        .copied()
                        .zip(b.reason_values.iter().copied()),
                )
                .collect();
            reasons.sort_unstable_by_key(|&(t, v)| (t, v));
            reasons.dedup();
            reasons
        };

        let mut count = 0;

        // Lower bound 1: m >= xL*y + yL*x - xL*yL
        if let (Some(ref xl), Some(ref yl)) = (&x_lb, &y_lb) {
            let reasons = joint_reasons(xl, yl);
            self.add_mccormick_bound(m, vars, &xl.value_big(), &yl.value_big(), true, reasons);
            count += 1;
        }
        // Lower bound 2: m >= xU*y + yU*x - xU*yU
        if let (Some(ref xu), Some(ref yu)) = (&x_ub, &y_ub) {
            let reasons = joint_reasons(xu, yu);
            self.add_mccormick_bound(m, vars, &xu.value_big(), &yu.value_big(), true, reasons);
            count += 1;
        }
        // Upper bound 1: m <= xU*y + yL*x - xU*yL
        if let (Some(ref xu), Some(ref yl)) = (&x_ub, &y_lb) {
            let reasons = joint_reasons(xu, yl);
            self.add_mccormick_bound(m, vars, &xu.value_big(), &yl.value_big(), false, reasons);
            count += 1;
        }
        // Upper bound 2: m <= xL*y + yU*x - xL*yU
        if let (Some(ref xl), Some(ref yu)) = (&x_lb, &y_ub) {
            let reasons = joint_reasons(xl, yu);
            self.add_mccormick_bound(m, vars, &xl.value_big(), &yu.value_big(), false, reasons);
            count += 1;
        }

        if self.debug {
            safe_eprintln!(
                "[NIA] McCormick envelope: {} constraints for m={:?}",
                count,
                m
            );
        }

        count
    }

    /// Add a tangent hyperplane constraint for a general degree-N monomial.
    ///
    /// For m = x1*x2*...*xn at model point v = (v1,...,vn):
    ///   T(x) = sum_i (prod_{j!=i} vj) * xi - (n-1) * prod_i vi
    ///
    /// Linear constraint: m - sum_i (prod_{j!=i} vj) * xi  [cmp]  -(n-1) * product
    pub(crate) fn add_tangent_constraint_general(
        &mut self,
        mon: &Monomial,
        factor_values: &[BigRational],
        is_below: bool,
    ) -> bool {
        let n = mon.vars.len();
        if n < 2 || n != factor_values.len() {
            return false;
        }

        let m = mon.aux_var;
        let m_var = self.lia.lra_solver_mut().ensure_var_registered(m);

        // Compute the full product: v1 * v2 * ... * vn
        let mut full_product = BigRational::one();
        for v in factor_values {
            full_product *= v;
        }

        // Build coefficients: m has coefficient 1, each xi has coefficient -(prod_{j!=i} vj)
        let mut coeffs = Vec::with_capacity(n + 1);
        coeffs.push((m_var, BigRational::one()));

        for (i, &var) in mon.vars.iter().enumerate() {
            let var_id = self.lia.lra_solver_mut().ensure_var_registered(var);

            // prod_{j!=i} vj = full_product / vi
            // If vi = 0, the partial derivative is 0 (skip this term)
            if factor_values[i].is_zero() {
                continue;
            }
            let partial = &full_product / &factor_values[i];
            coeffs.push((var_id, -partial));
        }

        // Bound: -(n-1) * full_product
        let n_minus_1 = BigRational::from_integer((n as i64 - 1).into());
        let bound = -(&n_minus_1 * &full_product);

        let cut = GomoryCut {
            coeffs,
            bound,
            is_lower: is_below,
            reasons: Vec::new(),
            source_term: None,
        };

        self.lia.lra_solver_mut().add_gomory_cut(&cut, m);

        if self.debug {
            safe_eprintln!(
                "[NIA] Added tangent hyperplane (degree {}): {} for m={:?}",
                n,
                if is_below { ">=" } else { "<=" },
                m
            );
        }

        true
    }

    /// Add basic non-negativity lemma for even-power monomials.
    ///
    /// For m = x^2 (or x^2k), m >= 0 is always true. When the LRA model
    /// assigns m < 0, this constraint forces the model to respect the
    /// algebraic identity.
    pub(crate) fn add_even_power_nonneg(&mut self, mon: &Monomial) -> bool {
        // Check if the monomial is an even power: all factors are the same variable.
        if mon.vars.is_empty() {
            return false;
        }
        let first = mon.vars[0];
        let is_even_power =
            mon.vars.len().is_multiple_of(2) && mon.vars.iter().all(|&v| v == first);
        if !is_even_power {
            return false;
        }

        // Check if aux value is already non-negative -- no lemma needed.
        if let Some(v) = self.var_value(mon.aux_var) {
            if v >= BigRational::zero() {
                return false;
            }
        }

        let m_var = self.lia.lra_solver_mut().ensure_var_registered(mon.aux_var);
        let coeffs = vec![(m_var, BigRational::one())];
        let bound = BigRational::zero();
        self.lia.lra_solver_mut().add_gomory_cut(
            &GomoryCut {
                coeffs,
                bound,
                is_lower: true, // m >= 0
                reasons: Vec::new(),
                source_term: None,
            },
            mon.aux_var,
        );
        true
    }

    /// Add McCormick constraints for higher-degree monomials via pairwise
    /// decomposition. For m = x1*x2*...*xN (N >= 3), try to find a
    /// registered sub-monomial aux_ij = xi*xj, then apply McCormick to
    /// aux_ij * (remaining factors treated as a single virtual variable
    /// with model-derived bounds). (#8453)
    ///
    /// Returns the number of constraints added (0 if not applicable).
    pub(crate) fn add_mccormick_pairwise(&mut self, mon: &Monomial) -> usize {
        let n = mon.vars.len();
        if n < 3 || mon.is_binary() {
            return 0;
        }

        // Try each consecutive pair to find a registered sub-monomial
        for i in 0..n {
            for j in (i + 1)..n {
                let mut sub_key = vec![mon.vars[i], mon.vars[j]];
                sub_key.sort_by_key(|t| t.0);
                let sub_aux = match self.monomials.get(&sub_key) {
                    Some(sub_mon) => sub_mon.aux_var,
                    None => continue,
                };

                // Compute the product of remaining factors from the model
                let mut remaining_product = BigRational::one();
                let mut all_known = true;
                for (k, &var) in mon.vars.iter().enumerate() {
                    if k == i || k == j {
                        continue;
                    }
                    if let Some(val) = self.var_value(var) {
                        remaining_product *= val;
                    } else {
                        all_known = false;
                        break;
                    }
                }
                if !all_known || remaining_product.is_zero() {
                    continue;
                }

                // We now treat this as: m = sub_aux * remaining_product_value
                // Since remaining_product is a model-derived constant, we can
                // add: m >= remaining * sub_aux  (or <=) as a tangent-style cut
                // This is equivalent to fixing the remaining variables at their
                // model values and doing McCormick on the sub_aux * rest pair.

                // Get bounds on sub_aux
                let (sub_lb, sub_ub) = match self.lia.lra_solver().get_bounds(sub_aux) {
                    Some((lb, ub)) => (lb, ub),
                    None => continue,
                };

                let m = mon.aux_var;
                let m_var = self.lia.lra_solver_mut().ensure_var_registered(m);
                let sub_var = self.lia.lra_solver_mut().ensure_var_registered(sub_aux);
                let mut count = 0;

                // McCormick-style bounds with the remaining product as a constant multiplier:
                // m = sub_aux * R  where R = remaining_product (constant at model point)
                // If R > 0: m >= R * sub_lb  and  m <= R * sub_ub
                // If R < 0: m <= R * sub_lb  and  m >= R * sub_ub
                let r_positive = remaining_product > BigRational::zero();

                // Lower bound using sub_lb
                if let Some(ref lb) = sub_lb {
                    let lb_val = lb.value_big();
                    // m - R * sub_aux >= -R * sub_lb  (when R > 0)
                    // Rearranged: m >= R * sub_aux + something (not quite McCormick)
                    // Simpler: direct bound: m [>=|<=] R * lb_val
                    let bound_val = &remaining_product * &lb_val;
                    self.lia.lra_solver_mut().add_gomory_cut(
                        &GomoryCut {
                            coeffs: vec![(m_var, BigRational::one())],
                            bound: bound_val,
                            is_lower: r_positive,
                            reasons: Vec::new(),
                            source_term: None,
                        },
                        m,
                    );
                    count += 1;
                }

                // Upper bound using sub_ub
                if let Some(ref ub) = sub_ub {
                    let ub_val = ub.value_big();
                    let bound_val = &remaining_product * &ub_val;
                    self.lia.lra_solver_mut().add_gomory_cut(
                        &GomoryCut {
                            coeffs: vec![(m_var, BigRational::one())],
                            bound: bound_val,
                            is_lower: !r_positive,
                            reasons: Vec::new(),
                            source_term: None,
                        },
                        m,
                    );
                    count += 1;
                }

                // Also add a linearization: m - R * sub_aux [cmp] 0
                // which encodes m = R * sub_aux at the tangent point
                let coeffs = vec![
                    (m_var, BigRational::one()),
                    (sub_var, -remaining_product.clone()),
                ];
                // When m < R * sub_aux, we need m >= R * sub_aux (is_lower = true)
                let m_val = self.var_value(m);
                let sub_val = self.var_value(sub_aux);
                if let (Some(mv), Some(sv)) = (m_val, sub_val) {
                    let target = &remaining_product * &sv;
                    let is_lower = mv < target;
                    self.lia.lra_solver_mut().add_gomory_cut(
                        &GomoryCut {
                            coeffs,
                            bound: BigRational::zero(),
                            is_lower,
                            reasons: Vec::new(),
                            source_term: None,
                        },
                        m,
                    );
                    count += 1;
                }

                if self.debug && count > 0 {
                    safe_eprintln!(
                        "[NIA] McCormick pairwise: {} constraints for degree-{} m={:?} via sub={:?}",
                        count,
                        n,
                        m,
                        sub_aux
                    );
                }

                return count;
            }
        }

        0
    }

    /// Add secant cut for even-power monomials m = x^(2k).
    ///
    /// For x in [L, U], the secant line from (L, L^(2k)) to (U, U^(2k))
    /// provides a sound upper bound: m <= slope * x + intercept
    /// where slope = (U^(2k) - L^(2k)) / (U - L).
    ///
    /// This is tighter than the tangent plane for convex even-power functions
    /// because the tangent underestimates while the secant provides the global
    /// upper envelope. Together they form a tighter relaxation. (#8453)
    pub(crate) fn add_secant_cut(&mut self, mon: &Monomial) -> bool {
        // Check: even power of a single variable
        if mon.vars.is_empty() {
            return false;
        }
        let first = mon.vars[0];
        let is_even_power = mon.vars.len().is_multiple_of(2)
            && mon.vars.len() >= 2
            && mon.vars.iter().all(|&v| v == first);
        if !is_even_power {
            return false;
        }

        let degree = mon.vars.len();

        // Get bounds on the base variable
        let (lb_opt, ub_opt) = match self.lia.lra_solver().get_bounds(first) {
            Some((lb, ub)) => (lb, ub),
            None => return false,
        };

        let (lb_bound, ub_bound) = match (lb_opt, ub_opt) {
            (Some(lb), Some(ub)) => (lb, ub),
            _ => return false,
        };

        let l = lb_bound.value_big();
        let u = ub_bound.value_big();

        // Need L != U for the secant slope to be well-defined
        if l == u {
            return false;
        }

        // Compute L^degree and U^degree
        let mut l_pow = BigRational::one();
        for _ in 0..degree {
            l_pow *= &l;
        }
        let mut u_pow = BigRational::one();
        for _ in 0..degree {
            u_pow *= &u;
        }

        // Slope = (U^deg - L^deg) / (U - L)
        let denom = &u - &l;
        if denom.is_zero() {
            return false;
        }
        let slope = (&u_pow - &l_pow) / &denom;

        // Intercept = L^deg - slope * L
        let intercept = &l_pow - &slope * &l;

        // Add cut: m <= slope * x + intercept
        // Rearranged: m - slope * x <= intercept
        let m_var = self.lia.lra_solver_mut().ensure_var_registered(mon.aux_var);
        let x_var = self.lia.lra_solver_mut().ensure_var_registered(first);

        let coeffs = vec![(m_var, BigRational::one()), (x_var, -slope.clone())];

        self.lia.lra_solver_mut().add_gomory_cut(
            &GomoryCut {
                coeffs,
                bound: intercept,
                is_lower: false, // m - slope*x <= intercept (upper bound)
                reasons: Vec::new(),
                source_term: None,
            },
            mon.aux_var,
        );

        if self.debug {
            safe_eprintln!(
                "[NIA] Secant cut: x^{} for x={:?}, L={}, U={}, slope={}",
                degree,
                first,
                l,
                u,
                slope
            );
        }

        true
    }

    /// Apply enhanced refinement: McCormick pairwise decomposition and secant
    /// cuts for monomials that the basic tangent planes cannot handle well.
    /// Returns the total number of constraints added. (#8453)
    pub(crate) fn apply_enhanced_refinement(&mut self) -> usize {
        let mut count = 0;

        // Collect inconsistent monomials sorted for deterministic processing
        let mut inconsistent: Vec<Monomial> = Vec::new();
        let mut sorted_mons: Vec<_> = self.monomials.values().collect();
        sorted_mons.sort_unstable_by(|a, b| a.vars.cmp(&b.vars));

        for mon in sorted_mons {
            if !self.check_monomial_consistency(mon) {
                inconsistent.push(mon.clone());
            }
        }

        for mon in &inconsistent {
            // Higher-degree: try pairwise McCormick decomposition
            if !mon.is_binary() && mon.vars.len() >= 3 {
                count += self.add_mccormick_pairwise(mon);
            }

            // Even-power: add secant cut (tighter upper bound)
            if self.add_secant_cut(mon) {
                count += 1;
            }
        }

        if self.debug && count > 0 {
            safe_eprintln!(
                "[NIA] Enhanced refinement: {} constraints for {} inconsistent monomials",
                count,
                inconsistent.len()
            );
        }

        count
    }

    /// Add linearization constraints for all monomials with incorrect values.
    /// Uses McCormick envelopes for binary monomials (sound, globally valid).
    /// Falls back to tangent hyperplanes when McCormick is unavailable.
    /// Returns `(total_added, used_tangent_hyperplane)` where `used_tangent_hyperplane`
    /// is true if any tangent hyperplane (model-point approximation) was added.
    pub(crate) fn add_tangent_constraints_for_incorrect_monomials(&mut self) -> (usize, bool) {
        let mut binary_mons: Vec<(Monomial, Vec<BigRational>, bool)> = Vec::new();
        let mut general_constrain: Vec<(Monomial, Vec<BigRational>, bool)> = Vec::new();

        let mut sorted_mons: Vec<_> = self.monomials.values().collect();
        sorted_mons.sort_unstable_by(|a, b| a.vars.cmp(&b.vars));

        for mon in sorted_mons {
            // Collect factor values for all monomials
            let mut factor_values = Vec::with_capacity(mon.vars.len());
            let mut all_known = true;
            for &var in &mon.vars {
                if let Some(val) = self.var_value(var) {
                    factor_values.push(val);
                } else {
                    all_known = false;
                    break;
                }
            }
            if !all_known {
                continue;
            }

            let Some(v) = self.var_value(mon.aux_var) else {
                continue;
            };

            let mut c = BigRational::one();
            for fv in &factor_values {
                c *= fv;
            }

            if v == c {
                continue;
            }

            if mon.is_binary() {
                binary_mons.push((mon.clone(), factor_values, v < c));
            } else {
                general_constrain.push((mon.clone(), factor_values, v < c));
            }
        }

        let mut count = 0;
        let mut used_tangent = false;

        // Binary monomials: try McCormick first, fall back to tangent hyperplane
        for (mon, factor_values, is_below) in binary_mons {
            let mc = self.add_mccormick_constraints(&mon);
            if mc > 0 {
                count += mc;
            } else {
                // McCormick unavailable (unbounded variables). Add basic lemmas
                // and tangent hyperplane at model point instead.
                if self.add_even_power_nonneg(&mon) {
                    count += 1;
                }
                if self.add_tangent_constraint_general(&mon, &factor_values, is_below) {
                    count += 1;
                    used_tangent = true;
                }
            }
        }

        // Higher-degree monomials: McCormick pairwise first, then tangent hyperplane
        for (mon, factor_values, is_below) in general_constrain {
            self.add_even_power_nonneg(&mon);
            // Try pairwise McCormick decomposition first (#8453)
            let mc_pairwise = self.add_mccormick_pairwise(&mon);
            if mc_pairwise > 0 {
                count += mc_pairwise;
            }
            // Add secant cut for even-power monomials (#8453)
            if self.add_secant_cut(&mon) {
                count += 1;
            }
            // Always add tangent hyperplane too (different cut, cumulative tightening)
            if self.add_tangent_constraint_general(&mon, &factor_values, is_below) {
                count += 1;
                used_tangent = true;
            }
        }

        (count, used_tangent)
    }

    /// Recursively scan a term for nonlinear subterms and register them
    pub(crate) fn collect_nonlinear_terms(&mut self, term: TermId) {
        match self.terms.get(term) {
            TermData::App(Symbol::Named(name), args) => {
                match name.as_str() {
                    "*" => {
                        // Find constant factors and variable factors. Track the
                        // PRODUCT of the constant factors so we can reject a term
                        // whose value is `const * product(vars)` rather than the
                        // bare `product(vars)` that the monomial invariant assumes.
                        let mut var_args = Vec::new();
                        let mut const_product = BigInt::one();
                        for &arg in args {
                            if let Some(c) = self.terms.extract_integer_constant(arg) {
                                const_product *= c;
                            } else {
                                var_args.push(arg);
                            }
                        }

                        // If more than one variable factor, it's nonlinear.
                        //
                        // SOUNDNESS (#nia-const-factor): the monomial machinery
                        // (sign/McCormick/tangent/even-power/congruence/
                        // has_inconsistent_monomials) ASSUMES the registered
                        // `aux_var` equals `product(vars)` EXACTLY. When the `*`
                        // term carries a constant factor `c != 1` (e.g. SOM
                        // substitution turns `(* a a)` with `a = 2*b` into
                        // `(* b b 4)`), the term's value is `c * product(vars)`,
                        // so registering it as the aux var makes every consumer
                        // enforce `c*b*b == b*b` — a false relation that excises
                        // genuine models and yields a WRONG-UNSAT (false theorem).
                        // Only register when the constant factor is exactly 1, so
                        // `aux_var == product(vars)` holds. Otherwise leave the
                        // term as an opaque LIA variable: LIA over-approximates it
                        // (any value), which is sound (never wrong-unsat) — the
                        // nonlinear link is simply not enforced for that term.
                        if var_args.len() >= 2 && const_product.is_one() {
                            // Sort for canonical form
                            var_args.sort_by_key(|t| t.0);

                            // Register this monomial if not already registered
                            if !self.monomials.contains_key(&var_args) {
                                // The term itself serves as the auxiliary variable
                                // (representing the value of the product)
                                self.register_monomial(var_args.clone(), term);
                                if self.debug {
                                    safe_eprintln!(
                                        "[NIA] Registered nonlinear term {:?} with vars {:?}",
                                        term,
                                        var_args
                                    );
                                }
                            }
                        } else if var_args.len() >= 2 && self.debug {
                            safe_eprintln!(
                                "[NIA] Skipping scaled monomial {:?} (const factor {:?} != 1) \
                                 to preserve aux==product(vars) invariant",
                                term,
                                const_product
                            );
                        }

                        // Recurse into arguments
                        for &arg in args {
                            self.collect_nonlinear_terms(arg);
                        }
                    }
                    "/" if args.len() == 2 => {
                        // Division purification (#6811, #8453): (/ num denom) with
                        // symbolic denominator -> track for refinement via
                        // denom * div_term = num.
                        let num = args[0];
                        let denom = args[1];
                        let denom_is_const = self.terms.extract_integer_constant(denom).is_some();
                        if !denom_is_const
                            && !self.div_purifications.iter().any(|p| p.div_term == term)
                        {
                            self.div_purifications.push(DivPurification {
                                div_term: term,
                                numerator: num,
                                denominator: denom,
                            });
                        }
                        // Recurse into operands
                        for &arg in args {
                            self.collect_nonlinear_terms(arg);
                        }
                    }
                    "+" | "-" | "/" => {
                        // Recurse into arithmetic operations
                        for &arg in args {
                            self.collect_nonlinear_terms(arg);
                        }
                    }
                    "<" | "<=" | ">" | ">=" | "=" | "distinct" => {
                        // Recurse into comparison operands
                        for &arg in args {
                            self.collect_nonlinear_terms(arg);
                        }
                    }
                    _ => {
                        // Unknown function - still recurse
                        for &arg in args {
                            self.collect_nonlinear_terms(arg);
                        }
                    }
                }
            }
            TermData::Not(inner) => {
                self.collect_nonlinear_terms(*inner);
            }
            TermData::Ite(cond, then_b, else_b) => {
                self.collect_nonlinear_terms(*cond);
                self.collect_nonlinear_terms(*then_b);
                self.collect_nonlinear_terms(*else_b);
            }
            TermData::Let(_, body) => {
                self.collect_nonlinear_terms(*body);
            }
            _ => {}
        }
    }

    /// Collect integer variables from a term
    pub(crate) fn collect_integer_vars(&mut self, term: TermId) {
        match self.terms.get(term) {
            TermData::Var(_, _) => {
                if matches!(self.terms.sort(term), Sort::Int) {
                    self.lia.register_integer_var(term);
                }
            }
            TermData::App(_, args) => {
                for &arg in args {
                    self.collect_integer_vars(arg);
                }
            }
            TermData::Not(inner) => {
                self.collect_integer_vars(*inner);
            }
            TermData::Ite(c, t, e) => {
                self.collect_integer_vars(*c);
                self.collect_integer_vars(*t);
                self.collect_integer_vars(*e);
            }
            TermData::Let(_, body) => {
                self.collect_integer_vars(*body);
            }
            _ => {}
        }
    }
}
