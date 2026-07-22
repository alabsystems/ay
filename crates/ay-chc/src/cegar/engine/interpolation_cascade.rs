// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Pointwise interpolation, interpolation cascade, Farkas cascade, and
//! shared equality probing for CEGAR counterexample refinement.

use super::*;

impl CegarEngine {
    /// Original point-by-point interpolation (fallback when sequence interpolation
    /// does not produce predicates).
    pub(super) fn refine_from_trace_pointwise(&mut self, trace: &[usize]) -> CexAnalysis {
        // For each split point k in the trace where the clause at step k has
        // a predicate head, we build an interpolation query:
        //
        //   A = constraints from steps 0..=k, linked via equalities,
        //       with head args at step k unified with interface variables
        //   B = interface variables unified with body args at step k+1,
        //       constraints from steps k+1..end, linked via equalities
        //
        // The interface variables are the ONLY shared variables between A and B.
        // The interpolant over interface variables becomes a new predicate.

        // Phase 1: Rename variables per step
        let mut step_substs: Vec<Vec<(ChcVar, ChcExpr)>> = Vec::new();
        let mut step_constraints: Vec<ChcExpr> = Vec::new();

        for (step, &edge_idx) in trace.iter().enumerate() {
            let edge = &self.edges[edge_idx];
            let clause = &self.problem.clauses()[edge.clause_index];
            let subst = rename_clause_vars(clause, "_ref", step);
            step_constraints.push(
                clause
                    .body
                    .constraint
                    .as_ref()
                    .map_or(ChcExpr::Bool(true), |c| c.substitute(&subst)),
            );
            step_substs.push(subst);
        }

        // Phase 2: Build linking equalities
        let links = self.build_trace_links(trace, &step_substs);

        // Phase 3: Try interpolation at each split point
        let mut new_predicates: Vec<(PredicateId, ChcExpr)> = Vec::new();

        for split_point in 0..trace.len() {
            let edge = &self.edges[trace[split_point]];
            let clause = &self.problem.clauses()[edge.clause_index];

            let (target_relation, head_args) = match &clause.head {
                ClauseHead::Predicate(pid, args) => (*pid, args.clone()),
                ClauseHead::False => continue,
            };

            if split_point + 1 >= trace.len() {
                continue;
            }

            // Create interface variables for the split point's head
            let canonical_vars = self.canonical_vars(target_relation);
            let iface_vars: Vec<ChcVar> = canonical_vars
                .iter()
                .enumerate()
                .map(|(i, cv)| ChcVar::new(format!("_iface_{i}"), cv.sort.clone()))
                .collect();

            // A-part: constraints for steps 0..=split_point, internal links,
            // and head[split_point] == iface vars
            let mut a_parts: Vec<ChcExpr> = Vec::new();
            a_parts.extend(step_constraints[..=split_point].iter().cloned());
            // Internal A-side links (both endpoints within A)
            for link in &links {
                if link.from_step <= split_point && link.to_step <= split_point {
                    a_parts.extend(link.equalities.iter().cloned());
                }
            }
            // Interface: head args at split_point == iface vars
            for (h_arg, iface_v) in head_args.iter().zip(iface_vars.iter()) {
                let renamed_head = h_arg.substitute(&step_substs[split_point]);
                a_parts.push(ChcExpr::eq(renamed_head, ChcExpr::var(iface_v.clone())));
            }

            // B-part: constraints for steps split_point+1..end, internal links,
            // and iface vars == body args at step split_point+1
            let mut b_parts: Vec<ChcExpr> = Vec::new();
            b_parts.extend(step_constraints[(split_point + 1)..].iter().cloned());
            // Internal B-side links (both endpoints within B)
            for link in &links {
                if link.from_step > split_point && link.to_step > split_point {
                    b_parts.extend(link.equalities.iter().cloned());
                }
            }
            // Interface: iface vars == body args at the first B step that consumes
            // the split_point's head
            for link in &links {
                if link.from_step == split_point && link.to_step > split_point {
                    // Replace the renamed head in the equalities with iface vars
                    let prev_clause =
                        &self.problem.clauses()[self.edges[trace[split_point]].clause_index];
                    if let ClauseHead::Predicate(_, ref prev_head_args) = prev_clause.head {
                        let next_clause =
                            &self.problem.clauses()[self.edges[trace[link.to_step]].clause_index];
                        for (body_pred_id, body_args) in &next_clause.body.predicates {
                            if *body_pred_id == target_relation
                                && body_args.len() == prev_head_args.len()
                            {
                                for (iface_v, b_arg) in iface_vars.iter().zip(body_args.iter()) {
                                    let renamed_body = b_arg.substitute(&step_substs[link.to_step]);
                                    b_parts.push(ChcExpr::eq(
                                        ChcExpr::var(iface_v.clone()),
                                        renamed_body,
                                    ));
                                }
                                break;
                            }
                        }
                    }
                }
            }

            if b_parts.is_empty() {
                continue;
            }

            // Resolve var-var and var-const equalities to express A and B
            // purely in terms of the shared interface variables. The Farkas-based
            // interpolation methods require constraints over shared variables;
            // without resolution, chained equalities like (_ref_0_A = 1) and
            // (_ref_0_A = _iface_0) remain as separate constraints that the
            // syntactic methods cannot combine.
            let iface_names: FxHashSet<String> =
                iface_vars.iter().map(|v| v.name.clone()).collect();

            let a_parts = Self::resolve_equalities(&a_parts, &iface_names);
            let b_parts = Self::resolve_equalities(&b_parts, &iface_names);
            let interpolant =
                self.try_interpolation_cascade(split_point, &a_parts, &b_parts, &iface_names);

            if let Some(interpolant) = interpolant {
                // The interpolant is over _iface_* variables.
                // Map them back to canonical predicate variables.
                let mut back_subst = Vec::new();
                for (iface_v, canonical) in iface_vars.iter().zip(canonical_vars.iter()) {
                    back_subst.push((iface_v.clone(), ChcExpr::var(canonical.clone())));
                }
                let pred = interpolant.substitute(&back_subst);
                if self.config.base.verbose {
                    safe_eprintln!("CEGAR: split {} -> predicate: {}", split_point, pred);
                }

                if !matches!(pred, ChcExpr::Bool(true | false)) {
                    new_predicates.push((target_relation, pred));
                }
            }
        }

        if new_predicates.is_empty() {
            new_predicates = self.generate_template_predicates(trace);
        }

        if new_predicates.is_empty() {
            CexAnalysis::AnalysisFailed
        } else {
            CexAnalysis::Spurious(new_predicates)
        }
    }

    /// Try the full interpolation cascade at a split point.
    /// Mirrors PDR's 5-method approach from pdr/solver/blocking.rs.
    pub(super) fn try_interpolation_cascade(
        &mut self,
        split_point: usize,
        a_parts: &[ChcExpr],
        b_parts: &[ChcExpr],
        shared_vars: &FxHashSet<String>,
    ) -> Option<ChcExpr> {
        let verbose = self.config.base.verbose;

        // Method 1: InterpolatingSmtContext (SMT-backed Farkas via check_with_query)
        let a_formula = ChcExpr::and_all(a_parts.to_vec());
        let b_formula = ChcExpr::and_all(b_parts.to_vec());

        if verbose {
            safe_eprintln!("CEGAR: split {} A-parts ({}):", split_point, a_parts.len());
            for (i, ap) in a_parts.iter().enumerate() {
                safe_eprintln!("  A[{}]: {}", i, ap);
            }
            safe_eprintln!("CEGAR: split {} B-parts ({}):", split_point, b_parts.len());
            for (i, bp) in b_parts.iter().enumerate() {
                safe_eprintln!("  B[{}]: {}", i, bp);
            }
            safe_eprintln!(
                "CEGAR: split {} shared vars: {:?}",
                split_point,
                shared_vars
            );
        }

        // First, verify A∧B is actually UNSAT using the direct check_sat method.
        // The assumption-based solver (InterpolatingSmtContext) can produce false Sat
        // results on formulas with chained var-var equalities, so we use the standard
        // solver as the ground truth for satisfiability.
        let combined = ChcExpr::and(a_formula.clone(), b_formula.clone());
        let direct_check = self
            .smt
            .check_sat_with_timeout(&combined, self.config.query_timeout);
        if !direct_check.is_unsat() {
            if verbose {
                safe_eprintln!(
                    "CEGAR: split {} -> A∧B satisfiable (direct check), skipping",
                    split_point
                );
            }
            return None;
        }

        // A∧B is confirmed UNSAT. Try interpolation methods.

        // Method 0: Equality probing — check if A implies equalities between
        // shared integer variables. Farkas-based methods are biased toward
        // inequalities and often miss equalities like B = C that are critical
        // for multi-predicate chain problems (gj2007_m_1/2/3).
        let eq_itp = self.probe_shared_equalities(split_point, a_parts, b_parts, shared_vars);

        // When equalities are found, they're usually sufficient as predicates
        // on their own. Skip Farkas cascade to avoid bloating the predicate
        // set with redundant bounds (e.g., x ≤ 0 ∧ -x ≤ 0 when x = 0 is
        // already captured). Redundant predicates slow convergence by
        // increasing the number of abstraction checks per state.
        if eq_itp.is_some() {
            return eq_itp;
        }

        // No equalities found — try Farkas-based methods.
        let ineq_itp = self.try_farkas_cascade(
            split_point,
            a_parts,
            b_parts,
            shared_vars,
            &a_formula,
            &b_formula,
        );

        if ineq_itp.is_some() {
            return ineq_itp;
        }

        if verbose {
            safe_eprintln!(
                "CEGAR: split {} -> all interpolation methods failed",
                split_point
            );
        }
        None
    }

    /// Run Farkas-based interpolation methods (1-5) without equality probing.
    /// Returns the first successful interpolant, or None if all methods fail.
    fn try_farkas_cascade(
        &mut self,
        split_point: usize,
        a_parts: &[ChcExpr],
        b_parts: &[ChcExpr],
        shared_vars: &FxHashSet<String>,
        a_formula: &ChcExpr,
        b_formula: &ChcExpr,
    ) -> Option<ChcExpr> {
        let verbose = self.config.base.verbose;

        // Method 1: farkas::compute_interpolant (FM elimination + syntactic Farkas)
        if let Some(itp) = farkas_compute_interpolant(a_parts, b_parts, shared_vars) {
            if verbose {
                safe_eprintln!(
                    "CEGAR: split {} -> interpolant (syntactic Farkas): {}",
                    split_point,
                    itp
                );
            }
            return Some(itp);
        }
        if verbose {
            safe_eprintln!("CEGAR: split {} -> syntactic Farkas failed", split_point);
        }

        // Method 2: InterpolatingSmtContext (SMT-backed Farkas via check_with_query)
        let mut interp_ctx = InterpolatingSmtContext::new();
        interp_ctx.assert_a(a_formula.clone());
        let interp_result = interp_ctx.check_with_query(b_formula);

        match interp_result {
            InterpolatingResult::Unsat(itp) => {
                if verbose {
                    safe_eprintln!(
                        "CEGAR: split {} -> interpolant (SMT Farkas): {}",
                        split_point,
                        itp
                    );
                }
                return Some(itp);
            }
            InterpolatingResult::Sat(model) => {
                if verbose {
                    safe_eprintln!(
                        "CEGAR: split {} -> InterpolatingSmtContext spurious Sat (model bindings: {}, direct check confirmed UNSAT), trying fallbacks",
                        split_point,
                        model.len()
                    );
                }
            }
            InterpolatingResult::Unknown => {
                if verbose {
                    safe_eprintln!(
                        "CEGAR: split {} -> Unknown from InterpolatingSmtContext, trying fallbacks",
                        split_point
                    );
                }
            }
            InterpolatingResult::UnsatNoInterpolant { decode_misses } => {
                if verbose {
                    safe_eprintln!(
                        "CEGAR: split {} -> UnsatNoInterpolant (decode_misses={}), trying fallbacks",
                        split_point,
                        decode_misses,
                    );
                }
            }
        }

        // Method 3: interpolating_sat_constraints (syntactic Farkas/bounds/transitivity)
        match interpolating_sat_constraints(a_parts, b_parts, shared_vars) {
            InterpolatingSatResult::Unsat(itp) => {
                if verbose {
                    safe_eprintln!(
                        "CEGAR: split {} -> interpolant (syntactic sat): {}",
                        split_point,
                        itp
                    );
                }
                return Some(itp);
            }
            _ => {
                if verbose {
                    safe_eprintln!("CEGAR: split {} -> syntactic sat failed", split_point);
                }
            }
        }

        // Method 4: compute_interpolant_from_smt_farkas_history (IUC-based)
        if let Some(itp) = compute_interpolant_from_smt_farkas_history(
            &mut self.smt,
            a_parts,
            b_parts,
            shared_vars,
            verbose,
        ) {
            if verbose {
                safe_eprintln!(
                    "CEGAR: split {} -> interpolant (IUC Farkas history): {}",
                    split_point,
                    itp
                );
            }
            return Some(itp);
        }
        if verbose {
            safe_eprintln!("CEGAR: split {} -> IUC Farkas history failed", split_point);
        }

        // Method 5: compute_interpolant_from_lia_farkas (proof-based, pure LIA)
        if let Some(itp) =
            compute_interpolant_from_lia_farkas(&mut self.smt, a_parts, b_parts, shared_vars)
        {
            if verbose {
                safe_eprintln!(
                    "CEGAR: split {} -> interpolant (LIA Farkas): {}",
                    split_point,
                    itp
                );
            }
            return Some(itp);
        }
        // Method 6: Core-guided FM projection (#7910).
        // Extract the UNSAT core of A ∧ B, identify A-side core conjuncts that
        // mention A-only variables, and project those variables out using
        // Fourier-Motzkin elimination. Unlike method 3f (UNSAT core), which
        // drops any conjunct with A-only variables, this method retains the
        // information by eliminating the private variables algebraically.
        // Unlike method 1 (full-A FM), this focuses on the small UNSAT core,
        // avoiding combinatorial blowup.
        if let Some(itp) =
            self.core_guided_fm_projection(split_point, a_parts, b_parts, shared_vars)
        {
            if verbose {
                safe_eprintln!(
                    "CEGAR: split {} -> interpolant (core FM projection): {}",
                    split_point,
                    itp
                );
            }
            return Some(itp);
        }
        if verbose {
            safe_eprintln!("CEGAR: split {} -> all Farkas methods failed", split_point);
        }

        None
    }

    /// Core-guided Fourier-Motzkin projection interpolation.
    ///
    /// 1. Check A ∧ B is UNSAT and extract the UNSAT core
    /// 2. Partition core into A-side and B-side conjuncts
    /// 3. Identify A-only variables in A-side core
    /// 4. Apply FM elimination to project out A-only variables
    /// 5. Return the conjunction of projected constraints as interpolant
    fn core_guided_fm_projection(
        &mut self,
        split_point: usize,
        a_parts: &[ChcExpr],
        b_parts: &[ChcExpr],
        shared_vars: &FxHashSet<String>,
    ) -> Option<ChcExpr> {
        let verbose = self.config.base.verbose;

        // Build a string set of A-constraints for identification after core extraction.
        let a_strings: FxHashSet<String> = a_parts.iter().map(|e| format!("{e}")).collect();

        // Conjoin A ∧ B and check with core extraction.
        let mut all_parts: Vec<ChcExpr> = Vec::new();
        all_parts.extend_from_slice(a_parts);
        all_parts.extend_from_slice(b_parts);
        let combined = ChcExpr::and_all(all_parts);
        let result = self.smt.check_sat(&combined);

        // Extract core conjuncts.
        let core_conjuncts: Vec<ChcExpr> = match &result {
            SmtResult::UnsatWithCore(core) => core.conjuncts.clone(),
            SmtResult::Unsat | SmtResult::UnsatWithFarkas(_) => {
                // No core available — use all A-parts as fallback.
                a_parts.to_vec()
            }
            _ => return None, // SAT or Unknown — not UNSAT
        };

        // Partition core into A-side conjuncts.
        let a_core: Vec<&ChcExpr> = core_conjuncts
            .iter()
            .filter(|c| a_strings.contains(&format!("{c}")))
            .collect();

        if a_core.is_empty() {
            return None;
        }

        // Collect variables: identify which are shared and which are A-only.
        let mut a_only_vars: Vec<String> = Vec::new();
        let mut core_has_shared = false;
        for c in &a_core {
            for v in c.vars() {
                if shared_vars.contains(&v.name) {
                    core_has_shared = true;
                } else if !a_only_vars.contains(&v.name) {
                    a_only_vars.push(v.name.clone());
                }
            }
        }

        if !core_has_shared || a_only_vars.is_empty() {
            // Either no shared vars in core (nothing to project onto) or
            // no A-only vars to eliminate (already shared-only — method 3f handles this).
            return None;
        }

        // Parse A-core into linear constraints for FM elimination.
        use crate::farkas::{
            checked_r64_add, checked_r64_mul, parse_linear_constraints_split_eq, LinearConstraint,
        };
        let a_core_linear: Vec<LinearConstraint> = a_core
            .iter()
            .flat_map(|e| parse_linear_constraints_split_eq(e))
            .collect();

        if a_core_linear.is_empty() {
            return None;
        }

        // FM elimination: project out each A-only variable.
        a_only_vars.sort_unstable();
        let mut constraints = a_core_linear;

        for var_to_eliminate in &a_only_vars {
            let mut pos = Vec::new();
            let mut neg = Vec::new();
            let mut neutral = Vec::new();

            for c in &constraints {
                let coeff = c.get_coeff(var_to_eliminate);
                if coeff > num_rational::Rational64::from_integer(0) {
                    pos.push(c.clone());
                } else if coeff < num_rational::Rational64::from_integer(0) {
                    neg.push(c.clone());
                } else {
                    neutral.push(c.clone());
                }
            }

            let mut new_constraints = neutral;
            let max_derived = 20;
            let mut derived = 0;

            for p in &pos {
                for n in &neg {
                    if derived >= max_derived {
                        break;
                    }
                    let p_coeff = p.get_coeff(var_to_eliminate);
                    let n_coeff_abs =
                        crate::proof_interpolation::rational64_abs(n.get_coeff(var_to_eliminate));

                    // Combine: n_coeff_abs * p + p_coeff * n
                    let mut new_coeffs = ay_core::kani_compat::DetHashMap::default();
                    let mut overflow = false;

                    for (var, &coeff) in &p.coeffs {
                        let Some(scaled) = checked_r64_mul(coeff, n_coeff_abs) else {
                            overflow = true;
                            break;
                        };
                        *new_coeffs
                            .entry(var.clone())
                            .or_insert(num_rational::Rational64::from_integer(0)) = scaled;
                    }
                    if overflow {
                        continue;
                    }
                    for (var, &coeff) in &n.coeffs {
                        let Some(scaled) = checked_r64_mul(coeff, p_coeff) else {
                            overflow = true;
                            break;
                        };
                        let entry = new_coeffs
                            .entry(var.clone())
                            .or_insert(num_rational::Rational64::from_integer(0));
                        let Some(sum) = checked_r64_add(*entry, scaled) else {
                            overflow = true;
                            break;
                        };
                        *entry = sum;
                    }
                    if overflow {
                        continue;
                    }

                    let bound_p = checked_r64_mul(p.bound, n_coeff_abs);
                    let bound_n = checked_r64_mul(n.bound, p_coeff);
                    let bound = match (bound_p, bound_n) {
                        (Some(bp), Some(bn)) => checked_r64_add(bp, bn),
                        _ => None,
                    };
                    let Some(bound) = bound else { continue };

                    // Remove the eliminated variable and any zero coefficients.
                    new_coeffs.remove(var_to_eliminate);
                    new_coeffs.retain(|_, v| *v != num_rational::Rational64::from_integer(0));

                    new_constraints.push(LinearConstraint {
                        coeffs: new_coeffs,
                        bound,
                        strict: p.strict || n.strict,
                        // CEGAR's cascade parses via the Int-only path and emits
                        // Int atoms (#chc25-lra-convergence: LinearConstraint gained
                        // a var_sort field; this site remains integer).
                        var_sort: crate::ChcSort::Int,
                    });
                    derived += 1;
                }
            }

            constraints = new_constraints;
        }

        // Filter: keep only constraints over shared variables.
        let shared_constraints: Vec<_> = constraints
            .iter()
            .filter(|c| !c.coeffs.is_empty() && c.coeffs.keys().all(|v| shared_vars.contains(v)))
            .collect();

        if shared_constraints.is_empty() {
            return None;
        }

        // Build candidate interpolant from projected constraints.
        use crate::farkas::build_linear_inequality;
        let mut candidates: Vec<ChcExpr> = Vec::new();
        for c in &shared_constraints {
            // i128-lockstep: scaling overflow -> skip candidate (abstention).
            if let Some(expr) = build_linear_inequality(&c.coeffs, c.bound, c.strict) {
                candidates.push(expr);
            }
        }
        if candidates.is_empty() {
            return None;
        }

        let candidate = if candidates.len() == 1 {
            candidates.swap_remove(0)
        } else {
            ChcExpr::and_all(candidates)
        };

        // Validate: A ⊨ candidate and candidate ∧ B is UNSAT.
        let a_formula = ChcExpr::and_all(a_parts.to_vec());
        let b_formula = ChcExpr::and_all(b_parts.to_vec());
        let timeout = std::time::Duration::from_secs(2);

        // Check A ∧ ¬candidate is UNSAT (A implies candidate).
        let a_implies = ChcExpr::and(a_formula, ChcExpr::not(candidate.clone()));
        let check1 = crate::engine_utils::check_sat_with_timeout(&a_implies, timeout);
        if !check1.is_unsat() {
            if verbose {
                safe_eprintln!(
                    "CEGAR: split {} -> core FM: candidate not implied by A",
                    split_point
                );
            }
            return None;
        }

        // Check candidate ∧ B is UNSAT.
        let blocks_b = ChcExpr::and(candidate.clone(), b_formula);
        let check2 = crate::engine_utils::check_sat_with_timeout(&blocks_b, timeout);
        if !check2.is_unsat() {
            if verbose {
                safe_eprintln!(
                    "CEGAR: split {} -> core FM: candidate does not block B",
                    split_point
                );
            }
            return None;
        }

        Some(candidate)
    }

    /// Probe pairs of shared integer variables to find equalities implied by A.
    ///
    /// For each pair (iface_i, iface_j) of integer shared variables, check if
    /// `A ∧ ¬(iface_i = iface_j)` is UNSAT. If so, `A ⊨ iface_i = iface_j`,
    /// making the equality a valid interpolant.
    ///
    /// Prioritizes direct equalities (iface_i = iface_j) over scaled ones
    /// (iface_i = k * iface_j). Direct equalities are almost always inductive
    /// invariants, while scaled ones are often artifacts of trace unrolling depth
    /// that add noise to the predicate set without helping convergence.
    fn probe_shared_equalities(
        &mut self,
        split_point: usize,
        a_parts: &[ChcExpr],
        _b_parts: &[ChcExpr],
        shared_vars: &FxHashSet<String>,
    ) -> Option<ChcExpr> {
        let verbose = self.config.base.verbose;

        // Collect shared integer variables from A-side (sufficient since shared
        // vars must appear in both sides by construction).
        let mut int_shared: Vec<ChcVar> = Vec::new();
        for part in a_parts {
            for v in part.vars() {
                if shared_vars.contains(&v.name)
                    && v.sort == ChcSort::Int
                    && !int_shared.iter().any(|iv| iv.name == v.name)
                {
                    int_shared.push(v);
                }
            }
        }

        if int_shared.is_empty() {
            return None;
        }

        let a_formula = ChcExpr::and_all(a_parts.to_vec());

        // Phase 0: Constant value probing (#7910).
        // Check if A implies v = c for each shared variable and small constants.
        // Catches cases like B = 0 or C = 1 that the var=var probing misses.
        // These constant equalities are critical for multiplication/accumulator
        // invariants where initial values are part of the inductive predicate.
        {
            let probe_timeout = std::time::Duration::from_secs(1);
            let mut const_eqs: Vec<ChcExpr> = Vec::new();
            for v in &int_shared {
                for c in [0i128, 1, -1, 2, -2] {
                    let eq = ChcExpr::eq(ChcExpr::var(v.clone()), ChcExpr::Int(c));
                    let neg_eq = ChcExpr::not(eq.clone());
                    let check = ChcExpr::and(a_formula.clone(), neg_eq);
                    let result = self.smt.check_sat_with_timeout(&check, probe_timeout);
                    if result.is_unsat() {
                        if verbose {
                            safe_eprintln!(
                                "CEGAR: split {} -> constant probe: A ⊨ {} = {}",
                                split_point,
                                v.name,
                                c
                            );
                        }
                        const_eqs.push(eq);
                        break; // one constant per variable is sufficient
                    }
                }
            }
            if !const_eqs.is_empty() {
                let result = if const_eqs.len() == 1 {
                    const_eqs.swap_remove(0)
                } else {
                    ChcExpr::and_all(const_eqs)
                };
                if verbose {
                    safe_eprintln!(
                        "CEGAR: split {} -> interpolant (constant probe): {}",
                        split_point,
                        result
                    );
                }
                return Some(result);
            }
        }

        if int_shared.len() < 2 {
            return None;
        }

        // Phase 1: Probe direct equalities using Union-Find to produce a
        // minimal spanning set. For n variables in the same equivalence class,
        // we need exactly n-1 equalities (a spanning tree), not O(n²).
        // This reduces both predicate bloat and SMT calls.
        let n = int_shared.len();
        let mut uf_parent: Vec<usize> = (0..n).collect();

        fn uf_find(parent: &mut [usize], x: usize) -> usize {
            let mut root = x;
            while parent[root] != root {
                root = parent[root];
            }
            // Path compression
            let mut cur = x;
            while parent[cur] != root {
                let next = parent[cur];
                parent[cur] = root;
                cur = next;
            }
            root
        }

        let mut direct_eqs: Vec<ChcExpr> = Vec::new();

        for i in 0..n {
            for j in (i + 1)..n {
                // Skip if already in same equivalence class — the equality
                // is already implied by transitivity of existing equalities.
                if uf_find(&mut uf_parent, i) == uf_find(&mut uf_parent, j) {
                    continue;
                }

                let eq = ChcExpr::eq(
                    ChcExpr::var(int_shared[i].clone()),
                    ChcExpr::var(int_shared[j].clone()),
                );
                let neg_eq = ChcExpr::not(eq.clone());
                let check = ChcExpr::and(a_formula.clone(), neg_eq);
                let probe_timeout = std::time::Duration::from_secs(1);
                let result = self.smt.check_sat_with_timeout(&check, probe_timeout);
                if result.is_unsat() {
                    if verbose {
                        safe_eprintln!(
                            "CEGAR: split {} -> equality probe: A ⊨ {} = {}",
                            split_point,
                            int_shared[i].name,
                            int_shared[j].name
                        );
                    }
                    direct_eqs.push(eq);
                    // Merge equivalence classes
                    let ri = uf_find(&mut uf_parent, i);
                    let rj = uf_find(&mut uf_parent, j);
                    uf_parent[ri] = rj;
                }
            }
        }

        // If we found direct equalities, return them and skip scaled probing.
        // Direct equalities are more likely to be inductive invariants.
        // Scaled equalities (A = 4*C) are often trace-depth artifacts.
        if !direct_eqs.is_empty() {
            let result = if direct_eqs.len() == 1 {
                direct_eqs.swap_remove(0)
            } else {
                ChcExpr::and_all(direct_eqs)
            };
            if verbose {
                safe_eprintln!(
                    "CEGAR: split {} -> interpolant (equality probe): {}",
                    split_point,
                    result
                );
            }
            return Some(result);
        }

        // Phase 1b: Sum/difference probing (#7910).
        // Check if A implies v_i + v_j = c or v_i - v_j = c for small constants.
        // Critical for multiplication/accumulator invariants where the sum of two
        // variables is preserved across loop iterations (e.g., B + C = original_A).
        {
            let probe_timeout = std::time::Duration::from_secs(1);
            let mut sum_eqs: Vec<ChcExpr> = Vec::new();
            'outer_sum: for i in 0..n {
                for j in (i + 1)..n {
                    let vi = ChcExpr::var(int_shared[i].clone());
                    let vj = ChcExpr::var(int_shared[j].clone());
                    // Try v_i + v_j = c for small constants
                    let sum = ChcExpr::add(vi.clone(), vj.clone());
                    for c in [0i128, 1, -1, 2, -2] {
                        let eq = ChcExpr::eq(sum.clone(), ChcExpr::Int(c));
                        let neg_eq = ChcExpr::not(eq.clone());
                        let check = ChcExpr::and(a_formula.clone(), neg_eq);
                        let result = self.smt.check_sat_with_timeout(&check, probe_timeout);
                        if result.is_unsat() {
                            if verbose {
                                safe_eprintln!(
                                    "CEGAR: split {} -> sum probe: A ⊨ {} + {} = {}",
                                    split_point,
                                    int_shared[i].name,
                                    int_shared[j].name,
                                    c
                                );
                            }
                            sum_eqs.push(eq);
                            if sum_eqs.len() >= 3 {
                                break 'outer_sum;
                            }
                            break; // one sum constant per pair
                        }
                    }
                    // Try v_i - v_j = c for small constants
                    let diff = ChcExpr::sub(vi, vj);
                    for c in [0i128, 1, -1, 2, -2] {
                        let eq = ChcExpr::eq(diff.clone(), ChcExpr::Int(c));
                        let neg_eq = ChcExpr::not(eq.clone());
                        let check = ChcExpr::and(a_formula.clone(), neg_eq);
                        let result = self.smt.check_sat_with_timeout(&check, probe_timeout);
                        if result.is_unsat() {
                            if verbose {
                                safe_eprintln!(
                                    "CEGAR: split {} -> diff probe: A ⊨ {} - {} = {}",
                                    split_point,
                                    int_shared[i].name,
                                    int_shared[j].name,
                                    c
                                );
                            }
                            sum_eqs.push(eq);
                            if sum_eqs.len() >= 3 {
                                break 'outer_sum;
                            }
                            break; // one diff constant per pair
                        }
                    }
                }
            }
            if !sum_eqs.is_empty() {
                let result = if sum_eqs.len() == 1 {
                    sum_eqs.swap_remove(0)
                } else {
                    ChcExpr::and_all(sum_eqs)
                };
                if verbose {
                    safe_eprintln!(
                        "CEGAR: split {} -> interpolant (sum/diff probe): {}",
                        split_point,
                        result
                    );
                }
                return Some(result);
            }
        }

        // Phase 1c: Product probing for multiplication invariants.
        // For s_multipl benchmarks, the invariant is often of the form
        // A * B + C = N (accumulator identity). Probe v_i * v_j = v_k and
        // v_i * v_j + v_k = c. Only when we have 3+ shared variables.
        if n >= 3 {
            let probe_timeout = std::time::Duration::from_secs(1);
            let mut product_eqs: Vec<ChcExpr> = Vec::new();
            'outer_prod: for i in 0..n {
                for j in (i + 1)..n {
                    // Try v_i * v_j = v_k for each remaining variable k
                    let vi = ChcExpr::var(int_shared[i].clone());
                    let vj = ChcExpr::var(int_shared[j].clone());
                    let product = ChcExpr::mul(vi.clone(), vj.clone());
                    for k in 0..n {
                        if k == i || k == j {
                            continue;
                        }
                        let eq = ChcExpr::eq(product.clone(), ChcExpr::var(int_shared[k].clone()));
                        let neg_eq = ChcExpr::not(eq.clone());
                        let check = ChcExpr::and(a_formula.clone(), neg_eq);
                        let result = self.smt.check_sat_with_timeout(&check, probe_timeout);
                        if result.is_unsat() {
                            if verbose {
                                safe_eprintln!(
                                    "CEGAR: split {} -> product probe: A ⊨ {} * {} = {}",
                                    split_point,
                                    int_shared[i].name,
                                    int_shared[j].name,
                                    int_shared[k].name
                                );
                            }
                            product_eqs.push(eq);
                            if product_eqs.len() >= 2 {
                                break 'outer_prod;
                            }
                        }
                    }
                    // Try v_i * v_j + v_k = c for each k and small constants.
                    // This captures the accumulator identity A*B + C = N.
                    for k in 0..n {
                        if k == i || k == j {
                            continue;
                        }
                        let sum =
                            ChcExpr::add(product.clone(), ChcExpr::var(int_shared[k].clone()));
                        for c in [0i128, 1, -1, 2, -2] {
                            let eq = ChcExpr::eq(sum.clone(), ChcExpr::Int(c));
                            let neg_eq = ChcExpr::not(eq.clone());
                            let check = ChcExpr::and(a_formula.clone(), neg_eq);
                            let result = self.smt.check_sat_with_timeout(&check, probe_timeout);
                            if result.is_unsat() {
                                if verbose {
                                    safe_eprintln!(
                                        "CEGAR: split {} -> product+sum probe: A ⊨ {} * {} + {} = {}",
                                        split_point,
                                        int_shared[i].name,
                                        int_shared[j].name,
                                        int_shared[k].name,
                                        c
                                    );
                                }
                                product_eqs.push(eq);
                                if product_eqs.len() >= 2 {
                                    break 'outer_prod;
                                }
                                break; // one constant per triple
                            }
                        }
                    }
                    if product_eqs.len() >= 2 {
                        break 'outer_prod;
                    }
                }
            }
            if !product_eqs.is_empty() {
                let result = if product_eqs.len() == 1 {
                    product_eqs.swap_remove(0)
                } else {
                    ChcExpr::and_all(product_eqs)
                };
                if verbose {
                    safe_eprintln!(
                        "CEGAR: split {} -> interpolant (product probe): {}",
                        split_point,
                        result
                    );
                }
                return Some(result);
            }
        }

        // Phase 1d: Self-product probing for quadratic/triangular invariants.
        // s_multipl_22: 2*B = A*(A+1). #7931 accumulator: sum <= i*i.
        if n >= 2 {
            let probe_timeout = std::time::Duration::from_secs(1);
            let mut self_prod_eqs: Vec<ChcExpr> = Vec::new();
            'outer_self: for i in 0..n {
                let vi = ChcExpr::var(int_shared[i].clone());
                let sq = ChcExpr::mul(vi.clone(), vi.clone());
                for j in 0..n {
                    if j == i {
                        continue;
                    }
                    let vj = ChcExpr::var(int_shared[j].clone());
                    // v_i^2 = v_j
                    let eq = ChcExpr::eq(sq.clone(), vj.clone());
                    let neg = ChcExpr::not(eq.clone());
                    let check = ChcExpr::and(a_formula.clone(), neg);
                    if self
                        .smt
                        .check_sat_with_timeout(&check, probe_timeout)
                        .is_unsat()
                    {
                        if verbose {
                            safe_eprintln!(
                                "CEGAR: split {} -> self-product: A |= {}^2 = {}",
                                split_point,
                                int_shared[i].name,
                                int_shared[j].name
                            );
                        }
                        self_prod_eqs.push(eq);
                        if self_prod_eqs.len() >= 2 {
                            break 'outer_self;
                        }
                    }
                    // v_i^2 + v_i = 2*v_j (triangular identity)
                    let tri = ChcExpr::eq(
                        ChcExpr::add(sq.clone(), vi.clone()),
                        ChcExpr::mul(ChcExpr::int(2), vj.clone()),
                    );
                    let neg = ChcExpr::not(tri.clone());
                    let check = ChcExpr::and(a_formula.clone(), neg);
                    if self
                        .smt
                        .check_sat_with_timeout(&check, probe_timeout)
                        .is_unsat()
                    {
                        if verbose {
                            safe_eprintln!(
                                "CEGAR: split {} -> triangular: A |= {}^2+{} = 2*{}",
                                split_point,
                                int_shared[i].name,
                                int_shared[i].name,
                                int_shared[j].name
                            );
                        }
                        self_prod_eqs.push(tri);
                        if self_prod_eqs.len() >= 2 {
                            break 'outer_self;
                        }
                    }
                    // v_i^2 <= v_j (quadratic bound for #7931)
                    let le = ChcExpr::le(sq.clone(), vj);
                    let neg = ChcExpr::not(le.clone());
                    let check = ChcExpr::and(a_formula.clone(), neg);
                    if self
                        .smt
                        .check_sat_with_timeout(&check, probe_timeout)
                        .is_unsat()
                    {
                        if verbose {
                            safe_eprintln!(
                                "CEGAR: split {} -> self-product: A |= {}^2 <= {}",
                                split_point,
                                int_shared[i].name,
                                int_shared[j].name
                            );
                        }
                        self_prod_eqs.push(le);
                        if self_prod_eqs.len() >= 2 {
                            break 'outer_self;
                        }
                    }
                }
                if self_prod_eqs.len() >= 2 {
                    break 'outer_self;
                }
            }
            if !self_prod_eqs.is_empty() {
                let result = if self_prod_eqs.len() == 1 {
                    self_prod_eqs.swap_remove(0)
                } else {
                    ChcExpr::and_all(self_prod_eqs)
                };
                if verbose {
                    safe_eprintln!(
                        "CEGAR: split {} -> interpolant (self-product): {}",
                        split_point,
                        result
                    );
                }
                return Some(result);
            }
        }

        // Phase 2: No direct equalities — try scaled equalities as fallback.
        // Only probe small constants (2..=5) to keep it bounded.
        for i in 0..n {
            for j in 0..n {
                if i == j {
                    continue;
                }
                for k in 2i128..=5 {
                    let scaled = ChcExpr::mul(ChcExpr::Int(k), ChcExpr::var(int_shared[j].clone()));
                    let eq = ChcExpr::eq(ChcExpr::var(int_shared[i].clone()), scaled);
                    let neg_eq = ChcExpr::not(eq.clone());
                    let check = ChcExpr::and(a_formula.clone(), neg_eq);
                    let probe_timeout = std::time::Duration::from_secs(1);
                    let result = self.smt.check_sat_with_timeout(&check, probe_timeout);
                    if result.is_unsat() {
                        if verbose {
                            safe_eprintln!(
                                "CEGAR: split {} -> scaled equality probe: A ⊨ {} = {}*{}",
                                split_point,
                                int_shared[i].name,
                                k,
                                int_shared[j].name
                            );
                        }
                        // Return the first scaled equality found (most constrained)
                        return Some(eq);
                    }
                }
            }
        }

        if verbose {
            safe_eprintln!(
                "CEGAR: split {} -> equality probe: no implied equalities among {} shared vars",
                split_point,
                int_shared.len()
            );
        }
        None
    }
}
