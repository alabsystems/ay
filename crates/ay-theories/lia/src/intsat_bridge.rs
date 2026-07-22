// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Bridge between the LIA theory solver and the IntSat CDCL-style ILP solver.
//!
//! IntSat operates on a standalone constraint system (pure integer linear
//! constraints in `<= form`), while LIA is embedded in a DPLL(T) framework
//! with incremental push/pop, Nelson-Oppen, and Farkas certificates.
//!
//! This bridge extracts the current integer constraint system from LIA's
//! asserted atoms and variable bounds, translates it to IntSat format, and
//! runs IntSat as a supplementary UNSAT detector. The key use case is:
//!
//! - **Fast UNSAT detection**: IntSat's CDCL-style search with integer
//!   rounding can detect infeasibility faster than the simplex + branch-and-bound
//!   path for certain constraint structures (e.g., tightly-bounded problems
//!   with many integer variables).
//!
//! IntSat is NOT used as a model source: DPLL(T) requires theory models to
//! be consistent with the Boolean assignment, which IntSat cannot guarantee
//! since it operates on a snapshot of constraints without the Boolean structure.
//!
//! Reference: Nieuwenhuis, Oliveras, Rodriguez-Carbonell.
//! "IntSat: Integer Linear Programming by Conflict-Driven Constraint-Learning."
//! arXiv:2402.15522, February 2024.

// #8529: Use deterministic hash maps in all builds.
use ay_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};
use num_bigint::BigInt;
use num_traits::{One, Zero};

use ay_core::term::{Constant, Symbol, TermData, TermId};
use ay_core::TheoryLit;
use ay_intsat::{Constraint, IntSatResult, VarId};

use crate::LiaSolver;

/// Result of an IntSat probe on the current LIA constraint state.
#[derive(Debug)]
pub(crate) enum IntSatProbeResult {
    /// IntSat determined the constraint system is infeasible.
    Unsat(Vec<TheoryLit>),
    /// IntSat could not determine infeasibility (SAT or resource limit).
    /// The LIA solver should continue with its normal simplex path.
    Inconclusive,
}

/// Maximum number of integer variables for which IntSat probing is attempted.
/// Problems with more variables make the translation overhead and IntSat search
/// too expensive relative to simplex.
const MAX_INTSAT_VARS: usize = 64;

/// Maximum number of constraints extracted for IntSat probing.
const MAX_INTSAT_CONSTRAINTS: usize = 256;

/// Maximum conflicts for the IntSat probe (kept low to avoid spending too
/// much time on a supplementary check).
const INTSAT_PROBE_CONFLICTS: usize = 5_000;

impl LiaSolver<'_> {
    /// Run IntSat as a supplementary UNSAT detector on the current constraint state.
    ///
    /// Extracts integer constraints from asserted atoms and variable bounds,
    /// translates to IntSat format, and runs a bounded search. Returns `Unsat`
    /// only when IntSat proves infeasibility; otherwise returns `Inconclusive`.
    ///
    /// This is designed to be called from `check_inner()` as an early UNSAT
    /// detection path, before the expensive Gomory/HNF/branch-and-bound loop.
    pub(crate) fn intsat_probe(&self) -> IntSatProbeResult {
        // Only attempt on problems with bounded integer variables.
        if self.integer_vars.is_empty() || self.integer_vars.len() > MAX_INTSAT_VARS {
            return IntSatProbeResult::Inconclusive;
        }

        // Build a deterministic variable index.
        let (term_to_idx, idx_to_term) = self.build_var_index();
        let num_vars = idx_to_term.len();

        // Extract constraints from asserted atoms.
        let mut constraints = Vec::new();
        let mut initial_bounds: Vec<(VarId, BigInt, BigInt)> = Vec::new();
        let asserted_lookup: HashSet<(TermId, bool)> = self.asserted.iter().copied().collect();
        let mut bound_reason_literals: Vec<(TermId, bool)> = Vec::new();

        // Collect bounds from LRA solver for each integer variable.
        let mut has_all_bounds = true;
        for (idx, &term) in idx_to_term.iter().enumerate() {
            let Some((lb_opt, ub_opt)) = self.lra.get_bounds(term) else {
                has_all_bounds = false;
                continue;
            };

            for bound in [&lb_opt, &ub_opt].into_iter().flatten() {
                if bound.reasons.is_empty() {
                    return IntSatProbeResult::Inconclusive;
                }
                if bound.reasons.len() != bound.reason_values.len() {
                    return IntSatProbeResult::Inconclusive;
                }
                for (&reason_term, &reason_value) in bound.reasons.iter().zip(&bound.reason_values)
                {
                    // SOUNDNESS GATE #8744: only trust LRA bounds whose supporting
                    // literals are present in the current asserted assignment.
                    if !asserted_lookup.contains(&(reason_term, reason_value)) {
                        return IntSatProbeResult::Inconclusive;
                    }
                    bound_reason_literals.push((reason_term, reason_value));
                }
            }

            let lower = lb_opt.as_ref().map(Self::effective_int_lower);

            let upper = ub_opt.as_ref().map(Self::effective_int_upper);

            match (lower, upper) {
                (Some(lb), Some(ub)) => {
                    initial_bounds.push((VarId(idx as u32), lb, ub));
                }
                // SOUNDNESS (#wrong-unsat): a variable that is unbounded on either
                // side has an INFINITE true domain. Previously this fabricated a
                // ±1,000,000-wide finite box ("large upper/lower bound"), then ran
                // IntSat on the box. If the only integer witness lies outside the
                // fabricated window (e.g. `1000000007*x + 1000000009*y = 1`, whose
                // solutions are x = 26 + 1000000009*t), IntSat reports the box
                // infeasible and the probe emits a spurious UNSAT — a false proof.
                // IntSat may only soundly certify UNSAT over a GENUINELY finite box,
                // so treat any one-sided/unbounded variable as "missing bounds" and
                // decline the probe.
                _ => {
                    has_all_bounds = false;
                }
            }
        }

        // IntSat requires all variables to have bounds. If some are missing,
        // skip the probe (IntSat can't handle unbounded variables well).
        if !has_all_bounds {
            return IntSatProbeResult::Inconclusive;
        }

        // Extract linear constraints from asserted atoms.
        let mut contributing_asserted_literals: Vec<(TermId, bool)> = Vec::new();
        for &(atom, value) in &self.asserted {
            if constraints.len() >= MAX_INTSAT_CONSTRAINTS {
                break;
            }

            let constraints_before = constraints.len();
            match self.terms.get(atom) {
                TermData::App(Symbol::Named(name), args) if args.len() == 2 => {
                    let lhs = args[0];
                    let rhs = args[1];

                    match (name.as_str(), value) {
                        // (= lhs rhs) asserted true: lhs - rhs = 0
                        // Encode as: lhs - rhs <= 0 AND rhs - lhs <= 0
                        ("=", true) => {
                            if let Some((c1, c2)) =
                                self.extract_equality_constraints(lhs, rhs, &term_to_idx)
                            {
                                constraints.push(c1);
                                constraints.push(c2);
                            }
                        }
                        // (<= lhs rhs) asserted true: lhs - rhs <= 0
                        ("<=", true) => {
                            if let Some(c) = self.extract_le_constraint(lhs, rhs, &term_to_idx) {
                                constraints.push(c);
                            }
                        }
                        // (>= lhs rhs) asserted true: rhs - lhs <= 0
                        (">=", true) => {
                            if let Some(c) = self.extract_le_constraint(rhs, lhs, &term_to_idx) {
                                constraints.push(c);
                            }
                        }
                        // (< lhs rhs) asserted true: lhs - rhs <= -1 (integers)
                        ("<", true) => {
                            if let Some(mut c) = self.extract_le_constraint(lhs, rhs, &term_to_idx)
                            {
                                c.rhs -= BigInt::one();
                                constraints.push(c);
                            }
                        }
                        // (> lhs rhs) asserted true: rhs - lhs <= -1 (integers)
                        (">", true) => {
                            if let Some(mut c) = self.extract_le_constraint(rhs, lhs, &term_to_idx)
                            {
                                c.rhs -= BigInt::one();
                                constraints.push(c);
                            }
                        }
                        // Negated constraints
                        ("<=", false) => {
                            // NOT(lhs <= rhs) => lhs > rhs => rhs - lhs <= -1
                            if let Some(mut c) = self.extract_le_constraint(rhs, lhs, &term_to_idx)
                            {
                                c.rhs -= BigInt::one();
                                constraints.push(c);
                            }
                        }
                        (">=", false) => {
                            // NOT(lhs >= rhs) => lhs < rhs => lhs - rhs <= -1
                            if let Some(mut c) = self.extract_le_constraint(lhs, rhs, &term_to_idx)
                            {
                                c.rhs -= BigInt::one();
                                constraints.push(c);
                            }
                        }
                        ("<", false) => {
                            // NOT(lhs < rhs) => lhs >= rhs => rhs - lhs <= 0
                            if let Some(c) = self.extract_le_constraint(rhs, lhs, &term_to_idx) {
                                constraints.push(c);
                            }
                        }
                        (">", false) => {
                            // NOT(lhs > rhs) => lhs <= rhs => lhs - rhs <= 0
                            if let Some(c) = self.extract_le_constraint(lhs, rhs, &term_to_idx) {
                                constraints.push(c);
                            }
                        }
                        _ => {}
                    }
                }
                _ => {}
            }

            if constraints.len() > constraints_before {
                contributing_asserted_literals.push((atom, value));
            }
        }

        if constraints.is_empty() {
            return IntSatProbeResult::Inconclusive;
        }

        // Run IntSat with a bounded conflict budget.
        // #8749: Propagate the LIA deadline so the IntSat BigInt loop honours
        // `--timeout`. Without this the probe can take multiple seconds to
        // exhaust its conflict budget on large instances, overshooting the
        // user-configured timeout.
        let dl = self.deadline_for_intsat();
        let config = ay_intsat::IntSatConfig {
            max_conflicts: INTSAT_PROBE_CONFLICTS,
            max_learned: 2_000,
            deadline: dl,
        };

        let mut solver = ay_intsat::IntSatSolver::new(constraints, num_vars, config);
        for (var, lb, ub) in &initial_bounds {
            solver.add_initial_bound(*var, lb.clone(), ub.clone());
        }

        match solver.solve() {
            IntSatResult::Unsat => {
                let mut conflict_literals = Vec::new();
                let mut seen = HashSet::default();

                for &(term, value) in &contributing_asserted_literals {
                    if seen.insert((term, value)) {
                        conflict_literals.push(TheoryLit::new(term, value));
                    }
                }
                for &(term, value) in &bound_reason_literals {
                    if seen.insert((term, value)) {
                        conflict_literals.push(TheoryLit::new(term, value));
                    }
                }

                IntSatProbeResult::Unsat(conflict_literals)
            }
            IntSatResult::Sat(_) | IntSatResult::Unknown => IntSatProbeResult::Inconclusive,
        }
    }

    /// Extract a `<= constraint` from `lhs <= rhs` in IntSat format.
    ///
    /// Parses both sides as linear expressions and produces:
    /// `sum(coeff_i * x_i) <= constant`
    /// where the constant absorbs the RHS constant.
    fn extract_le_constraint(
        &self,
        lhs: TermId,
        rhs: TermId,
        term_to_idx: &HashMap<TermId, usize>,
    ) -> Option<Constraint> {
        let mut var_coeffs: HashMap<TermId, BigInt> = HashMap::default();
        let mut constant = BigInt::zero();

        // Collect lhs - rhs into var_coeffs and constant.
        self.collect_intsat_linear(lhs, &BigInt::one(), &mut var_coeffs, &mut constant);
        self.collect_intsat_linear(rhs, &-BigInt::one(), &mut var_coeffs, &mut constant);

        // Remove zero coefficients.
        var_coeffs.retain(|_, c| !c.is_zero());

        // Map TermIds to IntSat VarIds.
        let mut coeffs = Vec::new();
        for (term, coeff) in &var_coeffs {
            let idx = term_to_idx.get(term)?;
            coeffs.push((VarId(*idx as u32), coeff.clone()));
        }
        coeffs.sort_by_key(|(v, _)| *v);

        Some(Constraint {
            coeffs,
            rhs: -constant, // lhs - rhs <= 0 => sum(coeffs) <= -constant
        })
    }

    /// Extract equality `lhs = rhs` as two `<=` constraints.
    fn extract_equality_constraints(
        &self,
        lhs: TermId,
        rhs: TermId,
        term_to_idx: &HashMap<TermId, usize>,
    ) -> Option<(Constraint, Constraint)> {
        let c1 = self.extract_le_constraint(lhs, rhs, term_to_idx)?;
        let c2 = self.extract_le_constraint(rhs, lhs, term_to_idx)?;
        Some((c1, c2))
    }

    /// Collect linear coefficients from a term for IntSat translation.
    ///
    /// Accumulates `scale * term` into var_coeffs (TermId -> BigInt) and constant.
    fn collect_intsat_linear(
        &self,
        term: TermId,
        scale: &BigInt,
        coeffs: &mut HashMap<TermId, BigInt>,
        constant: &mut BigInt,
    ) {
        match self.terms.get(term) {
            TermData::Const(Constant::Int(n)) => {
                *constant += scale * n;
            }
            TermData::Const(Constant::Rational(r)) if r.0.denom().is_one() => {
                *constant += scale * r.0.numer();
            }
            TermData::Var(_, _) => {
                *coeffs.entry(term).or_insert_with(BigInt::zero) += scale;
            }
            TermData::App(Symbol::Named(name), args) => match name.as_str() {
                "+" => {
                    for &arg in args {
                        self.collect_intsat_linear(arg, scale, coeffs, constant);
                    }
                }
                "-" => {
                    if args.len() == 1 {
                        // Unary minus
                        let neg_scale = -scale;
                        self.collect_intsat_linear(args[0], &neg_scale, coeffs, constant);
                    } else if args.len() == 2 {
                        // Binary minus: a - b
                        self.collect_intsat_linear(args[0], scale, coeffs, constant);
                        let neg_scale = -scale;
                        self.collect_intsat_linear(args[1], &neg_scale, coeffs, constant);
                    }
                }
                "*" => {
                    // Try to extract a constant factor.
                    if args.len() == 2 {
                        if let Some(k) = self.terms.extract_integer_constant(args[0]) {
                            let new_scale = scale * &k;
                            self.collect_intsat_linear(args[1], &new_scale, coeffs, constant);
                            return;
                        }
                        if let Some(k) = self.terms.extract_integer_constant(args[1]) {
                            let new_scale = scale * &k;
                            self.collect_intsat_linear(args[0], &new_scale, coeffs, constant);
                            return;
                        }
                    }
                    // Non-linear multiplication: treat as opaque variable.
                    *coeffs.entry(term).or_insert_with(BigInt::zero) += scale;
                }
                _ => {
                    // Opaque term (UF application, etc.): treat as variable.
                    *coeffs.entry(term).or_insert_with(BigInt::zero) += scale;
                }
            },
            _ => {
                // Unknown structure: treat as opaque variable.
                *coeffs.entry(term).or_insert_with(BigInt::zero) += scale;
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use ay_core::term::TermStore;

    #[test]
    fn test_intsat_probe_empty_solver() {
        let terms = TermStore::new();
        let solver = LiaSolver::new(&terms);
        // No assertions, no variables: should be inconclusive.
        let result = solver.intsat_probe();
        assert!(matches!(result, IntSatProbeResult::Inconclusive));
    }
}
