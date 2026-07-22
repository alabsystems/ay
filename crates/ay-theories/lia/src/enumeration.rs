// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Direct enumeration solver for LIA.
//!
//! This module implements direct lattice enumeration for solving systems of
//! linear integer equations. For equality-dense problems where Gaussian elimination
//! leaves at most 2 free variables, this can enumerate all candidate solutions
//! directly rather than iterating with cutting planes.
//!
//! ## Algorithm Overview
//!
//! 1. Build coefficient matrix from asserted equalities
//! 2. Perform rational Gaussian elimination to row echelon form
//! 3. Identify free variables (columns without pivots)
//! 4. Derive bounds on free variables from inequalities
//! 5. Enumerate candidate integer assignments within bounds
//! 6. Return first satisfying assignment or UNSAT if none exists

// #8529: Use deterministic hash maps in all builds.
use ay_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};
use ay_core::term::{Constant, Symbol, TermData, TermId, TermStore};
use ay_core::Sort;
use num_bigint::BigInt;
use num_rational::BigRational;
use num_traits::{One, Signed, Zero};
use tracing::info;

use crate::{
    DirectEnumResult, EnumMatrix, EnumRrefCache, EnumRrefOutcome, IneqOp, LiaModel, LiaSolver,
    SubstitutionTriple,
};

mod bounds;
mod bounds_single;
mod bounds_two_var;
mod finite_domain;
mod model;

/// Result of one Gaussian elimination run over the enumeration matrix
/// (private to `try_direct_enumeration`; the cacheable subset is mirrored
/// into `EnumRrefOutcome`).
enum EnumElimination {
    /// Reduced row echelon form + pivot columns.
    Rref(EnumMatrix, Vec<usize>),
    /// A coefficient exceeded `MAX_COEFF_BITS` (deterministic, cacheable).
    CoeffExplosion,
    /// Cooperative timeout fired mid-elimination (wall-clock dependent,
    /// never cached).
    Timeout,
}

/// #probe-rref-memo observability: hit/miss counters for the
/// `try_direct_enumeration` elimination memo, printed to stderr every 1000
/// lookups when `AY_PROBE_STATS` is set (same gate as `probe_stats_record`).
/// Zero overhead when unset (one cached env read).
fn enum_rref_stats_record(hit: bool) {
    use std::sync::atomic::{AtomicU64, Ordering};
    static LOOKUPS: AtomicU64 = AtomicU64::new(0);
    static HITS: AtomicU64 = AtomicU64::new(0);
    static ENABLED: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    if !*ENABLED.get_or_init(|| std::env::var_os("AY_PROBE_STATS").is_some()) {
        return;
    }
    let n = LOOKUPS.fetch_add(1, Ordering::Relaxed) + 1;
    if hit {
        HITS.fetch_add(1, Ordering::Relaxed);
    }
    if n.is_multiple_of(1000) {
        safe_eprintln!(
            "[ENUM-RREF] lookups={} hits={}",
            n,
            HITS.load(Ordering::Relaxed)
        );
    }
}

impl LiaSolver<'_> {
    /// Rational Gaussian elimination to reduced row echelon form, extracted
    /// verbatim from `try_direct_enumeration` for the #probe-rref-memo. Pure
    /// function of `matrix` (fixed pivot order; the only solver reads are the
    /// cooperative-timeout poll and the debug flag, neither of which affects
    /// the algebra) — this purity is what makes the memo exact.
    ///
    /// SOUNDNESS FIX (#421): coefficient size limit to prevent BigInt
    /// explosion — the GCD computation on large BigInts is O(n^2) and can
    /// hang indefinitely, so abort when any coefficient exceeds the
    /// threshold.
    fn eliminate_enum_matrix(
        &self,
        mut matrix: EnumMatrix,
        num_vars: usize,
        debug: bool,
    ) -> EnumElimination {
        const MAX_COEFF_BITS: u64 = 256; // ~77 decimal digits

        let mut pivot_cols: Vec<usize> = Vec::new();
        let mut pivot_row = 0;

        for col in 0..num_vars {
            if self.should_timeout() {
                if debug {
                    safe_eprintln!("[ENUM] Aborting: timeout");
                }
                return EnumElimination::Timeout;
            }

            // Find pivot in this column
            let mut best_row = None;
            for (row, row_data) in matrix.iter().enumerate().skip(pivot_row) {
                if !row_data.0[col].is_zero() {
                    best_row = Some(row);
                    break;
                }
            }

            let Some(prow) = best_row else {
                continue; // No pivot in this column, it's a free variable
            };

            // Swap rows
            if prow != pivot_row {
                matrix.swap(prow, pivot_row);
            }

            // Scale pivot row to make pivot = 1
            let pivot_val = matrix[pivot_row].0[col].clone();
            for c in 0..num_vars {
                matrix[pivot_row].0[c] = &matrix[pivot_row].0[c] / &pivot_val;
            }
            matrix[pivot_row].1 = &matrix[pivot_row].1 / &pivot_val;

            // Eliminate other rows
            for row in 0..matrix.len() {
                if row == pivot_row {
                    continue;
                }
                let factor = matrix[row].0[col].clone();
                if factor.is_zero() {
                    continue;
                }
                for c in 0..num_vars {
                    let sub = &factor * &matrix[pivot_row].0[c];
                    matrix[row].0[c] = &matrix[row].0[c] - &sub;
                }
                let sub = &factor * &matrix[pivot_row].1;
                matrix[row].1 = &matrix[row].1 - &sub;
            }

            pivot_cols.push(col);
            pivot_row += 1;

            // SOUNDNESS FIX (#421): Check for coefficient explosion after each elimination step.
            // Abort if any coefficient exceeds the bit threshold to prevent hung GCD computation.
            for (row_coeffs, row_const) in &matrix {
                for coeff in row_coeffs {
                    let numer_bits = coeff.numer().bits();
                    let denom_bits = coeff.denom().bits();
                    if numer_bits > MAX_COEFF_BITS || denom_bits > MAX_COEFF_BITS {
                        if debug {
                            safe_eprintln!(
                                "[ENUM] Aborting: coefficient explosion (numer {} bits, denom {} bits)",
                                numer_bits, denom_bits
                            );
                        }
                        return EnumElimination::CoeffExplosion;
                    }
                }
                let const_numer_bits = row_const.numer().bits();
                let const_denom_bits = row_const.denom().bits();
                if const_numer_bits > MAX_COEFF_BITS || const_denom_bits > MAX_COEFF_BITS {
                    if debug {
                        safe_eprintln!(
                            "[ENUM] Aborting: constant explosion (numer {} bits, denom {} bits)",
                            const_numer_bits,
                            const_denom_bits
                        );
                    }
                    return EnumElimination::CoeffExplosion;
                }
            }

            if pivot_row >= matrix.len() {
                break;
            }
        }

        EnumElimination::Rref(matrix, pivot_cols)
    }

    /// Try to solve the integer system directly by enumeration.
    ///
    /// For equality-dense problems (k equalities with n variables, k close to n),
    /// this can enumerate solutions when there are at most 2 free variables,
    /// avoiding the slow iterative HNF cuts approach.
    ///
    /// Returns `DirectEnumResult::SatWitness` if a solution is found (stored in
    /// `self.direct_enum_witness`), `DirectEnumResult::Unsat` if enumeration proves
    /// infeasibility, or `DirectEnumResult::NoConclusion` if the method doesn't apply.
    /// True when the enumerated `solution` provably satisfies every Int-sorted
    /// CROSS-THEORY equality LIA holds (#enum-shared-eq, 2026-07-11).
    ///
    /// Direct enumeration builds its system from the asserted literals only —
    /// it never consults `shared_equalities`, the equalities forwarded from
    /// EUF/UF (`assert_shared_equality`). That RELAXATION keeps the `Unsat`
    /// leg sound (a relaxation that is infeasible proves the full system
    /// infeasible), but its WITNESS can violate an equality it never saw: the
    /// QF_AUFLIRA cross-sort shape `g(phase) = phase` with `phase = 1` came
    /// back with `g(phase) = 0`, an invalid model that the independent gate
    /// then (correctly) refuted, degrading a genuine sat to unknown. Verify
    /// the witness against those equalities and fall back to the simplex path
    /// when it cannot be confirmed — enumeration is purely an optimization.
    ///
    /// Fail-closed: an equality whose linear form mentions a variable the
    /// enumeration did not determine returns `false` (unverifiable ⇒ do not
    /// use the witness). Real-sorted shared equalities are skipped: they
    /// constrain the LRA relaxation, not this Int witness.
    fn witness_satisfies_shared_equalities(
        &self,
        solution: &[(usize, BigInt)],
        idx_to_term: &[TermId],
    ) -> bool {
        if self.shared_equalities.is_empty() {
            // INTERFACE-DIET C4/R2 (empty-unlocks-Sat site): with a withheld
            // equality the empty interface is not complete, so "no constraints
            // to violate ⇒ witness OK" would be a false accept. Fail-closed
            // (unverifiable ⇒ do not use the witness) when the interface is hidden.
            return !self.hidden_interface;
        }
        let mut values: HashMap<TermId, BigRational> = HashMap::default();
        for (col, val) in solution {
            let Some(&term) = idx_to_term.get(*col) else {
                return false;
            };
            values.insert(term, BigRational::from(val.clone()));
        }
        for (lhs, rhs, _) in &self.shared_equalities {
            if !matches!(self.terms.sort(*lhs), Sort::Int)
                || !matches!(self.terms.sort(*rhs), Sort::Int)
            {
                continue;
            }
            let lhs_coeffs = self.term_to_linear_coeffs(*lhs);
            let rhs_coeffs = self.term_to_linear_coeffs(*rhs);
            let mut acc = &lhs_coeffs.constant - &rhs_coeffs.constant;
            for (var, coeff) in lhs_coeffs
                .vars
                .iter()
                .map(|(v, c)| (v, c.clone()))
                .chain(rhs_coeffs.vars.iter().map(|(v, c)| (v, -c.clone())))
            {
                let Some(val) = values.get(var) else {
                    return false; // undetermined variable: cannot verify
                };
                acc += coeff * val;
            }
            if !acc.is_zero() {
                return false;
            }
        }
        true
    }

    pub(crate) fn try_direct_enumeration(&mut self) -> DirectEnumResult {
        let debug = self.debug_enum;
        self.direct_enum_witness = None;

        let num_equalities = self.count_equalities();
        let num_vars = self.integer_vars.len();

        // Direct enumeration is purely an optimization. Keep it conservative to avoid
        // performance regressions on large equality-dense systems where rational Gaussian
        // elimination can dominate.
        const MAX_ENUM_VARS: usize = 64;
        const MAX_ENUM_ROWS: usize = 64;
        if num_vars > MAX_ENUM_VARS {
            if debug {
                safe_eprintln!(
                    "[ENUM] Skipping direct enumeration: {} vars exceeds max {}",
                    num_vars,
                    MAX_ENUM_VARS
                );
            }
            return DirectEnumResult::NoConclusion;
        }

        const MAX_ENUM_ASSERTED_LITS: usize = 256;
        if self.asserted.len() > MAX_ENUM_ASSERTED_LITS {
            if debug {
                safe_eprintln!(
                    "[ENUM] Skipping direct enumeration: {} asserted lits exceeds max {}",
                    self.asserted.len(),
                    MAX_ENUM_ASSERTED_LITS
                );
            }
            return DirectEnumResult::NoConclusion;
        }

        // Only apply when we have at most 2 free variables
        // (k equalities reduce n vars to n-k free vars, assuming linear independence)
        if num_equalities == 0 || num_vars == 0 {
            return DirectEnumResult::NoConclusion;
        }
        let expected_free = num_vars.saturating_sub(num_equalities);
        if expected_free > 2 {
            return DirectEnumResult::NoConclusion; // Too many free vars for enumeration
        }

        info!(
            target: "ay::lia",
            equalities = num_equalities,
            vars = num_vars,
            expected_free,
            "Direct enumeration attempt"
        );

        if debug {
            safe_eprintln!(
                "[ENUM] Trying direct enumeration: {} equalities, {} vars, ~{} free",
                num_equalities,
                num_vars,
                expected_free
            );
        }

        let (term_to_idx, idx_to_term) = self.build_var_index();

        // Build the rational matrix from equalities
        // Each row is [coeffs... | constant] representing sum(coeff_i * x_i) = constant
        let mut matrix: Vec<(Vec<BigRational>, BigRational)> = Vec::new();

        for &literal in &self.assertion_view().positive_equalities {
            let TermData::App(Symbol::Named(name), args) = self.terms.get(literal) else {
                continue;
            };

            if name != "=" || args.len() != 2 {
                continue;
            }

            let Some((var_coeffs, constant)) =
                self.parse_equality_for_dioph(args[0], args[1], &term_to_idx)
            else {
                continue;
            };

            if var_coeffs.is_empty() {
                continue;
            }

            // Convert to rational row
            let mut row: Vec<BigRational> = vec![BigRational::zero(); num_vars];
            for (idx, coeff) in var_coeffs {
                row[idx] = BigRational::from(coeff);
            }
            matrix.push((row, BigRational::from(constant)));
        }

        if matrix.is_empty() {
            return DirectEnumResult::NoConclusion;
        }
        if matrix.len() > MAX_ENUM_ROWS {
            if debug {
                safe_eprintln!(
                    "[ENUM] Skipping direct enumeration: {} equalities exceeds max {}",
                    matrix.len(),
                    MAX_ENUM_ROWS
                );
            }
            return DirectEnumResult::NoConclusion;
        }

        if debug {
            safe_eprintln!(
                "[ENUM] Built matrix with {} rows, {} cols",
                matrix.len(),
                num_vars
            );
        }

        // Gaussian elimination over rationals, behind the #probe-rref-memo
        // (see `EnumRrefCache`): a FULL structural compare of the freshly
        // built matrix against the cached key makes a hit exact by
        // construction. The conflict-probe loop re-enters here once per
        // candidate shared equality with a byte-identical matrix (shared
        // equalities never enter it), so steps 2..k skip the elimination.
        let rref: std::rc::Rc<(EnumMatrix, Vec<usize>)> = {
            let cached = match &self.enum_rref_cache {
                Some(cache) if cache.key == matrix => Some(cache.outcome.clone()),
                _ => None,
            };
            let hit = cached.is_some();
            enum_rref_stats_record(hit);
            match cached {
                Some(EnumRrefOutcome::CoeffExplosion) => {
                    // Deterministic abort replay (same matrix ⇒ same abort).
                    if debug {
                        safe_eprintln!("[ENUM] Aborting: coefficient explosion (memoized)");
                    }
                    return DirectEnumResult::NoConclusion;
                }
                Some(EnumRrefOutcome::Rref(rc)) => rc,
                None => match self.eliminate_enum_matrix(matrix.clone(), num_vars, debug) {
                    EnumElimination::Rref(work, pivot_cols) => {
                        let rc = std::rc::Rc::new((work, pivot_cols));
                        self.enum_rref_cache = Some(EnumRrefCache {
                            key: matrix,
                            outcome: EnumRrefOutcome::Rref(std::rc::Rc::clone(&rc)),
                        });
                        rc
                    }
                    EnumElimination::CoeffExplosion => {
                        self.enum_rref_cache = Some(EnumRrefCache {
                            key: matrix,
                            outcome: EnumRrefOutcome::CoeffExplosion,
                        });
                        return DirectEnumResult::NoConclusion;
                    }
                    // Wall-clock dependent — never cached.
                    EnumElimination::Timeout => return DirectEnumResult::NoConclusion,
                },
            }
        };
        let (matrix, pivot_cols) = (&rref.0, &rref.1);

        // Check for inconsistency: row of all zeros with non-zero constant
        for (row, constant) in matrix.iter() {
            if row.iter().all(Zero::is_zero) && !constant.is_zero() {
                if debug {
                    safe_eprintln!("[ENUM] Infeasible: 0 = {}", constant);
                }
                return DirectEnumResult::Unsat(self.conflict_from_asserted());
            }
        }

        // Identify free variables (columns without pivots)
        let pivot_set: HashSet<usize> = pivot_cols.iter().copied().collect();
        let free_vars: Vec<usize> = (0..num_vars).filter(|c| !pivot_set.contains(c)).collect();

        if debug {
            safe_eprintln!(
                "[ENUM] Pivot cols: {:?}, free vars: {:?}",
                pivot_cols,
                free_vars
            );
        }

        if free_vars.is_empty() {
            // Fully determined - first build solution, then check inequalities
            if debug {
                safe_eprintln!("[ENUM] System fully determined, checking solution");
            }

            // Build solution array
            let mut solution: Vec<(usize, BigInt)> = Vec::new();
            for (row_idx, &pivot_col) in pivot_cols.iter().enumerate() {
                let val = &matrix[row_idx].1;
                // Check if integer
                if !val.denom().is_one() {
                    if debug {
                        safe_eprintln!(
                            "[ENUM] Non-integer solution for pivot col {}: {}",
                            pivot_col,
                            val
                        );
                    }
                    return DirectEnumResult::Unsat(self.conflict_from_asserted());
                }
                solution.push((pivot_col, val.numer().clone()));
            }

            // Check if solution satisfies all asserted literals.
            let Some(satisfies) =
                self.check_solution_satisfies_asserted(&solution, &idx_to_term, debug)
            else {
                return DirectEnumResult::NoConclusion;
            };
            if satisfies {
                info!(
                    target: "ay::lia",
                    outcome = "sat",
                    free_vars = 0usize,
                    "Direct enumeration: fully determined system is SAT"
                );
                if debug {
                    safe_eprintln!("[ENUM] Solution satisfies all constraints - SAT witness");
                }
                if !self.witness_satisfies_shared_equalities(&solution, &idx_to_term) {
                    if debug {
                        safe_eprintln!("[ENUM] Witness violates a shared equality - falling back");
                    }
                    return DirectEnumResult::NoConclusion;
                }
                self.direct_enum_witness = Some(Self::solution_to_model(&solution, &idx_to_term));
                return DirectEnumResult::SatWitness;
            } else {
                info!(
                    target: "ay::lia",
                    outcome = "unsat",
                    free_vars = 0usize,
                    "Direct enumeration: fully determined system violates inequalities"
                );
                // Solution determined by equalities doesn't satisfy inequalities
                if debug {
                    safe_eprintln!("[ENUM] Solution violates inequalities - infeasible");
                }
                return DirectEnumResult::Unsat(self.conflict_from_asserted());
            }
        }

        if free_vars.len() > 2 {
            // Too many free variables for enumeration
            return DirectEnumResult::NoConclusion;
        }

        // Build substitution expressions: pivot_var = constant - Σ(coeff * free_var)
        // After RREF, each pivot row has: x_pivot + Σ(coeff_f * x_free) = constant
        // So: x_pivot = constant - Σ(coeff_f * x_free)
        let mut substitutions: Vec<SubstitutionTriple<usize, BigRational>> = Vec::new();
        for (row_idx, &pivot_col) in pivot_cols.iter().enumerate() {
            let mut coeffs: Vec<(usize, BigRational)> = Vec::new();
            for &free_col in &free_vars {
                let c = &matrix[row_idx].0[free_col];
                if !c.is_zero() {
                    coeffs.push((free_col, -c.clone())); // Note: negated because pivot = const - Σ
                }
            }
            substitutions.push((pivot_col, coeffs, matrix[row_idx].1.clone()));
        }

        if debug {
            for (pivot, coeffs, constant) in &substitutions {
                safe_eprintln!("[ENUM] x{} = {} + Σ{:?}", pivot, constant, coeffs);
            }
        }

        // Get bounds on free variables from inequalities
        // For each inequality, substitute pivot vars to get constraint on free vars
        let (free_lower, free_upper) = self.compute_free_var_bounds(
            &free_vars,
            &substitutions,
            &idx_to_term,
            &term_to_idx,
            debug,
        );

        if debug {
            for (i, &fv) in free_vars.iter().enumerate() {
                safe_eprintln!(
                    "[ENUM] Free var x{}: bounds [{:?}, {:?}]",
                    fv,
                    free_lower.get(i),
                    free_upper.get(i)
                );
            }
        }

        // Check if bounds are finite and small enough for enumeration
        let max_enum_range: i64 = 10000;
        let max_total_points: i64 = 2_000_000;

        if free_vars.len() == 1 {
            let lo = free_lower.first().cloned().flatten();
            let hi = free_upper.first().cloned().flatten();

            if let (Some(lo_val), Some(hi_val)) = (&lo, &hi) {
                if lo_val > hi_val {
                    if debug {
                        safe_eprintln!("[ENUM] Infeasible bounds: {} > {}", lo_val, hi_val);
                    }
                    return DirectEnumResult::Unsat(self.conflict_from_asserted());
                }

                let range = hi_val - lo_val;
                if range <= BigInt::from(max_enum_range) {
                    // Enumerate candidate assignments for the free variable. We only need a
                    // single integer SAT witness; return immediately on the first satisfying
                    // point.
                    if debug {
                        safe_eprintln!("[ENUM] Enumerating free var in [{}, {}]", lo_val, hi_val);
                    }

                    let free_col = free_vars[0];
                    let mut t = lo_val.clone();
                    while &t <= hi_val {
                        if self.should_timeout() {
                            if debug {
                                safe_eprintln!("[ENUM] Aborting: timeout");
                            }
                            return DirectEnumResult::NoConclusion;
                        }

                        // Compute all pivot vars
                        let t_rat = BigRational::from(t.clone());
                        let mut all_integer = true;
                        let mut solution: Vec<(usize, BigInt)> = Vec::new();

                        // Set free var
                        solution.push((free_col, t.clone()));

                        // Compute pivot vars
                        for (pivot_col, coeffs, constant) in &substitutions {
                            let mut val = constant.clone();
                            for (fc, coeff) in coeffs {
                                if *fc == free_col {
                                    val = &val + coeff * &t_rat;
                                }
                            }

                            if !val.denom().is_one() {
                                all_integer = false;
                                break;
                            }
                            solution.push((*pivot_col, val.numer().clone()));
                        }

                        if all_integer {
                            let Some(satisfies) = self.check_solution_satisfies_asserted(
                                &solution,
                                &idx_to_term,
                                debug,
                            ) else {
                                return DirectEnumResult::NoConclusion;
                            };
                            if satisfies {
                                info!(
                                    target: "ay::lia",
                                    outcome = "sat",
                                    free_vars = 1usize,
                                    "Direct enumeration found witness (1D)"
                                );
                                if debug {
                                    safe_eprintln!("[ENUM] Found valid solution: {:?}", solution);
                                }
                                if !self
                                    .witness_satisfies_shared_equalities(&solution, &idx_to_term)
                                {
                                    return DirectEnumResult::NoConclusion;
                                }
                                self.direct_enum_witness =
                                    Some(Self::solution_to_model(&solution, &idx_to_term));
                                return DirectEnumResult::SatWitness;
                            }
                        }

                        t += BigInt::one();
                    }

                    info!(
                        target: "ay::lia",
                        outcome = "unsat",
                        free_vars = 1usize,
                        "Direct enumeration proved UNSAT (1D)"
                    );
                    if debug {
                        safe_eprintln!("[ENUM] No valid solution found in range");
                    }
                    return DirectEnumResult::Unsat(self.conflict_from_asserted());
                }
            }
        }

        if free_vars.len() == 2 {
            let lo0 = free_lower.first().cloned().flatten();
            let hi0 = free_upper.first().cloned().flatten();
            let lo1 = free_lower.get(1).cloned().flatten();
            let hi1 = free_upper.get(1).cloned().flatten();

            if let (Some(lo0), Some(hi0), Some(lo1), Some(hi1)) = (&lo0, &hi0, &lo1, &hi1) {
                if lo0 > hi0 || lo1 > hi1 {
                    if debug {
                        safe_eprintln!(
                            "[ENUM] Infeasible bounds: [{}, {}] x [{}, {}]",
                            lo0,
                            hi0,
                            lo1,
                            hi1
                        );
                    }
                    return DirectEnumResult::Unsat(self.conflict_from_asserted());
                }

                let range0 = hi0 - lo0;
                let range1 = hi1 - lo1;
                if range0 <= BigInt::from(max_enum_range) && range1 <= BigInt::from(max_enum_range)
                {
                    let count0 = range0 + BigInt::one();
                    let count1 = range1 + BigInt::one();
                    let total_points = &count0 * &count1;

                    if total_points <= BigInt::from(max_total_points) {
                        if debug {
                            safe_eprintln!(
                                "[ENUM] Enumerating 2D grid: x{} in [{}, {}], x{} in [{}, {}] ({} points)",
                                free_vars[0],
                                lo0,
                                hi0,
                                free_vars[1],
                                lo1,
                                hi1,
                                total_points
                            );
                        }

                        let free_col0 = free_vars[0];
                        let free_col1 = free_vars[1];

                        // Enumerate candidate assignments for the free variables. We only need a
                        // single integer SAT witness; return immediately on the first satisfying
                        // point.
                        let mut point_count: u64 = 0;
                        let mut t0 = lo0.clone();
                        while &t0 <= hi0 {
                            let t0_rat = BigRational::from(t0.clone());
                            let mut t1 = lo1.clone();
                            while &t1 <= hi1 {
                                if point_count.trailing_zeros() >= 12 && self.should_timeout() {
                                    if debug {
                                        safe_eprintln!("[ENUM] Aborting: timeout");
                                    }
                                    return DirectEnumResult::NoConclusion;
                                }
                                point_count += 1;

                                let t1_rat = BigRational::from(t1.clone());

                                // Compute all pivot vars
                                let mut all_integer = true;
                                let mut solution: Vec<(usize, BigInt)> = Vec::new();

                                // Set free vars
                                solution.push((free_col0, t0.clone()));
                                solution.push((free_col1, t1.clone()));

                                // Compute pivot vars
                                for (pivot_col, coeffs, constant) in &substitutions {
                                    let mut val = constant.clone();
                                    for (fc, coeff) in coeffs {
                                        if *fc == free_col0 {
                                            val = &val + coeff * &t0_rat;
                                        } else if *fc == free_col1 {
                                            val = &val + coeff * &t1_rat;
                                        }
                                    }

                                    if !val.denom().is_one() {
                                        all_integer = false;
                                        break;
                                    }
                                    solution.push((*pivot_col, val.numer().clone()));
                                }

                                if all_integer {
                                    let Some(satisfies) = self.check_solution_satisfies_asserted(
                                        &solution,
                                        &idx_to_term,
                                        debug,
                                    ) else {
                                        return DirectEnumResult::NoConclusion;
                                    };
                                    if satisfies {
                                        info!(
                                            target: "ay::lia",
                                            outcome = "sat",
                                            free_vars = 2usize,
                                            points_checked = point_count,
                                            "Direct enumeration found witness (2D)"
                                        );
                                        if debug {
                                            safe_eprintln!(
                                                "[ENUM] Found valid solution: {:?}",
                                                solution
                                            );
                                        }
                                        if !self.witness_satisfies_shared_equalities(
                                            &solution,
                                            &idx_to_term,
                                        ) {
                                            return DirectEnumResult::NoConclusion;
                                        }
                                        self.direct_enum_witness =
                                            Some(Self::solution_to_model(&solution, &idx_to_term));
                                        return DirectEnumResult::SatWitness;
                                    }
                                }

                                t1 += BigInt::one();
                            }
                            t0 += BigInt::one();
                        }

                        info!(
                            target: "ay::lia",
                            outcome = "unsat",
                            free_vars = 2usize,
                            points_checked = point_count,
                            "Direct enumeration proved UNSAT (2D)"
                        );
                        if debug {
                            safe_eprintln!("[ENUM] No valid solution found in 2D range");
                        }
                        return DirectEnumResult::Unsat(self.conflict_from_asserted());
                    }
                }
            }
        }

        // Can't cheaply enumerate (or no finite bounds found).
        DirectEnumResult::NoConclusion
    }
}
