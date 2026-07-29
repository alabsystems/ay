// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! HNF-based cutting plane generation.
//!
//! Collects tight equality constraints and uses HNF decomposition to
//! identify non-integer coordinates in the transformed space, generating
//! valid cutting planes in the original variable space.

// #8529: Use deterministic hash maps in all builds.
use ay_core::kani_compat::DetHashMap as HashMap;
use num_bigint::BigInt;

use num_integer::Integer;
use num_traits::{One, Signed, Zero};
use tracing::{debug, info};

use super::matrix::IntMatrix;
use super::{compute_hnf, determinant_of_rectangular_matrix};

/// HNF cut: (coeffs, bound) representing Σ(coeff * var) <= bound
#[derive(Debug, Clone)]
pub(crate) struct HnfCut {
    /// Coefficients indexed by original variable index
    pub coeffs: Vec<(usize, BigInt)>,
    /// Upper bound (floor of transformed RHS)
    pub bound: BigInt,
}

/// HNF cutter state
pub(crate) struct HnfCutter {
    /// Constraint matrix rows (each row is coefficients for integer vars)
    pub(super) rows: Vec<Vec<BigInt>>,
    /// Right-hand sides
    rhs: Vec<BigInt>,
    /// Whether each constraint is an upper bound (true) or lower bound (false)
    is_upper: Vec<bool>,
    /// Variable indices in column order (for mapping column back to original var)
    pub(super) var_indices: Vec<usize>,
    /// O(1) lookup: original var index -> column position (#3077)
    var_to_col: HashMap<usize, usize>,
    /// Maximum absolute coefficient (for overflow detection)
    abs_max: BigInt,
}

impl HnfCutter {
    /// Create a new HNF cutter
    pub(crate) fn new() -> Self {
        Self {
            rows: Vec::new(),
            rhs: Vec::new(),
            is_upper: Vec::new(),
            var_indices: Vec::new(),
            var_to_col: HashMap::default(),
            abs_max: BigInt::zero(),
        }
    }

    /// Register a variable for the cut matrix. O(1) via HashMap (#3077).
    pub(crate) fn register_var(&mut self, idx: usize) {
        if !self.var_to_col.contains_key(&idx) {
            let col = self.var_indices.len();
            self.var_indices.push(idx);
            self.var_to_col.insert(idx, col);
        }
    }

    /// Add a tight constraint (equality at current solution)
    /// coeffs: (var_index, coefficient) pairs
    /// rhs: right-hand side
    /// upper: true if upper bound constraint, false if lower
    pub(crate) fn add_constraint(&mut self, coeffs: &[(usize, BigInt)], rhs: BigInt, upper: bool) {
        // Register variables and track max coefficient
        for (idx, coeff) in coeffs {
            self.register_var(*idx);
            let abs_coeff = coeff.abs();
            if abs_coeff > self.abs_max {
                self.abs_max = abs_coeff;
            }
        }

        // Build row in variable order
        let mut row = vec![BigInt::zero(); self.var_indices.len()];
        let sign = if upper { BigInt::one() } else { -BigInt::one() };

        for (var_idx, coeff) in coeffs {
            if let Some(&pos) = self.var_to_col.get(var_idx) {
                row[pos] = &sign * coeff;
            }
        }

        let adjusted_rhs = if upper { rhs } else { -rhs };

        self.rows.push(row);
        self.rhs.push(adjusted_rhs);
        self.is_upper.push(upper);
    }

    /// Check if we have enough constraints
    pub(crate) fn has_constraints(&self) -> bool {
        !self.rows.is_empty() && !self.var_indices.is_empty()
    }

    /// Generate HNF cuts
    ///
    /// Returns a list of cuts, each of the form Σ(coeff * x_i) <= bound
    #[allow(clippy::many_single_char_names)]
    pub(crate) fn generate_cuts(&self) -> Vec<HnfCut> {
        if !self.has_constraints() {
            return Vec::new();
        }

        let debug = {
            static FLAG: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
            *FLAG.get_or_init(|| ay_core::debug_channel_active(ay_core::DebugChannel::Hnf))
        };

        use num_rational::BigRational;

        // Build matrix A
        let m = self.rows.len();
        let n = self.var_indices.len();

        if n == 0 {
            return Vec::new();
        }

        // Dimension gate (#hnf-dimension-gate, defense in depth — the entry
        // gate lives in `try_hnf_cuts`): past this size the abs_max^6
        // Bareiss threshold below cannot hold and the whole build is wasted
        // BigInt churn.
        if m > 128 || n > 512 || m.saturating_mul(n) > 32_768 {
            if debug {
                safe_eprintln!("[HNF] matrix too large ({m}x{n}), skipping");
            }
            return Vec::new();
        }

        if debug {
            safe_eprintln!("[HNF] Building {}x{} matrix", m, n);
        }

        let mut a = IntMatrix::new(m, n);
        for (i, row) in self.rows.iter().enumerate() {
            for j in 0..n {
                if j < row.len() {
                    a.set(i, j, row[j].clone());
                }
            }
        }

        // Compute determinant and find basis
        // Use a larger threshold to prevent spurious overflow in Bareiss algorithm.
        // The intermediate values can grow to O(max_coeff^n) where n is matrix dimension.
        // Use abs_max^6 to be safe for typical matrices (4-8 rows).
        let big_number = if self.abs_max.is_zero() {
            BigInt::from(1_000_000_000_000_000_i64) // 10^15
        } else {
            let cubed = &self.abs_max * &self.abs_max * &self.abs_max;
            &cubed * &cubed // abs_max^6
        };

        let Some((d, basis_rows)) = determinant_of_rectangular_matrix(&a, &big_number) else {
            debug!(
                target: "ay::lia",
                matrix_rows = m,
                matrix_cols = n,
                "HNF aborted: overflow in determinant computation"
            );
            if debug {
                safe_eprintln!("[HNF] Overflow in determinant computation");
            }
            return Vec::new();
        };

        if d >= big_number {
            debug!(
                target: "ay::lia",
                matrix_rows = m,
                matrix_cols = n,
                "HNF aborted: determinant too large"
            );
            if debug {
                safe_eprintln!("[HNF] Determinant too large: {}", d);
            }
            return Vec::new();
        }

        if basis_rows.is_empty() {
            return Vec::new();
        }

        if debug {
            safe_eprintln!("[HNF] Determinant: {}, basis rows: {:?}", d, basis_rows);
        }

        // Shrink matrix to basis rows
        let mut a_basis = a.clone();
        a_basis.shrink_to_rows(&basis_rows);

        // Build RHS vector for basis rows
        let b: Vec<BigInt> = basis_rows.iter().map(|&i| self.rhs[i].clone()).collect();

        // Compute HNF
        let Some(hnf) = compute_hnf(&a_basis, &d) else {
            debug!(
                target: "ay::lia",
                matrix_rows = m,
                matrix_cols = n,
                basis_rows = basis_rows.len(),
                "HNF aborted: coefficient explosion in HNF computation"
            );
            if debug {
                safe_eprintln!("[HNF] Aborting: coefficient explosion in HNF computation");
            }
            return Vec::new();
        };

        // Solve y0 = H^{-1} * b (forward substitution; H is lower triangular).
        // We need exact rationals here (Z3 uses mpq); integer division is incorrect.
        let h = &hnf.h;
        let mut y0: Vec<BigRational> = b.iter().map(|bi| BigRational::from(bi.clone())).collect();
        for i in 0..h.row_count() {
            for j in 0..i {
                let h_ij = BigRational::from(h.get(i, j).clone());
                y0[i] = &y0[i] - h_ij * y0[j].clone();
            }
            let hii = h.get(i, i);
            if hii.is_zero() {
                return Vec::new(); // Singular
            }
            y0[i] = &y0[i] / BigRational::from(hii.clone());
            if debug && !y0[i].denom().is_one() {
                safe_eprintln!("[HNF] Row {} has non-integer RHS: {}", i, y0[i]);
            }
        }

        let mut cut_rows: Vec<usize> = (0..y0.len()).filter(|&i| !y0[i].denom().is_one()).collect();
        if cut_rows.is_empty() {
            if debug {
                safe_eprintln!("[HNF] No cut row found (all RHS are integer)");
            }
            return Vec::new();
        }

        // Cap the number of cuts per HNF call to avoid constraint explosion on large problems.
        // For equality-dense problems with many non-integer rows, we still limit to prevent
        // excessive cut generation that doesn't significantly improve convergence.
        const MAX_CUTS_PER_CALL: usize = 5;
        if cut_rows.len() > MAX_CUTS_PER_CALL {
            cut_rows.truncate(MAX_CUTS_PER_CALL);
        }

        let mut cuts_out = Vec::new();
        for &cut_i in &cut_rows {
            if debug {
                safe_eprintln!("[HNF] Cut from row {}", cut_i);
            }

            // Compute e_i * H^{-1} (row vector): solve f * H = e_i for f.
            let mut f: Vec<BigRational> = vec![BigRational::zero(); h.row_count()];
            f[cut_i] = BigRational::one();

            // Back substitution from row cut_i down to 0
            let hii = BigRational::from(h.get(cut_i, cut_i).clone());
            f[cut_i] = &f[cut_i] / &hii;

            for k in (0..cut_i).rev() {
                let mut sum = BigRational::zero();
                for (l, f_l) in f.iter().enumerate().take(cut_i + 1).skip(k + 1) {
                    let h_lk = BigRational::from(h.get(l, k).clone());
                    sum = &sum + &h_lk * f_l;
                }
                let hkk = BigRational::from(h.get(k, k).clone());
                f[k] = -&sum / &hkk;
            }

            // Cut coefficients `c = f * A_basis` and the value `v = f * b` that
            // `c . x` is FORCED to take by the asserted equalities.
            //
            // SOUNDNESS (#hnf-gcd-cut): `c` and `v` are both built from the SAME
            // multiplier row `f`, so `c . x = f . (A_basis x) = f . b = v` holds
            // for every `x` satisfying the equalities — an identity that stands
            // whatever `f` is, and in particular whether or not the modulo-HNF
            // that produced `f` is exact. It therefore replaces the previous
            // bound source `y0[cut_i] = (H^-1 b)[cut_i]`, which is only equal to
            // `v` when `H` is the exact Hermite form of `A_basis`. When the
            // modulo reduction in `compute_hnf` is driven by a modulus that is
            // not the true determinant, `y0` and `v` DIVERGE and the old
            // `c . x <= floor(y0)` was asserted against a system that actually
            // forces `c . x = v > floor(y0)` — an invalid cut carrying the
            // equality atoms as its reasons, i.e. a wrong `unsat`. Observed on
            // `(= r (- 1.5)) /\ (= (mod (to_int r) 3) 1)`, where the equalities
            // `to_int(r) = 3q + rr /\ rr = 1` yielded the bogus cut `q >= 0` and
            // refuted a satisfiable formula.
            let mut rational_coeffs: Vec<(usize, BigRational)> = Vec::new();
            let mut unmapped_column = false;
            for j in 0..a_basis.col_count() {
                let mut coeff = BigRational::zero();
                for (i, f_i) in f.iter().enumerate().take(a_basis.row_count()) {
                    let a_ij = BigRational::from(a_basis.get(i, j).clone());
                    coeff = &coeff + f_i * &a_ij;
                }
                if !coeff.is_zero() {
                    let col_idx = a_basis.adjust_col(j);
                    if col_idx < self.var_indices.len() {
                        let orig_var_idx = self.var_indices[col_idx];
                        rational_coeffs.push((orig_var_idx, coeff));
                    } else {
                        // Dropping a non-zero coefficient would break the
                        // `c . x = v` identity the soundness argument rests on.
                        unmapped_column = true;
                        break;
                    }
                }
            }

            if unmapped_column || rational_coeffs.is_empty() {
                continue;
            }

            // v = f . b, the value the equalities force on `c . x`.
            let mut implied_value = BigRational::zero();
            for (i, f_i) in f.iter().enumerate().take(b.len()) {
                implied_value = &implied_value + f_i * BigRational::from(b[i].clone());
            }

            // Make integer coefficients: multiply by LCM of denominators
            // (coefficients and the implied value).
            let mut lcm = BigInt::one();
            for (_, coeff) in &rational_coeffs {
                lcm = num_integer::lcm(lcm, coeff.denom().clone());
            }
            lcm = num_integer::lcm(lcm, implied_value.denom().clone());

            let lcm_rat = BigRational::from(lcm.clone());

            let mut cut_coeffs: Vec<(usize, BigInt)> = Vec::new();
            let mut non_integer_after_scaling = false;
            for (idx, coeff) in rational_coeffs {
                let scaled = coeff * lcm_rat.clone();
                if scaled.denom().is_one() {
                    cut_coeffs.push((idx, scaled.numer().clone()));
                } else {
                    if debug {
                        safe_eprintln!(
                            "[HNF] Skipping cut with non-integer coefficient after scaling: {}",
                            scaled
                        );
                    }
                    non_integer_after_scaling = true;
                    break;
                }
            }

            if non_integer_after_scaling || cut_coeffs.is_empty() {
                continue;
            }

            // Scaled identity: `cut_coeffs . x = scaled_value` for every `x`
            // satisfying the asserted equalities, with both sides integral.
            let scaled_value = implied_value * lcm_rat;
            if !scaled_value.denom().is_one() {
                continue;
            }
            let scaled_value = scaled_value.numer().clone();

            // `cut_coeffs . x` is a multiple of `g = gcd(cut_coeffs)` at every
            // INTEGER point, so `cut_coeffs . x <= g * floor(scaled_value / g)`
            // is valid over the integers: at an integer solution of the
            // equalities the left side equals `scaled_value` and is a multiple
            // of `g`, hence at most the largest multiple of `g` below it. When
            // `g` divides `scaled_value` the bound IS `scaled_value` and the cut
            // is already implied by the equalities, so it carries no
            // information; the useful case is `g doesn't divide scaled_value`,
            // where no integer solution exists and the cut closes the branch —
            // exactly the classical GCD test, and the only conclusion an
            // equality-only HNF row can soundly support.
            let mut g = BigInt::zero();
            for (_, coeff) in &cut_coeffs {
                g = g.gcd(coeff);
            }
            if g.is_zero() {
                continue;
            }
            if (&scaled_value % &g).is_zero() {
                if debug {
                    safe_eprintln!(
                        "[HNF] Row {} carries no GCD conflict (gcd {} divides {}), no cut",
                        cut_i,
                        g,
                        scaled_value
                    );
                }
                continue;
            }
            let cut_bound = &g * scaled_value.div_floor(&g);

            if debug {
                safe_eprintln!(
                    "[HNF] Cut: y0[{}]={}, implied={}, lcm={}, gcd={}, coeffs: {:?}, bound: {}",
                    cut_i,
                    y0[cut_i],
                    scaled_value,
                    lcm,
                    g,
                    cut_coeffs,
                    cut_bound
                );
            }

            cuts_out.push(HnfCut {
                coeffs: cut_coeffs,
                bound: cut_bound,
            });
        }

        info!(
            target: "ay::lia",
            cuts_generated = cuts_out.len(),
            matrix_rows = m,
            matrix_cols = n,
            basis_rows = basis_rows.len(),
            non_integer_rows = cut_rows.len(),
            "HNF cut generation"
        );

        cuts_out
    }
}

impl Default for HnfCutter {
    fn default() -> Self {
        Self::new()
    }
}
