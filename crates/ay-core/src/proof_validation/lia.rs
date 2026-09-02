// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Semantic validation for LIA (Linear Integer Arithmetic) proof certificates.
//!
//! LIA theory lemmas can arise from three proof shapes:
//!
//! - **BoundsGap**: The Farkas combination of conflict literals yields integer
//!   bounds `lower > upper` after rounding. For example, `x >= 6 AND x <= 5`
//!   is a bounds gap because no integer satisfies both.
//!
//! - **Divisibility**: The GCD of a constraint's variable coefficients does not
//!   divide the constant term, proving no integer solution exists. For example,
//!   `2x = 3` has no integer solution because `gcd(2) = 2` does not divide 3.
//!
//! - **CuttingPlane**: A Farkas combination followed by integer rounding
//!   (Gomory cut). The combination produces a valid real inequality, which after
//!   dividing by a divisor and rounding to integers becomes contradictory.
//!
//! All three shapes ultimately reduce to Farkas certificate verification with
//! additional integer-specific checks.

use thiserror::Error;

use crate::{
    CuttingPlaneAnnotation, FarkasAnnotation, LiaAnnotation, ProofId, TermId, TermStore, TheoryLit,
};

/// Exact lattice gap used to lower one checked integer-divisibility theorem.
///
/// For `equality = (= lhs rhs)`, `difference = lhs - rhs` ranges over one
/// residue class modulo the GCD of its variable coefficients.  A validated
/// divisibility theorem proves that zero is not in that class.  Consequently
/// every valuation satisfies `difference <= lower` or `upper <= difference`,
/// where `lower < 0 < upper` are the adjacent values in that residue class.
///
/// This is evidence, not a second recognizer: construction reruns the exact
/// arithmetic used by [`recognize_lia_divisibility`] and returns `None` for
/// every unsupported or non-tautological clause.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LiaDivisibilityEqualityWitness {
    /// The left operand of the certified equality.
    pub lhs: TermId,
    /// The right operand of the certified equality.
    pub rhs: TermId,
    /// Greatest attainable value of `lhs - rhs` below zero.
    pub lower: num_bigint::BigInt,
    /// Least attainable value of `lhs - rhs` above zero.
    pub upper: num_bigint::BigInt,
}

/// Errors returned when an LIA proof certificate fails validation.
#[derive(Debug, Error, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub enum LiaValidationError {
    /// The underlying Farkas certificate is invalid.
    #[error("Farkas validation failed: {reason}")]
    FarkasInvalid {
        /// Detail from the Farkas validator.
        reason: String,
    },

    /// BoundsGap: the Farkas combination does not produce a contradiction
    /// when rounded to integers.
    #[error("bounds gap does not produce integer contradiction")]
    BoundsGapNotContradictory,

    /// CuttingPlane: the divisor is non-positive.
    #[error("cutting plane divisor must be positive, got {divisor}")]
    InvalidDivisor {
        /// The invalid divisor value.
        divisor: i64,
    },

    /// The LIA annotation is missing but required for strict validation.
    #[error("LIA theory lemma in strict mode requires an LiaAnnotation")]
    MissingAnnotation,

    /// The Farkas annotation is missing but required for the LIA proof shape.
    #[error("LIA proof shape {shape} requires a Farkas annotation")]
    MissingFarkas {
        /// The proof shape that requires Farkas coefficients.
        shape: &'static str,
    },

    /// The LIA proof shape claims integer-specific reasoning (a GCD/divisibility
    /// argument) that this checker does not yet verify. STRICT mode FAILS CLOSED:
    /// rather than accept the clause on a structural check alone (which would let a
    /// forged annotation certify a non-tautological clause -- a meta-false-PROVE),
    /// the lemma is rejected so the proof cannot be strict-Verified.
    #[error("LIA proof shape {shape} requires integer reasoning that is not yet verified; rejected fail-closed")]
    IntegerReasoningUnverified {
        /// The proof shape whose integer reasoning is unverified.
        shape: &'static str,
    },
}

/// Validate an LIA theory lemma given its annotation, clause, and Farkas certificate.
///
/// This is the main entry point for LIA strict-mode validation. It dispatches
/// to the appropriate shape-specific validator based on the `LiaAnnotation`.
pub fn validate_lia_theory_lemma(
    terms: &TermStore,
    step_id: ProofId,
    clause: &[TermId],
    farkas: Option<&FarkasAnnotation>,
    lia: &LiaAnnotation,
) -> Result<(), LiaValidationError> {
    match lia {
        LiaAnnotation::BoundsGap => validate_bounds_gap(terms, clause, farkas),
        LiaAnnotation::Divisibility => validate_divisibility(terms, step_id, clause),
        LiaAnnotation::CuttingPlane(cp) => validate_cutting_plane(terms, clause, cp),
        LiaAnnotation::LinearIdentity => validate_linear_identity(terms, clause),
    }
}

/// Recognize whether `clause` is a strict-checkable linear-arithmetic IDENTITY —
/// a single POSITIVE equality `(= L R)` whose difference `L - R` reduces to the
/// identically-zero integer linear form (every variable coefficient 0 AND the
/// constant 0), so `L = R` holds for all integer assignments. This is the exact
/// inverse of `validate_linear_identity`, so a classifier upgrading a lemma to
/// `LiaGeneric`/`LinearIdentity` can never drift from the strict checker.
#[must_use]
pub fn recognize_lia_linear_identity(terms: &TermStore, clause: &[TermId]) -> bool {
    validate_linear_identity(terms, clause).is_ok()
}

/// Validate a [`LiaAnnotation::LinearIdentity`] lemma: a unit positive equality
/// `(= L R)` that is a linear-arithmetic tautology because `L - R` is the
/// identically-zero linear form.
///
/// SOUND independent of how deeply `*` is parsed: a nonlinear subterm that
/// `parse_linear_expr` treats as an opaque atom only PREVENTS recognition
/// (fail-closed) — it never causes a false accept, because a linear combination
/// of atoms that is identically zero equals zero for every value of those atoms
/// (hence for every value of the original variables). `int_linear_diff` also
/// fails closed on any non-`Int`-sorted variable.
fn validate_linear_identity(
    terms: &TermStore,
    clause: &[TermId],
) -> Result<(), LiaValidationError> {
    use num_traits::Zero;
    let unverified = || LiaValidationError::IntegerReasoningUnverified {
        shape: "LinearIdentity",
    };
    if clause.len() != 1 {
        return Err(unverified());
    }
    let (l, r) = decode_eq(terms, clause[0]).ok_or_else(unverified)?;
    let (coeffs, constant) = int_linear_diff(terms, l, r).ok_or_else(unverified)?;
    if constant.is_zero() && coeffs.values().all(num_bigint::BigInt::is_zero) {
        Ok(())
    } else {
        Err(unverified())
    }
}

/// Recognize a strict-checkable SMT-LIB Euclidean-remainder range theorem.
///
/// This is the exact inverse of [`validate_lia_mod_range`], so proof producers
/// can only classify clauses that the strict checker independently accepts.
#[must_use]
pub fn recognize_lia_mod_range(terms: &TermStore, clause: &[TermId]) -> bool {
    validate_lia_mod_range(terms, clause).is_ok()
}

/// Validate a unit theorem saying a symbolic Euclidean remainder cannot equal
/// an out-of-range integer constant.
///
/// SMT-LIB integer `mod` satisfies `0 <= (mod x d) < |d|` for every non-zero
/// integer divisor `d`.  Consequently
/// `(not (= (mod x d) r))` is valid for every `x` exactly when the constant
/// `r` is negative or at least `|d|`.  The checker accepts only that closed
/// schema; importantly, divisor zero and non-constant divisors are rejected.
pub fn validate_lia_mod_range(
    terms: &TermStore,
    clause: &[TermId],
) -> Result<(), LiaValidationError> {
    use crate::term::{Constant, Symbol, TermData};
    use crate::Sort;
    use num_traits::{Signed, Zero};

    let fail = || LiaValidationError::IntegerReasoningUnverified { shape: "ModRange" };
    let [literal] = clause else {
        return Err(fail());
    };
    let TermData::Not(equality) = terms.get(*literal) else {
        return Err(fail());
    };
    let (lhs, rhs) = decode_eq(terms, *equality).ok_or_else(fail)?;

    let int_constant = |term: TermId| match terms.get(term) {
        TermData::Const(Constant::Int(value)) => Some(value),
        _ => None,
    };
    let decode = |mod_term: TermId, remainder_term: TermId| {
        let TermData::App(Symbol::Named(name), args) = terms.get(mod_term) else {
            return None;
        };
        let [dividend, divisor] = args.as_slice() else {
            return None;
        };
        if name != "mod"
            || !matches!(terms.sort(mod_term), Sort::Int)
            || !matches!(terms.sort(*dividend), Sort::Int)
            || !matches!(terms.sort(*divisor), Sort::Int)
            || !matches!(terms.sort(remainder_term), Sort::Int)
        {
            return None;
        }
        Some((int_constant(*divisor)?, int_constant(remainder_term)?))
    };
    let (divisor, remainder) = decode(lhs, rhs)
        .or_else(|| decode(rhs, lhs))
        .ok_or_else(fail)?;
    if divisor.is_zero() {
        return Err(fail());
    }
    let modulus = divisor.abs();
    if remainder.is_negative() || remainder >= &modulus {
        Ok(())
    } else {
        Err(fail())
    }
}

/// Decode a POSITIVE equality `(= A B)` into `(A, B)`.
fn decode_eq(terms: &TermStore, lit: TermId) -> Option<(TermId, TermId)> {
    use crate::term::{Symbol, TermData};
    match terms.get(lit) {
        TermData::App(Symbol::Named(n), args) if n == "=" => match args.as_slice() {
            [a, b] => Some((*a, *b)),
            _ => None,
        },
        _ => None,
    }
}

/// Validate a BoundsGap LIA proof.
///
/// A bounds gap proof asserts that the Farkas combination of conflict literals
/// yields a contradiction after integer rounding. Specifically, if the Farkas
/// combination produces `0 <= -epsilon` for some positive epsilon, then in the
/// integer domain the contradiction is even stronger.
///
/// The Farkas combination itself already proves real-arithmetic UNSAT. For
/// BoundsGap, we just verify the Farkas certificate is valid (the integer
/// strengthening is implicit).
fn validate_bounds_gap(
    terms: &TermStore,
    clause: &[TermId],
    farkas: Option<&FarkasAnnotation>,
) -> Result<(), LiaValidationError> {
    // A strict inequality over Int rounds to the next integer.  Two bounds on
    // the same integral linear form can therefore have an EMPTY rounded
    // interval even when their rational relaxations overlap, e.g.
    // `0 < m` and `m - 1 < 0` become `m >= 1` and `m <= 0`.  This is the
    // integer-specific BoundsGap promised by the annotation; it cannot be
    // delegated to rational Farkas validation.
    if recognize_rounded_integer_bounds_gap(terms, clause) {
        return Ok(());
    }

    let farkas = farkas.ok_or(LiaValidationError::MissingFarkas { shape: "BoundsGap" })?;

    // Convert blocking clause literals to conflict literals
    let conflict: Vec<TheoryLit> = clause
        .iter()
        .map(|&lit| blocking_lit_to_conflict(terms, lit))
        .collect();

    // Delegate to the shared Farkas validator
    crate::proof_validation::verify_farkas_conflict_lits_full(terms, &conflict, farkas).map_err(
        |e| LiaValidationError::FarkasInvalid {
            reason: e.to_string(),
        },
    )
}

/// Recognize a strict-checkable pair of integer bounds whose rounded lower
/// endpoint exceeds its rounded upper endpoint.
///
/// Both literals must be blocking-clause negations of comparisons over the
/// SAME all-Int linear form. `parse_int_bound` performs the exact integer
/// rounding and rejects Real/nonlinear/non-integral forms. This function is
/// the producer-facing inverse of the first arm of `validate_bounds_gap`.
#[must_use]
pub fn recognize_lia_bounds_gap(terms: &TermStore, clause: &[TermId]) -> bool {
    recognize_rounded_integer_bounds_gap(terms, clause)
}

/// Recognize an exact two-literal integer clause whose simultaneous falsity
/// would impose contradictory rounded bounds on the same linear form.
/// Unlike the historical bounds-gap recognizer, literals may be positive
/// (cover clause) or negated (mutex clause); `parse_int_bound` converts each
/// blocking literal to the constraint asserted by the clause's negation.
#[must_use]
pub fn recognize_int_bounds_tautology(terms: &TermStore, clause: &[TermId]) -> bool {
    recognize_rounded_integer_bounds_gap(terms, clause)
}

/// Recognize the exact guarded split generated for an arithmetic
/// disequality. The first two literals are the split branches and the third is
/// the equality guard. Integer branches leave exactly the one-value equality
/// gap; Real branches are the two strict orders on the guarded operands.
///
/// Over `Int` the guard may be the branch equality SCALED by a positive
/// integer — see [`arith_disequality_split_guard_multiplier`], which this
/// delegates to.
#[must_use]
pub fn recognize_arith_disequality_split(terms: &TermStore, clause: &[TermId]) -> bool {
    arith_disequality_split_guard_multiplier(terms, clause).is_some()
}

/// True exactly when `clause` is a guarded arithmetic disequality split whose
/// guard is PRIMITIVE — the `k = 1` case, where the guard's canonical linear
/// form is the branch form itself (every `Real` split is primitive by
/// construction).
///
/// This is the emission-side narrowing of [`recognize_arith_disequality_split`]:
/// a printer that lowers the lemma to `(<= lhs rhs)` / `(<= rhs lhs)` over the
/// GUARD's own operands justifies those two sub-steps only when the guard and
/// the branches share one linear form. For `k >= 2` the guard's operands span a
/// wider interval than the branches do, so that lowering is not licensed and
/// the caller must fall back to an unreconstructed wire step.
#[must_use]
pub fn arith_disequality_split_has_primitive_guard(terms: &TermStore, clause: &[TermId]) -> bool {
    use num_traits::One;
    arith_disequality_split_guard_multiplier(terms, clause)
        .is_some_and(|k| k == num_bigint::BigInt::one())
}

/// The positive integer `k` scaling the guard of a guarded arithmetic
/// disequality split, or `None` when `clause` is not such a split.
///
/// # Soundness
///
/// The clause is `(cl  C_b <= T_b - 1   C_b >= T_b + 1   guard)` where `C_b` is
/// the branches' shared canonical integer linear form and `guard` is an
/// equality whose own canonical form is `C_g = T_g`. Take any INTEGER
/// assignment. If either branch holds the clause holds. Otherwise
/// `¬(C_b <= T_b - 1) ∧ ¬(C_b >= T_b + 1)` gives `C_b >= T_b` and `C_b <= T_b`,
/// hence `C_b = T_b` — this is where integrality is load-bearing, and
/// `int_linear_diff` fails closed on any non-`Int`-sorted atom or
/// non-integral coefficient, so a `Real` form (satisfiable strictly between the
/// branches) can never reach here. Then `C_g = k·C_b = k·T_b`, so the guard
/// holds precisely when `T_g = k·T_b`. Both conditions are checked, so the
/// accepted clause is a tautology over the integers.
///
/// `k` MUST be a positive integer and the multiplier is verified against EVERY
/// coefficient, not just a pivot:
///
/// * `k = 0` collapses `C_g` and `k·T_b` to zero, which would admit any guard
///   whose canonical form is `0 = 0` regardless of the branches — rejected;
/// * `k < 0` would need the branch bracketing to flip direction — rejected;
/// * a non-integer `k` leaves `k·T_b` outside `ℤ` and is not licensed by the
///   argument above — rejected (fail-closed: some such clauses are in fact
///   valid, e.g. `2q<=-1 ∨ 2q>=1 ∨ 3q=0`, and are simply not certified here);
/// * a coefficient set that is not uniformly scaled — a different variable, a
///   missing variable, or a per-variable ratio — is rejected by the full
///   verification loop.
///
/// The affine case needs no separate handling: `canonical_int_equality` and
/// `parse_int_comparison` both push the constant term into the TARGET, so
/// `T_g = k·T_b` IS the requirement that the constant scale with the
/// coefficients. The benchmark shape `q <= -1 ∨ q >= 1 ∨ 2q+1 = 4q+1`
/// canonicalizes to branch `(C_b = q, T_b = 0)` and guard `(C_g = 2q, T_g = 0)`,
/// i.e. `k = 2` with `T_g = 2·0`.
#[must_use]
pub fn arith_disequality_split_guard_multiplier(
    terms: &TermStore,
    clause: &[TermId],
) -> Option<num_bigint::BigInt> {
    use crate::term::{Symbol, TermData};
    use crate::Sort;
    use num_traits::One;

    let [first, second, guard] = clause else {
        return None;
    };
    let decode_equality = |term: TermId| match terms.get(term) {
        TermData::App(Symbol::Named(name), args) if name == "=" => match args.as_slice() {
            [a, b] => Some((*a, *b)),
            _ => None,
        },
        TermData::Not(inner) => match terms.get(*inner) {
            TermData::App(Symbol::Named(name), args) if name == "distinct" => {
                match args.as_slice() {
                    [a, b] => Some((*a, *b)),
                    _ => None,
                }
            }
            _ => None,
        },
        _ => None,
    };
    let (lhs, rhs) = decode_equality(*guard)?;
    if terms.sort(lhs) != terms.sort(rhs) {
        return None;
    }

    match terms.sort(lhs) {
        Sort::Real => {
            let decode_lt = |term: TermId| match terms.get(term) {
                TermData::App(Symbol::Named(name), args) if name == "<" => match args.as_slice() {
                    [a, b] => Some((*a, *b)),
                    _ => None,
                },
                _ => None,
            };
            let a = decode_lt(*first);
            let b = decode_lt(*second);
            // The external lowering pairs the forward non-strict inequality
            // with the reverse strict branch and vice versa. Keep the producer
            // order exact instead of silently accepting a permutation for
            // which that derivation would be invalid.
            (a == Some((lhs, rhs)) && b == Some((rhs, lhs))).then(num_bigint::BigInt::one)
        }
        Sort::Int => {
            let (eq_coeffs, eq_target) = canonical_int_equality(terms, lhs, rhs)?;
            let (a_coeffs, a_upper, a_value) = parse_int_comparison(terms, *first, true)?;
            let (b_coeffs, b_upper, b_value) = parse_int_comparison(terms, *second, true)?;
            // The two branches must bracket ONE shared linear form with the
            // exact one-value gap `C_b <= T_b - 1` / `C_b >= T_b + 1`.
            if a_coeffs != b_coeffs || !a_upper || b_upper {
                return None;
            }
            let branch_target = a_value + num_bigint::BigInt::one();
            if b_value != &branch_target + num_bigint::BigInt::one() {
                return None;
            }
            // `k = 1`: the guard IS the branch equality. This is the historical
            // rule, kept as its own arm so the accepted set below is a strict
            // SUPERSET of what it accepted (including the degenerate
            // no-variable form, which the multiplier search rejects).
            if eq_coeffs == a_coeffs && eq_target == branch_target {
                return Some(num_bigint::BigInt::one());
            }
            let k = positive_integer_scale(&a_coeffs, &eq_coeffs)?;
            (eq_target == &k * &branch_target).then_some(k)
        }
        _ => None,
    }
}

/// The unique positive integer `k` with `scaled == k * base` coefficient-wise,
/// or `None` when no such `k` exists.
///
/// Both maps come from [`int_linear_diff`], whose `LinearExpr` source is
/// CANONICAL — a key is present exactly when its coefficient is non-zero — so
/// the pivot below cannot be a hidden zero and equal lengths plus a full
/// per-key check means the key SETS are equal. Every rejection is fail-closed:
/// an empty/all-zero `base` (no pivot), a `scaled` missing the pivot,
/// a non-integral ratio, `k <= 0`, or any coefficient that does not scale.
pub(super) fn positive_integer_scale(
    base: &std::collections::BTreeMap<TermId, num_bigint::BigInt>,
    scaled: &std::collections::BTreeMap<TermId, num_bigint::BigInt>,
) -> Option<num_bigint::BigInt> {
    use num_integer::Integer;
    use num_traits::{Signed, Zero};

    if base.len() != scaled.len() {
        return None;
    }
    let (pivot_var, pivot_base) = base.iter().find(|(_, c)| !c.is_zero())?;
    let pivot_scaled = scaled.get(pivot_var)?;
    let (k, remainder) = pivot_scaled.div_rem(pivot_base);
    if !remainder.is_zero() || !k.is_positive() {
        return None;
    }
    for (var, coeff) in base {
        if scaled.get(var) != Some(&(&k * coeff)) {
            return None;
        }
    }
    Some(k)
}

fn recognize_rounded_integer_bounds_gap(terms: &TermStore, clause: &[TermId]) -> bool {
    let [first, second] = clause else {
        return false;
    };
    let Some((first_coeffs, first_upper, first_value)) = parse_int_bound(terms, *first) else {
        return false;
    };
    let Some((second_coeffs, second_upper, second_value)) = parse_int_bound(terms, *second) else {
        return false;
    };
    if first_coeffs != second_coeffs || first_upper == second_upper {
        return false;
    }
    let (lower, upper) = if first_upper {
        (second_value, first_value)
    } else {
        (first_value, second_value)
    };
    lower > upper
}

/// Recognize whether `clause` is a strict-checkable integer-divisibility
/// tautology — a single negated equality `(not (= A B))` with all-integer
/// variables and `gcd(variable coefficients) ∤ constant`, so `A = B` has no
/// integer solution.
///
/// Used by the proof builder to PROMOTE a `Generic`/trust lemma of this shape to
/// a `LiaGeneric` step carrying [`LiaAnnotation::Divisibility`]. It delegates to
/// the SAME `validate_divisibility` the strict checker runs, so the classifier
/// and checker cannot drift: a clause this accepts is genuinely re-validated, and
/// any other clause stays trust (fail-closed). The promotion changes no verdict —
/// the lemma is already a valid integer tautology.
#[must_use]
pub fn recognize_lia_divisibility(terms: &TermStore, clause: &[TermId]) -> bool {
    validate_divisibility(terms, ProofId(0), clause).is_ok()
}

/// Recover the adjacent lattice values around zero for a unit divisibility
/// theorem `(not (= lhs rhs))`.
///
/// The returned split is suitable for a checked Alethe derivation: the split
/// itself is an integer `la_generic` tautology, while each branch contradicts
/// the equality over ordinary linear arithmetic.  Multi-literal bounded cuts
/// remain outside this lowering and return `None`.
#[must_use]
pub fn lia_divisibility_equality_witness(
    terms: &TermStore,
    clause: &[TermId],
) -> Option<LiaDivisibilityEqualityWitness> {
    use num_integer::Integer;
    use num_traits::{Signed, Zero};

    // Bind this carrier to the checker, including the all-Int sort guard.
    validate_divisibility(terms, ProofId(0), clause).ok()?;
    let [literal] = clause else {
        return None;
    };
    let (lhs, rhs) = decode_negated_eq(terms, *literal)?;
    let (coeffs, constant) = int_linear_diff(terms, lhs, rhs)?;
    let gcd = coeffs
        .values()
        .fold(num_bigint::BigInt::zero(), |gcd, coefficient| {
            gcd.gcd(&coefficient.abs())
        });
    if gcd.is_zero() || (&constant % &gcd).is_zero() {
        return None;
    }

    // `mod_floor` gives the unique representative in [0,gcd). Divisibility
    // rejection excludes zero, so these neighbors are strictly signed.
    let upper = constant.mod_floor(&gcd);
    let lower = &upper - &gcd;
    debug_assert!(lower < num_bigint::BigInt::zero());
    debug_assert!(upper > num_bigint::BigInt::zero());
    Some(LiaDivisibilityEqualityWitness {
        lhs,
        rhs,
        lower,
        upper,
    })
}

/// Validate a Divisibility LIA proof.
///
/// A divisibility lemma is a single negated equality `(not (= A B))` that is an
/// integer tautology because `A = B` has no integer solution: writing
/// `A - B = Σ cᵢ·vᵢ + c₀`, the equation `Σ cᵢ·vᵢ = -c₀` is integer-solvable iff
/// `gcd(cᵢ) | c₀`, so the disequality holds in EVERY integer model exactly when
/// `gcd(cᵢ) ∤ c₀`. (E.g. `2y = 7`: `gcd(2) = 2 ∤ 7`.)
///
/// This performs the REAL GCD check (replacing the former fail-closed stub),
/// reusing the audited linear normalizer. SOUNDNESS GUARDS — any of which, if
/// dropped, would admit a non-tautology and let a forged lemma drive a
/// meta-false-PROVE — every one fails CLOSED:
///   * exactly one literal, a negated equality (`(not (= A B))`);
///   * **every variable is INTEGER-sorted** — a `Real` variable makes `A = B`
///     rationally solvable (`2y = 7 ⟹ y = 3.5`), so the divisibility argument is
///     INVALID; a genuinely-nonlinear factor (e.g. `(* x y)`) is normalized to an
///     opaque atom with coefficient `1`, forcing `gcd = 1 | c₀` ⟹ rejected;
///   * every coefficient and the constant are integers;
///   * `gcd(variable coefficients) ∤ c₀` (no-variable case: `c₀ ≠ 0`).
///
/// Treating a constrained integer atom as a free integer only ENLARGES the
/// solution space, so "no free-integer solution" ⟹ "no constrained solution" —
/// the over-approximation is sound.
fn validate_divisibility(
    terms: &TermStore,
    _step_id: ProofId,
    clause: &[TermId],
) -> Result<(), LiaValidationError> {
    use num_bigint::BigInt;
    use num_integer::Integer;
    use num_traits::{Signed, Zero};

    let fail = || LiaValidationError::IntegerReasoningUnverified {
        shape: "Divisibility",
    };

    // gcd of the (already-checked-integer) variable coefficients of a linear form.
    let gcd_of = |coeffs: &std::collections::BTreeMap<TermId, BigInt>| -> BigInt {
        let mut g = BigInt::zero();
        for c in coeffs.values() {
            g = g.gcd(&c.abs());
        }
        g
    };

    match clause.len() {
        // ── Equality `(not (= A B))` — integer-infeasible iff gcd ∤ constant. ──
        1 => {
            let (a, b) = decode_negated_eq(terms, clause[0]).ok_or_else(fail)?;
            let (coeffs, c0) = int_linear_diff(terms, a, b).ok_or_else(fail)?;
            let g = gcd_of(&coeffs);
            if g.is_zero() {
                // No variables: `A = B ⟺ c₀ = 0`; disequality holds iff `c₀ ≠ 0`.
                return if c0.is_zero() { Err(fail()) } else { Ok(()) };
            }
            if (&c0 % &g).is_zero() {
                return Err(fail()); // gcd | c₀ ⟹ an integer solution exists.
            }
            Ok(())
        }
        // ── Bounded gcd range `(not (≤ L ku)) ∨ (not (≥ L kl))` — a genuine
        // integer CUT: `L = Σ cᵢ·vᵢ` takes EXACTLY the multiples of `g = gcd(cᵢ)`
        // (Bézout), so `kl ≤ L ≤ ku` is integer-infeasible iff no multiple of `g`
        // lies in `[kl, ku]`. Restricted to a NON-EMPTY range (`kl ≤ ku`); the
        // empty-range case is a plain bounds gap left to the Farkas path. ──
        2 => {
            let (c1, up1, v1) = parse_int_bound(terms, clause[0]).ok_or_else(fail)?;
            let (c2, up2, v2) = parse_int_bound(terms, clause[1]).ok_or_else(fail)?;
            if c1 != c2 {
                return Err(fail()); // bounds must constrain the SAME linear `L`.
            }
            let (lo, hi) = match (up1, up2) {
                (false, true) => (v1, v2),
                (true, false) => (v2, v1),
                _ => return Err(fail()), // need exactly one lower + one upper.
            };
            let g = gcd_of(&c1);
            if g.is_zero() {
                return Err(fail()); // no variables → not a cut.
            }
            // Smallest multiple of `g` that is ≥ lo; infeasible iff it exceeds hi.
            if lo <= hi && &g * lo.div_ceil(&g) > hi {
                Ok(())
            } else {
                Err(fail())
            }
        }
        _ => Err(fail()),
    }
}

/// Decode `(not (= A B))` → `(A, B)`.
fn decode_negated_eq(terms: &TermStore, lit: TermId) -> Option<(TermId, TermId)> {
    use crate::term::{Symbol, TermData};
    let inner = match terms.get(lit) {
        TermData::Not(i) => *i,
        _ => return None,
    };
    match terms.get(inner) {
        TermData::App(Symbol::Named(n), args) if n == "=" => match args.as_slice() {
            [a, b] => Some((*a, *b)),
            _ => None,
        },
        _ => None,
    }
}

/// `A - B` as an INTEGER linear form: `(variable→coefficient, constant)`, all
/// integers. Returns `None` (fail-closed) if any variable is non-`Int`-sorted (a
/// `Real` variable would make the constraint rationally solvable — the key
/// soundness guard) or any coefficient/constant is non-integer.
pub(super) fn int_linear_diff(
    terms: &TermStore,
    a: TermId,
    b: TermId,
) -> Option<(
    std::collections::BTreeMap<TermId, num_bigint::BigInt>,
    num_bigint::BigInt,
)> {
    use crate::Sort;
    use num_traits::One;
    let mut d = super::farkas::parse_linear_expr(terms, a);
    let mut nb = super::farkas::parse_linear_expr(terms, b);
    nb.negate();
    d.add_scaled(&nb, &num_rational::BigRational::one());
    let mut coeffs = std::collections::BTreeMap::new();
    for (var, c) in &d.coeffs {
        if !matches!(terms.sort(*var), Sort::Int) {
            return None;
        }
        if !c.is_integer() {
            return None;
        }
        coeffs.insert(*var, c.to_integer());
    }
    if !d.constant.is_integer() {
        return None;
    }
    Some((coeffs, d.constant.to_integer()))
}

/// Parse `(not BOUND)` where `BOUND` is an integer comparison `(<=|<|>=|> A B)`,
/// returning the linear `L = A - B`'s variable coefficients, whether the literal
/// constrains `L` from ABOVE (`true`) or BELOW, and the (integer-rounded) bound
/// value on `L`. `A ≤ B ⟺ L ≤ -const`; strict `<`/`>` round by ±1 over integers.
pub(super) fn parse_int_bound(
    terms: &TermStore,
    lit: TermId,
) -> Option<(
    std::collections::BTreeMap<TermId, num_bigint::BigInt>,
    bool,
    num_bigint::BigInt,
)> {
    use crate::term::TermData;
    let (bound, asserted_value) = match terms.get(lit) {
        TermData::Not(i) => (*i, true),
        _ => (lit, false),
    };
    parse_int_comparison(terms, bound, asserted_value)
}

/// [`parse_int_comparison`] under its blocking-row contract, for the sibling
/// guarded-split module: the returned triple is the constraint that holds
/// when `bound` evaluates to `asserted_value`.
pub(super) fn parse_int_comparison_row(
    terms: &TermStore,
    bound: TermId,
    asserted_value: bool,
) -> Option<(
    std::collections::BTreeMap<TermId, num_bigint::BigInt>,
    bool,
    num_bigint::BigInt,
)> {
    parse_int_comparison(terms, bound, asserted_value)
}

fn parse_int_comparison(
    terms: &TermStore,
    bound: TermId,
    asserted_value: bool,
) -> Option<(
    std::collections::BTreeMap<TermId, num_bigint::BigInt>,
    bool,
    num_bigint::BigInt,
)> {
    use crate::term::{Symbol, TermData};
    let (op, a, b) = match terms.get(bound) {
        TermData::App(Symbol::Named(n), args) => match args.as_slice() {
            [a, b] => (n.as_str(), *a, *b),
            _ => return None,
        },
        _ => return None,
    };
    let (coeffs, c0) = int_linear_diff(terms, a, b)?;
    // `A op B` with `A - B = L + c₀`: solve for the bound on `L`.
    let (is_upper, val) = match (op, asserted_value) {
        ("<=", true) | (">", false) => (true, -c0),
        ("<", true) | (">=", false) => (true, -c0 - 1),
        (">=", true) | ("<", false) => (false, -c0),
        (">", true) | ("<=", false) => (false, -c0 + 1),
        _ => return None,
    };
    // Canonicalize the sign so the SAME `L` written either way compares equal:
    // `mk_ge(L,k)` lowers to `(<= k L)`, which parses with NEGATED coefficients.
    // If the leading coefficient is negative, multiply the bound by `-1` (flips
    // both the direction and the value), making the leading coefficient positive.
    use num_traits::Signed;
    let flip = coeffs
        .values()
        .next()
        .is_some_and(num_bigint::BigInt::is_negative);
    if flip {
        let coeffs = coeffs.into_iter().map(|(v, c)| (v, -c)).collect();
        return Some((coeffs, !is_upper, -val));
    }
    Some((coeffs, is_upper, val))
}

include!("lia/canonical_equality.rs");

/// Validate a CuttingPlane LIA proof.
///
/// A cutting plane proof:
/// 1. Combines conflict literals using Farkas coefficients
/// 2. Divides by a positive integer divisor
/// 3. Rounds (ceiling) to obtain tighter integer bounds
/// 4. The tightened bounds are contradictory
///
/// We validate:
/// - The divisor is positive
/// - The Farkas combination is a REAL contradiction (full semantic check), not
///   merely structurally well-shaped.
///
/// STRICT soundness: the previous implementation checked only the Farkas SHAPE
/// (non-negative coefficients + count), which accepts a forged
/// `TheoryLemma{CuttingPlane, clause:[not p]}` whose coefficients never combine
/// to a contradiction -- a meta-false-PROVE. We now run the SAME full semantic
/// Farkas validator as BoundsGap (`verify_farkas_conflict_lits_full`), which
/// admits the clause only when the non-negative combination of its literals
/// cancels all variables to a numerically false ground atom. This rejects every
/// forgery; it conservatively rejects a genuine integer cut whose contradiction
/// emerges only after the divide-and-round step (sound -- a rejected proof is
/// never strict-Verified, never falsely accepted). A certified Gomory cutting
/// plane (the divide/round step) is future work.
fn validate_cutting_plane(
    terms: &TermStore,
    clause: &[TermId],
    cp: &CuttingPlaneAnnotation,
) -> Result<(), LiaValidationError> {
    if cp.divisor <= 0 {
        return Err(LiaValidationError::InvalidDivisor {
            divisor: cp.divisor,
        });
    }

    // Full semantic Farkas check on the underlying combination (mirrors
    // validate_bounds_gap). SHAPE alone is NOT sufficient for soundness.
    let conflict: Vec<TheoryLit> = clause
        .iter()
        .map(|&lit| blocking_lit_to_conflict(terms, lit))
        .collect();

    crate::proof_validation::verify_farkas_conflict_lits_full(terms, &conflict, &cp.farkas).map_err(
        |e| LiaValidationError::FarkasInvalid {
            reason: e.to_string(),
        },
    )
}

/// Convert a blocking-clause literal to the corresponding conflict `TheoryLit`.
///
/// Same polarity inversion as in the LRA Farkas validator:
/// - `NOT(atom)` in blocking clause -> conflict literal `atom = true`
/// - `atom` in blocking clause -> conflict literal `atom = false`
fn blocking_lit_to_conflict(terms: &TermStore, lit: TermId) -> TheoryLit {
    use crate::TermData;
    match terms.get(lit) {
        TermData::Not(inner) => TheoryLit {
            term: *inner,
            value: true,
        },
        _ => TheoryLit {
            term: lit,
            value: false,
        },
    }
}
