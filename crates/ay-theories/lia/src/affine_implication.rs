// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Bounded affine equality implication checks for LIA.
//!
//! This is a small production pre-check for cases where asserted linear
//! equalities imply an asserted disequality's equality atom. It complements the
//! Nelson-Oppen equality propagation code, which only propagates `x = y` and
//! tight-bound equalities.

use super::*;
use num_rational::Rational64;

const MAX_AFFINE_EQS: usize = 64;
const MAX_AFFINE_DISEQS: usize = 64;
const MAX_AFFINE_VARS: usize = 64;

/// Match the established exact-RREF guard used by direct enumeration.  The
/// affine check is only an UNSAT accelerator, so declining inputs or
/// intermediates above this bound is complete-safe and prevents a single
/// `BigRational` normalization from monopolizing a cancelled worker.
const MAX_AFFINE_COEFF_BITS: u64 = 256;

/// A shared budget for the base and augmented rank computations.  Under the
/// 64-row/64-variable structural bounds, both Gauss-Jordan passes require
/// fewer than 300,000 cell updates in total.
const AFFINE_RANK_FUEL: usize = 300_000;

/// Fuel budget (BigRational cell operations) for one minimal-core extraction
/// (#23 Stage 2). The structural bounds above cap the elimination at
/// 64 rows x (65 + 64) tracked columns, so this is generous; it exists as a
/// hard backstop so the narrowing path can NEVER cost more than a small
/// multiple of the trusted `rational_rank` checks it complements.
const MIN_CORE_FUEL: usize = 4_000_000;

#[derive(Clone)]
struct AffineEquation {
    coeffs: HashMap<TermId, BigInt>,
    constant: BigInt,
    reasons: Vec<TheoryLit>,
    /// The single reason literal is KNOWN to denote exactly this row
    /// (the row was parsed from it, or from the literal's own `=` pair), so
    /// certificate attribution (#rank-4 increment 2) needs no re-parse.
    reason_row_exact: bool,
}

struct AffineDisequality {
    coeffs: HashMap<TermId, BigInt>,
    constant: BigInt,
    reasons: Vec<TheoryLit>,
}

impl LiaSolver<'_> {
    /// Return a conflict when positive affine equalities imply a negative
    /// equality atom. Example: `a = b + 1`, `b = c - 1`, `a != c`.
    ///
    /// When the Stage-2 minimal-core path succeeds, the conflict carries a
    /// Farkas certificate built from the Gaussian-elimination multipliers
    /// (#rank-4 increment 2): the target row is exactly `Σ λ_i · row_i` over
    /// the core equations, so `|λ_i|` per single-reason equation literal plus
    /// weight 1 on the disequality literal is an equality-implication
    /// certificate (validated by `verify_farkas_conflict_lits_full`'s
    /// case-split rule). Certificates are post-verdict metadata: conflict
    /// literals are unchanged, and any mapping failure (multi-literal
    /// reasons, reason/row mismatch, coefficient overflow) drops the
    /// certificate, never the conflict.
    pub(crate) fn check_affine_disequality_implication(
        &mut self,
        debug: bool,
    ) -> Option<TheoryConflict> {
        if self.should_timeout() {
            return None;
        }
        let view = self.assertion_view();
        if view.positive_equalities.is_empty() && self.shared_equalities.is_empty()
            || view.negative_equalities.is_empty() && self.shared_disequalities.is_empty()
        {
            return None;
        }
        let equality_count = view.positive_equalities.len() + self.shared_equalities.len();
        let disequality_count = view.negative_equalities.len() + self.shared_disequalities.len();
        if equality_count > MAX_AFFINE_EQS || disequality_count > MAX_AFFINE_DISEQS {
            if debug {
                safe_eprintln!(
                    "[LIA Affine] skipped: {} equalities, {} disequalities exceed bounded check",
                    equality_count,
                    disequality_count
                );
            }
            return None;
        }

        let mut positive_literals = view.positive_equalities.clone();
        positive_literals.sort_by_key(|term| term.0);

        let mut equations = Vec::with_capacity(positive_literals.len());
        for literal in positive_literals {
            if self.should_timeout() {
                return None;
            }
            if let Some((coeffs, constant)) = self.parse_arithmetic_equality(literal) {
                equations.push(AffineEquation {
                    coeffs,
                    constant,
                    reasons: vec![TheoryLit::new(literal, true)],
                    // Row parsed from the reason literal itself.
                    reason_row_exact: true,
                });
            }
        }
        for (lhs, rhs, reasons) in &self.shared_equalities {
            if self.should_timeout() {
                return None;
            }
            if reasons.is_empty() {
                continue;
            }
            if let Some((coeffs, constant)) = self.parse_arithmetic_pair(*lhs, *rhs) {
                // Cheap structural check: the single positive reason literal
                // IS the equality of this pair (either orientation), so the
                // row is the literal's row up to global negation.
                let reason_row_exact = match reasons.as_slice() {
                    [reason] if reason.value => match self.terms.get(reason.term) {
                        TermData::App(Symbol::Named(name), args)
                            if name == "=" && args.len() == 2 =>
                        {
                            (args[0] == *lhs && args[1] == *rhs)
                                || (args[0] == *rhs && args[1] == *lhs)
                        }
                        _ => false,
                    },
                    _ => false,
                };
                equations.push(AffineEquation {
                    coeffs,
                    constant,
                    reasons: reasons.clone(),
                    reason_row_exact,
                });
            }
        }
        if equations.is_empty() {
            return None;
        }

        let mut disequalities = Vec::with_capacity(disequality_count);
        let mut negative_literals = view.negative_equalities.clone();
        negative_literals.sort_by_key(|term| term.0);
        for literal in negative_literals {
            if self.should_timeout() {
                return None;
            }
            if let Some((coeffs, constant)) = self.parse_arithmetic_equality(literal) {
                disequalities.push(AffineDisequality {
                    coeffs,
                    constant,
                    reasons: vec![TheoryLit::new(literal, false)],
                });
            }
        }
        for (lhs, rhs, reasons) in &self.shared_disequalities {
            if self.should_timeout() {
                return None;
            }
            if reasons.is_empty() {
                continue;
            }
            if let Some((coeffs, constant)) = self.parse_arithmetic_pair(*lhs, *rhs) {
                disequalities.push(AffineDisequality {
                    coeffs,
                    constant,
                    reasons: reasons.clone(),
                });
            }
        }

        for disequality in disequalities {
            if self.should_timeout() {
                return None;
            }
            let target_coeffs = disequality.coeffs;
            let target_constant = disequality.constant;

            if target_coeffs.is_empty() {
                if target_constant.is_zero() {
                    let mut conflict = disequality.reasons;
                    conflict.sort_unstable();
                    conflict.dedup();
                    if self.conflict_reasons_all_live(&conflict) {
                        // A syntactically self-contradictory disequality
                        // (`t != t` after linearization): weight 1 on the
                        // single literal is a valid case-split certificate —
                        // but ONLY if that literal actually denotes this
                        // target row. Shared-disequality reasons are
                        // combiner-propagated and need not be the
                        // `(= lhs rhs)` atom; on mismatch DROP the
                        // certificate, keep the conflict (verdict unchanged).
                        if conflict.len() == 1
                            && self.diseq_reason_denotes_row(
                                conflict[0],
                                &target_coeffs,
                                &target_constant,
                            )
                        {
                            return Some(TheoryConflict::with_farkas(
                                conflict,
                                FarkasAnnotation::new(vec![Rational64::from(1)]),
                            ));
                        }
                        return Some(TheoryConflict::new(conflict));
                    }
                }
                continue;
            }

            if self.affine_equations_imply(&equations, &target_coeffs, &target_constant) {
                // #23 Stage 2: narrow the conflict to the equations that
                // actually participate in implying the target. The candidate
                // core comes from multiplier tracking during Gaussian
                // elimination and is only used after RE-VERIFYING — with the
                // same bounded exact `rational_rank` test — that the subset
                // alone still implies the target. Any failure (fuel,
                // coefficient growth, cancellation, verification) falls
                // back to the baseline fat conflict unless cancelled.
                // Minimal-core affine conflict narrowing (#23 Stage 2) is
                // always on (former `AY_AFFINE_MIN_CORE` kill-switch removed;
                // enabled was the default). A `None` core falls back to the
                // baseline fat-conflict path below.
                let core =
                    self.affine_minimal_core(&equations, &target_coeffs, &target_constant, debug);
                // Optional core extraction may have observed cancellation
                // after the baseline implication proof completed. Honour it
                // instead of publishing a late (albeit sound) fat conflict.
                if self.should_timeout() {
                    return None;
                }
                let mut conflict: Vec<TheoryLit> = match &core {
                    Some(entries) => entries
                        .iter()
                        .flat_map(|&(i, _)| equations[i].reasons.iter().copied())
                        .collect(),
                    None => equations
                        .iter()
                        .flat_map(|eq| eq.reasons.iter().copied())
                        .collect(),
                };
                conflict.extend(disequality.reasons.iter().copied());
                conflict.sort_unstable();
                conflict.dedup();
                if !self.conflict_reasons_all_live(&conflict) {
                    continue;
                }
                if debug {
                    safe_eprintln!(
                        "[LIA Affine] disequality contradicted by {} affine equalities ({} reasons{})",
                        equations.len(),
                        conflict.len(),
                        match &core {
                            Some(entries) => format!(", min-core of {} equations", entries.len()),
                            None => String::new(),
                        }
                    );
                }
                // #rank-4 increment 2: post-verdict Farkas certificate from
                // the tracked Gaussian multipliers. Never affects the
                // conflict literals; any mapping failure drops it.
                let farkas = core.as_ref().and_then(|entries| {
                    self.affine_conflict_farkas(
                        &equations,
                        entries,
                        &disequality.reasons,
                        &target_coeffs,
                        &target_constant,
                        &conflict,
                    )
                });
                return Some(match farkas {
                    Some(farkas) => TheoryConflict::with_farkas(conflict, farkas),
                    None => TheoryConflict::new(conflict),
                });
            }
        }

        None
    }

    /// Map the minimal-core Gaussian multipliers to per-literal Farkas
    /// coefficients (#rank-4 increment 2).
    ///
    /// The core invariant is `target_row == Σ multiplier_i · row_i`, so the
    /// magnitudes `|multiplier_i|` on the (single-reason) equation literals
    /// plus weight 1 on the disequality literal form an equality-implication
    /// certificate: both branches of the disequality case split admit a
    /// Farkas contradiction with these magnitudes (sign selection is the
    /// validator's per-equality orientation choice).
    ///
    /// Returns `None` — certificate dropped, conflict unchanged — when:
    /// - the disequality has multiple reason literals (shared/propagated),
    /// - the disequality's reason literal does not denote the target row
    ///   (shared-disequality reasons are combiner-propagated and need not be
    ///   the `(= lhs rhs)` atom; weight 1 on an unrelated literal would
    ///   certify the wrong combination),
    /// - a core equation has zero or multiple reason literals,
    /// - a core equation's row does not re-parse from its reason literal
    ///   (up to global negation), so per-literal attribution would be wrong,
    /// - one literal backs more than one core row (ambiguous attribution),
    /// - a multiplier does not fit `Rational64`.
    fn affine_conflict_farkas(
        &self,
        equations: &[AffineEquation],
        core: &[(usize, BigRational)],
        diseq_reasons: &[TheoryLit],
        target_coeffs: &HashMap<TermId, BigInt>,
        target_constant: &BigInt,
        conflict: &[TheoryLit],
    ) -> Option<FarkasAnnotation> {
        let [diseq_lit] = diseq_reasons else {
            return None;
        };
        // The disequality reason literal gets weight 1, so it must denote
        // exactly the target row (up to global negation / operand swap).
        if !self.diseq_reason_denotes_row(*diseq_lit, target_coeffs, target_constant) {
            return None;
        }

        let mut weights: HashMap<TheoryLit, BigRational> = HashMap::default();
        for &(index, ref multiplier) in core {
            let equation = equations.get(index)?;
            let [reason] = equation.reasons.as_slice() else {
                return None;
            };
            if !reason.value {
                // A negated reason cannot assert an equality row.
                return None;
            }
            // The reason literal must denote this exact row (up to global
            // negation): shared-equality rows can carry propagated reasons
            // whose literal is a different constraint, and per-literal
            // attribution would then certify the wrong combination. Rows
            // tagged exact at construction time skip the re-parse.
            if !equation.reason_row_exact {
                let (lit_coeffs, lit_constant) = self.parse_arithmetic_equality(reason.term)?;
                if !Self::rows_equal_up_to_negation(
                    &lit_coeffs,
                    &lit_constant,
                    &equation.coeffs,
                    &equation.constant,
                ) {
                    return None;
                }
            }
            if weights.insert(*reason, multiplier.clone()).is_some() {
                return None;
            }
        }
        if weights.insert(*diseq_lit, BigRational::one()).is_some() {
            return None;
        }

        let mut coefficients = Vec::with_capacity(conflict.len());
        for lit in conflict {
            let weight = weights.get(lit).cloned().unwrap_or_else(BigRational::zero);
            coefficients.push(Self::bigrational_abs_to_rational64(&weight)?);
        }
        Some(FarkasAnnotation::new(coefficients))
    }

    /// Whether `reason` denotes exactly the disequality of the target row
    /// (adversarial-review fix for #rank-4 increment 2).
    ///
    /// The literal must be an `=` asserted false or a `distinct` asserted
    /// true (after unwrapping `not` wrappers), and its `lhs - rhs` row must
    /// equal the target row up to global negation — which also covers
    /// operand swap, exactly like `rows_equal_up_to_negation` does for the
    /// core equations. Anything else fails closed: the caller drops the
    /// certificate but keeps the conflict, so the verdict is unchanged.
    fn diseq_reason_denotes_row(
        &self,
        reason: TheoryLit,
        target_coeffs: &HashMap<TermId, BigInt>,
        target_constant: &BigInt,
    ) -> bool {
        let mut term = reason.term;
        let mut value = reason.value;
        while let TermData::Not(inner) = self.terms.get(term) {
            term = *inner;
            value = !value;
        }
        let TermData::App(Symbol::Named(name), args) = self.terms.get(term) else {
            return false;
        };
        if args.len() != 2 {
            return false;
        }
        let denotes_disequality = match name.as_str() {
            "=" => !value,
            "distinct" => value,
            _ => false,
        };
        if !denotes_disequality {
            return false;
        }
        let Some((coeffs, constant)) = self.parse_arithmetic_pair(args[0], args[1]) else {
            return false;
        };
        Self::rows_equal_up_to_negation(&coeffs, &constant, target_coeffs, target_constant)
    }

    /// `|value|` as a `Rational64`, or `None` when it does not fit.
    fn bigrational_abs_to_rational64(value: &BigRational) -> Option<Rational64> {
        let abs = value.abs();
        let numer = i64::try_from(abs.numer()).ok()?;
        let denom = i64::try_from(abs.denom()).ok()?;
        (denom != 0).then(|| Rational64::new(numer, denom))
    }

    /// Whether two linear equality rows denote the same equation, either
    /// exactly or with every coefficient and the constant negated.
    fn rows_equal_up_to_negation(
        lhs_coeffs: &HashMap<TermId, BigInt>,
        lhs_constant: &BigInt,
        rhs_coeffs: &HashMap<TermId, BigInt>,
        rhs_constant: &BigInt,
    ) -> bool {
        if lhs_coeffs.len() != rhs_coeffs.len() {
            return false;
        }
        let exact = lhs_constant == rhs_constant
            && lhs_coeffs
                .iter()
                .all(|(var, coeff)| rhs_coeffs.get(var) == Some(coeff));
        if exact {
            return true;
        }
        *lhs_constant == -rhs_constant.clone()
            && lhs_coeffs
                .iter()
                .all(|(var, coeff)| rhs_coeffs.get(var).is_some_and(|rc| *coeff == -rc.clone()))
    }

    fn parse_arithmetic_equality(
        &self,
        literal: TermId,
    ) -> Option<(HashMap<TermId, BigInt>, BigInt)> {
        let TermData::App(Symbol::Named(name), args) = self.terms.get(literal) else {
            return None;
        };
        if name != "=" || args.len() != 2 {
            return None;
        }
        self.parse_arithmetic_pair(args[0], args[1])
    }

    fn parse_arithmetic_pair(
        &self,
        lhs: TermId,
        rhs: TermId,
    ) -> Option<(HashMap<TermId, BigInt>, BigInt)> {
        let lhs_sort = self.terms.sort(lhs);
        let rhs_sort = self.terms.sort(rhs);
        if !matches!(lhs_sort, Sort::Int | Sort::Real)
            || !matches!(rhs_sort, Sort::Int | Sort::Real)
        {
            return None;
        }

        let (mut coeffs, constant) = self.parse_linear_expr_with_vars(lhs, rhs);
        coeffs.retain(|_, coeff| !coeff.is_zero());
        Some((coeffs, constant))
    }

    fn affine_equations_imply(
        &self,
        equations: &[AffineEquation],
        target_coeffs: &HashMap<TermId, BigInt>,
        target_constant: &BigInt,
    ) -> bool {
        if self.should_timeout()
            || !Self::integer_is_bounded(target_constant)
            || target_coeffs
                .values()
                .any(|coefficient| !Self::integer_is_bounded(coefficient))
            || equations.iter().any(|equation| {
                !Self::integer_is_bounded(&equation.constant)
                    || equation
                        .coeffs
                        .values()
                        .any(|coefficient| !Self::integer_is_bounded(coefficient))
            })
        {
            return false;
        }

        let mut vars: Vec<TermId> = Vec::new();
        let mut seen: HashSet<TermId> = HashSet::default();
        for eq in equations {
            if self.should_timeout() {
                return false;
            }
            for &var in eq.coeffs.keys() {
                if seen.insert(var) {
                    vars.push(var);
                }
            }
        }
        for &var in target_coeffs.keys() {
            if self.should_timeout() {
                return false;
            }
            if seen.insert(var) {
                vars.push(var);
            }
        }
        if vars.len() > MAX_AFFINE_VARS {
            return false;
        }
        vars.sort_unstable_by_key(|term| term.0);

        let mut rows = Vec::with_capacity(equations.len());
        for eq in equations {
            if self.should_timeout() {
                return false;
            }
            rows.push(Self::affine_row(&vars, &eq.coeffs, &eq.constant));
        }
        let mut rows_with_target = rows.clone();
        rows_with_target.push(Self::affine_row(&vars, target_coeffs, target_constant));

        let mut fuel = AFFINE_RANK_FUEL;
        let mut should_abort = || self.should_timeout();
        let Some(rank) = Self::rational_rank(rows, &mut fuel, &mut should_abort) else {
            return false;
        };
        let Some(rank_with_target) =
            Self::rational_rank(rows_with_target, &mut fuel, &mut should_abort)
        else {
            return false;
        };
        rank == rank_with_target
    }

    /// Minimal-core extraction for an affine implication conflict (#23 Stage 2).
    ///
    /// Precondition: `affine_equations_imply(equations, target_coeffs,
    /// target_constant)` returned `true` (the fat conflict is valid).
    ///
    /// Returns `Some(entries)` — `(index, multiplier)` pairs into `equations`
    /// whose rows alone still imply the target, with the tracked Gaussian
    /// multipliers satisfying `target == Σ multiplier_i · row_i` (#rank-4
    /// increment 2: the multipliers ARE the Farkas coefficients) — only when
    /// the candidate subset has been RE-VERIFIED with the same bounded exact
    /// `rational_rank` equality test. Returns `None` on any failure (fuel
    /// exhaustion, cancellation, coefficient growth, tracking failure,
    /// verification failure); the caller then falls back to the baseline fat
    /// conflict unless cancellation was observed.
    fn affine_minimal_core(
        &mut self,
        equations: &[AffineEquation],
        target_coeffs: &HashMap<TermId, BigInt>,
        target_constant: &BigInt,
        debug: bool,
    ) -> Option<Vec<(usize, BigRational)>> {
        self.affine_min_core_attempts += 1;

        // Rebuild the variable ordering and rows exactly as
        // `affine_equations_imply` does, so row indices line up.
        let mut vars: Vec<TermId> = Vec::new();
        let mut seen: HashSet<TermId> = HashSet::default();
        for eq in equations {
            for &var in eq.coeffs.keys() {
                if seen.insert(var) {
                    vars.push(var);
                }
            }
        }
        for &var in target_coeffs.keys() {
            if seen.insert(var) {
                vars.push(var);
            }
        }
        if vars.len() > MAX_AFFINE_VARS {
            return None;
        }
        vars.sort_unstable_by_key(|term| term.0);

        let mut rows = Vec::with_capacity(equations.len());
        for eq in equations {
            rows.push(Self::affine_row(&vars, &eq.coeffs, &eq.constant));
        }
        let target = Self::affine_row(&vars, target_coeffs, target_constant);

        let mut fuel = MIN_CORE_FUEL;
        let candidate = {
            let mut should_abort = || self.should_timeout();
            Self::affine_core_candidate_with_multipliers_bounded(
                &rows,
                &target,
                &mut fuel,
                &mut should_abort,
            )?
        };
        let candidate_indices: Vec<usize> = candidate.iter().map(|&(index, _)| index).collect();

        // SOUNDNESS GATE: only accept the candidate if the exact subset alone
        // still implies the target, judged by the same trusted rank routine
        // the fat path uses. Anything else falls back to the fat conflict.
        let verified = {
            let mut fuel = AFFINE_RANK_FUEL;
            let mut should_abort = || self.should_timeout();
            Self::affine_core_verified_bounded(
                &rows,
                &target,
                &candidate_indices,
                &mut fuel,
                &mut should_abort,
            )
        };
        if !verified {
            if debug {
                safe_eprintln!(
                    "[LIA Affine] min-core candidate of {} rows FAILED re-verification; using fat conflict",
                    candidate.len()
                );
            }
            return None;
        }

        self.affine_min_core_successes += 1;
        Some(candidate)
    }

    /// Identify a candidate core: indices of `rows` that participate with a
    /// nonzero multiplier when `target` is expressed as a linear combination
    /// of the rows (Gaussian elimination with combination tracking).
    ///
    /// Returns `None` if `fuel` (a count of BigRational cell operations) runs
    /// out, on shape mismatch, or if the target does not reduce to the zero
    /// row (not in the row span — cannot happen when the trusted rank test
    /// said "implied", but handled defensively).
    ///
    /// Deletion-minimization on top of this candidate (considered as a #23
    /// Stage 2 follow-up) is provably a no-op, so it is intentionally not
    /// implemented: by induction over the elimination, every pivot row's
    /// combination only references original rows that themselves became
    /// pivots, and those source rows are linearly independent (the pivot
    /// rows are independent and live in their span). The returned support is
    /// therefore a subset of an independent set; deleting any member while
    /// still spanning the target would exhibit a nontrivial dependency among
    /// independent rows — impossible. (A smaller core with *different*
    /// support can exist, but single-row deletion cannot reach it.)
    #[cfg_attr(not(test), allow(dead_code))] // index-only view used by the Stage-2 unit tests
    pub(crate) fn affine_core_candidate(
        rows: &[Vec<BigRational>],
        target: &[BigRational],
        fuel: &mut usize,
    ) -> Option<Vec<usize>> {
        Self::affine_core_candidate_with_multipliers(rows, target, fuel)
            .map(|core| core.into_iter().map(|(index, _)| index).collect())
    }

    /// `affine_core_candidate` with the tracked multipliers per surviving
    /// row: `target == Σ multiplier_i · rows[index_i]` (#rank-4 increment 2).
    pub(crate) fn affine_core_candidate_with_multipliers(
        rows: &[Vec<BigRational>],
        target: &[BigRational],
        fuel: &mut usize,
    ) -> Option<Vec<(usize, BigRational)>> {
        let mut never_abort = || false;
        Self::affine_core_candidate_with_multipliers_bounded(rows, target, fuel, &mut never_abort)
    }

    fn affine_core_candidate_with_multipliers_bounded<F: FnMut() -> bool>(
        rows: &[Vec<BigRational>],
        target: &[BigRational],
        fuel: &mut usize,
        should_abort: &mut F,
    ) -> Option<Vec<(usize, BigRational)>> {
        let row_count = rows.len();
        if should_abort() || row_count == 0 {
            return None;
        }
        let width = target.len();
        if rows.iter().any(|row| row.len() != width)
            || !target.iter().all(Self::rational_is_bounded)
            || !rows.iter().flatten().all(Self::rational_is_bounded)
        {
            return None;
        }

        // Each work row is (data, combo) with the invariant
        // `data == Σ combo[j] * rows[j]` over the ORIGINAL rows.
        let mut work: Vec<(Vec<BigRational>, Vec<BigRational>)> = rows
            .iter()
            .enumerate()
            .map(|(index, row)| {
                let mut combo = vec![BigRational::zero(); row_count];
                combo[index] = BigRational::one();
                (row.clone(), combo)
            })
            .collect();

        // Target tracking invariant: `t_data == target - Σ t_combo[j] * rows[j]`.
        let mut t_data = target.to_vec();
        let mut t_combo = vec![BigRational::zero(); row_count];

        let mut rank = 0;
        for col in 0..width {
            if should_abort() {
                return None;
            }
            let Some(pivot) = (rank..row_count).find(|&row| !work[row].0[col].is_zero()) else {
                continue;
            };
            work.swap(rank, pivot);

            // Normalize the pivot row (data tail + full combo).
            let pivot_value = work[rank].0[col].clone();
            {
                let (data, combo) = &mut work[rank];
                for cell in data.iter_mut().skip(col) {
                    if !Self::affine_step_allowed(fuel, should_abort) {
                        return None;
                    }
                    *cell = Self::bounded_rational_div(cell, &pivot_value)?;
                }
                for cell in combo.iter_mut() {
                    if !Self::affine_step_allowed(fuel, should_abort) {
                        return None;
                    }
                    *cell = Self::bounded_rational_div(cell, &pivot_value)?;
                }
            }
            let (pivot_data, pivot_combo) = work[rank].clone();

            // Eliminate the pivot column from the rows below (echelon form).
            for row in (rank + 1)..row_count {
                if should_abort() {
                    return None;
                }
                let factor = work[row].0[col].clone();
                if factor.is_zero() {
                    continue;
                }
                let (data, combo) = &mut work[row];
                for (cell, pivot_cell) in data.iter_mut().skip(col).zip(pivot_data.iter().skip(col))
                {
                    if !Self::affine_step_allowed(fuel, should_abort) {
                        return None;
                    }
                    *cell = Self::bounded_rational_scaled_sub(cell, &factor, pivot_cell)?;
                }
                for (cell, pivot_cell) in combo.iter_mut().zip(pivot_combo.iter()) {
                    if !Self::affine_step_allowed(fuel, should_abort) {
                        return None;
                    }
                    *cell = Self::bounded_rational_scaled_sub(cell, &factor, pivot_cell)?;
                }
            }

            // Reduce the target by the pivot row, accumulating multipliers.
            let t_factor = t_data[col].clone();
            if !t_factor.is_zero() {
                for (cell, pivot_cell) in
                    t_data.iter_mut().skip(col).zip(pivot_data.iter().skip(col))
                {
                    if !Self::affine_step_allowed(fuel, should_abort) {
                        return None;
                    }
                    *cell = Self::bounded_rational_scaled_sub(cell, &t_factor, pivot_cell)?;
                }
                for (cell, pivot_cell) in t_combo.iter_mut().zip(pivot_combo.iter()) {
                    if !Self::affine_step_allowed(fuel, should_abort) {
                        return None;
                    }
                    *cell = Self::bounded_rational_scaled_add(cell, &t_factor, pivot_cell)?;
                }
            }

            rank += 1;
            if rank == row_count {
                break;
            }
        }

        // The target is in the row span iff it reduced to the zero row.
        // (Echelon-order reduction guarantees no earlier column re-fills.)
        if t_data.iter().any(|cell| !cell.is_zero()) {
            return None;
        }

        let core: Vec<(usize, BigRational)> = (0..row_count)
            .filter(|&index| !t_combo[index].is_zero())
            .map(|index| (index, t_combo[index].clone()))
            .collect();
        Some(core)
    }

    /// Trusted re-verification: does the exact subset `core` of `rows` alone
    /// still imply `target`? Any bounded-elimination abort rejects the
    /// candidate; the caller retains the already-proved fat conflict.
    #[cfg_attr(not(test), allow(dead_code))]
    pub(crate) fn affine_core_verified(
        rows: &[Vec<BigRational>],
        target: &[BigRational],
        core: &[usize],
    ) -> bool {
        let mut fuel = AFFINE_RANK_FUEL;
        let mut never_abort = || false;
        Self::affine_core_verified_bounded(rows, target, core, &mut fuel, &mut never_abort)
    }

    fn affine_core_verified_bounded<F: FnMut() -> bool>(
        rows: &[Vec<BigRational>],
        target: &[BigRational],
        core: &[usize],
        fuel: &mut usize,
        should_abort: &mut F,
    ) -> bool {
        if should_abort()
            || core.iter().any(|&index| index >= rows.len())
            || !target.iter().all(Self::rational_is_bounded)
            || core
                .iter()
                .flat_map(|&index| rows[index].iter())
                .any(|value| !Self::rational_is_bounded(value))
        {
            return false;
        }
        let core_rows: Vec<Vec<BigRational>> =
            core.iter().map(|&index| rows[index].clone()).collect();
        let mut core_rows_with_target = core_rows.clone();
        core_rows_with_target.push(target.to_vec());
        let Some(rank) = Self::rational_rank(core_rows, fuel, should_abort) else {
            return false;
        };
        let Some(rank_with_target) = Self::rational_rank(core_rows_with_target, fuel, should_abort)
        else {
            return false;
        };
        rank == rank_with_target
    }

    fn affine_row(
        vars: &[TermId],
        coeffs: &HashMap<TermId, BigInt>,
        constant: &BigInt,
    ) -> Vec<BigRational> {
        let mut row = Vec::with_capacity(vars.len() + 1);
        for var in vars {
            row.push(BigRational::from(
                coeffs.get(var).cloned().unwrap_or_else(BigInt::zero),
            ));
        }
        row.push(BigRational::from(constant.clone()));
        row
    }

    fn integer_is_bounded(value: &BigInt) -> bool {
        value.bits() <= MAX_AFFINE_COEFF_BITS
    }

    fn rational_is_bounded(value: &BigRational) -> bool {
        value.numer().bits() <= MAX_AFFINE_COEFF_BITS
            && value.denom().bits() <= MAX_AFFINE_COEFF_BITS
    }

    fn affine_step_allowed<F: FnMut() -> bool>(fuel: &mut usize, should_abort: &mut F) -> bool {
        if *fuel == 0 || should_abort() {
            return false;
        }
        *fuel -= 1;
        true
    }

    fn bounded_rational_div(dividend: &BigRational, divisor: &BigRational) -> Option<BigRational> {
        if divisor.is_zero()
            || !Self::rational_is_bounded(dividend)
            || !Self::rational_is_bounded(divisor)
        {
            return None;
        }
        let result = dividend / divisor;
        Self::rational_is_bounded(&result).then_some(result)
    }

    fn bounded_rational_scaled_sub(
        value: &BigRational,
        factor: &BigRational,
        pivot: &BigRational,
    ) -> Option<BigRational> {
        if !Self::rational_is_bounded(value)
            || !Self::rational_is_bounded(factor)
            || !Self::rational_is_bounded(pivot)
        {
            return None;
        }
        let product = factor * pivot;
        if !Self::rational_is_bounded(&product) {
            return None;
        }
        let result = value - &product;
        Self::rational_is_bounded(&result).then_some(result)
    }

    fn bounded_rational_scaled_add(
        value: &BigRational,
        factor: &BigRational,
        pivot: &BigRational,
    ) -> Option<BigRational> {
        if !Self::rational_is_bounded(value)
            || !Self::rational_is_bounded(factor)
            || !Self::rational_is_bounded(pivot)
        {
            return None;
        }
        let product = factor * pivot;
        if !Self::rational_is_bounded(&product) {
            return None;
        }
        let result = value + &product;
        Self::rational_is_bounded(&result).then_some(result)
    }

    /// Exact Gauss-Jordan rank with cooperative cancellation, cell-operation
    /// fuel, and a coefficient-size invariant. `None` means "rank not proved"
    /// and must never be mapped to a numeric rank or used to emit a conflict.
    fn rational_rank<F: FnMut() -> bool>(
        mut rows: Vec<Vec<BigRational>>,
        fuel: &mut usize,
        should_abort: &mut F,
    ) -> Option<usize> {
        if should_abort() {
            return None;
        }
        if rows.is_empty() {
            return Some(0);
        }

        let row_count = rows.len();
        let col_count = rows[0].len();
        if rows.iter().any(|row| row.len() != col_count)
            || !rows.iter().flatten().all(Self::rational_is_bounded)
        {
            return None;
        }
        let mut rank = 0;

        for col in 0..col_count {
            if should_abort() {
                return None;
            }
            let Some(pivot) = (rank..row_count).find(|&row| !rows[row][col].is_zero()) else {
                continue;
            };
            rows.swap(rank, pivot);

            let pivot_value = rows[rank][col].clone();
            for cell in rows[rank].iter_mut().take(col_count).skip(col) {
                if !Self::affine_step_allowed(fuel, should_abort) {
                    return None;
                }
                *cell = Self::bounded_rational_div(cell, &pivot_value)?;
            }
            let pivot_tail: Vec<_> = rows[rank][col..col_count].to_vec();

            for (row, row_values) in rows.iter_mut().enumerate().take(row_count) {
                if should_abort() {
                    return None;
                }
                if row == rank || row_values[col].is_zero() {
                    continue;
                }
                let factor = row_values[col].clone();
                for (cell, pivot_cell) in row_values
                    .iter_mut()
                    .take(col_count)
                    .skip(col)
                    .zip(&pivot_tail)
                {
                    if !Self::affine_step_allowed(fuel, should_abort) {
                        return None;
                    }
                    *cell = Self::bounded_rational_scaled_sub(cell, &factor, pivot_cell)?;
                }
            }

            rank += 1;
            if rank == row_count {
                break;
            }
        }

        Some(rank)
    }
}
