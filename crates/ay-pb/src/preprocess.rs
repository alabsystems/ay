// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Pseudo-Boolean constraint preprocessing.
//!
//! Implements preprocessing techniques from RoundingSat (Elffers & Nordstrom,
//! SAT 2018) and Exact (Devriendt et al., CP 2021) to simplify PB instances
//! before solving. All transformations preserve equisatisfiability.
//!
//! # Techniques
//!
//! 1. **Normalization** — Convert all constraints to `sum(a_i * l_i) >= rhs`
//!    with positive coefficients by replacing negative-coefficient literals with
//!    their complements.
//! 2. **Coefficient tightening (saturation)** — Cap any coefficient exceeding
//!    the RHS at the RHS value, since larger coefficients contribute no extra
//!    propagation power.
//! 3. **GCD strengthening** — Divide all coefficients and the RHS (ceiling) by
//!    the GCD of the coefficients.
//! 4. **Trivial constraint detection** — Remove tautological constraints and
//!    detect unsatisfiable ones early.
//! 5. **Literal fixing (unit propagation)** — Fix literals that are forced by
//!    individual constraints and propagate across the instance.
//! 6. **Dominance pruning** — Remove exact-shape duplicates, weaker
//!    same-left-hand-side constraints, and dominated cardinality supersets.
//!
//! # Reference
//!
//! - Elffers & Nordstrom, "Divide and Conquer: Towards Faster Pseudo-Boolean
//!   Solving" (SAT 2018)
//! - Devriendt, Bogaerts, & Bruynooghe, "Exact: An improved version of the
//!   PB solver RoundingSat" (CP 2021)

use std::collections::{BTreeMap as HashMap, BTreeSet as HashSet};

use crate::propagation::{Lit, LitValue, PbPropagator, PropResult};
use crate::types::{PbConstraint, PbInstance, PbLit, PbObjective, PbRel, PbTerm};

/// Result of preprocessing: either a simplified instance or early UNSAT.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub enum PreprocessResult {
    /// Simplified instance ready for solving.
    ///
    /// The `fixed_literals` map contains variable assignments that were deduced
    /// during preprocessing (literal fixing / unit propagation / probing) or
    /// CHOSEN by optimum-preserving self-reductions (pure/monotone literal
    /// elimination). The solver must incorporate these into its model for
    /// correctness.
    ///
    /// # Contract for optimization callers
    ///
    /// Choice fixings are validated against `instance.objective` at
    /// preprocessing time: they never exclude every model and never move the
    /// minimum of THAT objective. Optimizing a DIFFERENT objective over the
    /// simplified instance is unsupported and may return a wrong optimum (all
    /// in-tree callers pass the instance's own objective). Every remaining row
    /// is still implied by the ORIGINAL constraint conjunction, so using the
    /// rows alone for lower bounds (e.g. LP floors) stays sound even when
    /// `fixed_literals` is discarded.
    Simplified {
        instance: PbInstance,
        /// Variables fixed during preprocessing: `var -> true/false`.
        fixed_literals: HashMap<u32, bool>,
    },
    /// The instance is trivially unsatisfiable.
    Unsatisfiable,
    /// Preprocessing was interrupted before a stable result was produced.
    Interrupted,
}

/// Statistics about preprocessing reductions.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct PreprocessStats {
    /// Constraints removed as trivially satisfied.
    pub trivially_satisfied: u32,
    /// Constraints detected as unsatisfiable.
    pub trivially_unsat: u32,
    /// Number of coefficients tightened (saturated).
    pub coefficients_tightened: u32,
    /// Number of constraints strengthened by GCD division.
    pub gcd_strengthened: u32,
    /// Number of literals fixed by unit propagation.
    pub literals_fixed: u32,
    /// Number of constraints removed by subsumption.
    pub subsumed: u32,
    /// Number of cardinality constraints (all coefficients are 1).
    pub cardinality_constraints: u32,
    /// Number of general (weighted) PB constraints.
    pub weighted_constraints: u32,
    /// Number of variables fixed by failed-literal probing.
    pub probing_fixed: u32,
    /// Number of variables probed (tentatively assigned and propagated).
    pub probes_run: u32,
    /// Rows removed by generalized weighted dominance (superset support with
    /// coefficient dominance), excluding unit-coefficient cardinality pairs.
    pub dominated_weighted: u32,
    /// Rows removed by unit-coefficient cardinality subset dominance.
    pub dominated_cardinality: u32,
    /// Variables fixed by pure/monotone literal elimination (rows + objective
    /// jointly monotone in the fixed polarity).
    pub pure_fixed: u32,
    /// Rows rewritten by the single-residue GCD division (all coefficients but
    /// one share a divisor > 1; the odd coefficient is rounded to the exact
    /// case-split equivalent and the row divided through).
    pub gcd_residue_strengthened: u32,
}

/// Counts cardinality vs weighted constraints in a PB instance.
///
/// Returns `(cardinality_count, weighted_count)`. Useful for instance
/// classification and strategy selection.
#[must_use]
pub fn count_constraint_types(instance: &PbInstance) -> (u32, u32) {
    let mut cardinality = 0u32;
    let mut weighted = 0u32;
    for constraint in &instance.constraints {
        if crate::types::is_cardinality(constraint) {
            cardinality += 1;
        } else {
            weighted += 1;
        }
    }
    (cardinality, weighted)
}

/// Preprocesses a PB instance, returning a simplified (equisatisfiable) instance
/// or an early UNSAT result.
///
/// The preprocessing pipeline runs in order:
/// 1. Normalize all constraints to `>= ` form with positive coefficients
/// 2. Remove trivially satisfied constraints; detect trivially UNSAT ones
/// 3. Apply coefficient tightening (saturation)
/// 4. Apply GCD strengthening
/// 5. Fix forced literals (unit propagation) and simplify
/// 6. Remove weaker same-shape constraints, exact duplicates, and dominated
///    cardinality supersets
///
/// Each step is sound: the returned instance is equisatisfiable with the input.
#[must_use]
pub fn preprocess(instance: &PbInstance) -> PreprocessResult {
    let mut never_stop = || false;
    let mut stats = PreprocessStats::default();
    preprocess_with_stop(
        instance,
        ProbeBudget::default(),
        ChoiceFixings::Forbid,
        &mut stats,
        &mut never_stop,
    )
}

/// Preprocesses a PB instance, also returning per-pass reduction statistics.
#[must_use]
pub fn preprocess_with_stats(instance: &PbInstance) -> (PreprocessResult, PreprocessStats) {
    let mut never_stop = || false;
    let mut stats = PreprocessStats::default();
    let result = preprocess_with_stop(
        instance,
        ProbeBudget::default(),
        ChoiceFixings::Forbid,
        &mut stats,
        &mut never_stop,
    );
    (result, stats)
}

/// Preprocesses a PB instance but allows interruption during expensive passes.
#[must_use]
pub fn preprocess_interruptible<F>(instance: &PbInstance, mut should_stop: F) -> PreprocessResult
where
    F: FnMut() -> bool,
{
    let mut stats = PreprocessStats::default();
    preprocess_with_stop(
        instance,
        ProbeBudget::default(),
        ChoiceFixings::Forbid,
        &mut stats,
        &mut should_stop,
    )
}

/// Preprocesses for a ONE-SHOT solve of the instance as-is, additionally
/// applying optimum-preserving CHOICE reductions (pure/monotone literal
/// elimination) on top of the default entailed-only pipeline.
///
/// # Caller contract (stricter than [`preprocess`])
///
/// Choice fixings may shrink the solution set (they never empty it and never
/// move the minimum of `instance.objective`). They are therefore ONLY sound
/// when the simplified instance is solved exactly as returned:
///
/// * no later `solve_with_assumptions` queries (an assumption contradicting a
///   choice fixing would wrongly report UNSAT with that assumption as core),
/// * no constraints added after preprocessing (`add_constraint_runtime`-style
///   APIs; a later row can invalidate the choice), and
/// * optimization only against `instance.objective` itself.
///
/// The default [`preprocess`] keeps only transformations valid under those
/// APIs; every consumer that cannot guarantee the contract must use it
/// instead.
#[must_use]
pub fn preprocess_one_shot(instance: &PbInstance) -> (PreprocessResult, PreprocessStats) {
    let mut never_stop = || false;
    let mut stats = PreprocessStats::default();
    let result = preprocess_with_stop(
        instance,
        ProbeBudget::default(),
        ChoiceFixings::Allow,
        &mut stats,
        &mut never_stop,
    );
    (result, stats)
}

/// Interruptible variant of [`preprocess_one_shot`] (same caller contract,
/// same return contract: the result plus per-pass reduction statistics).
#[must_use]
pub fn preprocess_one_shot_interruptible<F>(
    instance: &PbInstance,
    mut should_stop: F,
) -> (PreprocessResult, PreprocessStats)
where
    F: FnMut() -> bool,
{
    let mut stats = PreprocessStats::default();
    let result = preprocess_with_stop(
        instance,
        ProbeBudget::default(),
        ChoiceFixings::Allow,
        &mut stats,
        &mut should_stop,
    );
    (result, stats)
}

/// Whether optimum-preserving CHOICE reductions (pure/monotone literal
/// elimination) may be applied. `Forbid` keeps the pipeline entailed-only /
/// solution-set-exact, which is required for solvers that later run
/// assumption queries or add constraints at runtime.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum ChoiceFixings {
    Forbid,
    Allow,
}

/// Preprocesses with an explicit probing budget (used by tests to disable or
/// constrain probing).
#[cfg(test)]
fn preprocess_with_probe_budget(instance: &PbInstance, budget: ProbeBudget) -> PreprocessResult {
    let mut never_stop = || false;
    let mut stats = PreprocessStats::default();
    preprocess_with_stop(
        instance,
        budget,
        ChoiceFixings::Forbid,
        &mut stats,
        &mut never_stop,
    )
}

fn preprocess_with_stop<F>(
    instance: &PbInstance,
    probe_budget: ProbeBudget,
    choice_fixings: ChoiceFixings,
    stats: &mut PreprocessStats,
    should_stop: &mut F,
) -> PreprocessResult
where
    F: FnMut() -> bool,
{
    if should_stop() {
        return PreprocessResult::Interrupted;
    }

    let mut constraints: Vec<PbConstraint> = Vec::with_capacity(instance.constraints.len());
    for (index, constraint) in instance.constraints.iter().enumerate() {
        if index % 32 == 0 && should_stop() {
            return PreprocessResult::Interrupted;
        }
        match normalize_constraint_into(constraint, &mut constraints) {
            NormalizationOutcome::Constraints(()) => {}
            NormalizationOutcome::Unsatisfiable => return PreprocessResult::Unsatisfiable,
            // Keep preprocessing sound if normalization would require
            // coefficients or bounds outside the solver's i128 representation.
            NormalizationOutcome::OverflowNonTrivial => {
                return PreprocessResult::Simplified {
                    instance: instance.clone(),
                    fixed_literals: HashMap::new(),
                };
            }
        }
    }

    // Fixed literal assignments: var -> true/false.
    let mut fixed: HashMap<u32, bool> = HashMap::new();

    // Iterate preprocessing to fixpoint (literal fixing can enable more
    // tightening and subsumption). HUGE instances run a single round: every
    // pass here is optional strengthening/simplification on top of a sound
    // round-0 result (fix_literals already reaches its own internal fixpoint
    // within a round), and on multi-million-row instances the extra rounds
    // rarely find anything while costing seconds of the solve budget each
    // (measured: lopes-172, 6.4M rows, round 1 found 0 fixings/deletions).
    // The gate is evaluated once on the normalized row count, so the pipeline
    // shape is deterministic per instance.
    let max_rounds = if constraints.len() > HUGE_INSTANCE_ROW_CAP {
        1
    } else {
        10
    };
    for _ in 0..max_rounds {
        if should_stop() {
            return PreprocessResult::Interrupted;
        }
        let before_fixed = fixed.len();

        // Trivial constraint removal.
        let mut kept = Vec::with_capacity(constraints.len());
        for (index, c) in constraints.into_iter().enumerate() {
            if index % 64 == 0 && should_stop() {
                return PreprocessResult::Interrupted;
            }
            match classify_trivial(&c) {
                TrivialClass::Satisfied => continue,
                TrivialClass::Unsatisfiable => return PreprocessResult::Unsatisfiable,
                TrivialClass::NonTrivial => kept.push(c),
            }
        }
        constraints = kept;

        // Coefficient tightening.
        for (index, c) in constraints.iter_mut().enumerate() {
            if index % 64 == 0 && should_stop() {
                return PreprocessResult::Interrupted;
            }
            tighten_coefficients(c);
        }

        // GCD strengthening, then single-residue GCD division for rows where
        // exactly one coefficient blocks the plain division.
        for (index, c) in constraints.iter_mut().enumerate() {
            if index % 64 == 0 && should_stop() {
                return PreprocessResult::Interrupted;
            }
            gcd_strengthen(c);
            gcd_residue_strengthen(c, stats);
        }

        // Literal fixing.
        if should_stop() {
            return PreprocessResult::Interrupted;
        }
        match fix_literals_interruptible(&mut constraints, &mut fixed, should_stop) {
            FixResult::Ok { .. } => {}
            FixResult::Conflict => return PreprocessResult::Unsatisfiable,
            FixResult::Interrupted => return PreprocessResult::Interrupted,
        }

        // Failed-literal probing: tentatively assign each unfixed variable and
        // propagate over the original constraints. A propagation conflict on one
        // polarity forces the opposite value (a sound consequence). Newly forced
        // fixings are then propagated into the constraint set like unit fixings.
        if should_stop() {
            return PreprocessResult::Interrupted;
        }
        match probe_failed_literals(&constraints, &mut fixed, &probe_budget, should_stop) {
            ProbeResult::Ok { found_fixings } => {
                if found_fixings {
                    match propagate_fixed_interruptible(&mut constraints, &fixed, should_stop) {
                        PropagateResult::Ok => {}
                        PropagateResult::Conflict => return PreprocessResult::Unsatisfiable,
                        PropagateResult::Interrupted => return PreprocessResult::Interrupted,
                    }
                }
            }
            ProbeResult::Unsatisfiable => return PreprocessResult::Unsatisfiable,
            ProbeResult::Interrupted => return PreprocessResult::Interrupted,
        }

        // Remove weaker constraints with the same normalized left-hand side,
        // exact duplicates, and rows implied by another row (weighted dominance).
        if remove_subsumed_interruptible(&mut constraints, stats, should_stop) {
            return PreprocessResult::Interrupted;
        }

        // Pure/monotone literal elimination (rows + objective jointly) — only
        // for one-shot callers (see `ChoiceFixings`): these fixings are
        // optimum-preserving CHOICES, not entailments, and would corrupt later
        // assumption queries or runtime-added constraints. Fixing a pure
        // literal only weakens rows, so propagating the fixings can never
        // conflict; a conflict would indicate a purity-analysis bug, so fail
        // closed to the UNTOUCHED original instance rather than risk a wrong
        // UNSAT verdict on a non-entailed (choice) fixing.
        match fix_pure_literals_interruptible(
            &constraints,
            instance.objective.as_ref(),
            choice_fixings,
            &mut fixed,
            stats,
            should_stop,
        ) {
            PureResult::Ok { found_fixings } => {
                if found_fixings {
                    match propagate_fixed_interruptible(&mut constraints, &fixed, should_stop) {
                        PropagateResult::Ok => {}
                        PropagateResult::Conflict => {
                            debug_assert!(
                                false,
                                "pure-literal fixing must not conflict (rows only weaken)"
                            );
                            return PreprocessResult::Simplified {
                                instance: instance.clone(),
                                fixed_literals: HashMap::new(),
                            };
                        }
                        PropagateResult::Interrupted => return PreprocessResult::Interrupted,
                    }
                }
            }
            PureResult::Interrupted => return PreprocessResult::Interrupted,
        }

        // Row deletion/subsumption cannot make remaining rows stronger. Only
        // new fixed literals can enable another useful propagation round.
        if fixed.len() == before_fixed {
            break;
        }
    }

    // Rebuild the instance with the simplified constraints.
    // Compute num_vars from remaining constraints.
    let mut max_var = instance.num_vars;
    for c in &constraints {
        for term in &c.terms {
            for lit in &term.lits {
                if lit.var > max_var {
                    max_var = lit.var;
                }
            }
        }
    }

    PreprocessResult::Simplified {
        instance: PbInstance {
            num_vars: max_var,
            num_constraints: constraints.len() as u32,
            constraints,
            objective: instance.objective.clone(),
        },
        fixed_literals: fixed,
    }
}

/// Normalizes a constraint to `>= ` form with all positive coefficients.
///
/// - `Eq` constraints are split into two `Ge` constraints: `sum >= rhs` and `-sum >= -rhs`.
/// - Negative coefficients are eliminated by replacing `a * l` with `-a * ~l`
///   and adjusting the RHS.
///
/// Returns one or two normalized constraints.
#[cfg(test)]
fn normalize_constraint(c: &PbConstraint) -> NormalizationOutcome {
    let mut normalized = Vec::new();
    match normalize_constraint_into(c, &mut normalized) {
        NormalizationOutcome::Constraints(()) => NormalizationOutcome::Constraints(normalized),
        NormalizationOutcome::Unsatisfiable => NormalizationOutcome::Unsatisfiable,
        NormalizationOutcome::OverflowNonTrivial => NormalizationOutcome::OverflowNonTrivial,
    }
}

fn normalize_constraint_into(
    c: &PbConstraint,
    normalized: &mut Vec<PbConstraint>,
) -> NormalizationOutcome<()> {
    // SOUNDNESS: the negative-coefficient literal flip below (replace `a * l`
    // with `|a| * ~l` and subtract `a` from the RHS) is justified by
    // `l = 1 - ~l`, which holds ONLY for a SINGLE-literal (linear) term. For a
    // non-linear product term `a * (l1 AND l2 AND ...)`, flipping every literal
    // would assert `|a| * (~l1 AND ~l2 AND ...)`, but De Morgan gives
    // `~(l1 AND l2) = ~l1 OR ~l2 != ~l1 AND ~l2` -- the WRONG truth function.
    // So if ANY term is non-linear we must NOT run the flip. We instead preserve
    // the constraint's exact truth function (and the all-`>=` invariant the rest
    // of preprocessing relies on) WITHOUT any literal flip. The flip path below
    // then only ever processes LINEAR (single-literal) terms, matching the development proof project's
    // normalization-faithfulness proof scope (`ay_pb_normalization_faithful.lean`)
    // exactly.
    if c.terms.iter().any(|term| term.lits.len() != 1) {
        return normalize_nonlinear_without_flip(c, normalized);
    }

    if matches!(c.rel, PbRel::Ge) {
        if let Some(ge) = normalize_ge_exact(c) {
            normalized.push(ge);
            return NormalizationOutcome::Constraints(());
        }
    }

    if let Some(exact_normalized) = normalize_constraint_exact(c) {
        normalized.extend(exact_normalized);
        return NormalizationOutcome::Constraints(());
    }

    match normalize_constraint_wide(c) {
        NormalizationOutcome::Constraints(wide_normalized) => {
            normalized.extend(wide_normalized);
            NormalizationOutcome::Constraints(())
        }
        NormalizationOutcome::Unsatisfiable => NormalizationOutcome::Unsatisfiable,
        NormalizationOutcome::OverflowNonTrivial => NormalizationOutcome::OverflowNonTrivial,
    }
}

enum NormalizationOutcome<T = Vec<PbConstraint>> {
    Constraints(T),
    Unsatisfiable,
    OverflowNonTrivial,
}

/// Normalizes a constraint that contains at least one non-linear (product) term
/// to `>=` form WITHOUT applying the negative-coefficient literal flip (which is
/// unsound on products -- see [`normalize_constraint_into`]).
///
/// The constraint's exact truth function is preserved verbatim:
/// - A `>=` row is already in normal direction, so it is kept UNCHANGED
///   (`c.clone()`); negative coefficients on product terms are retained as-is.
/// - An `=` row is split into the two equivalent `>=` rows
///   (`sum >= rhs` AND `-sum >= -rhs`) by NEGATING coefficients and the RHS
///   only -- never flipping a literal -- so the all-`>=` downstream invariant is
///   maintained while the meaning is unchanged.
///
/// NO constraint is ever dropped here. Negating a coefficient or the RHS for the
/// `=` split can overflow `i128` (e.g. `i128::MIN`); in that case we report
/// [`NormalizationOutcome::OverflowNonTrivial`], and the top-level
/// [`preprocess_with_stop`] then keeps the ORIGINAL instance unchanged (sound).
fn normalize_nonlinear_without_flip(
    c: &PbConstraint,
    normalized: &mut Vec<PbConstraint>,
) -> NormalizationOutcome<()> {
    match c.rel {
        PbRel::Ge => {
            // Already `>=`; keep the row verbatim (no flip, no drop).
            normalized.push(c.clone());
            NormalizationOutcome::Constraints(())
        }
        PbRel::Eq => {
            // sum = rhs  <=>  sum >= rhs  AND  -sum >= -rhs.
            // Build the `<=` side by negating coefficients/RHS; NO literal flip.
            let mut negated_terms = Vec::with_capacity(c.terms.len());
            for term in &c.terms {
                let Some(neg_coeff) = term.coeff.checked_neg() else {
                    return NormalizationOutcome::OverflowNonTrivial;
                };
                negated_terms.push(PbTerm {
                    coeff: neg_coeff,
                    lits: term.lits.clone(),
                });
            }
            let Some(neg_rhs) = c.rhs.checked_neg() else {
                return NormalizationOutcome::OverflowNonTrivial;
            };
            normalized.push(PbConstraint {
                terms: c.terms.clone(),
                rel: PbRel::Ge,
                rhs: c.rhs,
            });
            normalized.push(PbConstraint {
                terms: negated_terms,
                rel: PbRel::Ge,
                rhs: neg_rhs,
            });
            NormalizationOutcome::Constraints(())
        }
    }
}

fn normalize_constraint_exact(c: &PbConstraint) -> Option<Vec<PbConstraint>> {
    match c.rel {
        PbRel::Ge => Some(vec![normalize_ge_exact(c)?]),
        PbRel::Eq => {
            // sum = rhs  <=>  sum >= rhs AND -sum >= -rhs
            let ge = normalize_ge_exact(c)?;
            let le = normalize_ge_exact(&PbConstraint {
                terms: c
                    .terms
                    .iter()
                    .map(|t| {
                        Some(PbTerm {
                            coeff: t.coeff.checked_neg()?,
                            lits: t.lits.clone(),
                        })
                    })
                    .collect::<Option<Vec<_>>>()?,
                rel: PbRel::Ge,
                rhs: c.rhs.checked_neg()?,
            })?;
            Some(vec![ge, le])
        }
    }
}

/// Normalizes a `>=` constraint so all coefficients are positive.
///
/// For each term with negative coefficient `a * l` (a < 0), replace with
/// `|a| * ~l` and subtract `a` from the RHS:
///   `a * l >= rhs`  becomes `|a| * ~l >= rhs - a`
/// since `l = 1 - ~l`, so `a * l = a * (1 - ~l) = a - a * ~l = -|a| * ~l + a`
/// giving `sum + a - |a| * ~l >= rhs`, i.e. `|a| * ~l <= sum + a - rhs`.
fn normalize_ge_exact(c: &PbConstraint) -> Option<PbConstraint> {
    if ge_constraint_needs_no_exact_normalization(c) {
        return Some(c.clone());
    }

    let mut terms = Vec::with_capacity(c.terms.len());
    let mut rhs = c.rhs;

    for term in &c.terms {
        if term.coeff >= 0 {
            if term.coeff > 0 {
                terms.push(term.clone());
            }
            // Drop zero-coefficient terms.
        } else {
            // a * l -> |a| * ~l, rhs -> rhs - a (= rhs + |a|)
            rhs = rhs.checked_sub(term.coeff)?;
            let negated_lits: Vec<PbLit> = term
                .lits
                .iter()
                .map(|l| PbLit {
                    var: l.var,
                    negated: !l.negated,
                })
                .collect();
            terms.push(PbTerm {
                coeff: term.coeff.checked_neg()?,
                lits: negated_lits,
            });
        }
    }

    // Canonicalize term order. For the dominant case — all-linear rows whose
    // variables are pairwise distinct — sorting the owned terms in place by
    // variable produces EXACTLY `compact_linear_terms`' output (each variable
    // occurs once, so there is nothing to merge) without its per-row map,
    // re-sort, and term reallocation; this halved normalization time on a
    // 6.4M-row instance. Rows with duplicate variables (or any non-linear
    // term) take the exact compaction path unchanged: merging is
    // order-independent here because all coefficients are positive at this
    // point, so compacting the sorted terms equals compacting the originals.
    // One deliberate ORDER-ONLY exception to output identity with the
    // pre-sort code: if compaction bails because a per-(var,polarity)
    // coefficient sum overflows i128 (needs near-2^127 coefficients on a
    // duplicate variable; both old and new code bail on exactly the same
    // rows since overflow of positive sums is order-independent), the row
    // is emitted var-sorted instead of in pre-normalization term order —
    // same term multiset and RHS, semantics unchanged.
    if terms.iter().all(|term| term.lits.len() == 1) {
        terms.sort_unstable_by_key(|term| term.lits[0].var);
        let has_duplicate_var = terms
            .windows(2)
            .any(|pair| pair[0].lits[0].var == pair[1].lits[0].var);
        if has_duplicate_var {
            if let Some((compacted_terms, compacted_rhs)) = compact_linear_terms(&terms, rhs) {
                terms = compacted_terms;
                rhs = compacted_rhs;
            }
        }
    } else if let Some((compacted_terms, compacted_rhs)) = compact_linear_terms(&terms, rhs) {
        terms = compacted_terms;
        rhs = compacted_rhs;
    }

    Some(PbConstraint {
        terms,
        rel: PbRel::Ge,
        rhs,
    })
}

fn ge_constraint_needs_no_exact_normalization(c: &PbConstraint) -> bool {
    if !matches!(c.rel, PbRel::Ge) {
        return false;
    }

    let mut all_terms_linear = true;
    let mut linear_terms_sorted_by_var = true;
    let mut previous_var = None;

    for term in &c.terms {
        if term.coeff <= 0 {
            return false;
        }

        let [lit] = term.lits.as_slice() else {
            all_terms_linear = false;
            continue;
        };

        if previous_var.is_some_and(|previous| previous >= lit.var) {
            linear_terms_sorted_by_var = false;
        }
        previous_var = Some(lit.var);
    }

    // `compact_linear_terms` only rewrites all-linear constraints. Any positive
    // non-linear term means exact normalization would preserve the constraint.
    !all_terms_linear || linear_terms_sorted_by_var
}

fn normalize_constraint_wide(c: &PbConstraint) -> NormalizationOutcome {
    match c.rel {
        PbRel::Ge => normalize_ge_wide(
            c.terms
                .iter()
                .map(|term| (term.coeff, term.lits.as_slice())),
            c.rhs,
        ),
        PbRel::Eq => {
            let ge = normalize_ge_wide(
                c.terms
                    .iter()
                    .map(|term| (term.coeff, term.lits.as_slice())),
                c.rhs,
            );
            // The `<=` side negates every coefficient and the RHS. Negation of
            // `i128::MIN` overflows, so fail closed instead of wrapping.
            let mut negated = Vec::with_capacity(c.terms.len());
            for term in &c.terms {
                let Some(neg_coeff) = term.coeff.checked_neg() else {
                    return NormalizationOutcome::OverflowNonTrivial;
                };
                negated.push((neg_coeff, term.lits.as_slice()));
            }
            let Some(neg_rhs) = c.rhs.checked_neg() else {
                return NormalizationOutcome::OverflowNonTrivial;
            };
            let le = normalize_ge_wide(negated, neg_rhs);
            combine_normalization_outcomes(ge, le)
        }
    }
}

fn combine_normalization_outcomes(
    left: NormalizationOutcome,
    right: NormalizationOutcome,
) -> NormalizationOutcome {
    match (left, right) {
        (NormalizationOutcome::Unsatisfiable, _) | (_, NormalizationOutcome::Unsatisfiable) => {
            NormalizationOutcome::Unsatisfiable
        }
        (NormalizationOutcome::OverflowNonTrivial, _)
        | (_, NormalizationOutcome::OverflowNonTrivial) => NormalizationOutcome::OverflowNonTrivial,
        (
            NormalizationOutcome::Constraints(mut left_constraints),
            NormalizationOutcome::Constraints(right_constraints),
        ) => {
            left_constraints.extend(right_constraints);
            NormalizationOutcome::Constraints(left_constraints)
        }
    }
}

fn normalize_ge_wide<'a, I>(terms: I, rhs: i128) -> NormalizationOutcome
where
    I: IntoIterator<Item = (i128, &'a [PbLit])>,
{
    let mut normalized_terms = Vec::new();
    let mut normalized_rhs = rhs;

    for (coeff, lits) in terms {
        if coeff > 0 {
            normalized_terms.push((coeff, lits.to_vec()));
        } else if coeff < 0 {
            // Normalizing `a*l` (a < 0) into `|a|*~l` subtracts `a` from the
            // RHS and negates the coefficient. Both steps can overflow the
            // i128 accumulator (e.g. when `a == i128::MIN`); detect that and
            // fail closed rather than silently wrapping to a wrong constraint.
            let Some(next_rhs) = normalized_rhs.checked_sub(coeff) else {
                return NormalizationOutcome::OverflowNonTrivial;
            };
            normalized_rhs = next_rhs;
            let Some(neg_coeff) = coeff.checked_neg() else {
                return NormalizationOutcome::OverflowNonTrivial;
            };
            let negated_lits = lits
                .iter()
                .map(|lit| PbLit {
                    var: lit.var,
                    negated: !lit.negated,
                })
                .collect();
            normalized_terms.push((neg_coeff, negated_lits));
        }
    }

    match classify_normalized_trivial_wide(&normalized_terms, normalized_rhs) {
        Some(TrivialClass::Satisfied) => return NormalizationOutcome::Constraints(Vec::new()),
        Some(TrivialClass::Unsatisfiable) => return NormalizationOutcome::Unsatisfiable,
        Some(TrivialClass::NonTrivial) => {}
        None => return NormalizationOutcome::OverflowNonTrivial,
    }

    // `normalized_rhs` is already `i128`; the wide-overflow case was handled by
    // `classify_normalized_trivial_wide` above, so this conversion is total.
    let rhs = normalized_rhs;

    let mut exact_terms = Vec::with_capacity(normalized_terms.len());
    for (coeff, lits) in normalized_terms {
        // `coeff` is already `i128` (wide-overflow handled above); conversion is total.
        exact_terms.push(PbTerm { coeff, lits });
    }

    if let Some((compacted_terms, compacted_rhs)) = compact_linear_terms(&exact_terms, rhs) {
        exact_terms = compacted_terms;
        return NormalizationOutcome::Constraints(vec![PbConstraint {
            terms: exact_terms,
            rel: PbRel::Ge,
            rhs: compacted_rhs,
        }]);
    }

    NormalizationOutcome::Constraints(vec![PbConstraint {
        terms: exact_terms,
        rel: PbRel::Ge,
        rhs,
    }])
}

fn classify_normalized_trivial_wide(
    terms: &[(i128, Vec<PbLit>)],
    rhs: i128,
) -> Option<TrivialClass> {
    if rhs <= 0 {
        return Some(TrivialClass::Satisfied);
    }

    // All coefficients are positive here, so the maximum achievable LHS is the
    // sum of coefficients. If that sum overflows i128 the constraint is not
    // representable; report overflow rather than wrapping into a wrong verdict.
    let mut max_sum = 0i128;
    for (coeff, _) in terms {
        max_sum = max_sum.checked_add(*coeff)?;
    }
    if max_sum < rhs || terms.is_empty() {
        return Some(TrivialClass::Unsatisfiable);
    }

    Some(TrivialClass::NonTrivial)
}

fn compact_linear_terms(terms: &[PbTerm], rhs: i128) -> Option<(Vec<PbTerm>, i128)> {
    if terms.iter().any(|term| term.lits.len() != 1) {
        return None;
    }

    let mut prev_var = None;
    let mut already_canonical = true;
    for term in terms {
        let var = term.lits[0].var;
        if prev_var.is_some_and(|prev| prev >= var) {
            already_canonical = false;
            break;
        }
        prev_var = Some(var);
    }
    if already_canonical {
        return None;
    }

    let mut by_var: HashMap<u32, (i128, i128)> = HashMap::new();
    for term in terms {
        let lit = term.lits[0];
        let entry = by_var.entry(lit.var).or_insert((0, 0));
        // Checked accumulation: the per-variable coefficient sum can overflow
        // i128; bail (treat the row as non-compactable) instead of wrapping. The
        // old `> i128::MAX` guard was a no-op — an i128 is never above i128::MAX.
        let target = if lit.negated {
            &mut entry.1
        } else {
            &mut entry.0
        };
        *target = target.checked_add(term.coeff)?;
    }

    let mut compacted_rhs = rhs;
    let mut compacted_terms = Vec::with_capacity(by_var.len() * 2);
    let mut vars: Vec<u32> = by_var.keys().copied().collect();
    vars.sort_unstable();

    for var in vars {
        let (positive, negative) = by_var[&var];
        let shared = positive.min(negative);
        compacted_rhs -= shared;

        let positive_remainder = positive - shared;
        if positive_remainder > 0 {
            compacted_terms.push(PbTerm {
                coeff: positive_remainder,
                lits: vec![PbLit {
                    var,
                    negated: false,
                }],
            });
        }

        let negative_remainder = negative - shared;
        if negative_remainder > 0 {
            compacted_terms.push(PbTerm {
                coeff: negative_remainder,
                lits: vec![PbLit { var, negated: true }],
            });
        }
    }

    let compacted_rhs = i128::try_from(compacted_rhs).ok()?;

    Some((compacted_terms, compacted_rhs))
}

/// Classification of a constraint as trivially satisfiable, unsatisfiable, or non-trivial.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum TrivialClass {
    Satisfied,
    Unsatisfiable,
    NonTrivial,
}

/// Classifies whether a normalized `>= ` constraint is trivially SAT/UNSAT.
///
/// - Trivially satisfied: `rhs <= 0` (empty sum or all-zero always satisfies `>= 0`).
/// - Trivially unsatisfiable: max possible sum of coefficients < rhs.
fn classify_trivial(c: &PbConstraint) -> TrivialClass {
    // Soundness with NEGATIVE coefficients (preserved non-linear product rows can
    // carry them -- the literal flip that would make every coefficient
    // non-negative is unsound on products, see `normalize_constraint_into`):
    // `sum a_i * term_i >= rhs` is
    //   * trivially SATISFIED when even the MINIMUM achievable LHS is `>= rhs`, and
    //   * trivially UNSAT     when even the MAXIMUM achievable LHS is `<  rhs`.
    // Each term contributes its coefficient (when "on") or 0 (when "off"), so a
    // sound lower bound on the LHS is the sum of the NEGATIVE coefficients and a
    // sound upper bound is the sum of the POSITIVE coefficients.
    //
    // For the all-non-negative rows the normalizer produces on LINEAR constraints
    // the lower bound is 0, so the satisfied test reduces to the historical
    // `rhs <= 0` and the unsat test to the historical `max_sum < rhs`
    // (byte-identical behavior on that path).
    let mut min_lhs = 0i128;
    let mut min_overflow = false;
    let mut max_lhs = 0i128;
    let mut max_overflow = false;
    for term in &c.terms {
        if term.coeff < 0 {
            match min_lhs.checked_add(term.coeff) {
                Some(sum) => min_lhs = sum,
                None => min_overflow = true,
            }
        } else {
            match max_lhs.checked_add(term.coeff) {
                Some(sum) => max_lhs = sum,
                None => max_overflow = true,
            }
        }
    }

    // Trivially satisfied: the minimum LHS already meets `rhs`. If the lower bound
    // overflowed `i128` (only reachable with negative coefficients) we cannot
    // prove it, so we fall through rather than wrongly DROP the row.
    if !min_overflow && c.rhs <= min_lhs {
        return TrivialClass::Satisfied;
    }

    // Trivially unsatisfiable: even the maximum LHS cannot reach `rhs`. On
    // overflow of the upper bound we fail open to NonTrivial (keeping the row),
    // matching the historical checked-add bailout.
    if !max_overflow && max_lhs < c.rhs {
        return TrivialClass::Unsatisfiable;
    }

    TrivialClass::NonTrivial
}

/// Caps each coefficient at the RHS value (saturation / coefficient tightening).
///
/// For `sum(a_i * l_i) >= rhs`, if `a_i > rhs`, replace `a_i` with `rhs`.
/// This is sound because the literal can contribute at most `rhs` to satisfying
/// the constraint — anything beyond that is wasted slack.
///
/// Reference: Elffers & Nordstrom, SAT 2018 (Section 3.1).
fn tighten_coefficients(c: &mut PbConstraint) {
    if c.rhs <= 0 {
        return;
    }
    // Saturation (`a_i > rhs -> a_i = rhs`) is only sound when EVERY coefficient
    // is non-negative: with a negative coefficient present, capping a positive
    // one can change the set of satisfying assignments (the row could be
    // satisfied via the negative term contributing less than the capped positive
    // term, an assignment the cap would wrongly exclude). Preserved non-linear
    // product rows may carry negative coefficients, so skip tightening them.
    // Linear rows are always all-non-negative after normalization, so this guard
    // never triggers on that path (behavior byte-identical).
    if c.terms.iter().any(|term| term.coeff < 0) {
        return;
    }
    for term in &mut c.terms {
        if term.coeff > c.rhs {
            term.coeff = c.rhs;
        }
    }
}

/// Divides all coefficients and the RHS by the GCD of the coefficients.
///
/// For `sum(a_i * l_i) >= rhs`, if `g = gcd(a_1, ..., a_n) > 1`, transform to
/// `sum((a_i / g) * l_i) >= ceil(rhs / g)`.
///
/// This is sound because the LHS is always a multiple of `g`, so rounding up
/// the RHS to the next multiple of `g` does not change satisfiability.
///
/// Reference: Elffers & Nordstrom, SAT 2018 (Section 3.2).
fn gcd_strengthen(c: &mut PbConstraint) {
    let Some(g_signed) = gcd_strengthening_divisor(&c.terms) else {
        return;
    };
    for term in &mut c.terms {
        term.coeff /= g_signed;
    }
    // ceiling division: ceil(rhs / g)
    c.rhs = ceiling_div(c.rhs, g_signed);
}

/// Single-residue GCD division: if every coefficient EXCEPT ONE shares a
/// divisor `g > 1`, the row can be divided by `g` after rounding the odd
/// coefficient to its exact case-split equivalent.
///
/// For `a_j*l_j + R >= d` where every coefficient in `R` is a multiple of `g`:
/// - `l_j = 0`: `R >= d` iff `R/g >= ceil(d/g)` (R is a multiple of g).
/// - `l_j = 1`: `R >= d - a_j` iff `R/g >= ceil((d - a_j)/g)`.
///
/// Setting `d' = ceil(d/g)` and `a_j' = ceil(d/g) - ceil((d - a_j)/g)`, the row
/// `a_j'*l_j + R/g >= d'` matches BOTH cases exactly, so the rewrite preserves
/// the row's solution set verbatim (an equivalence, not just an implication).
/// When `a_j' = 0` the literal drops out entirely.
///
/// Only linear rows with all-positive coefficients and positive degree are
/// eligible (the normalizer's output); preserved non-linear rows are skipped
/// (fail closed). Coefficient tightening runs before this pass each round, so
/// `a_j <= d` and hence `0 <= a_j' <= d'`.
fn gcd_residue_strengthen(c: &mut PbConstraint, stats: &mut PreprocessStats) {
    // Each successful application divides every coefficient but one by g >= 2
    // (a strict decrease of the coefficient sum), so the fixpoint terminates in
    // well under 128 iterations for i128 coefficients; the cap is a backstop.
    let mut rewritten = false;
    for _ in 0..200 {
        if !gcd_residue_strengthen_once(c) {
            break;
        }
        rewritten = true;
        // The rewritten row may expose a plain common divisor (e.g. the rounded
        // residue coefficient can share a factor with the divided rest).
        gcd_strengthen(c);
    }
    // Count ROWS rewritten (per the `gcd_residue_strengthened` doc), not
    // individual fixpoint applications: a row needing several residue+GCD
    // iterations still counts once per sweep.
    if rewritten {
        stats.gcd_residue_strengthened += 1;
    }
}

/// One application of the single-residue GCD division. Returns whether the row
/// was rewritten. See [`gcd_residue_strengthen`] for the equivalence proof.
fn gcd_residue_strengthen_once(c: &mut PbConstraint) -> bool {
    if c.rhs <= 0 || c.terms.len() < 2 {
        return false;
    }
    for term in &c.terms {
        if term.lits.len() != 1 || term.coeff <= 0 {
            return false;
        }
    }

    // Prefix/suffix GCDs to find the divisor of "all but one" coefficient.
    let n = c.terms.len();
    let mut prefix = vec![0u128; n + 1];
    for (i, term) in c.terms.iter().enumerate() {
        prefix[i + 1] = gcd_u128(prefix[i], term.coeff.unsigned_abs());
    }
    if prefix[n] > 1 {
        // Plain GCD strengthening applies (handled by `gcd_strengthen`).
        return false;
    }
    let mut suffix = vec![0u128; n + 1];
    for i in (0..n).rev() {
        suffix[i] = gcd_u128(suffix[i + 1], c.terms[i].coeff.unsigned_abs());
    }

    let mut best: Option<(usize, i128)> = None;
    for j in 0..n {
        let g = gcd_u128(prefix[j], suffix[j + 1]);
        if g > 1 {
            let Ok(g) = i128::try_from(g) else { continue };
            if best.is_none_or(|(_, best_g)| g > best_g) {
                best = Some((j, g));
            }
        }
    }
    let Some((j, g)) = best else {
        return false;
    };

    let d = c.rhs;
    let a_j = c.terms[j].coeff;
    // `ceiling_div(d, g)` computes `(d + g - 1) / g` for non-negative `d`;
    // guard the intermediate sum against i128 overflow (fail closed: keep the
    // row unchanged).
    if d > i128::MAX - g {
        return false;
    }
    let new_d = ceiling_div(d, g);
    // Tightening runs before this pass each round, so `a_j <= d` and the
    // residue requirement `d - a_j` is non-negative; `ceiling_div` would also
    // handle a negative value exactly, so the algebra stays sound either way.
    let new_aj = new_d - ceiling_div(d - a_j, g);
    debug_assert!(new_aj >= 0, "saturated rows keep a_j <= d");

    // TRAJECTORY GUARD (bell3a regression, 2026-07-12): when even the divided
    // row keeps a huge coefficient spread (max post-division coefficient above
    // the encoding layer's big-coefficient adder cutoff), the rewrite buys no
    // encoding-tier improvement — the row stays adder-routed either way — but
    // it perturbs coefficient structure that search exploits (measured: bell3a
    // ~2% incumbent quality, deterministic 2/2, power-of-2-heavy rows with one
    // odd residue). Skipping is sound: the rewrite is an equivalence, so not
    // applying it keeps the identical solution set.
    const RESIDUE_DIVISION_MAX_POST_COEFF: i128 = 10_000;
    let post_max = c
        .terms
        .iter()
        .enumerate()
        .map(|(i, term)| if i == j { new_aj } else { term.coeff / g })
        .max()
        .unwrap_or(0);
    if post_max > RESIDUE_DIVISION_MAX_POST_COEFF {
        return false;
    }

    for (i, term) in c.terms.iter_mut().enumerate() {
        if i == j {
            term.coeff = new_aj;
        } else {
            term.coeff /= g;
        }
    }
    c.rhs = new_d;
    if new_aj == 0 {
        c.terms.remove(j);
    }
    true
}

fn gcd_strengthening_divisor(terms: &[PbTerm]) -> Option<i128> {
    let mut g = 0u128;
    for term in terms {
        let coeff = term.coeff.unsigned_abs();
        if coeff == 0 {
            continue;
        }
        if coeff == 1 {
            return None;
        }

        g = if g == 0 { coeff } else { gcd_u128(g, coeff) };
        if g <= 1 {
            return None;
        }
    }

    i128::try_from(g).ok().filter(|&g| g > 1)
}

/// Identifies and fixes literals forced by individual constraints.
///
/// A literal is forced true if removing it from the constraint makes it
/// unsatisfiable. Specifically, for `sum(a_i * l_i) >= rhs`, literal `l_j` is
/// forced true if `sum(a_i for i != j) < rhs`, meaning all other terms cannot
/// satisfy the constraint alone.
///
/// Also handles single-term constraints: `a * l >= rhs` with `a >= rhs > 0`
/// forces `l = true`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum FixResult {
    Ok { changed: bool },
    Conflict,
    Interrupted,
}

#[cfg(test)]
fn fix_literals(constraints: &mut Vec<PbConstraint>, fixed: &mut HashMap<u32, bool>) -> FixResult {
    let mut never_stop = || false;
    fix_literals_interruptible(constraints, fixed, &mut never_stop)
}

fn fix_literals_interruptible<F>(
    constraints: &mut Vec<PbConstraint>,
    fixed: &mut HashMap<u32, bool>,
    should_stop: &mut F,
) -> FixResult
where
    F: FnMut() -> bool,
{
    let mut changed = true;
    let mut any_change = false;
    while changed {
        if should_stop() {
            return FixResult::Interrupted;
        }
        changed = false;
        for (constraint_index, c) in constraints.iter().enumerate() {
            if constraint_index % 32 == 0 && should_stop() {
                return FixResult::Interrupted;
            }
            if c.rhs <= 0 {
                continue;
            }

            if linear_row_cannot_force_fast(c) {
                continue;
            }

            // Only handle linear constraints (single-literal terms).
            if c.terms.iter().any(|t| t.lits.len() != 1) {
                continue;
            }

            let total = c
                .terms
                .iter()
                .try_fold(0i128, |sum, term| sum.checked_add(term.coeff))
                .map(EitherSum::I64)
                .unwrap_or_else(|| EitherSum::I128(c.terms.iter().map(|term| term.coeff).sum()));

            for (term_index, term) in c.terms.iter().enumerate() {
                if term_index % 32 == 0 && should_stop() {
                    return FixResult::Interrupted;
                }
                let others_too_small = match total {
                    EitherSum::I64(total) => total - term.coeff < c.rhs,
                    EitherSum::I128(total) => total - term.coeff < c.rhs,
                };
                if others_too_small && term.coeff > 0 {
                    // This literal is forced true.
                    let lit = &term.lits[0];
                    let required_value = !lit.negated;
                    match fixed.get(&lit.var) {
                        Some(&existing) if existing != required_value => {
                            return FixResult::Conflict;
                        }
                        Some(_) => {} // Already fixed to the correct value.
                        None => {
                            fixed.insert(lit.var, required_value);
                            changed = true;
                            any_change = true;
                        }
                    }
                }
            }
        }

        // Propagate current fixings into constraints.
        if changed {
            match propagate_fixed_interruptible(constraints, fixed, should_stop) {
                PropagateResult::Ok => {}
                PropagateResult::Conflict => return FixResult::Conflict,
                PropagateResult::Interrupted => return FixResult::Interrupted,
            }
        }
    }
    FixResult::Ok {
        changed: any_change,
    }
}

fn linear_row_cannot_force_fast(c: &PbConstraint) -> bool {
    if c.terms.len() <= 1 {
        return false;
    }

    if unit_linear_cardinality_row_cannot_force(c) || positive_linear_row_has_nonforcing_slack(c) {
        return true;
    }

    false
}

fn unit_linear_cardinality_row_cannot_force(c: &PbConstraint) -> bool {
    let Ok(rhs) = usize::try_from(c.rhs) else {
        return false;
    };
    if rhs > c.terms.len() - 1 {
        return false;
    }

    c.terms
        .iter()
        .all(|term| term.coeff == 1 && term.lits.len() == 1)
}

fn positive_linear_row_has_nonforcing_slack(c: &PbConstraint) -> bool {
    let mut largest = 0i128;
    for term in &c.terms {
        if term.coeff <= 0 || term.lits.len() != 1 {
            return false;
        }
        largest = largest.max(term.coeff);
    }

    // The row "has nonforcing slack" iff the sum of all coefficients EXCEPT the
    // single largest still meets `rhs` (then even forcing the largest literal
    // false leaves the row satisfiable, so no literal is forced). Compute that
    // residual sum DIRECTLY: the full total can exceed i128 even when the residual
    // does not, so summing the whole row and subtracting would overflow. If the
    // residual itself overflows i128 it trivially exceeds any valid i128 `rhs`.
    let mut rest = 0i128;
    let mut dropped_largest = false;
    for term in &c.terms {
        if !dropped_largest && term.coeff == largest {
            dropped_largest = true;
            continue;
        }
        match rest.checked_add(term.coeff) {
            Some(v) => rest = v,
            None => return true,
        }
    }

    rest >= c.rhs
}

/// Result of propagating fixed literals into constraints.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum PropagateResult {
    Ok,
    Conflict,
    Interrupted,
}

/// Outcome of the pure-literal elimination pass.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum PureResult {
    Ok { found_fixings: bool },
    Interrupted,
}

/// Pure/monotone literal elimination over rows and objective JOINTLY.
///
/// A variable `v` whose complement polarity never appears in any (normalized,
/// all-linear, all-positive-coefficient `>=`) row can be fixed to the polarity
/// that appears, provided the objective does not get worse. Variables that
/// appear in the objective only (no rows) are fixed to their objective-minimal
/// polarity.
///
/// # Soundness (equisatisfiability + optimum preservation)
///
/// This is a CHOICE (self-reduction), not an entailment: it may shrink the
/// solution set, but never to empty, and never past the optimum:
///
/// * **Feasibility**: take any model `σ`. Flipping `v` to the fixed polarity
///   only INCREASES the LHS of every row containing `v` (the fixed polarity is
///   the only one occurring, with a positive coefficient) and leaves all other
///   rows untouched, so the flipped assignment is still a model. Hence the
///   reduced instance is satisfiable iff the original is.
/// * **Objective preservation** (minimization): the fix is only applied when
///   the objective contribution of the fixed polarity is `<=` that of the
///   opposite polarity (computed per-variable over the LINEAR objective
///   terms), so the flip above does not increase the objective value; some
///   optimal model maps to an optimal model with `v` fixed, and the optimum
///   value is unchanged.
/// * **Joint fixes**: multiple pure fixes computed against the same row set
///   compose: each flip weakens rows monotonically and objective effects are
///   additive over a LINEAR objective, so applying all fixes simultaneously
///   preserves feasibility and the optimum.
/// * **Downstream consumers**: every later row of the preprocessed instance is
///   still implied by the ORIGINAL constraint conjunction (substituting the
///   monotone polarity only weakens a row: `a_v * v + R >= d` implies
///   `R >= d - a_v` for every assignment), so consumers that use the reduced
///   rows for LOWER bounds (e.g. the OLL LP floor, which discards
///   `fixed_literals`) remain sound.
///
/// # Fail-closed gates
///
/// The pass is skipped entirely when any row contains a non-linear (product)
/// term or a non-positive coefficient (only preserved non-linear rows can
/// carry those), or when the objective contains a non-linear term: monotone
/// reasoning over products and the additive-objective argument are only
/// established for the linear fragment. Per-variable, an overflowing objective
/// contribution sum also disqualifies that variable.
fn fix_pure_literals_interruptible<F>(
    constraints: &[PbConstraint],
    objective: Option<&PbObjective>,
    choice_fixings: ChoiceFixings,
    fixed: &mut HashMap<u32, bool>,
    stats: &mut PreprocessStats,
    should_stop: &mut F,
) -> PureResult
where
    F: FnMut() -> bool,
{
    if choice_fixings == ChoiceFixings::Forbid {
        return PureResult::Ok {
            found_fixings: false,
        };
    }

    // Fail-closed structural gates (see doc comment).
    for (index, c) in constraints.iter().enumerate() {
        if index % 64 == 0 && should_stop() {
            return PureResult::Interrupted;
        }
        for term in &c.terms {
            if term.lits.len() != 1 || term.coeff <= 0 {
                return PureResult::Ok {
                    found_fixings: false,
                };
            }
        }
    }
    if objective.is_some_and(|objective| objective.terms.iter().any(|term| term.lits.len() != 1)) {
        return PureResult::Ok {
            found_fixings: false,
        };
    }

    // Occurrence polarity per variable across all rows.
    #[derive(Default, Clone, Copy)]
    struct VarOcc {
        seen_pos: bool,
        seen_neg: bool,
    }
    let mut occ: HashMap<u32, VarOcc> = HashMap::new();
    for (index, c) in constraints.iter().enumerate() {
        if index % 64 == 0 && should_stop() {
            return PureResult::Interrupted;
        }
        for term in &c.terms {
            let lit = term.lits[0];
            let entry = occ.entry(lit.var).or_default();
            if lit.negated {
                entry.seen_neg = true;
            } else {
                entry.seen_pos = true;
            }
        }
    }

    // Objective contribution per polarity. `None` marks an overflow-poisoned
    // variable that must not be fixed by this pass.
    let mut obj_contrib: HashMap<u32, Option<(i128, i128)>> = HashMap::new();
    if let Some(objective) = objective {
        for (index, term) in objective.terms.iter().enumerate() {
            if index % 64 == 0 && should_stop() {
                return PureResult::Interrupted;
            }
            let lit = term.lits[0];
            let entry = obj_contrib.entry(lit.var).or_insert(Some((0, 0)));
            *entry = entry.and_then(|(when_true, when_false)| {
                if lit.negated {
                    Some((when_true, when_false.checked_add(term.coeff)?))
                } else {
                    Some((when_true.checked_add(term.coeff)?, when_false))
                }
            });
        }
    }

    let mut found_fixings = false;
    let mut candidates: Vec<u32> = occ.keys().copied().collect();
    for var in obj_contrib.keys() {
        if !occ.contains_key(var) {
            candidates.push(*var);
        }
    }

    for (index, var) in candidates.into_iter().enumerate() {
        if index % 64 == 0 && should_stop() {
            return PureResult::Interrupted;
        }
        if fixed.contains_key(&var) {
            continue;
        }
        let var_occ = occ.get(&var).copied().unwrap_or_default();
        let (when_true, when_false) = match obj_contrib.get(&var) {
            Some(Some(contrib)) => *contrib,
            Some(None) => continue, // overflow-poisoned
            None => (0, 0),
        };
        let value = match (var_occ.seen_pos, var_occ.seen_neg) {
            (true, true) => continue, // both polarities constrained: not pure
            (true, false) => {
                if when_true > when_false {
                    continue; // fixing true would (possibly) worsen the optimum
                }
                true
            }
            (false, true) => {
                if when_false > when_true {
                    continue;
                }
                false
            }
            // Objective-only variable: pick the objective-minimal polarity.
            (false, false) => when_true <= when_false,
        };
        fixed.insert(var, value);
        stats.pure_fixed += 1;
        found_fixings = true;
    }

    PureResult::Ok { found_fixings }
}

#[derive(Debug, Clone, Copy)]
enum EitherSum {
    I64(i128),
    I128(i128),
}

/// Dense fixed-variable lookup built once per propagation pass so the per-term
/// hit test is O(1) instead of a tree lookup (the tree lookups alone dominated
/// this pass on multi-million-row instances).
struct FixedLookup {
    /// `table[var]`: 0 = fixed false, 1 = fixed true, 2 = not fixed.
    table: Vec<u8>,
}

impl FixedLookup {
    fn new(fixed: &HashMap<u32, bool>) -> Self {
        let max_fixed_var = fixed.last_key_value().map_or(0, |(&var, _)| var);
        let mut table = vec![2u8; max_fixed_var as usize + 1];
        for (&var, &value) in fixed {
            table[var as usize] = u8::from(value);
        }
        Self { table }
    }

    #[inline]
    fn get(&self, var: u32) -> Option<bool> {
        match self.table.get(var as usize) {
            Some(0) => Some(false),
            Some(1) => Some(true),
            _ => None,
        }
    }
}

fn propagate_fixed_interruptible<F>(
    constraints: &mut Vec<PbConstraint>,
    fixed: &HashMap<u32, bool>,
    should_stop: &mut F,
) -> PropagateResult
where
    F: FnMut() -> bool,
{
    if fixed.is_empty() {
        return PropagateResult::Ok;
    }

    let lookup = FixedLookup::new(fixed);

    // Phase A (read-only): find the rows that actually mention a fixed
    // variable in a LINEAR term. Fixed variables inside non-linear product
    // terms are intentionally not substituted, exactly as before. On huge
    // instances (millions of rows, few fixings) the old rebuild-everything
    // loop cloned every untouched row's nested term/literal vectors, which
    // dominated this pass; untouched rows are now left in place, uncloned.
    let mut touched: Vec<usize> = Vec::new();
    for (constraint_index, c) in constraints.iter().enumerate() {
        if constraint_index % 32 == 0 && should_stop() {
            return PropagateResult::Interrupted;
        }
        if c.terms
            .iter()
            .any(|term| matches!(term.lits.as_slice(), [lit] if lookup.get(lit.var).is_some()))
        {
            touched.push(constraint_index);
        }
    }

    if touched.is_empty() {
        return PropagateResult::Ok;
    }

    // Phase B (read-only): build the replacement for every touched row.
    // `None` means the row is dropped (satisfied). A conflict aborts before
    // any mutation, and interruption likewise leaves `constraints` untouched
    // (pinned by test_propagate_fixed_interruptible_leaves_constraints_unchanged).
    let mut replacements: Vec<Option<PbConstraint>> = Vec::with_capacity(touched.len());
    for (touched_pos, &constraint_index) in touched.iter().enumerate() {
        if touched_pos % 32 == 0 && should_stop() {
            return PropagateResult::Interrupted;
        }
        let c = &constraints[constraint_index];
        let mut new_terms: Vec<PbTerm> = Vec::with_capacity(c.terms.len().saturating_sub(1));
        let mut rhs = c.rhs;
        let mut wide_rhs = None;

        for (term_index, term) in c.terms.iter().enumerate() {
            if term_index % 64 == 0 && should_stop() {
                return PropagateResult::Interrupted;
            }
            // Only handle linear terms (single literal).
            let [lit] = term.lits.as_slice() else {
                new_terms.push(term.clone());
                continue;
            };

            if let Some(val) = lookup.get(lit.var) {
                let lit_true = val != lit.negated;
                if lit_true {
                    // Literal is true: subtract coefficient from RHS.
                    if let Some(wide_rhs) = wide_rhs.as_mut() {
                        *wide_rhs -= term.coeff;
                    } else if let Some(updated_rhs) = rhs.checked_sub(term.coeff) {
                        rhs = updated_rhs;
                    } else {
                        wide_rhs = Some(rhs - term.coeff);
                    }
                }
                // else: literal is false, term contributes 0 — just drop it.
            } else {
                new_terms.push(term.clone());
            }
        }

        if let Some(wide_rhs) = wide_rhs {
            if wide_rhs <= 0 {
                replacements.push(None);
                continue;
            }
            rhs = i128::try_from(wide_rhs)
                .expect("propagating fixed literals only decreases rhs from an i128 bound");
        }

        let simplified = PbConstraint {
            terms: new_terms,
            rel: PbRel::Ge,
            rhs,
        };

        match classify_trivial(&simplified) {
            TrivialClass::Satisfied => replacements.push(None),
            TrivialClass::Unsatisfiable => return PropagateResult::Conflict,
            TrivialClass::NonTrivial => replacements.push(Some(simplified)),
        }
    }

    // Phase C (apply): overwrite/drop the touched rows in place, preserving
    // order. Pure moves with no allocation or polling; untouched rows are
    // never cloned.
    let mut touched_iter = touched.iter().zip(replacements).peekable();
    let mut index = 0usize;
    constraints.retain_mut(|row| {
        let keep = match touched_iter.peek_mut() {
            Some(&mut (&touched_index, ref mut replacement)) if touched_index == index => {
                let keep = match replacement.take() {
                    Some(new_row) => {
                        *row = new_row;
                        true
                    }
                    None => false,
                };
                touched_iter.next();
                keep
            }
            _ => true,
        };
        index += 1;
        keep
    });
    PropagateResult::Ok
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
enum CanonicalLitsKey {
    Single((u32, bool)),
    Product(Vec<(u32, bool)>),
}

type CanonicalTermKey = (i128, CanonicalLitsKey);
type ConstraintShapeKey = Vec<CanonicalTermKey>;
type CardinalitySupportKey = Vec<(u32, bool)>;

#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
enum SubsumptionShapeKey {
    Cardinality(CardinalitySupportKey),
    General(ConstraintShapeKey),
}

impl SubsumptionShapeKey {
    #[cfg(test)]
    fn cardinality_support(&self) -> Option<&[(u32, bool)]> {
        match self {
            Self::Cardinality(support) => Some(support.as_slice()),
            Self::General(_) => None,
        }
    }
}

#[derive(Debug, Clone, Copy)]
struct CardinalityEntry {
    retained_index: usize,
    rhs: i128,
    support_len: usize,
}

/// A linear row's sorted support with coefficients, used for generalized
/// (weighted) row-dominance checks: `[( (var, negated), coeff ), ...]` sorted
/// by `(var, negated)` with all coefficients strictly positive.
type DominanceSupport = Vec<((u32, bool), i128)>;

/// Extracts the dominance support of a normalized row, or `None` when the row
/// does not qualify for the weighted-dominance rule.
///
/// Qualifying rows are exactly the LINEAR rows the normalizer produces:
/// every term is a single literal with a strictly positive coefficient and the
/// degree (rhs) is strictly positive. Non-linear (product) rows and preserved
/// negative-coefficient rows are excluded (fail closed: exclusion only forgoes
/// an optional deletion). Rows with a duplicate `(var, negated)` key are also
/// excluded so the sorted-merge subset walk below stays well-defined.
fn dominance_support(constraint: &PbConstraint) -> Option<DominanceSupport> {
    if constraint.rhs <= 0 {
        return None;
    }
    let mut support: DominanceSupport = Vec::with_capacity(constraint.terms.len());
    for term in &constraint.terms {
        let [lit] = term.lits.as_slice() else {
            return None;
        };
        if term.coeff <= 0 {
            return None;
        }
        support.push(((lit.var, lit.negated), term.coeff));
    }
    support.sort_unstable_by_key(|(lit, _)| *lit);
    if support.windows(2).any(|pair| pair[0].0 == pair[1].0) {
        return None;
    }
    Some(support)
}

/// Non-allocating over-approximation of "this row would get a WEIGHTED
/// (non-unit-coefficient) [`dominance_support`]": positive degree, every term a
/// single positive-coefficient literal, and at least one coefficient != 1.
///
/// Over-approximates because rows with a duplicate `(var, negated)` key are
/// counted here but rejected by `dominance_support`. That is safe for the
/// weighted-participation cap: over-counting can only make the pass skip
/// weighted rows earlier, and skipping is always sound (deletions are
/// optional). Rows for which `dominance_support` returns a weighted support
/// are ALWAYS counted (the predicate checks the same term conditions).
fn is_weighted_dominance_candidate(constraint: &PbConstraint) -> bool {
    if constraint.rhs <= 0 {
        return false;
    }
    let mut any_non_unit = false;
    for term in &constraint.terms {
        if term.lits.len() != 1 || term.coeff <= 0 {
            return false;
        }
        if term.coeff != 1 {
            any_non_unit = true;
        }
    }
    any_non_unit
}

/// Returns whether row A (support `small`, degree `d`) IMPLIES row B (support
/// `large`, degree `e`), where both are normalized linear rows
/// `sum(coeff * lit) >= degree` with positive coefficients and degrees.
///
/// # Soundness (solution-set preservation of deleting B)
///
/// Sufficient condition with a single rational multiplier `λ = e/d > 0`:
/// if the literal set of A is a subset of B's (identical `(var, negated)`
/// keys) and for every shared literal `b_i * d >= a_i * e` (i.e. `b_i >= λ a_i`),
/// then from A: `Σ_S a_i l_i >= d`, multiply by `λ`: `Σ_S λ a_i l_i >= e`, and
/// since `b_i >= λ a_i` termwise and B's extra literals contribute `>= 0`
/// (positive coefficients, 0/1 literals): `Σ_T b_i l_i >= Σ_S b_i l_i >= e`.
/// So every assignment satisfying A satisfies B, and deleting B leaves the
/// instance's solution set (and hence any objective optimum) unchanged as long
/// as A is retained (or itself deleted only under a surviving dominator, which
/// the caller's processing order guarantees — see
/// `mark_dominated_rows_interruptible`).
///
/// The products are computed with checked i128 multiplication; if any product
/// overflows we fall back to the uniform `λ = 1` test (`b_i >= a_i` for all i
/// and `e <= d`), which is the same argument with multiplier 1. Mixing the two
/// multipliers across terms would be UNSOUND, so the fallback re-checks every
/// term under `λ = 1`.
fn weighted_row_implies(
    small: &DominanceSupport,
    d: i128,
    large: &DominanceSupport,
    e: i128,
) -> bool {
    debug_assert!(d > 0 && e > 0);
    // Both certificates are tracked ACROSS ALL matched terms from the start:
    // a row is only implied when one single multiplier works for every term
    // (mixing λ = e/d on some terms with λ = 1 on others would be unsound).
    let mut scaled_all = true; // λ = e/d: b_i * d >= a_i * e for every matched i
    let mut unit_all = e <= d; // λ = 1:  b_i >= a_i for every matched i, e <= d
    let mut i = 0usize;
    let mut j = 0usize;
    while i < small.len() && j < large.len() {
        use std::cmp::Ordering;
        match small[i].0.cmp(&large[j].0) {
            Ordering::Less => return false, // literal of A missing from B
            Ordering::Greater => j += 1,
            Ordering::Equal => {
                if scaled_all {
                    match (large[j].1.checked_mul(d), small[i].1.checked_mul(e)) {
                        (Some(bd), Some(ae)) => scaled_all = bd >= ae,
                        // Overflow: cannot certify this term with λ = e/d.
                        _ => scaled_all = false,
                    }
                }
                if unit_all {
                    unit_all = large[j].1 >= small[i].1;
                }
                if !scaled_all && !unit_all {
                    return false;
                }
                i += 1;
                j += 1;
            }
        }
    }
    i == small.len() && (scaled_all || unit_all)
}

fn canonical_constraint_shape(constraint: &PbConstraint) -> ConstraintShapeKey {
    if let Some(key) = canonical_sorted_linear_constraint_shape(constraint) {
        return key;
    }

    let mut key: ConstraintShapeKey = constraint
        .terms
        .iter()
        .map(|term| (term.coeff, canonical_lits_key_for_general_shape(&term.lits)))
        .collect();
    key.sort_unstable_by(|left, right| left.1.cmp(&right.1).then(left.0.cmp(&right.0)));
    key
}

fn canonical_subsumption_shape(constraint: &PbConstraint) -> SubsumptionShapeKey {
    if let Some(support) = canonical_cardinality_support(constraint) {
        return SubsumptionShapeKey::Cardinality(support);
    }

    SubsumptionShapeKey::General(canonical_constraint_shape(constraint))
}

fn canonical_lits_key_for_general_shape(lits: &[PbLit]) -> CanonicalLitsKey {
    if let [lit] = lits {
        return CanonicalLitsKey::Single((lit.var, lit.negated));
    }

    let mut lits: Vec<(u32, bool)> = lits.iter().map(|lit| (lit.var, lit.negated)).collect();
    lits.sort_unstable();
    CanonicalLitsKey::Product(lits)
}

fn canonical_sorted_linear_constraint_shape(
    constraint: &PbConstraint,
) -> Option<ConstraintShapeKey> {
    let mut key = Vec::with_capacity(constraint.terms.len());
    let mut previous_lit = None;

    for term in &constraint.terms {
        let [lit] = term.lits.as_slice() else {
            return None;
        };
        let lit_key = (lit.var, lit.negated);
        if previous_lit.is_some_and(|previous| previous >= lit_key) {
            return None;
        }
        previous_lit = Some(lit_key);
        key.push((term.coeff, CanonicalLitsKey::Single(lit_key)));
    }

    Some(key)
}

fn canonical_cardinality_support(constraint: &PbConstraint) -> Option<CardinalitySupportKey> {
    let mut support = Vec::with_capacity(constraint.terms.len());
    let mut prev_var = None;
    let mut already_sorted = true;
    for term in &constraint.terms {
        if term.coeff != 1 || term.lits.len() != 1 {
            return None;
        }
        let lit = term.lits[0];
        if prev_var.is_some_and(|prev| prev >= lit.var) {
            already_sorted = false;
        }
        prev_var = Some(lit.var);
        support.push((lit.var, lit.negated));
    }
    if !already_sorted {
        support.sort_unstable();
    }
    Some(support)
}

#[cfg(test)]
fn canonical_cardinality_shape_support(key: &ConstraintShapeKey) -> Option<&ConstraintShapeKey> {
    key.iter()
        .all(|(coeff, lits)| *coeff == 1 && matches!(lits, CanonicalLitsKey::Single(_)))
        .then_some(key)
}

#[cfg(test)]
fn cardinality_shape_lit(term: &CanonicalTermKey) -> (u32, bool) {
    match &term.1 {
        CanonicalLitsKey::Single(lit) => *lit,
        CanonicalLitsKey::Product(_) => {
            unreachable!("cardinality shape support must contain only single literals")
        }
    }
}

#[cfg(test)]
fn is_sorted_subset<T: Ord>(small: &[T], large: &[T]) -> bool {
    if small.len() > large.len() {
        return false;
    }

    let mut i = 0usize;
    let mut j = 0usize;
    while i < small.len() && j < large.len() {
        use std::cmp::Ordering;
        match small[i].cmp(&large[j]) {
            Ordering::Less => return false,
            Ordering::Equal => {
                i += 1;
                j += 1;
            }
            Ordering::Greater => j += 1,
        }
    }

    i == small.len()
}

#[cfg(test)]
fn is_cardinality_shape_subset(small: &ConstraintShapeKey, large: &ConstraintShapeKey) -> bool {
    if small.len() > large.len() {
        return false;
    }

    let mut i = 0usize;
    let mut j = 0usize;
    while i < small.len() && j < large.len() {
        use std::cmp::Ordering;
        match cardinality_shape_lit(&small[i]).cmp(&cardinality_shape_lit(&large[j])) {
            Ordering::Less => return false,
            Ordering::Equal => {
                i += 1;
                j += 1;
            }
            Ordering::Greater => j += 1,
        }
    }

    i == small.len()
}
/// Removes weaker constraints using two safe dominance rules.
///
/// 1. For exact same-shape constraints, the highest RHS is strongest and
///    implies every lower RHS sibling.
/// 2. For pure cardinality constraints with unit coefficients, a support set
///    subsumes any superset whose RHS is no stronger.
///
/// This stays intentionally conservative and linear-only; weighted subset
/// dominance is excluded here.
#[cfg(test)]
fn remove_subsumed(constraints: &mut Vec<PbConstraint>) {
    let mut never_stop = || false;
    let mut stats = PreprocessStats::default();
    let interrupted = remove_subsumed_interruptible(constraints, &mut stats, &mut never_stop);
    debug_assert!(
        !interrupted,
        "non-interruptible subsumption pass must complete"
    );
}

fn remove_subsumed_interruptible<F>(
    constraints: &mut Vec<PbConstraint>,
    stats: &mut PreprocessStats,
    should_stop: &mut F,
) -> bool
where
    F: FnMut() -> bool,
{
    if constraints.len() <= 1 {
        return false;
    }

    let mut shape_keys = Vec::with_capacity(constraints.len());

    for (index, constraint) in constraints.iter().enumerate() {
        if index % 32 == 0 && should_stop() {
            return true;
        }
        shape_keys.push(canonical_subsumption_shape(constraint));
    }

    // Group same-shape rows and keep, per shape, the FIRST row carrying the
    // group's strongest (maximum) RHS. Rows are grouped by a 64-bit shape hash
    // with full key equality inside each bucket, so hash collisions cannot
    // merge distinct shapes and the outcome is completely hash-independent:
    // `retained` holds exactly one winner index per distinct shape, in
    // ascending row order. (The previous two ordered-map passes over the full
    // Vec-typed keys cost ~4.4s per fixpoint round on a 6.4M-row instance;
    // the hash grouping is O(total key size).)
    //
    // Retained rows are tracked BY INDEX into `constraints` — cloning every
    // retained constraint up front cost ~1.5s alone on a 2.5M-row instance
    // (measured on dbst v50, P2e) even when the pass ends up deleting nothing.
    struct ShapeGroup {
        /// Representative row index; used only for full key-equality checks.
        representative: u32,
        strongest_rhs: i128,
        /// First row index whose RHS equals `strongest_rhs`.
        winner: u32,
    }
    // Bucket layout keeps the common no-collision case allocation-free: the
    // first group lives inline, additional same-hash groups spill to a Vec
    // (empty `Vec` does not allocate).
    let mut groups: rustc_hash::FxHashMap<u64, (ShapeGroup, Vec<ShapeGroup>)> =
        rustc_hash::FxHashMap::with_capacity_and_hasher(
            constraints.len(),
            rustc_hash::FxBuildHasher,
        );
    let mut winner_flags = vec![false; constraints.len()];
    for (index, (constraint, key)) in constraints.iter().zip(shape_keys.iter()).enumerate() {
        if index % 32 == 0 && should_stop() {
            return true;
        }
        let hash = {
            use std::hash::BuildHasher;
            rustc_hash::FxBuildHasher.hash_one(&key)
        };
        let update = |group: &mut ShapeGroup, winner_flags: &mut [bool]| {
            if constraint.rhs > group.strongest_rhs {
                winner_flags[group.winner as usize] = false;
                group.strongest_rhs = constraint.rhs;
                group.winner = index as u32;
                winner_flags[index] = true;
            }
        };
        let new_group = || ShapeGroup {
            representative: index as u32,
            strongest_rhs: constraint.rhs,
            winner: index as u32,
        };
        match groups.entry(hash) {
            std::collections::hash_map::Entry::Vacant(slot) => {
                slot.insert((new_group(), Vec::new()));
                winner_flags[index] = true;
            }
            std::collections::hash_map::Entry::Occupied(mut slot) => {
                let (first, spill) = slot.get_mut();
                if shape_keys[first.representative as usize] == *key {
                    update(first, &mut winner_flags);
                } else if let Some(group) = spill
                    .iter_mut()
                    .find(|group| shape_keys[group.representative as usize] == *key)
                {
                    update(group, &mut winner_flags);
                } else {
                    spill.push(new_group());
                    winner_flags[index] = true;
                }
            }
        }
    }
    drop(groups);
    let mut retained: Vec<usize> = Vec::new();
    for (index, &is_winner) in winner_flags.iter().enumerate() {
        if index % 4096 == 0 && should_stop() {
            return true;
        }
        if is_winner {
            retained.push(index);
        }
    }
    drop(winner_flags);

    // HUGE instances keep only the exact-shape dedup above: the dominance
    // stage below (support build + posting lists + subset scan) cost ~2.5s
    // per fixpoint round on a 6.4M-row instance while deleting a handful of
    // rows (measured: lopes-172, 21 of 6.34M). Skipping it is always sound —
    // deletions are optional strengthening — and the gate depends only on the
    // row count, so the pipeline stays deterministic per instance.
    if constraints.len() > HUGE_INSTANCE_ROW_CAP {
        if retained.len() == constraints.len() {
            return false;
        }
        let mut survivor = retained.iter().copied().peekable();
        let mut index = 0usize;
        constraints.retain(|_| {
            let keep = survivor.peek() == Some(&index);
            if keep {
                survivor.next();
            }
            index += 1;
            keep
        });
        return false;
    }

    // Weighted dominance yields little on huge weighted instances but their
    // posting lists are expensive to build; above the cap, restrict the pass
    // to unit-coefficient (cardinality) rows exactly as before the weighted
    // generalization. Skipping is always sound (deletions are optional).
    //
    // The candidate count is a cheap non-allocating pre-scan so that above the
    // cap NO per-row support build (Vec alloc + sort) is paid for weighted
    // rows at all — this pass runs once per fixpoint round. The scan
    // over-approximates `dominance_support` (duplicate-literal rows are
    // counted here but rejected there), which only trips the cap earlier;
    // see `is_weighted_dominance_candidate`.
    let mut weighted_candidate_count = 0usize;
    for (pos, &constraint_index) in retained.iter().enumerate() {
        if pos % 64 == 0 && should_stop() {
            return true;
        }
        if is_weighted_dominance_candidate(&constraints[constraint_index]) {
            weighted_candidate_count += 1;
        }
    }
    let skip_weighted = weighted_candidate_count > MAX_WEIGHTED_DOMINANCE_ENTRIES;

    let mut dominance_supports = Vec::with_capacity(retained.len());
    for (pos, &constraint_index) in retained.iter().enumerate() {
        if pos % 32 == 0 && should_stop() {
            return true;
        }
        let constraint = &constraints[constraint_index];
        if skip_weighted && is_weighted_dominance_candidate(constraint) {
            dominance_supports.push(None);
            continue;
        }
        dominance_supports.push(dominance_support(constraint));
    }

    let mut dominated = vec![false; retained.len()];
    if mark_dominated_rows_interruptible(
        constraints,
        &retained,
        &dominance_supports,
        &mut dominated,
        stats,
        should_stop,
    ) {
        return true;
    }

    // Rebuild only when the pass actually removed something; otherwise leave
    // `constraints` untouched (no clone, no reallocation). The rebuild keeps
    // surviving rows by MOVING them in place (order-preserving retain over the
    // ascending `retained` indices) — cloning every survivor cost ~1.4s on a
    // 6.4M-row instance that deleted a handful of rows.
    let kept = dominated.iter().filter(|&&d| !d).count();
    if retained.len() == constraints.len() && kept == retained.len() {
        return false;
    }
    let mut survivor = retained
        .iter()
        .zip(dominated.iter())
        .filter_map(|(&constraint_index, &is_dominated)| {
            (!is_dominated).then_some(constraint_index)
        })
        .peekable();
    let mut index = 0usize;
    constraints.retain(|_| {
        let keep = survivor.peek() == Some(&index);
        if keep {
            survivor.next();
        }
        index += 1;
        keep
    });
    false
}

/// Row count above which an instance takes the HUGE-instance preprocessing
/// fast path: a single fixpoint round, and subsumption restricted to the
/// exact-shape strongest-RHS dedup (no dominance stage). Every skipped pass
/// is optional strengthening, so the fast path is sound; the gate depends
/// only on the (deterministic) normalized row count. Sized above the ~2.5M-row
/// dbst family (which keeps the full pipeline; P2e measured wins there) and
/// below the 6.4M-row lopes family, whose pre-search preprocessing exceeded
/// whole 10s budgets before this path existed.
const HUGE_INSTANCE_ROW_CAP: usize = 4_000_000;

/// Maximum number of weighted (non-unit-coefficient) candidate rows (per
/// [`is_weighted_dominance_candidate`]) admitted into the dominance pass.
/// Weighted dominance rarely fires on huge weighted instances (measured: ~2
/// per million rows on PB24 LIN) while their posting lists dominate the
/// pass's cost, so beyond this cap only cardinality rows participate (the
/// pre-generalization behavior) and weighted rows skip the support build
/// entirely.
const MAX_WEIGHTED_DOMINANCE_ENTRIES: usize = 100_000;

/// Maximum dense posting-table slot count (2 slots per variable) for the
/// dominance pass. Instances whose variable indices exceed this (33.5M
/// variables) skip dominance marking entirely rather than allocating a
/// disproportionate dense table; skipping is always sound (deletions are
/// optional strengthening).
const DOMINANCE_DENSE_SLOT_CAP: usize = 1 << 26;

/// Total budget (in support-literal comparison steps) for one dominance pass.
/// The pass is optional strengthening, so exhausting the budget just stops
/// marking further rows — always sound. Sized so the pass stays well under the
/// probing budget's cost on pathological posting-list distributions.
const ROW_DOMINANCE_WORK_BUDGET: u64 = 50_000_000;

/// Marks rows that are IMPLIED by another retained row (generalized weighted
/// row dominance), so the caller can delete them.
///
/// For each qualifying linear row A (see [`dominance_support`]), every row B
/// whose literal support is a superset of A's and whose coefficients/degree
/// satisfy [`weighted_row_implies`] is marked dominated. This strictly
/// generalizes the previous unit-coefficient cardinality-superset rule (there
/// `a_i = b_i = 1` and the check reduces to `d >= e`).
///
/// # Deletion soundness (surviving-dominator argument)
///
/// A dominated row is only ever marked by an entry that was itself UNDOMINATED
/// at its processing time, and a row never marks itself. Every "deleted-by"
/// chain therefore has strictly increasing mark times going up the chain, so it
/// terminates at a SURVIVING row; by transitivity of implication that survivor
/// implies every row in its chain. Hence deleting all marked rows preserves
/// the instance's solution set exactly.
fn mark_dominated_rows_interruptible<F>(
    constraints: &[PbConstraint],
    retained: &[usize],
    dominance_supports: &[Option<DominanceSupport>],
    dominated: &mut [bool],
    stats: &mut PreprocessStats,
    should_stop: &mut F,
) -> bool
where
    F: FnMut() -> bool,
{
    let mut entries = Vec::with_capacity(dominance_supports.len());
    let mut min_support_len = usize::MAX;
    let mut max_support_len = 0usize;
    let mut all_unit_coefficients = true;

    for (index, support) in dominance_supports.iter().enumerate() {
        if index % 32 == 0 && should_stop() {
            return true;
        }
        let Some(support) = support else {
            continue;
        };
        entries.push(CardinalityEntry {
            retained_index: index,
            rhs: constraints[retained[index]].rhs,
            support_len: support.len(),
        });
        min_support_len = min_support_len.min(support.len());
        max_support_len = max_support_len.max(support.len());
        if all_unit_coefficients && support.iter().any(|(_, coeff)| *coeff != 1) {
            all_unit_coefficients = false;
        }
    }

    // With unit coefficients only, equal-length supports can only dominate via
    // identical support sets, which the exact-shape strongest-rhs dedup already
    // collapsed — so a uniform support length means no work. Weighted rows can
    // dominate each other on EQUAL supports (e.g. `2x + y >= 2` implies
    // `x + y >= 1`), so they must not take this early-out.
    if entries.len() <= 1 || (min_support_len == max_support_len && all_unit_coefficients) {
        return false;
    }

    entries.sort_unstable_by(|left, right| {
        left.support_len
            .cmp(&right.support_len)
            .then(right.rhs.cmp(&left.rhs))
            .then(left.retained_index.cmp(&right.retained_index))
    });

    // Literal posting lists in a flat CSR layout indexed by `var * 2 +
    // negated` (the ordered-map postings' tree operations were the dominant
    // cost of this pass on multi-million-row instances). Lists hold entry
    // positions in ascending order — exactly the order the map-based build
    // produced — so the `partition_point` prefix skip below still applies.
    let slot_of = |lit: (u32, bool)| -> usize { lit.0 as usize * 2 + usize::from(lit.1) };
    let mut slot_count = 0usize;
    for (entry_pos, entry) in entries.iter().enumerate() {
        if entry_pos % 32 == 0 && should_stop() {
            return true;
        }
        let support = dominance_supports[entry.retained_index]
            .as_ref()
            .expect("dominance entry must have support");
        for (lit, _) in support {
            slot_count = slot_count.max(slot_of(*lit) + 1);
        }
    }
    // Fail closed on pathological literal universes (variable indices so
    // sparse/large that the dense slot table would dwarf the instance):
    // dominance marking is optional strengthening, so skipping it is sound.
    if slot_count > DOMINANCE_DENSE_SLOT_CAP {
        return false;
    }

    // counts[slot] -> prefix-summed into list start offsets.
    let mut starts = vec![0u32; slot_count + 1];
    for (entry_pos, entry) in entries.iter().enumerate() {
        if entry_pos % 32 == 0 && should_stop() {
            return true;
        }
        let support = dominance_supports[entry.retained_index]
            .as_ref()
            .expect("dominance entry must have support");
        for (lit, _) in support {
            starts[slot_of(*lit) + 1] += 1;
        }
    }
    for slot in 1..starts.len() {
        starts[slot] += starts[slot - 1];
    }
    let mut lists = vec![0u32; *starts.last().expect("starts is never empty") as usize];
    let mut cursors = starts.clone();
    for (entry_pos, entry) in entries.iter().enumerate() {
        if entry_pos % 32 == 0 && should_stop() {
            return true;
        }
        let support = dominance_supports[entry.retained_index]
            .as_ref()
            .expect("dominance entry must have support");
        for (lit, _) in support {
            let slot = slot_of(*lit);
            lists[cursors[slot] as usize] = entry_pos as u32;
            cursors[slot] += 1;
        }
    }
    drop(cursors);
    let posting_list = |lit: (u32, bool)| -> &[u32] {
        let slot = slot_of(lit);
        &lists[starts[slot] as usize..starts[slot + 1] as usize]
    };

    let mut work_used: u64 = 0;

    for (entry_pos, entry) in entries.iter().enumerate() {
        if entry_pos % 16 == 0 && should_stop() {
            return true;
        }
        if work_used >= ROW_DOMINANCE_WORK_BUDGET {
            break;
        }
        if dominated[entry.retained_index] {
            continue;
        }

        let small_support = dominance_supports[entry.retained_index]
            .as_ref()
            .expect("dominance entry must have support");

        let mut best_candidates: Option<&[u32]> = None;
        for (lit, _) in small_support {
            let candidates = posting_list(*lit);
            match best_candidates {
                Some(best) if best.len() <= candidates.len() => {}
                _ => best_candidates = Some(candidates),
            }
        }

        let Some(candidate_positions) = best_candidates else {
            continue;
        };

        let start = candidate_positions.partition_point(|candidate_pos| {
            entries[*candidate_pos as usize].support_len < entry.support_len
        });

        for (candidate_offset, &candidate_pos) in candidate_positions[start..].iter().enumerate() {
            if candidate_offset % 64 == 0 && should_stop() {
                return true;
            }
            if work_used >= ROW_DOMINANCE_WORK_BUDGET {
                break;
            }
            let candidate = entries[candidate_pos as usize];
            if candidate.retained_index == entry.retained_index
                || dominated[candidate.retained_index]
            {
                continue;
            }
            let large_support = dominance_supports[candidate.retained_index]
                .as_ref()
                .expect("dominance entry must have support");
            work_used = work_used.saturating_add(large_support.len() as u64);
            if weighted_row_implies(small_support, entry.rhs, large_support, candidate.rhs) {
                dominated[candidate.retained_index] = true;
                let unit_pair = small_support.iter().all(|(_, coeff)| *coeff == 1)
                    && large_support.iter().all(|(_, coeff)| *coeff == 1);
                if unit_pair {
                    stats.dominated_cardinality += 1;
                } else {
                    stats.dominated_weighted += 1;
                }
            }
        }
        if work_used >= ROW_DOMINANCE_WORK_BUDGET {
            break;
        }
    }

    false
}

/// Removes exact duplicate constraints.
#[cfg(test)]
fn remove_duplicates(constraints: &mut Vec<PbConstraint>) {
    let mut never_stop = || false;
    let interrupted = remove_duplicates_interruptible(constraints, &mut never_stop);
    debug_assert!(
        !interrupted,
        "non-interruptible duplicate pass must complete"
    );
}

#[cfg(test)]
fn remove_duplicates_interruptible<F>(
    constraints: &mut Vec<PbConstraint>,
    should_stop: &mut F,
) -> bool
where
    F: FnMut() -> bool,
{
    if constraints.len() <= 1 {
        return false;
    }

    let mut seen: HashSet<(i128, ConstraintShapeKey)> = HashSet::new();
    let mut retained = Vec::with_capacity(constraints.len());

    for (index, constraint) in constraints.iter().cloned().enumerate() {
        if index % 16 == 0 && should_stop() {
            return true;
        }
        let key = (constraint.rhs, canonical_constraint_shape(&constraint));
        if seen.insert(key) {
            retained.push(constraint);
        }
    }

    *constraints = retained;
    false
}

/// Computes GCD of two unsigned 128-bit integers using the Euclidean algorithm.
fn gcd_u128(a: u128, b: u128) -> u128 {
    if b == 0 {
        return a;
    }
    let mut a = a;
    let mut b = b;
    while b != 0 {
        let t = b;
        b = a % b;
        a = t;
    }
    a
}

/// Ceiling division for signed integers: `ceil(a / b)`.
///
/// For `a >= 0, b > 0`: standard `(a + b - 1) / b`.
/// For `a < 0, b > 0`: `a / b` (truncation toward zero rounds up for negatives).
fn ceiling_div(a: i128, b: i128) -> i128 {
    debug_assert!(b > 0, "ceiling_div: divisor must be positive");
    if a >= 0 {
        (a + b - 1) / b
    } else {
        a / b
    }
}

// ---------------------------------------------------------------------------
// Failed-literal probing.
//
// For every currently-unfixed variable `x` we tentatively assign one polarity
// and run pseudo-Boolean unit propagation to a fixpoint over the *original*
// constraints. If that polarity provably leads to a propagation CONFLICT, the
// opposite polarity is a sound logical consequence of the constraints and is
// recorded as a forced fixing.
//
// Soundness:
//   * A recorded fixing is only ever the *opposite* of a polarity whose
//     propagation reached a conflict. A propagation conflict means the assumed
//     literal, together with the constraints, is jointly infeasible; therefore
//     the negation is entailed by the constraints alone. Entailed literals
//     preserve both satisfiability and the optimum.
//   * The propagator is the same watched-slack engine the CDCL search trusts;
//     a `Conflict` from it is authoritative. We never invent a conflict.
//   * No objective / dual reasoning is used: only logical propagation.
//   * If both polarities of a variable conflict, the instance is UNSAT.
//   * The probe trail is undone exactly after each probe, so probes do not
//     interfere with one another and the propagator state is restored to the
//     baseline (all known fixings installed) between probes.
//
// Budget: probing is bounded by `ProbeBudget` so it can never dominate solve
// time on large instances. Work is also cooperatively interruptible via the
// solver's `should_stop` hook.
// ---------------------------------------------------------------------------

/// Bounds on probing work so it stays cheap relative to solving.
#[derive(Debug, Clone, Copy)]
struct ProbeBudget {
    /// Skip probing entirely when the instance has more variables than this.
    max_vars: u32,
    /// Skip probing entirely when the instance has more constraints than this.
    max_constraints: usize,
    /// Maximum number of variables probed in a single probing pass.
    max_probes: u32,
    /// Maximum total propagation steps (assignments enqueued) across the pass.
    max_propagation_steps: u64,
}

impl Default for ProbeBudget {
    fn default() -> Self {
        Self {
            max_vars: 50_000,
            max_constraints: 200_000,
            max_probes: 20_000,
            max_propagation_steps: 5_000_000,
        }
    }
}

/// Outcome of a probing pass.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum ProbeResult {
    /// Probing completed within budget. `found_fixings` is true if at least one
    /// new forced fixing was recorded.
    Ok { found_fixings: bool },
    /// Probing proved the instance unsatisfiable (both polarities conflict).
    Unsatisfiable,
    /// Probing was interrupted by the stop hook.
    Interrupted,
}

/// Converts a 1-indexed variable + boolean value to a DIMACS-style literal.
fn var_value_to_lit(var: u32, value: bool) -> Lit {
    let magnitude = var as Lit;
    if value {
        magnitude
    } else {
        -magnitude
    }
}

/// Failed-literal probing over the original constraints.
///
/// `fixed` is both an input (already-known fixings, installed as the probing
/// baseline) and an output (newly forced fixings are inserted). Only fixings
/// that are proven propagation consequences are ever inserted.
fn probe_failed_literals<F>(
    constraints: &[PbConstraint],
    fixed: &mut HashMap<u32, bool>,
    budget: &ProbeBudget,
    should_stop: &mut F,
) -> ProbeResult
where
    F: FnMut() -> bool,
{
    // Soundness gate: skip probing entirely if any constraint contains a
    // non-linear (product) term. The rest of this crate fails closed on
    // non-linear constraints, and assumption-driven propagation over product
    // terms is outside the well-understood linear PB domain. Skipping is always
    // safe (it only forgoes optional reductions) and preserves the non-linear
    // fail-closed contract exactly.
    // Size / cost guard FIRST: probing is skipped entirely on instances with
    // too many constraints, so don't pay the non-linear gate scan or the
    // candidate-set build on them at all (the set build alone cost ~1s per
    // fixpoint round on a 6.4M-row instance, every round, for a pass that the
    // budget then unconditionally skipped).
    if constraints.len() > budget.max_constraints {
        return ProbeResult::Ok {
            found_fixings: false,
        };
    }

    if constraints
        .iter()
        .any(|c| c.terms.iter().any(|term| term.lits.len() != 1))
    {
        return ProbeResult::Ok {
            found_fixings: false,
        };
    }

    // Cheap allocation-free max-var scan so the `max_vars` budget gate is also
    // checked before the candidate set is built.
    let mut max_var: u32 = 0;
    for c in constraints {
        for term in &c.terms {
            // All terms are linear here (the non-linear gate above returned).
            max_var = max_var.max(term.lits[0].var);
        }
    }
    if max_var == 0 || max_var > budget.max_vars {
        return ProbeResult::Ok {
            found_fixings: false,
        };
    }

    // Collect the set of candidate variables.
    let mut candidate_vars: HashSet<u32> = HashSet::new();
    for c in constraints {
        for term in &c.terms {
            let var = term.lits[0].var;
            if !fixed.contains_key(&var) {
                candidate_vars.insert(var);
            }
        }
    }

    if candidate_vars.is_empty() {
        return ProbeResult::Ok {
            found_fixings: false,
        };
    }

    if should_stop() {
        return ProbeResult::Interrupted;
    }

    // Build a propagator over the original constraints once.
    let mut propagator = PbPropagator::new();
    for (index, c) in constraints.iter().enumerate() {
        if index % 64 == 0 && should_stop() {
            return ProbeResult::Interrupted;
        }
        let _ = propagator.add_from_pb_constraint(c);
    }

    // Install the already-known fixings as the probing baseline at level 0.
    // Any conflict here means the constraints together with the known fixings
    // are infeasible, i.e. the instance is UNSAT.
    let mut baseline_trail: Vec<Lit> = Vec::new();
    let baseline_lits: Vec<Lit> = fixed
        .iter()
        .map(|(&var, &value)| var_value_to_lit(var, value))
        .collect();
    for lit in baseline_lits {
        match assign_and_propagate(&mut propagator, lit, 0, &mut baseline_trail, should_stop) {
            DriveOutcome::Ok => {}
            DriveOutcome::Conflict => return ProbeResult::Unsatisfiable,
            DriveOutcome::Interrupted => return ProbeResult::Interrupted,
        }
    }

    // Probe candidate variables in a deterministic order.
    let mut order: Vec<u32> = candidate_vars.iter().copied().collect();
    order.sort_unstable();

    let mut found_fixings = false;

    // Harvest any candidate variables whose value was *determined* by the
    // baseline propagation of the existing fixings. Such values are unit
    // consequences of the known fixings + constraints, hence sound to record.
    // (In the full pipeline `fix_literals` usually catches these first, but
    // recording them here keeps probing self-consistent and lets later rounds
    // simplify the constraints.)
    for &var in &order {
        if fixed.contains_key(&var) {
            continue;
        }
        match propagator.value(var as Lit) {
            LitValue::True => {
                fixed.insert(var, true);
                found_fixings = true;
            }
            LitValue::False => {
                fixed.insert(var, false);
                found_fixings = true;
            }
            LitValue::Unassigned => {}
        }
    }

    let mut probes_done: u32 = 0;
    let mut steps_used: u64 = 0;

    for var in order {
        if probes_done >= budget.max_probes || steps_used >= budget.max_propagation_steps {
            break;
        }
        if should_stop() {
            return ProbeResult::Interrupted;
        }
        // Skip variables that became fixed by an earlier probe in this pass
        // (their value is already entailed and installed in the baseline).
        if fixed.contains_key(&var) {
            continue;
        }
        // Only probe variables that are actually still unassigned at the
        // baseline (a baseline propagation may have already implied a value).
        if propagator.value(var as Lit) != LitValue::Unassigned {
            continue;
        }

        probes_done += 1;

        // Probe x = true.
        let mut trail: Vec<Lit> = Vec::new();
        let true_outcome = assign_and_propagate(
            &mut propagator,
            var_value_to_lit(var, true),
            1,
            &mut trail,
            should_stop,
        );
        steps_used = steps_used.saturating_add(trail.len() as u64);
        undo_trail(&mut propagator, &mut trail);
        match true_outcome {
            DriveOutcome::Interrupted => return ProbeResult::Interrupted,
            DriveOutcome::Ok => {}
            DriveOutcome::Conflict => {
                // x = true is infeasible, so x = false is forced.
                match record_forced_fixing(
                    &mut propagator,
                    fixed,
                    var,
                    false,
                    &mut baseline_trail,
                    should_stop,
                ) {
                    DriveOutcome::Ok => {
                        found_fixings = true;
                        steps_used = steps_used.saturating_add(1);
                        continue;
                    }
                    DriveOutcome::Conflict => return ProbeResult::Unsatisfiable,
                    DriveOutcome::Interrupted => return ProbeResult::Interrupted,
                }
            }
        }

        // Probe x = false.
        let mut trail: Vec<Lit> = Vec::new();
        let false_outcome = assign_and_propagate(
            &mut propagator,
            var_value_to_lit(var, false),
            1,
            &mut trail,
            should_stop,
        );
        steps_used = steps_used.saturating_add(trail.len() as u64);
        undo_trail(&mut propagator, &mut trail);
        match false_outcome {
            DriveOutcome::Interrupted => return ProbeResult::Interrupted,
            DriveOutcome::Ok => {}
            DriveOutcome::Conflict => {
                // x = false is infeasible, so x = true is forced.
                match record_forced_fixing(
                    &mut propagator,
                    fixed,
                    var,
                    true,
                    &mut baseline_trail,
                    should_stop,
                ) {
                    DriveOutcome::Ok => {
                        found_fixings = true;
                        steps_used = steps_used.saturating_add(1);
                    }
                    DriveOutcome::Conflict => return ProbeResult::Unsatisfiable,
                    DriveOutcome::Interrupted => return ProbeResult::Interrupted,
                }
            }
        }
    }

    ProbeResult::Ok { found_fixings }
}

/// Records a forced fixing in `fixed` and installs it into the propagator
/// baseline (so subsequent probes in the same pass see it). The caller has
/// already proven that `value` is entailed for `var`.
///
/// Returns `Conflict` if installing the forced fixing immediately conflicts,
/// which (since the fixing is entailed) means the instance is UNSAT.
fn record_forced_fixing<F>(
    propagator: &mut PbPropagator,
    fixed: &mut HashMap<u32, bool>,
    var: u32,
    value: bool,
    baseline_trail: &mut Vec<Lit>,
    should_stop: &mut F,
) -> DriveOutcome
where
    F: FnMut() -> bool,
{
    match fixed.get(&var) {
        Some(&existing) if existing != value => {
            // The other polarity was already entailed: contradiction => UNSAT.
            return DriveOutcome::Conflict;
        }
        Some(_) => return DriveOutcome::Ok, // Already fixed to this value.
        None => {}
    }

    fixed.insert(var, value);
    assign_and_propagate(
        propagator,
        var_value_to_lit(var, value),
        0,
        baseline_trail,
        should_stop,
    )
}

/// Outcome of driving propagation to a fixpoint.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum DriveOutcome {
    Ok,
    Conflict,
    Interrupted,
}

/// Assigns `lit` at `decision_level` and drives pseudo-Boolean propagation to a
/// fixpoint, recording every newly assigned literal (the assumption and every
/// implied literal) onto `trail` for precise undo.
///
/// This mirrors the trusted CDCL propagation loop (`PbCdclSolver::propagate_all`):
/// a monotonically advancing `scan_cursor` performs the one-time full scan, while
/// event-driven `assign_literal` (watched-slack `notify_falsified`) and a
/// `pending_sources` recheck stack reach the same fixpoint without re-scanning
/// every constraint from 0 after each implication. PB unit propagation to a
/// fixpoint is confluent, so the set of forced literals and the conflict/no-conflict
/// verdict are identical to a repeated full scan — only far cheaper.
fn assign_and_propagate<F>(
    propagator: &mut PbPropagator,
    lit: Lit,
    decision_level: u32,
    trail: &mut Vec<Lit>,
    should_stop: &mut F,
) -> DriveOutcome
where
    F: FnMut() -> bool,
{
    if should_stop() {
        return DriveOutcome::Interrupted;
    }

    // If the literal is already true, there is nothing to do. If it is already
    // false, this assignment is an immediate conflict — but the variable is
    // held by the *opposite* (baseline) assignment, so we must NOT record `lit`
    // on the probe trail (undoing it would corrupt the baseline state).
    match propagator.value(lit) {
        LitValue::True => return DriveOutcome::Ok,
        LitValue::False => return DriveOutcome::Conflict,
        LitValue::Unassigned => {}
    }

    // `lit` is unassigned here, so `assign_literal` newly assigns it. Whether
    // the result is Ok, Propagated, or Conflict, the variable now holds `lit`
    // and must be recorded for undo. `assign_literal` is event-driven; any
    // resulting first implication is rediscovered by the cursor-based fixpoint
    // loop below (which begins with a single full scan).
    match propagator.assign_literal(lit, decision_level) {
        PropResult::Ok | PropResult::Propagated(_, _, _) => trail.push(lit),
        PropResult::Conflict(_, _) => {
            trail.push(lit);
            return DriveOutcome::Conflict;
        }
        PropResult::Interrupted => return DriveOutcome::Interrupted,
    }

    drive_to_fixpoint(propagator, trail, should_stop)
}

/// Origin of the most recent propagation result inside the cursor-based driver.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum ProbePropagationOrigin {
    /// Result came from the monotone full scan (`propagate_from`).
    Scan,
    /// Result came from re-checking a source constraint that previously fired.
    SourceRecheck,
    /// Result came from an event-driven `assign_literal` notification.
    Event,
}

/// Drives pseudo-Boolean propagation to a fixpoint without re-scanning every
/// constraint from 0 after each implication.
///
/// Behaviour-identical to a repeated full `propagate()` scan (the same fixpoint
/// of forced literals; the same conflict/no-conflict verdict), but uses the
/// trusted `propagate_all` strategy: event-driven `assign_literal` plus the
/// propagator's pending-check queue (which records every constraint whose
/// check reported a propagation during watch notification). The one-time
/// monotone full scan via `scan_cursor` runs only until the propagator first
/// reaches a scan-certified fixpoint (`needs_full_scan`); with up to 20k
/// failed-literal probes per pass, re-scanning every constraint per probe was
/// the dominant preprocessing cost on scan-heavy instances (P2d). Every newly
/// assigned literal is recorded on `trail` for precise undo.
fn drive_to_fixpoint<F>(
    propagator: &mut PbPropagator,
    trail: &mut Vec<Lit>,
    should_stop: &mut F,
) -> DriveOutcome
where
    F: FnMut() -> bool,
{
    let mut poll = 0u32;
    let scan_needed = propagator.needs_full_scan();
    let scan_token = propagator.full_scan_token();
    let mut scan_cursor = 0usize;
    let mut origin = ProbePropagationOrigin::Scan;
    // Most recent popped-but-not-yet-consumed pending re-check (D2
    // hardening): if the top-of-loop interrupt fires between the pop and the
    // match arm that consumes its result, the entry must go back on the
    // queue — post-scan, the queue is the only discovery vehicle for that
    // row's propagation. Cleared once the result is consumed.
    let mut unconsumed_recheck: Option<usize> = None;
    let mut result = if scan_needed {
        propagator.propagate_from(scan_cursor)
    } else {
        scan_cursor = propagator.num_constraints();
        PropResult::Ok
    };

    loop {
        poll = poll.wrapping_add(1);
        if poll.is_multiple_of(64) && should_stop() {
            if let Some(cid) = unconsumed_recheck {
                // Idempotent via the in-pending dedup flag.
                propagator.queue_pending_check(cid);
            }
            return DriveOutcome::Interrupted;
        }
        unconsumed_recheck = None;

        match result {
            PropResult::Ok => {
                if origin == ProbePropagationOrigin::Scan {
                    // The full scan reached the end: nothing below the cursor can
                    // propagate again until a new assignment notifies it.
                    scan_cursor = propagator.num_constraints();
                }
                if let Some(cid) = propagator.pop_pending_check() {
                    origin = ProbePropagationOrigin::SourceRecheck;
                    result = propagator.propagate_constraint(cid);
                    unconsumed_recheck = Some(cid);
                    continue;
                }
                if scan_needed && scan_cursor < propagator.num_constraints() {
                    origin = ProbePropagationOrigin::Scan;
                    result = propagator.propagate_from(scan_cursor);
                    continue;
                }
                if scan_needed {
                    propagator.mark_full_scan_complete(scan_token);
                }
                return DriveOutcome::Ok;
            }
            PropResult::Conflict(_, _) => return DriveOutcome::Conflict,
            PropResult::Interrupted => return DriveOutcome::Interrupted,
            PropResult::Propagated(implied, _, cid) => {
                if origin == ProbePropagationOrigin::Scan {
                    // The scanning constraint may still propagate after the
                    // assignment, so re-check it (via the pending queue) but do
                    // not re-scan the constraints already passed.
                    scan_cursor = cid.saturating_add(1);
                }
                // `check_propagation` only reports an UNASSIGNED literal, so the
                // implied literal is newly assigned here and must be recorded for
                // undo (defensive guards retained for already-set values).
                let newly_assigned = match propagator.value(implied) {
                    LitValue::True => false,
                    LitValue::False => return DriveOutcome::Conflict,
                    LitValue::Unassigned => true,
                };
                propagator.queue_pending_check(cid);
                result = match propagator.assign_literal(implied, 0) {
                    outcome @ (PropResult::Ok | PropResult::Propagated(_, _, _)) => {
                        if newly_assigned {
                            trail.push(implied);
                        }
                        outcome
                    }
                    PropResult::Conflict(_, _) => {
                        if newly_assigned {
                            trail.push(implied);
                        }
                        return DriveOutcome::Conflict;
                    }
                    PropResult::Interrupted => return DriveOutcome::Interrupted,
                };
                origin = ProbePropagationOrigin::Event;
            }
        }
    }
}

/// Unassigns every literal recorded on `trail`, in reverse order, restoring the
/// propagator to the state it had before the probe began.
///
/// Batched into a single `unassign_literals` call: per-literal unassignment
/// paid one slack-repair pass over the falsified-watch events PER LITERAL
/// (profiling showed this at ~65% of preprocessing wall time on probe-heavy
/// instances); the batch pays one pass for the whole probe trail, exactly
/// like the CDCL backtrack path.
fn undo_trail(propagator: &mut PbPropagator, trail: &mut Vec<Lit>) {
    trail.reverse();
    propagator.unassign_literals(trail);
    trail.clear();
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::parser::parse_opb;
    use crate::propagation::PbPropagator;
    use crate::types::{PbObjective, PbRel};

    fn lit(var: u32) -> PbLit {
        PbLit {
            var,
            negated: false,
        }
    }

    fn neg(var: u32) -> PbLit {
        PbLit { var, negated: true }
    }

    fn term(coeff: i128, l: PbLit) -> PbTerm {
        PbTerm {
            coeff,
            lits: vec![l],
        }
    }

    fn ge(terms: Vec<PbTerm>, rhs: i128) -> PbConstraint {
        PbConstraint {
            terms,
            rel: PbRel::Ge,
            rhs,
        }
    }

    fn eq_constraint(terms: Vec<PbTerm>, rhs: i128) -> PbConstraint {
        PbConstraint {
            terms,
            rel: PbRel::Eq,
            rhs,
        }
    }

    fn make_instance(num_vars: u32, constraints: Vec<PbConstraint>) -> PbInstance {
        let num_constraints = constraints.len() as u32;
        PbInstance {
            num_vars,
            num_constraints,
            constraints,
            objective: None,
        }
    }

    fn normalized_constraints(c: &PbConstraint) -> Vec<PbConstraint> {
        match normalize_constraint(c) {
            NormalizationOutcome::Constraints(normalized) => normalized,
            NormalizationOutcome::Unsatisfiable => {
                panic!("expected normalized constraints, got unsatisfiable")
            }
            NormalizationOutcome::OverflowNonTrivial => {
                panic!("expected normalized constraints, got overflow bailout")
            }
        }
    }

    fn nested_frontier_instance(num_families: u32, family_len: u32) -> PbInstance {
        let mut constraints = Vec::with_capacity((num_families * family_len) as usize);

        for family in 0..num_families {
            let family_base = family * (family_len + 2) + 1;
            let seed_a = family_base;
            let seed_b = family_base + 1;

            for depth in 0..family_len {
                let mut terms = Vec::with_capacity((depth + 2) as usize);
                terms.push(term(1, lit(seed_a)));
                terms.push(term(1, lit(seed_b)));
                for extra in 0..depth {
                    terms.push(term(1, lit(family_base + 2 + extra)));
                }
                constraints.push(ge(terms, 1));
            }
        }

        make_instance(num_families * (family_len + 2), constraints)
    }

    fn old_threshold_subsumed_constraints(constraints: &[PbConstraint]) -> Vec<PbConstraint> {
        const MAX_CARDINALITY_SUBSET_DOMINANCE_PAIRS: usize = 16_000_000;

        let mut strongest_rhs: HashMap<ConstraintShapeKey, i128> = HashMap::new();
        for constraint in constraints {
            let key = canonical_constraint_shape(constraint);
            strongest_rhs
                .entry(key)
                .and_modify(|rhs| *rhs = (*rhs).max(constraint.rhs))
                .or_insert(constraint.rhs);
        }

        let mut seen_best: HashSet<ConstraintShapeKey> = HashSet::new();
        let mut retained = Vec::with_capacity(constraints.len());
        for constraint in constraints.iter().cloned() {
            let key = canonical_constraint_shape(&constraint);
            let is_strongest = strongest_rhs
                .get(&key)
                .is_some_and(|rhs| *rhs == constraint.rhs);
            if is_strongest && seen_best.insert(key) {
                retained.push(constraint);
            }
        }

        let cardinality_supports: Vec<Option<CardinalitySupportKey>> =
            retained.iter().map(canonical_cardinality_support).collect();
        let cardinality_support_count = cardinality_supports
            .iter()
            .filter(|support| support.is_some())
            .count();
        let mut dominated = vec![false; retained.len()];

        if cardinality_support_count
            .checked_mul(cardinality_support_count)
            .is_some_and(|pairs| pairs <= MAX_CARDINALITY_SUBSET_DOMINANCE_PAIRS)
        {
            for i in 0..retained.len() {
                let Some(ref small_support) = cardinality_supports[i] else {
                    continue;
                };
                for j in 0..retained.len() {
                    if i == j || dominated[j] {
                        continue;
                    }
                    let Some(ref large_support) = cardinality_supports[j] else {
                        continue;
                    };
                    if retained[i].rhs < retained[j].rhs {
                        continue;
                    }
                    if is_sorted_subset(small_support, large_support) {
                        dominated[j] = true;
                    }
                }
            }
        }

        retained
            .into_iter()
            .enumerate()
            .filter_map(|(index, constraint)| (!dominated[index]).then_some(constraint))
            .collect()
    }

    fn build_propagator(constraints: &[PbConstraint]) -> PbPropagator {
        let mut propagator = PbPropagator::new();
        for constraint in constraints {
            let _ = propagator.add_from_pb_constraint(constraint);
        }
        propagator
    }

    // --- Coefficient tightening tests ---

    #[test]
    fn test_tighten_coefficients_caps_at_rhs() {
        // 5*x1 + 3*x2 + 2*x3 >= 4  ->  4*x1 + 3*x2 + 2*x3 >= 4
        let mut c = ge(vec![term(5, lit(1)), term(3, lit(2)), term(2, lit(3))], 4);
        tighten_coefficients(&mut c);
        assert_eq!(c.terms[0].coeff, 4);
        assert_eq!(c.terms[1].coeff, 3);
        assert_eq!(c.terms[2].coeff, 2);
        assert_eq!(c.rhs, 4);
    }

    #[test]
    fn test_tighten_coefficients_no_change_when_all_within_rhs() {
        let mut c = ge(vec![term(2, lit(1)), term(3, lit(2)), term(1, lit(3))], 4);
        tighten_coefficients(&mut c);
        assert_eq!(c.terms[0].coeff, 2);
        assert_eq!(c.terms[1].coeff, 3);
        assert_eq!(c.terms[2].coeff, 1);
    }

    #[test]
    fn test_tighten_coefficients_rhs_zero_no_change() {
        let mut c = ge(vec![term(5, lit(1))], 0);
        tighten_coefficients(&mut c);
        assert_eq!(c.terms[0].coeff, 5);
    }

    #[test]
    fn test_tighten_all_above_rhs() {
        // 10*x1 + 8*x2 >= 3  ->  3*x1 + 3*x2 >= 3
        let mut c = ge(vec![term(10, lit(1)), term(8, lit(2))], 3);
        tighten_coefficients(&mut c);
        assert_eq!(c.terms[0].coeff, 3);
        assert_eq!(c.terms[1].coeff, 3);
    }

    // --- GCD strengthening tests ---

    #[test]
    fn test_gcd_strengthen_divides_by_gcd() {
        // 6*x1 + 4*x2 + 2*x3 >= 5  ->  3*x1 + 2*x2 + 1*x3 >= 3
        let mut c = ge(vec![term(6, lit(1)), term(4, lit(2)), term(2, lit(3))], 5);
        gcd_strengthen(&mut c);
        assert_eq!(c.terms[0].coeff, 3);
        assert_eq!(c.terms[1].coeff, 2);
        assert_eq!(c.terms[2].coeff, 1);
        assert_eq!(c.rhs, 3); // ceil(5/2) = 3
    }

    #[test]
    fn test_gcd_strengthen_exact_division() {
        // 4*x1 + 2*x2 >= 4  ->  2*x1 + 1*x2 >= 2
        let mut c = ge(vec![term(4, lit(1)), term(2, lit(2))], 4);
        gcd_strengthen(&mut c);
        assert_eq!(c.terms[0].coeff, 2);
        assert_eq!(c.terms[1].coeff, 1);
        assert_eq!(c.rhs, 2); // 4/2 = 2
    }

    #[test]
    fn test_gcd_strengthen_no_common_factor() {
        // 3*x1 + 2*x2 >= 2  (gcd=1, no change)
        let mut c = ge(vec![term(3, lit(1)), term(2, lit(2))], 2);
        gcd_strengthen(&mut c);
        assert_eq!(c.terms[0].coeff, 3);
        assert_eq!(c.terms[1].coeff, 2);
        assert_eq!(c.rhs, 2);
    }

    #[test]
    fn test_gcd_strengthen_large_unit_cardinality_uses_fast_guard() {
        let mut c = ge((1..=4096).map(|var| term(1, lit(var))).collect(), 2048);
        let original = c.clone();

        assert_eq!(
            gcd_strengthening_divisor(&c.terms),
            None,
            "unit coefficients cannot be strengthened by gcd division"
        );
        gcd_strengthen(&mut c);
        assert_eq!(c, original);
    }

    #[test]
    fn test_gcd_strengthen_single_term() {
        // 6*x1 >= 4  ->  1*x1 >= 1 (gcd=6, ceil(4/6)=1)
        let mut c = ge(vec![term(6, lit(1))], 4);
        gcd_strengthen(&mut c);
        assert_eq!(c.terms[0].coeff, 1);
        assert_eq!(c.rhs, 1);
    }

    #[test]
    fn test_gcd_strengthen_empty_terms() {
        let mut c = ge(vec![], 0);
        gcd_strengthen(&mut c);
        assert!(c.terms.is_empty());
    }

    // --- Trivial constraint detection tests ---

    #[test]
    fn test_trivially_satisfied_negative_rhs() {
        let c = ge(vec![term(1, lit(1))], -1);
        assert_eq!(classify_trivial(&c), TrivialClass::Satisfied);
    }

    #[test]
    fn test_trivially_satisfied_zero_rhs() {
        let c = ge(vec![term(1, lit(1))], 0);
        assert_eq!(classify_trivial(&c), TrivialClass::Satisfied);
    }

    #[test]
    fn test_trivially_unsatisfiable_max_sum_too_small() {
        // 1*x1 + 1*x2 >= 5 (max sum = 2 < 5)
        let c = ge(vec![term(1, lit(1)), term(1, lit(2))], 5);
        assert_eq!(classify_trivial(&c), TrivialClass::Unsatisfiable);
    }

    #[test]
    fn test_trivially_unsatisfiable_empty_with_positive_rhs() {
        let c = ge(vec![], 1);
        assert_eq!(classify_trivial(&c), TrivialClass::Unsatisfiable);
    }

    #[test]
    fn test_non_trivial_constraint() {
        let c = ge(vec![term(1, lit(1)), term(1, lit(2))], 1);
        assert_eq!(classify_trivial(&c), TrivialClass::NonTrivial);
    }

    #[test]
    fn test_non_trivial_constraint_with_large_positive_sum() {
        let c = ge(vec![term(i128::MAX, lit(1)), term(1, lit(2))], i128::MAX);
        assert_eq!(classify_trivial(&c), TrivialClass::NonTrivial);
    }

    // --- Normalization tests ---

    #[test]
    fn test_normalize_negative_coefficient() {
        // -2*x1 + 3*x2 >= 1  ->  2*~x1 + 3*x2 >= 3
        let c = PbConstraint {
            terms: vec![term(-2, lit(1)), term(3, lit(2))],
            rel: PbRel::Ge,
            rhs: 1,
        };
        let normalized = normalized_constraints(&c);
        assert_eq!(normalized.len(), 1);
        let n = &normalized[0];
        assert_eq!(n.terms.len(), 2);
        assert_eq!(n.terms[0].coeff, 2);
        assert!(n.terms[0].lits[0].negated);
        assert_eq!(n.terms[0].lits[0].var, 1);
        assert_eq!(n.terms[1].coeff, 3);
        assert!(!n.terms[1].lits[0].negated);
        assert_eq!(n.rhs, 3); // 1 - (-2) = 3
    }

    #[test]
    fn test_normalize_equality_splits_into_two() {
        // x1 + x2 = 1  ->  x1 + x2 >= 1 AND ~x1 + ~x2 >= 1
        let c = eq_constraint(vec![term(1, lit(1)), term(1, lit(2))], 1);
        let normalized = normalized_constraints(&c);
        assert_eq!(normalized.len(), 2);
        // First: x1 + x2 >= 1
        assert_eq!(normalized[0].rhs, 1);
        assert_eq!(normalized[0].terms.len(), 2);
        // Second: ~x1 + ~x2 >= 1 (negated coefficients normalized)
        assert_eq!(normalized[1].rhs, 1);
    }

    #[test]
    fn test_normalize_zero_coefficient_removed() {
        let c = ge(vec![term(0, lit(1)), term(3, lit(2))], 2);
        assert!(
            !ge_constraint_needs_no_exact_normalization(&c),
            "zero terms must still take the canonicalizing normalization path"
        );
        let normalized = normalized_constraints(&c);
        assert_eq!(normalized.len(), 1);
        assert_eq!(normalized[0].terms.len(), 1);
        assert_eq!(normalized[0].terms[0].coeff, 3);
    }

    #[test]
    fn test_normalize_already_normalized_linear_constraint_uses_fast_guard() {
        let c = ge(vec![term(2, lit(1)), term(3, neg(2)), term(4, lit(3))], 5);

        assert!(
            ge_constraint_needs_no_exact_normalization(&c),
            "sorted positive linear constraints need no exact-normalization rewrite"
        );
        assert_eq!(normalized_constraints(&c), vec![c]);
    }

    #[test]
    fn test_normalize_merges_duplicate_linear_literals() {
        let c = ge(vec![term(2, lit(1)), term(3, lit(1)), term(1, lit(2))], 4);
        assert!(
            !ge_constraint_needs_no_exact_normalization(&c),
            "duplicate linear literals must still be compacted"
        );
        let normalized = normalized_constraints(&c);
        assert_eq!(normalized.len(), 1);
        assert_eq!(normalized[0].terms, vec![term(5, lit(1)), term(1, lit(2))]);
        assert_eq!(normalized[0].rhs, 4);
    }

    #[test]
    fn test_normalize_eliminates_complementary_linear_literals() {
        let c = ge(vec![term(2, lit(1)), term(3, neg(1)), term(1, lit(2))], 3);
        let normalized = normalized_constraints(&c);
        assert_eq!(normalized.len(), 1);
        assert_eq!(normalized[0].terms, vec![term(1, neg(1)), term(1, lit(2))]);
        assert_eq!(normalized[0].rhs, 1);
    }

    #[test]
    fn test_normalize_wide_i64_min_constraint_reports_overflow_bailout() {
        let c = ge(vec![term(i128::MIN, lit(1))], 0);
        assert!(matches!(
            normalize_constraint(&c),
            NormalizationOutcome::OverflowNonTrivial
        ));
    }

    // --- Non-linear (product) normalization hardening tests ---
    //
    // The negative-coefficient literal flip (`a*l` with a<0 -> `|a|*~l`) is only
    // sound on SINGLE-literal terms. On a product `a*(l1 AND l2)` it would assert
    // `|a|*(~l1 AND ~l2)`, but De Morgan gives `~(l1 AND l2) = ~l1 OR ~l2`, so the
    // flipped row has the WRONG truth function. These tests pin that the flip is
    // NEVER applied to a non-linear term, the constraint is preserved verbatim
    // (no drop, no flip), and the meaning is unchanged across all assignments.

    /// Builds a product term `coeff * (l1 AND l2 AND ...)`.
    fn prod(coeff: i128, lits: Vec<PbLit>) -> PbTerm {
        PbTerm { coeff, lits }
    }

    #[test]
    fn nonlinear_negative_coeff_product_is_not_flipped() {
        // -1 * (x1 AND x2) >= 0  must stay EXACTLY as-is (the buggy flip would
        // produce `1 * (~x1 AND ~x2) >= 1`).
        let c = ge(vec![prod(-1, vec![lit(1), lit(2)])], 0);
        let normalized = normalized_constraints(&c);
        assert_eq!(
            normalized,
            vec![c.clone()],
            "non-linear negative-coefficient product must be preserved verbatim, not flipped"
        );
        // Explicitly assert it was NOT turned into the De Morgan-wrong flipped row.
        let buggy_flip = ge(vec![prod(1, vec![neg(1), neg(2)])], 1);
        assert_ne!(
            normalized[0], buggy_flip,
            "normalization must not apply the unsound product literal flip"
        );
    }

    #[test]
    fn nonlinear_negative_coeff_product_preserves_truth_function() {
        // The normalized rows (a single >= row here) must accept EXACTLY the same
        // assignments as the original constraint, over all 2^2 assignments.
        let c = ge(vec![prod(-1, vec![lit(1), lit(2)])], 0);
        let normalized = normalized_constraints(&c);
        for mask in 0u32..4 {
            let assignment = [(mask & 1) == 1, (mask & 2) == 2];
            let original_holds = crate::eval_constraint(&c, &assignment);
            let normalized_holds = normalized
                .iter()
                .all(|row| crate::eval_constraint(row, &assignment));
            assert_eq!(
                original_holds, normalized_holds,
                "truth function changed for assignment {assignment:?}"
            );
            // The unsound flip `~x1 AND ~x2 >= 1` would disagree on x1=1,x2=0.
        }
    }

    #[test]
    fn nonlinear_eq_product_splits_into_two_ge_without_flip() {
        // (x1 AND x2) = 0  <=>  (x1 AND x2) >= 0  AND  -(x1 AND x2) >= 0,
        // with NO literal flip on either side.
        let c = eq_constraint(vec![prod(1, vec![lit(1), lit(2)])], 0);
        let normalized = normalized_constraints(&c);
        assert_eq!(normalized.len(), 2, "Eq must split into two >= rows");
        for row in &normalized {
            assert_eq!(row.rel, PbRel::Ge);
            // No literal was flipped: every literal stays non-negated as written.
            for term in &row.terms {
                for lit in &term.lits {
                    assert!(!lit.negated, "Eq split must not flip product literals");
                }
            }
        }
        // Exhaustive: original Eq holds iff BOTH >= rows hold.
        for mask in 0u32..4 {
            let assignment = [(mask & 1) == 1, (mask & 2) == 2];
            let original_holds = crate::eval_constraint(&c, &assignment);
            let split_holds = normalized
                .iter()
                .all(|row| crate::eval_constraint(row, &assignment));
            assert_eq!(
                original_holds, split_holds,
                "Eq split changed truth function for assignment {assignment:?}"
            );
        }
    }

    #[test]
    fn classify_trivial_sound_for_negative_coeff_product() {
        // -(x1 AND x2) ranges over {0, -1}. The historical `rhs <= 0 => Satisfied`
        // rule is UNSOUND here and would wrongly DROP the >= 0 row.
        assert_eq!(
            classify_trivial(&ge(vec![prod(-1, vec![lit(1), lit(2)])], 0)),
            TrivialClass::NonTrivial,
            "`-1 (x1 AND x2) >= 0` is NOT trivially satisfied (min LHS is -1)"
        );
        assert_eq!(
            classify_trivial(&ge(vec![prod(-1, vec![lit(1), lit(2)])], -1)),
            TrivialClass::Satisfied,
            "`-1 (x1 AND x2) >= -1` always holds (min LHS -1 >= -1)"
        );
        assert_eq!(
            classify_trivial(&ge(vec![prod(-1, vec![lit(1), lit(2)])], 1)),
            TrivialClass::Unsatisfiable,
            "`-1 (x1 AND x2) >= 1` is impossible (max LHS 0 < 1)"
        );
    }

    #[test]
    fn tighten_does_not_corrupt_negative_coeff_product_row() {
        // With a negative coefficient present, saturating the positive `3 x3` to
        // `rhs` would wrongly exclude x3=1,x1=1,x2=1. The guard must leave the row
        // untouched.
        let mut c = ge(vec![prod(-1, vec![lit(1), lit(2)]), term(3, lit(3))], 2);
        let before = c.clone();
        tighten_coefficients(&mut c);
        assert_eq!(
            c, before,
            "tightening must skip rows with a negative coefficient"
        );
    }

    #[test]
    fn preprocess_keeps_nonlinear_constraint_no_drop() {
        // Instance (b): the lone non-linear row must survive preprocessing
        // verbatim -- never dropped (a dropped row is a weaker problem and a
        // possible WRONG SAT) and never flipped.
        let nonlinear = ge(vec![prod(-1, vec![lit(1), lit(2)])], 0);
        let instance = make_instance(2, vec![nonlinear.clone()]);
        let nonlinear_in = count_nonlinear(&instance.constraints);
        assert_eq!(nonlinear_in, 1);

        match preprocess(&instance) {
            PreprocessResult::Simplified { instance: out, .. } => {
                assert_eq!(
                    count_nonlinear(&out.constraints),
                    nonlinear_in,
                    "the non-linear constraint count must be preserved through preprocess"
                );
                assert!(
                    out.constraints.contains(&nonlinear),
                    "the original non-linear row `-1 x1 x2 >= 0` must be retained verbatim, \
                     got {:?}",
                    out.constraints
                );
            }
            other => panic!("expected Simplified, got {other:?}"),
        }
    }

    #[test]
    fn preprocess_keeps_nonlinear_constraint_alongside_linear_fixings() {
        // Instance (a)-shaped: `-1 x1 x2 >= 0` plus `x1 >= 1`. The linear row may
        // be consumed by literal fixing, but the non-linear row must remain.
        let nonlinear = ge(vec![prod(-1, vec![lit(1), lit(2)])], 0);
        let instance = make_instance(2, vec![nonlinear.clone(), ge(vec![term(1, lit(1))], 1)]);

        match preprocess(&instance) {
            PreprocessResult::Simplified { instance: out, .. } => {
                assert_eq!(
                    count_nonlinear(&out.constraints),
                    1,
                    "the non-linear constraint must not be dropped"
                );
                assert!(
                    out.constraints.contains(&nonlinear),
                    "the non-linear row must be retained verbatim (not flipped), got {:?}",
                    out.constraints
                );
            }
            other => panic!("expected Simplified, got {other:?}"),
        }
    }

    fn count_nonlinear(constraints: &[PbConstraint]) -> usize {
        constraints
            .iter()
            .filter(|c| c.terms.iter().any(|t| t.lits.len() != 1))
            .count()
    }

    // --- Literal fixing tests ---

    #[test]
    fn test_fix_single_term_constraint() {
        // 3*x1 >= 2  ->  x1 must be true
        let mut constraints = vec![ge(vec![term(3, lit(1))], 2)];
        let mut fixed = HashMap::new();
        let result = fix_literals(&mut constraints, &mut fixed);
        assert!(matches!(result, FixResult::Ok { changed: true }));
        assert_eq!(fixed.get(&1), Some(&true));
    }

    #[test]
    fn test_fix_negated_literal() {
        // 3*~x1 >= 2  ->  ~x1 must be true, so x1 = false
        let mut constraints = vec![ge(vec![term(3, neg(1))], 2)];
        let mut fixed = HashMap::new();
        let result = fix_literals(&mut constraints, &mut fixed);
        assert!(matches!(result, FixResult::Ok { changed: true }));
        assert_eq!(fixed.get(&1), Some(&false));
    }

    #[test]
    fn test_fix_detects_conflict() {
        // x1 >= 1 AND ~x1 >= 1 -> x1=true AND x1=false -> conflict
        let mut constraints = vec![ge(vec![term(1, lit(1))], 1), ge(vec![term(1, neg(1))], 1)];
        let mut fixed = HashMap::new();
        let result = fix_literals(&mut constraints, &mut fixed);
        assert_eq!(result, FixResult::Conflict);
    }

    #[test]
    fn test_fix_multiple_forced_literals() {
        // x1 + x2 + x3 >= 3 -> all must be true
        let mut constraints = vec![ge(
            vec![term(1, lit(1)), term(1, lit(2)), term(1, lit(3))],
            3,
        )];
        let mut fixed = HashMap::new();
        let result = fix_literals(&mut constraints, &mut fixed);
        assert!(matches!(result, FixResult::Ok { changed: true }));
        assert_eq!(fixed.get(&1), Some(&true));
        assert_eq!(fixed.get(&2), Some(&true));
        assert_eq!(fixed.get(&3), Some(&true));
    }

    #[test]
    fn test_fix_literals_large_positive_sum_does_not_overflow() {
        let mut constraints = vec![ge(
            vec![term(i128::MAX, lit(1)), term(1, lit(2)), term(1, lit(3))],
            2,
        )];
        let mut fixed = HashMap::new();
        let result = fix_literals(&mut constraints, &mut fixed);
        assert_eq!(result, FixResult::Ok { changed: false });
        assert!(fixed.is_empty());
    }

    #[test]
    fn test_fix_literals_large_at_least_one_cardinality_uses_fast_guard() {
        let terms = (1..=4096).map(|var| term(1, lit(var))).collect::<Vec<_>>();
        let constraint = ge(terms, 1);

        assert_eq!(classify_trivial(&constraint), TrivialClass::NonTrivial);
        assert!(linear_row_cannot_force_fast(&constraint));

        let original = constraint.clone();
        let mut constraints = vec![constraint];
        let mut fixed = HashMap::new();
        let result = fix_literals(&mut constraints, &mut fixed);

        assert_eq!(result, FixResult::Ok { changed: false });
        assert!(fixed.is_empty());
        assert_eq!(constraints, vec![original]);
    }

    #[test]
    fn test_fix_literals_large_unit_cardinality_threshold_uses_fast_guard() {
        let terms = (1..=4096).map(|var| term(1, lit(var))).collect::<Vec<_>>();
        let constraint = ge(terms, 2048);

        assert_eq!(classify_trivial(&constraint), TrivialClass::NonTrivial);
        assert!(linear_row_cannot_force_fast(&constraint));

        let original = constraint.clone();
        let mut constraints = vec![constraint];
        let mut fixed = HashMap::new();
        let result = fix_literals(&mut constraints, &mut fixed);

        assert_eq!(result, FixResult::Ok { changed: false });
        assert!(fixed.is_empty());
        assert_eq!(constraints, vec![original]);
    }

    #[test]
    fn test_fix_literals_large_weighted_slack_uses_fast_guard() {
        let mut terms = Vec::with_capacity(4096);
        let mut total = 0i128;
        let mut largest = 0i128;
        for var in 1..=4096 {
            let coeff = if var % 5 == 0 { 7 } else { 3 };
            total += i128::from(coeff);
            largest = largest.max(i128::from(coeff));
            terms.push(term(coeff, lit(var)));
        }
        let rhs = i128::try_from(total - largest).expect("test rhs fits in i128");
        let constraint = ge(terms, rhs);

        assert_eq!(classify_trivial(&constraint), TrivialClass::NonTrivial);
        assert!(linear_row_cannot_force_fast(&constraint));

        let original = constraint.clone();
        let mut constraints = vec![constraint];
        let mut fixed = HashMap::new();
        let result = fix_literals(&mut constraints, &mut fixed);

        assert_eq!(result, FixResult::Ok { changed: false });
        assert!(fixed.is_empty());
        assert_eq!(constraints, vec![original]);
    }

    // --- Subsumption tests ---

    #[test]
    fn test_subsumption_removes_weaker_same_lhs() {
        let mut constraints = vec![
            ge(vec![term(3, lit(1)), term(2, lit(2))], 3),
            ge(vec![term(3, lit(1)), term(2, lit(2))], 2),
        ];
        remove_subsumed(&mut constraints);
        assert_eq!(constraints.len(), 1);
        assert_eq!(constraints[0].terms[0].coeff, 3);
        assert_eq!(constraints[0].rhs, 3);
    }

    #[test]
    fn test_canonical_shape_matches_unsorted_linear_constraint() {
        let sorted = ge(vec![term(3, lit(1)), term(2, neg(2)), term(4, lit(3))], 3);
        let unsorted = ge(vec![term(4, lit(3)), term(3, lit(1)), term(2, neg(2))], 3);

        assert_eq!(
            canonical_constraint_shape(&sorted),
            canonical_constraint_shape(&unsorted),
            "fast-path sorted linear keys must match the general canonical form"
        );
    }

    #[test]
    fn test_canonical_shape_matches_duplicate_linear_terms() {
        let first = ge(vec![term(2, lit(1)), term(3, lit(1)), term(1, lit(2))], 3);
        let second = ge(vec![term(3, lit(1)), term(2, lit(1)), term(1, lit(2))], 3);

        assert_eq!(
            canonical_constraint_shape(&first),
            canonical_constraint_shape(&second),
            "repeated-literal linear constraints must use the general canonical form"
        );
    }

    #[test]
    fn test_canonical_linear_shape_uses_single_lit_keys() {
        let sorted = ge(vec![term(3, lit(1)), term(2, neg(2)), term(4, lit(3))], 3);
        let unsorted = ge(vec![term(4, lit(3)), term(3, lit(1)), term(2, neg(2))], 3);

        let sorted_key = canonical_constraint_shape(&sorted);
        let unsorted_key = canonical_constraint_shape(&unsorted);

        assert_eq!(sorted_key, unsorted_key);
        assert!(
            sorted_key
                .iter()
                .all(|(_, lits)| matches!(lits, CanonicalLitsKey::Single(_))),
            "linear shape keys should avoid per-term product vectors"
        );
    }

    #[test]
    fn test_subsumption_fast_linear_shape_keeps_strongest_rhs() {
        let mut constraints = vec![
            ge(vec![term(3, lit(1)), term(2, neg(2)), term(4, lit(3))], 4),
            ge(vec![term(3, lit(1)), term(2, neg(2)), term(4, lit(3))], 6),
        ];

        remove_subsumed(&mut constraints);

        assert_eq!(constraints.len(), 1);
        assert_eq!(constraints[0].rhs, 6);
    }

    #[test]
    fn test_subsumption_keeps_different_weighted_constraints() {
        // Genuinely incomparable pair: neither row implies the other under any
        // single multiplier (2x+y>=2 allows x=1,y=0 which violates x+2y>=2,
        // and x+2y>=2 allows x=0,y=1 which violates 2x+y>=2).
        let mut constraints = vec![
            ge(vec![term(2, lit(1)), term(1, lit(2))], 2),
            ge(vec![term(1, lit(1)), term(2, lit(2))], 2),
        ];
        remove_subsumed(&mut constraints);
        assert_eq!(constraints.len(), 2);
    }

    #[test]
    fn test_subsumption_scaled_weighted_dominance_deletes_implied_row() {
        // x1 + x2 >= 2 implies 100x1 + 100x2 >= 100 (multiplier 50), so the
        // weaker row is deleted by generalized weighted dominance.
        let mut constraints = vec![
            ge(vec![term(100, lit(1)), term(100, lit(2))], 100),
            ge(vec![term(1, lit(1)), term(1, lit(2))], 2),
        ];
        remove_subsumed(&mut constraints);
        assert_eq!(
            constraints,
            vec![ge(vec![term(1, lit(1)), term(1, lit(2))], 2)]
        );
    }

    #[test]
    fn test_subsumption_equal_support_weighted_dominance() {
        // 2x1 + x2 >= 2 implies x1 + x2 >= 1 (multiplier 1/2): every model of
        // the first (x1=1, any x2) satisfies the second.
        let mut constraints = vec![
            ge(vec![term(2, lit(1)), term(1, lit(2))], 2),
            ge(vec![term(1, lit(1)), term(1, lit(2))], 1),
        ];
        remove_subsumed(&mut constraints);
        assert_eq!(
            constraints,
            vec![ge(vec![term(2, lit(1)), term(1, lit(2))], 2)]
        );
    }

    #[test]
    fn test_subsumption_weighted_superset_dominance_scaled() {
        // x1 + x2 >= 1 implies 3x1 + 3x2 + x3 >= 2 (multiplier 2; the extra
        // literal only adds), so the superset row is deleted.
        let mut constraints = vec![
            ge(vec![term(1, lit(1)), term(1, lit(2))], 1),
            ge(vec![term(3, lit(1)), term(3, lit(2)), term(1, lit(3))], 2),
        ];
        remove_subsumed(&mut constraints);
        assert_eq!(
            constraints,
            vec![ge(vec![term(1, lit(1)), term(1, lit(2))], 1)]
        );
    }

    #[test]
    fn test_subsumption_weighted_dominance_overflow_falls_back_to_unit_multiplier() {
        // Products b_i*d and a_i*e overflow i128, so the scaled certificate is
        // unavailable; the uniform multiplier-1 fallback still applies
        // (coefficients dominate termwise and the degree is no larger).
        let big = i128::MAX / 2;
        let mut constraints = vec![
            ge(vec![term(big, lit(1)), term(big, lit(2))], big),
            ge(
                vec![term(big, lit(1)), term(big, lit(2)), term(1, lit(3))],
                big - 1,
            ),
        ];
        remove_subsumed(&mut constraints);
        assert_eq!(
            constraints,
            vec![ge(vec![term(big, lit(1)), term(big, lit(2))], big)]
        );
    }

    #[test]
    fn test_subsumption_degree_matters() {
        // C1: 3*x1 + 2*x2 >= 2
        // C2: 3*x1 + 2*x2 >= 3
        // C2 does NOT subsume C1 (same coefficients but higher degree).
        // C1 does NOT subsume C2 (lower degree).
        let mut constraints = vec![
            ge(vec![term(3, lit(1)), term(2, lit(2))], 2),
            ge(vec![term(3, lit(1)), term(2, lit(2))], 3),
        ];
        remove_subsumed(&mut constraints);
        // C2 subsumes C1 because coefficients are same but C2.rhs (3) > C1.rhs (2),
        // and every solution of C2 satisfies C1.
        assert_eq!(constraints.len(), 1);
        assert_eq!(constraints[0].rhs, 3);
    }

    #[test]
    fn test_subsumption_removes_weaker_cardinality_superset() {
        let mut constraints = vec![
            ge(vec![term(1, lit(1)), term(1, lit(2))], 1),
            ge(vec![term(1, lit(1)), term(1, lit(2)), term(1, lit(3))], 1),
        ];
        remove_subsumed(&mut constraints);
        assert_eq!(constraints.len(), 1);
        assert_eq!(
            constraints[0],
            ge(vec![term(1, lit(1)), term(1, lit(2))], 1)
        );
    }

    #[test]
    fn test_subsumption_removes_cardinality_superset_with_lower_rhs() {
        let mut constraints = vec![
            ge(vec![term(1, lit(1)), term(1, lit(2))], 2),
            ge(vec![term(1, lit(1)), term(1, lit(2)), term(1, lit(3))], 1),
        ];
        remove_subsumed(&mut constraints);
        assert_eq!(constraints.len(), 1);
        assert_eq!(
            constraints[0],
            ge(vec![term(1, lit(1)), term(1, lit(2))], 2)
        );
    }

    #[test]
    fn test_subsumption_removes_unsorted_cardinality_superset() {
        let mut constraints = vec![
            ge(vec![term(1, lit(1)), term(1, neg(2))], 1),
            ge(vec![term(1, lit(3)), term(1, neg(2)), term(1, lit(1))], 1),
        ];
        remove_subsumed(&mut constraints);
        assert_eq!(constraints.len(), 1);
        assert_eq!(
            constraints[0],
            ge(vec![term(1, lit(1)), term(1, neg(2))], 1)
        );
    }

    #[test]
    fn test_subsumption_cardinality_key_matches_unsorted_support() {
        let sorted = ge(vec![term(1, lit(1)), term(1, neg(2)), term(1, lit(3))], 1);
        let unsorted = ge(vec![term(1, lit(3)), term(1, neg(2)), term(1, lit(1))], 1);

        let sorted_key = canonical_subsumption_shape(&sorted);
        let unsorted_key = canonical_subsumption_shape(&unsorted);

        assert_eq!(sorted_key, unsorted_key);
        assert_eq!(
            sorted_key.cardinality_support(),
            Some([(1, false), (2, true), (3, false)].as_slice())
        );
    }

    #[test]
    fn test_subsumption_large_cardinality_uses_shape_support() {
        let small = ge(
            (1..=2048)
                .rev()
                .map(|var| term(1, if var % 2 == 0 { neg(var) } else { lit(var) }))
                .collect(),
            1,
        );
        let large = ge(
            (1..=4096)
                .rev()
                .map(|var| term(1, if var % 2 == 0 { neg(var) } else { lit(var) }))
                .collect(),
            1,
        );

        let small_shape = canonical_constraint_shape(&small);
        let large_shape = canonical_constraint_shape(&large);
        let small_support = canonical_cardinality_shape_support(&small_shape)
            .expect("unit linear shape should be cardinality support");
        let large_support = canonical_cardinality_shape_support(&large_shape)
            .expect("unit linear shape should be cardinality support");
        let owned_large_support =
            canonical_cardinality_support(&large).expect("large row should be cardinality");
        let shape_large_support = large_support
            .iter()
            .map(cardinality_shape_lit)
            .collect::<Vec<_>>();

        assert_eq!(shape_large_support, owned_large_support);
        assert!(is_cardinality_shape_subset(small_support, large_support));

        let mut constraints = vec![small.clone(), large];
        remove_subsumed(&mut constraints);
        assert_eq!(constraints, vec![small]);
    }

    #[test]
    fn test_subsumption_keeps_cardinality_superset_with_higher_rhs() {
        let mut constraints = vec![
            ge(vec![term(1, lit(1)), term(1, lit(2))], 1),
            ge(vec![term(1, lit(1)), term(1, lit(2)), term(1, lit(3))], 2),
        ];
        remove_subsumed(&mut constraints);
        assert_eq!(constraints.len(), 2);
    }

    #[test]
    fn test_subsumption_weighted_superset_now_covered_by_weighted_dominance() {
        // Historical behavior kept both rows (the second is weighted, outside
        // the unit-coefficient cardinality rule). Generalized weighted
        // dominance proves x1 + x2 >= 1 implies 2x1 + x2 + x3 >= 1 and deletes
        // the superset row.
        let mut constraints = vec![
            ge(vec![term(1, lit(1)), term(1, lit(2))], 1),
            ge(vec![term(2, lit(1)), term(1, lit(2)), term(1, lit(3))], 1),
        ];
        remove_subsumed(&mut constraints);
        assert_eq!(
            constraints,
            vec![ge(vec![term(1, lit(1)), term(1, lit(2))], 1)]
        );
    }

    #[test]
    fn test_weighted_dominance_candidate_over_approximates_weighted_support() {
        // The cap pre-scan must count every row whose `dominance_support`
        // would be weighted (non-unit coefficients); over-counting rows that
        // `dominance_support` rejects (duplicate literal keys) is allowed.
        let weighted = ge(vec![term(2, lit(1)), term(1, lit(2))], 2);
        assert!(is_weighted_dominance_candidate(&weighted));
        assert!(dominance_support(&weighted)
            .is_some_and(|support| support.iter().any(|(_, coeff)| *coeff != 1)));

        // Unit-coefficient (cardinality) rows are not weighted candidates.
        let cardinality = ge(vec![term(1, lit(1)), term(1, lit(2))], 1);
        assert!(!is_weighted_dominance_candidate(&cardinality));
        assert!(dominance_support(&cardinality)
            .is_some_and(|support| support.iter().all(|(_, coeff)| *coeff == 1)));

        // Non-linear, non-positive-degree, and non-positive-coefficient rows
        // are excluded by both the pre-scan and the support builder.
        for row in [
            ge(vec![prod(2, vec![lit(1), lit(2)]), term(3, lit(3))], 2),
            ge(vec![term(2, lit(1)), term(3, lit(2))], 0),
            ge(vec![term(-2, lit(1)), term(3, lit(2))], 1),
        ] {
            assert!(!is_weighted_dominance_candidate(&row));
            assert!(dominance_support(&row).is_none());
        }

        // Duplicate-literal rows: counted by the pre-scan (safe
        // over-approximation) even though the support builder rejects them.
        let duplicate = ge(vec![term(2, lit(1)), term(3, lit(1))], 2);
        assert!(is_weighted_dominance_candidate(&duplicate));
        assert!(dominance_support(&duplicate).is_none());
    }

    #[test]
    fn test_weighted_dominance_cap_skips_weighted_rows_but_keeps_cardinality() {
        // Above MAX_WEIGHTED_DOMINANCE_ENTRIES weighted candidates, the pass
        // must (a) not delete via weighted dominance and (b) still delete
        // dominated cardinality rows — the pre-generalization behavior. This
        // pins the pre-scan cap path (weighted supports are never built).
        let weighted_rows = MAX_WEIGHTED_DOMINANCE_ENTRIES + 1;
        let mut constraints = Vec::with_capacity(weighted_rows + 3);
        // Weighted dominated pair: x1 + x2 >= 2 implies 5x1 + 5x2 >= 5, but
        // above the cap the implied row must SURVIVE.
        constraints.push(ge(vec![term(5, lit(1)), term(5, lit(2))], 5));
        constraints.push(ge(vec![term(1, lit(1)), term(1, lit(2))], 2));
        // Cardinality dominated pair: x3 + x4 >= 1 implies x3 + x4 + x5 >= 1;
        // the superset row must still be deleted above the cap.
        constraints.push(ge(vec![term(1, lit(3)), term(1, lit(4))], 1));
        constraints.push(ge(
            vec![term(1, lit(3)), term(1, lit(4)), term(1, lit(5))],
            1,
        ));
        // Distinct-variable weighted filler rows to push past the cap.
        for i in 0..weighted_rows as u32 {
            let v = 10 + 2 * i;
            constraints.push(ge(vec![term(2, lit(v)), term(1, lit(v + 1))], 2));
        }

        let expected_len = constraints.len() - 1; // only the cardinality superset goes
        remove_subsumed(&mut constraints);
        assert_eq!(constraints.len(), expected_len);
        assert!(
            constraints.contains(&ge(vec![term(5, lit(1)), term(5, lit(2))], 5)),
            "above the cap, weighted dominance must be skipped (row kept)"
        );
        assert!(
            !constraints.contains(&ge(
                vec![term(1, lit(3)), term(1, lit(4)), term(1, lit(5))],
                1
            )),
            "cardinality dominance must still fire above the cap"
        );
    }

    // --- Duplicate removal tests ---

    #[test]
    fn test_remove_duplicates() {
        let mut constraints = vec![
            ge(vec![term(2, lit(1)), term(3, lit(2))], 3),
            ge(vec![term(2, lit(1)), term(3, lit(2))], 3),
        ];
        remove_duplicates(&mut constraints);
        assert_eq!(constraints.len(), 1);
    }

    #[test]
    fn test_remove_duplicates_keeps_different() {
        let mut constraints = vec![
            ge(vec![term(2, lit(1)), term(3, lit(2))], 3),
            ge(vec![term(2, lit(1)), term(3, lit(2))], 4),
        ];
        remove_duplicates(&mut constraints);
        assert_eq!(constraints.len(), 2);
    }

    #[test]
    fn test_remove_duplicates_handles_non_linear_constraints() {
        let mut constraints = vec![
            ge(
                vec![PbTerm {
                    coeff: 1,
                    lits: vec![lit(1), neg(2)],
                }],
                1,
            ),
            ge(
                vec![PbTerm {
                    coeff: 1,
                    lits: vec![neg(2), lit(1)],
                }],
                1,
            ),
        ];
        remove_duplicates(&mut constraints);
        assert_eq!(constraints.len(), 1);
    }

    // --- Integration tests ---

    #[test]
    fn test_preprocess_full_pipeline_satisfiable() {
        // Instance: 6*x1 + 4*x2 + 3*x3 >= 5 (plus a complement row so the
        // variables are not pure and the tightened row stays observable; no
        // two coefficients of {5,4,3} share a divisor, so the residue-GCD
        // rewrite does not apply and saturation stays visible).
        // After tightening: 5*x1 + 4*x2 + 3*x3 >= 5
        let instance = make_instance(
            3,
            vec![
                ge(vec![term(6, lit(1)), term(4, lit(2)), term(3, lit(3))], 5),
                ge(vec![term(1, neg(1)), term(1, neg(2)), term(1, neg(3))], 1),
            ],
        );

        match preprocess(&instance) {
            PreprocessResult::Simplified {
                instance: result, ..
            } => {
                assert_eq!(result.constraints.len(), 2);
                // Coefficient x1 should be tightened from 6 to 5.
                let c = result
                    .constraints
                    .iter()
                    .find(|c| c.rhs == 5)
                    .expect("tightened row must survive");
                assert!(c.terms.iter().all(|t| t.coeff <= c.rhs));
            }
            PreprocessResult::Unsatisfiable => panic!("should not be UNSAT"),
            PreprocessResult::Interrupted => panic!("should not be interrupted"),
        }
    }

    #[test]
    fn test_preprocess_trivially_unsat() {
        // 1*x1 + 1*x2 >= 5 (max sum = 2 < 5)
        let instance = make_instance(2, vec![ge(vec![term(1, lit(1)), term(1, lit(2))], 5)]);

        assert_eq!(preprocess(&instance), PreprocessResult::Unsatisfiable);
    }

    #[test]
    fn test_preprocess_round_trip_bails_out_on_nontrivial_i64_min_normalization() {
        // The PARSER now rejects an i128::MIN coefficient outright (symmetric
        // magnitude cap, see `parse_i64_ascii`: a value whose negation does not
        // exist in the domain is not supportable), so this instance can no
        // longer arrive via `parse_opb`. A library consumer can still construct
        // it directly, and preprocess must keep bailing out to a clean
        // round-trip rather than normalize the un-negatable coefficient.
        let instance = make_instance(1, vec![ge(vec![term(i128::MIN, lit(1))], 0)]);

        match preprocess(&instance) {
            PreprocessResult::Simplified {
                instance: result,
                fixed_literals,
            } => {
                assert_eq!(result, instance);
                assert!(fixed_literals.is_empty());
            }
            PreprocessResult::Unsatisfiable => panic!("should preserve the original instance"),
            PreprocessResult::Interrupted => panic!("should not be interrupted"),
        }
    }

    #[test]
    fn test_preprocess_round_trip_eq_with_i64_min_rhs_is_unsat() {
        let input = "* #variable= 1 #constraint= 1\n+1 x1 = -9223372036854775808 ;\n";
        let instance = parse_opb(input).expect("should parse i128::MIN rhs");
        assert_eq!(preprocess(&instance), PreprocessResult::Unsatisfiable);
    }

    #[test]
    fn test_preprocess_removes_trivially_satisfied() {
        // Constraint 1: x1 + x2 >= 1 (non-trivial)
        // Constraint 2: x1 + x2 >= 0 (trivially satisfied)
        // Constraint 3: ~x1 + ~x2 >= 1 (keeps the variables impure)
        let instance = make_instance(
            2,
            vec![
                ge(vec![term(1, lit(1)), term(1, lit(2))], 1),
                ge(vec![term(1, lit(1)), term(1, lit(2))], 0),
                ge(vec![term(1, neg(1)), term(1, neg(2))], 1),
            ],
        );

        match preprocess(&instance) {
            PreprocessResult::Simplified {
                instance: result, ..
            } => {
                assert_eq!(result.constraints.len(), 2);
                assert!(result
                    .constraints
                    .contains(&ge(vec![term(1, lit(1)), term(1, lit(2))], 1)));
            }
            PreprocessResult::Unsatisfiable => panic!("should not be UNSAT"),
            PreprocessResult::Interrupted => panic!("should not be interrupted"),
        }
    }

    #[test]
    fn test_preprocess_gcd_strengthening_integrated() {
        // 6*x1 + 4*x2 + 2*x3 >= 6 (plus a complement row so the variables
        // are not pure and the strengthened row stays observable).
        // Tightening: all coeffs <= 6, no change.
        // GCD(6,4,2) = 2 -> 3*x1 + 2*x2 + 1*x3 >= 3, where no two of {3,2,1}
        // share a divisor (the residue rewrite does not apply).
        let instance = make_instance(
            3,
            vec![
                ge(vec![term(6, lit(1)), term(4, lit(2)), term(2, lit(3))], 6),
                ge(vec![term(1, neg(1)), term(1, neg(2)), term(1, neg(3))], 1),
            ],
        );

        match preprocess(&instance) {
            PreprocessResult::Simplified {
                instance: result, ..
            } => {
                assert_eq!(result.constraints.len(), 2);
                let c = result
                    .constraints
                    .iter()
                    .find(|c| c.rhs == 3)
                    .expect("gcd-strengthened row must survive");
                // After GCD: 3*x1 + 2*x2 + 1*x3 >= 3
                assert_eq!(c.terms[0].coeff, 3);
                assert_eq!(c.terms[1].coeff, 2);
                assert_eq!(c.terms[2].coeff, 1);
            }
            PreprocessResult::Unsatisfiable => panic!("should not be UNSAT"),
            PreprocessResult::Interrupted => panic!("should not be interrupted"),
        }
    }

    #[test]
    fn test_preprocess_literal_fixing_simplifies() {
        // x1 >= 1 forces x1=true. Then x1 + x2 >= 2 simplifies to x2 >= 1,
        // which forces x2=true. Both constraints should be removed.
        let instance = make_instance(
            2,
            vec![
                ge(vec![term(1, lit(1))], 1),
                ge(vec![term(1, lit(1)), term(1, lit(2))], 2),
            ],
        );

        match preprocess(&instance) {
            PreprocessResult::Simplified {
                instance: result, ..
            } => {
                // Both constraints should be satisfied and removed.
                assert_eq!(
                    result.constraints.len(),
                    0,
                    "all constraints should be removed after fixing x1=T, x2=T"
                );
            }
            PreprocessResult::Unsatisfiable => panic!("should not be UNSAT"),
            PreprocessResult::Interrupted => panic!("should not be interrupted"),
        }
    }

    #[test]
    fn test_preprocess_conflict_from_fixing() {
        // x1 >= 1 forces x1=true
        // ~x1 >= 1 forces x1=false
        // Conflict during literal fixing.
        let instance = make_instance(
            1,
            vec![ge(vec![term(1, lit(1))], 1), ge(vec![term(1, neg(1))], 1)],
        );

        assert_eq!(preprocess(&instance), PreprocessResult::Unsatisfiable);
    }

    #[test]
    fn test_preprocess_with_equality_constraint() {
        // x1 + x2 = 1 -> split into x1 + x2 >= 1 AND ~x1 + ~x2 >= 1
        let instance = make_instance(
            2,
            vec![eq_constraint(vec![term(1, lit(1)), term(1, lit(2))], 1)],
        );

        match preprocess(&instance) {
            PreprocessResult::Simplified {
                instance: result, ..
            } => {
                // The equality is split into two >= constraints.
                // ~x1 + ~x2 >= 1 means at most one is true.
                // x1 + x2 >= 1 means at least one is true.
                // No constraint is trivial, both should remain.
                assert!(
                    !result.constraints.is_empty(),
                    "equality should produce non-trivial constraints"
                );
            }
            PreprocessResult::Unsatisfiable => panic!("should not be UNSAT"),
            PreprocessResult::Interrupted => panic!("should not be interrupted"),
        }
    }

    #[test]
    fn test_preprocess_empty_instance() {
        let instance = make_instance(0, vec![]);
        match preprocess(&instance) {
            PreprocessResult::Simplified {
                instance: result, ..
            } => {
                assert!(result.constraints.is_empty());
            }
            PreprocessResult::Unsatisfiable => panic!("empty instance should be SAT"),
            PreprocessResult::Interrupted => panic!("should not be interrupted"),
        }
    }

    #[test]
    fn test_preprocess_preserves_objective() {
        let instance = PbInstance {
            num_vars: 2,
            num_constraints: 1,
            constraints: vec![ge(vec![term(1, lit(1)), term(1, lit(2))], 1)],
            objective: Some(PbObjective {
                terms: vec![term(1, lit(1)), term(2, lit(2))],
            }),
        };

        match preprocess(&instance) {
            PreprocessResult::Simplified {
                instance: result, ..
            } => {
                assert!(
                    result.objective.is_some(),
                    "objective should be preserved through preprocessing"
                );
            }
            PreprocessResult::Unsatisfiable => panic!("should not be UNSAT"),
            PreprocessResult::Interrupted => panic!("should not be interrupted"),
        }
    }

    #[test]
    fn test_preprocess_negative_coefficients_normalized() {
        // -1*x1 + 2*x2 + 3*x3 >= 2  ->  normalized to 1*~x1 + 2*x2 + 3*x3 >= 3
        // No literal is forced. A complement row keeps the variables impure so
        // the normalized row stays observable; no two of {1,2,3} share a
        // divisor, so the residue-GCD rewrite does not apply.
        let instance = make_instance(
            3,
            vec![
                PbConstraint {
                    terms: vec![term(-1, lit(1)), term(2, lit(2)), term(3, lit(3))],
                    rel: PbRel::Ge,
                    rhs: 2,
                },
                ge(vec![term(1, lit(1)), term(1, neg(2)), term(1, neg(3))], 1),
            ],
        );

        match preprocess(&instance) {
            PreprocessResult::Simplified {
                instance: result, ..
            } => {
                assert_eq!(result.constraints.len(), 2);
                let c = result
                    .constraints
                    .iter()
                    .find(|c| c.rhs == 3)
                    .expect("normalized row must survive");
                assert!(
                    c.terms.iter().all(|t| t.coeff > 0),
                    "all coefficients should be positive after normalization"
                );
            }
            PreprocessResult::Unsatisfiable => panic!("should not be UNSAT"),
            PreprocessResult::Interrupted => panic!("should not be interrupted"),
        }
    }

    #[test]
    fn test_public_style_nested_at_least_one_frontier_prunes_supersets() {
        // Frontier pruning at the subsumption-pass level: each family keeps
        // its smallest at-least-one row; supersets are dominated. The weighted
        // row (2x8 + x9 + x10 >= 1) is not related to any other row.
        let mut constraints = vec![
            ge(vec![term(1, lit(1)), term(1, lit(2))], 1),
            ge(vec![term(1, lit(1)), term(1, lit(2)), term(1, lit(3))], 1),
            ge(
                vec![
                    term(1, lit(1)),
                    term(1, lit(2)),
                    term(1, lit(3)),
                    term(1, lit(4)),
                ],
                1,
            ),
            ge(vec![term(1, lit(5)), term(1, lit(6))], 1),
            ge(vec![term(1, lit(5)), term(1, lit(6)), term(1, lit(7))], 1),
            ge(vec![term(2, lit(8)), term(1, lit(9)), term(1, lit(10))], 1),
        ];
        remove_subsumed(&mut constraints);

        assert_eq!(constraints.len(), 3);
        assert!(constraints.contains(&ge(vec![term(1, lit(1)), term(1, lit(2))], 1)));
        assert!(constraints.contains(&ge(vec![term(1, lit(5)), term(1, lit(6))], 1)));
        assert!(constraints.contains(&ge(
            vec![term(2, lit(8)), term(1, lit(9)), term(1, lit(10))],
            1
        )));
    }

    #[test]
    fn test_preprocess_public_style_all_positive_family_collapses_via_pure_literals() {
        // End-to-end, the all-positive at-least-one families are fully solved
        // by pure-literal elimination: every variable is fixed true and every
        // row is satisfied and removed. The fixings must form a model of the
        // original instance.
        let instance = make_instance(
            10,
            vec![
                ge(vec![term(1, lit(1)), term(1, lit(2))], 1),
                ge(vec![term(1, lit(1)), term(1, lit(2)), term(1, lit(3))], 1),
                ge(vec![term(1, lit(5)), term(1, lit(6))], 1),
                ge(vec![term(2, lit(8)), term(1, lit(9)), term(1, lit(10))], 1),
            ],
        );

        match preprocess_one_shot(&instance).0 {
            PreprocessResult::Simplified {
                instance: result,
                fixed_literals,
            } => {
                assert!(
                    result.constraints.is_empty(),
                    "pure-literal elimination should satisfy every row"
                );
                // Every fixing must be true-polarity and the induced assignment
                // must satisfy the original instance.
                assert!(fixed_literals.values().all(|&value| value));
                let assignment: Vec<bool> = (1..=instance.num_vars)
                    .map(|var| fixed_literals.get(&var).copied().unwrap_or(false))
                    .collect();
                assert!(crate::verify_all_constraints(
                    &instance.constraints,
                    &assignment
                ));
            }
            PreprocessResult::Unsatisfiable => panic!("should not be UNSAT"),
            PreprocessResult::Interrupted => panic!("should not be interrupted"),
        }
    }

    #[test]
    fn test_public_style_negated_neighborhood_frontier_prunes_supersets() {
        let mut constraints = vec![
            ge(vec![term(1, neg(1)), term(1, neg(2))], 1),
            ge(vec![term(1, neg(1)), term(1, neg(2)), term(1, neg(3))], 1),
            ge(
                vec![
                    term(1, neg(1)),
                    term(1, neg(2)),
                    term(1, neg(3)),
                    term(1, neg(4)),
                ],
                1,
            ),
        ];
        remove_subsumed(&mut constraints);

        assert_eq!(
            constraints,
            vec![ge(vec![term(1, neg(1)), term(1, neg(2))], 1)]
        );
    }

    #[test]
    fn test_preprocess_negated_neighborhood_collapses_via_pure_literals() {
        // End-to-end, the negated-only family is fully solved by pure-literal
        // elimination (every variable fixed false satisfies every row).
        let instance = make_instance(
            4,
            vec![
                ge(vec![term(1, neg(1)), term(1, neg(2))], 1),
                ge(vec![term(1, neg(1)), term(1, neg(2)), term(1, neg(3))], 1),
            ],
        );

        match preprocess_one_shot(&instance).0 {
            PreprocessResult::Simplified {
                instance: result,
                fixed_literals,
            } => {
                assert!(result.constraints.is_empty());
                assert!(fixed_literals.iter().all(|(_, &value)| !value));
                let assignment: Vec<bool> = (1..=instance.num_vars)
                    .map(|var| fixed_literals.get(&var).copied().unwrap_or(false))
                    .collect();
                assert!(crate::verify_all_constraints(
                    &instance.constraints,
                    &assignment
                ));
            }
            PreprocessResult::Unsatisfiable => panic!("should not be UNSAT"),
            PreprocessResult::Interrupted => panic!("should not be interrupted"),
        }
    }

    #[test]
    fn test_nested_frontier_cardinality_family_collapses() {
        let mut constraints = nested_frontier_instance(6, 12).constraints;
        remove_subsumed(&mut constraints);

        assert_eq!(constraints.len(), 6);
        for family in 0..6 {
            let base = family * (12 + 2) + 1;
            assert!(constraints.contains(&ge(vec![term(1, lit(base)), term(1, lit(base + 1))], 1)));
        }
    }

    #[test]
    fn test_removes_exact_duplicates_via_subsumption_pass() {
        let mut constraints = vec![
            ge(vec![term(1, lit(1)), term(1, lit(2))], 1),
            ge(vec![term(1, lit(1)), term(1, lit(2))], 1),
            ge(vec![term(1, lit(1)), term(1, lit(2)), term(1, lit(3))], 1),
        ];
        remove_subsumed(&mut constraints);

        assert_eq!(
            constraints,
            vec![ge(vec![term(1, lit(1)), term(1, lit(2))], 1)]
        );
    }

    #[test]
    fn test_preprocess_complementary_literals_enable_fixing() {
        // 3*x1 + 2*~x1 >= 3  ->  x1 >= 1 after complementary-literal elimination,
        // which should then be fixed and removed.
        let instance = make_instance(1, vec![ge(vec![term(3, lit(1)), term(2, neg(1))], 3)]);

        match preprocess(&instance) {
            PreprocessResult::Simplified {
                instance: result,
                fixed_literals,
            } => {
                assert_eq!(fixed_literals.get(&1), Some(&true));
                assert!(
                    result.constraints.is_empty(),
                    "the strengthened unit should be propagated away"
                );
            }
            PreprocessResult::Unsatisfiable => panic!("should not be UNSAT"),
            PreprocessResult::Interrupted => panic!("should not be interrupted"),
        }
    }

    #[test]
    fn test_preprocess_complementary_literals_can_trivialize_constraint() {
        // x1 + ~x1 >= 1 is always true once normalized and compacted.
        let instance = make_instance(1, vec![ge(vec![term(1, lit(1)), term(1, neg(1))], 1)]);

        match preprocess(&instance) {
            PreprocessResult::Simplified {
                instance: result, ..
            } => {
                assert!(
                    result.constraints.is_empty(),
                    "complementary literals should reduce the tautology away"
                );
            }
            PreprocessResult::Unsatisfiable => panic!("should not be UNSAT"),
            PreprocessResult::Interrupted => panic!("should not be interrupted"),
        }
    }

    #[test]
    fn test_preprocess_combined_tighten_then_gcd() {
        // 12*x1 + 8*x2 + 6*x3 >= 6 (plus a complement row so the variables are
        // not pure and the rewritten row stays observable).
        // Step 1: tighten 12->6, 8->6: 6*x1 + 6*x2 + 6*x3 >= 6
        // Step 2: GCD(6,6,6)=6: x1 + x2 + x3 >= 1 (a clause; the residue
        // rewrite does not apply to unit coefficients).
        let instance = make_instance(
            3,
            vec![
                ge(vec![term(12, lit(1)), term(8, lit(2)), term(6, lit(3))], 6),
                ge(vec![term(1, neg(1)), term(1, neg(2)), term(1, neg(3))], 1),
            ],
        );

        match preprocess(&instance) {
            PreprocessResult::Simplified {
                instance: result, ..
            } => {
                assert_eq!(result.constraints.len(), 2);
                assert!(result.constraints.contains(&ge(
                    vec![term(1, lit(1)), term(1, lit(2)), term(1, lit(3))],
                    1
                )));
            }
            PreprocessResult::Unsatisfiable => panic!("should not be UNSAT"),
            PreprocessResult::Interrupted => panic!("should not be interrupted"),
        }
    }

    // --- Helper function tests ---

    #[test]
    fn test_preprocess_interruptible_honors_immediate_stop() {
        let instance = make_instance(2, vec![ge(vec![term(1, lit(1)), term(1, lit(2))], 1)]);
        assert_eq!(
            preprocess_interruptible(&instance, || true),
            PreprocessResult::Interrupted
        );
    }

    #[test]
    fn test_remove_subsumed_interruptible_leaves_constraints_unchanged() {
        let mut constraints = vec![
            ge(vec![term(1, lit(1)), term(1, lit(2))], 1),
            ge(vec![term(1, lit(1)), term(1, lit(2)), term(1, lit(3))], 1),
            ge(vec![term(1, lit(2)), term(1, lit(3)), term(1, lit(4))], 1),
        ];
        let original = constraints.clone();
        let mut checks = 0u32;

        let mut stats = PreprocessStats::default();
        let interrupted = remove_subsumed_interruptible(&mut constraints, &mut stats, &mut || {
            checks += 1;
            checks >= 2
        });

        assert!(interrupted, "subsumption pass should be interruptible");
        assert_eq!(
            constraints, original,
            "interrupted subsumption must not partially rewrite constraints"
        );
    }

    #[test]
    fn test_remove_subsumed_interruptible_leaves_constraints_unchanged_in_postings_frontier() {
        let mut constraints = nested_frontier_instance(1, 33).constraints;
        let original = constraints.clone();
        let mut checks = 0u32;

        let mut stats = PreprocessStats::default();
        let interrupted = remove_subsumed_interruptible(&mut constraints, &mut stats, &mut || {
            checks += 1;
            checks >= 10
        });

        assert!(
            interrupted,
            "subsumption pass should be interruptible inside postings frontier scanning"
        );
        assert!(
            checks >= 10,
            "stop budget should reach the postings/frontier dominance loop"
        );
        assert_eq!(
            constraints, original,
            "interrupted cardinality postings frontier must not partially rewrite constraints"
        );
    }

    #[test]
    fn test_remove_subsumed_same_length_cardinality_skips_postings_frontier() {
        let mut constraints = (0..33)
            .map(|offset| {
                let base = offset * 2 + 1;
                ge(vec![term(1, lit(base)), term(1, lit(base + 1))], 1)
            })
            .collect::<Vec<_>>();
        let original = constraints.clone();
        let mut checks = 0u32;

        let mut stats = PreprocessStats::default();
        let interrupted = remove_subsumed_interruptible(&mut constraints, &mut stats, &mut || {
            checks += 1;
            checks >= 12
        });

        assert!(
            !interrupted,
            "same-length cardinality supports should skip postings/frontier dominance"
        );
        assert_eq!(constraints, original);
        assert_eq!(
            checks, 10,
            "stop budget should only cover the shape, dedup-group, winner-collect, \
             weighted-candidate pre-scan, dominance-support, and dominance-entry scans (the \
             same-length unit-coefficient early-out is taken)"
        );
    }

    #[test]
    fn test_remove_duplicates_interruptible_leaves_constraints_unchanged() {
        let mut constraints = vec![
            ge(vec![term(1, lit(1)), term(1, lit(2))], 1),
            ge(vec![term(1, lit(1)), term(1, lit(2))], 1),
            ge(vec![term(1, lit(2)), term(1, lit(3))], 1),
        ];
        let original = constraints.clone();
        let mut checks = 0u32;

        let interrupted = remove_duplicates_interruptible(&mut constraints, &mut || {
            checks += 1;
            checks >= 1
        });

        assert!(interrupted, "duplicate pass should be interruptible");
        assert_eq!(
            constraints, original,
            "interrupted duplicate removal must not partially rewrite constraints"
        );
    }

    #[test]
    fn test_propagate_fixed_interruptible_leaves_constraints_unchanged() {
        let mut constraints = vec![
            ge(vec![term(1, lit(1)), term(1, lit(2))], 1),
            ge(vec![term(1, lit(2)), term(1, lit(3))], 1),
        ];
        let original = constraints.clone();
        let fixed = HashMap::from([(1, true)]);
        let mut checks = 0u32;

        let result = propagate_fixed_interruptible(&mut constraints, &fixed, &mut || {
            checks += 1;
            checks >= 2
        });

        assert_eq!(result, PropagateResult::Interrupted);
        assert_eq!(
            constraints, original,
            "interrupted fixed-literal propagation must not partially rewrite constraints"
        );
    }

    #[test]
    fn test_propagate_fixed_large_unaffected_row_uses_lazy_rebuild() {
        let large = ge((1..=4096).map(|var| term(1, lit(var))).collect(), 2048);
        let mut constraints = vec![large.clone(), ge(vec![term(1, lit(5000))], 1)];
        let fixed = HashMap::from([(5000, true)]);

        let mut never_stop = || false;
        let result = propagate_fixed_interruptible(&mut constraints, &fixed, &mut never_stop);

        assert_eq!(result, PropagateResult::Ok);
        assert_eq!(
            constraints,
            vec![large],
            "rows without fixed variables should be retained unchanged while affected rows rebuild"
        );
    }

    #[test]
    fn test_preprocess_interruptible_stops_during_fix_literals_scan() {
        let instance = make_instance(1, vec![ge(vec![term(1, lit(1))], 1); 65]);
        let mut checks = 0u32;

        let result = preprocess_interruptible(&instance, || {
            checks += 1;
            checks >= 10
        });

        assert_eq!(
            result,
            PreprocessResult::Interrupted,
            "preprocess should honor stop requests inside literal fixing"
        );
    }

    #[test]
    fn test_gcd_u128_basic() {
        assert_eq!(gcd_u128(12, 8), 4);
        assert_eq!(gcd_u128(6, 4), 2);
        assert_eq!(gcd_u128(7, 3), 1);
        assert_eq!(gcd_u128(0, 5), 5);
        assert_eq!(gcd_u128(5, 0), 5);
        assert_eq!(gcd_u128(0, 0), 0);
    }

    #[test]
    fn test_ceiling_div_basic() {
        assert_eq!(ceiling_div(5, 2), 3);
        assert_eq!(ceiling_div(4, 2), 2);
        assert_eq!(ceiling_div(0, 3), 0);
        assert_eq!(ceiling_div(1, 3), 1);
        assert_eq!(ceiling_div(-1, 3), 0);
        assert_eq!(ceiling_div(-5, 2), -2);
    }

    // --- Constraint type counting tests ---

    #[test]
    fn test_count_constraint_types_pure_cardinality() {
        let instance = make_instance(
            3,
            vec![
                ge(vec![term(1, lit(1)), term(1, lit(2)), term(1, lit(3))], 2),
                ge(vec![term(1, neg(1)), term(1, neg(2))], 1),
            ],
        );
        let (card, weighted) = count_constraint_types(&instance);
        assert_eq!(card, 2);
        assert_eq!(weighted, 0);
    }

    #[test]
    fn test_count_constraint_types_mixed() {
        let instance = make_instance(
            3,
            vec![
                ge(vec![term(1, lit(1)), term(1, lit(2))], 1),
                ge(vec![term(3, lit(2)), term(2, lit(3))], 4),
            ],
        );
        let (card, weighted) = count_constraint_types(&instance);
        assert_eq!(card, 1);
        assert_eq!(weighted, 1);
    }

    #[test]
    fn test_count_constraint_types_all_weighted() {
        let instance = make_instance(2, vec![ge(vec![term(5, lit(1)), term(3, lit(2))], 4)]);
        let (card, weighted) = count_constraint_types(&instance);
        assert_eq!(card, 0);
        assert_eq!(weighted, 1);
    }

    #[test]
    fn preprocess_collapses_each_nested_cardinality_frontier() {
        let instance = nested_frontier_instance(12, 8);
        let result = preprocess(&instance);

        let PreprocessResult::Simplified {
            instance: simplified,
            fixed_literals,
        } = result
        else {
            panic!("nested frontier fixture should remain satisfiable");
        };

        assert!(fixed_literals.is_empty());
        assert_eq!(
            simplified.constraints.len(),
            12,
            "each family should collapse to its minimal frontier"
        );
        assert!(simplified
            .constraints
            .iter()
            .all(|row| row.terms.len() == 2));
    }

    #[test]
    fn preprocess_collapses_deep_nested_cardinality_frontiers() {
        let instance = nested_frontier_instance(2, 128);
        let result = preprocess(&instance);

        let PreprocessResult::Simplified {
            instance: simplified,
            fixed_literals,
        } = result
        else {
            panic!("deep nested frontier fixture should remain satisfiable");
        };

        assert!(fixed_literals.is_empty());
        assert_eq!(
            simplified.constraints.len(),
            2,
            "each family should collapse to its minimal frontier"
        );
        assert!(simplified
            .constraints
            .iter()
            .all(|row| row.terms.len() == 2));
    }

    #[test]
    fn preprocess_crosses_old_pair_threshold_without_skipping_dominance() {
        // 4,002 rows cross the former 16,000,000-pair guard with only
        // two or three literals per row, keeping this a bounded fixture.
        let instance = nested_frontier_instance(2_001, 2);

        let old_constraints = old_threshold_subsumed_constraints(&instance.constraints);
        let old_propagator = build_propagator(&old_constraints);
        let result = preprocess(&instance);

        let PreprocessResult::Simplified {
            instance: simplified,
            fixed_literals,
        } = result
        else {
            panic!("threshold-crossing frontier benchmark instance should remain satisfiable");
        };

        let new_propagator = build_propagator(&simplified.constraints);

        assert!(fixed_literals.is_empty());
        assert_eq!(
            old_constraints.len(),
            instance.constraints.len(),
            "pre-#8893 thresholding should skip subset dominance above 4000 cardinality constraints"
        );
        assert_eq!(old_propagator.num_constraints(), old_constraints.len());
        assert_eq!(simplified.constraints.len(), 2_001);
        assert_eq!(
            new_propagator.num_constraints(),
            simplified.constraints.len()
        );
    }

    #[test]
    fn test_count_constraint_types_empty() {
        let instance = make_instance(0, vec![]);
        let (card, weighted) = count_constraint_types(&instance);
        assert_eq!(card, 0);
        assert_eq!(weighted, 0);
    }

    // --- Failed-literal probing tests ---

    /// Brute-force reference oracle for small instances: returns the set of
    /// satisfying assignments (as bitmasks over vars 1..=num_vars) and the
    /// minimum objective value among them (None if UNSAT).
    fn brute_force_models(instance: &PbInstance) -> (Vec<u64>, Option<i128>) {
        let n = instance.num_vars;
        assert!(n <= 20, "brute force only for tiny instances");
        let mut models = Vec::new();
        let mut best: Option<i128> = None;
        for mask in 0u64..(1u64 << n) {
            let value = |lit: &PbLit| -> bool {
                let bit = (mask >> (lit.var - 1)) & 1 == 1;
                bit != lit.negated
            };
            let sat = instance.constraints.iter().all(|c| {
                let lhs: i128 = c
                    .terms
                    .iter()
                    .map(|t| {
                        let all_true = t.lits.iter().all(&value);
                        if all_true {
                            t.coeff
                        } else {
                            0
                        }
                    })
                    .sum();
                match c.rel {
                    PbRel::Ge => lhs >= c.rhs,
                    PbRel::Eq => lhs == c.rhs,
                }
            });
            if sat {
                models.push(mask);
                if let Some(ref obj) = instance.objective {
                    let cost: i128 = obj
                        .terms
                        .iter()
                        .map(|t| {
                            if t.lits.iter().all(&value) {
                                t.coeff
                            } else {
                                0
                            }
                        })
                        .sum();
                    best = Some(best.map_or(cost, |b| b.min(cost)));
                }
            }
        }
        (models, best)
    }

    /// Runs probing directly on a set of normalized constraints (helper for
    /// focused unit tests). Returns the forced fixings and the result.
    fn run_probe(
        constraints: &[PbConstraint],
        seed_fixed: HashMap<u32, bool>,
    ) -> (HashMap<u32, bool>, ProbeResult) {
        let mut fixed = seed_fixed;
        let mut never_stop = || false;
        let result = probe_failed_literals(
            constraints,
            &mut fixed,
            &ProbeBudget::default(),
            &mut never_stop,
        );
        (fixed, result)
    }

    #[test]
    fn test_probe_forces_fixing_via_two_implications() {
        // ~x1 + x2 >= 1   (x1 -> x2)
        // ~x1 + ~x2 >= 1  (x1 -> ~x2)
        // No single constraint forces anything (unit fixing is inert), but
        // x1=true propagates x2 both true and false -> conflict, forcing x1=F.
        let constraints = vec![
            ge(vec![term(1, neg(1)), term(1, lit(2))], 1),
            ge(vec![term(1, neg(1)), term(1, neg(2))], 1),
        ];

        // Confirm plain unit fixing does NOT fix x1.
        let mut unit_fixed = HashMap::new();
        let mut unit_constraints = constraints.clone();
        assert_eq!(
            fix_literals(&mut unit_constraints, &mut unit_fixed),
            FixResult::Ok { changed: false }
        );
        assert!(unit_fixed.is_empty(), "unit fixing should not fix x1");

        let (fixed, result) = run_probe(&constraints, HashMap::new());
        assert_eq!(
            result,
            ProbeResult::Ok {
                found_fixings: true
            }
        );
        assert_eq!(fixed.get(&1), Some(&false), "probing must force x1 = false");
    }

    #[test]
    fn test_probe_chain_forces_fixing() {
        // Implication chain: x1 -> x2 -> x3, plus x3 forbidden.
        //   ~x1 + x2 >= 1   (x1 -> x2)
        //   ~x2 + x3 >= 1   (x2 -> x3)
        //   ~x3 >= 1        (x3 = false)  [this unit-fixes x3=false]
        // After x3 is fixed false, probing x1=true chains to x3=true -> conflict,
        // forcing x1=false (and x2=false).
        let constraints = vec![
            ge(vec![term(1, neg(1)), term(1, lit(2))], 1),
            ge(vec![term(1, neg(2)), term(1, lit(3))], 1),
            ge(vec![term(1, neg(3))], 1),
        ];
        // Seed with the unit-fixing of x3 = false (what the pipeline would do).
        let mut seed = HashMap::new();
        seed.insert(3u32, false);
        let (fixed, result) = run_probe(&constraints, seed);
        assert_eq!(
            result,
            ProbeResult::Ok {
                found_fixings: true
            }
        );
        assert_eq!(fixed.get(&1), Some(&false), "x1 must be forced false");
        assert_eq!(fixed.get(&2), Some(&false), "x2 must be forced false");
    }

    #[test]
    fn test_probe_detects_unsat_both_polarities_conflict() {
        // Build an instance where some variable conflicts on both polarities.
        //   ~x1 + x2 >= 1   (x1 -> x2)
        //   ~x1 + ~x2 >= 1  (x1 -> ~x2)   => x1 must be false
        //   x1 + x2 >= 1    (~x1 -> x2)
        //   x1 + ~x2 >= 1   (~x1 -> ~x2)  => x1 must be true
        // Contradiction: instance is UNSAT and probing should detect it.
        let constraints = vec![
            ge(vec![term(1, neg(1)), term(1, lit(2))], 1),
            ge(vec![term(1, neg(1)), term(1, neg(2))], 1),
            ge(vec![term(1, lit(1)), term(1, lit(2))], 1),
            ge(vec![term(1, lit(1)), term(1, neg(2))], 1),
        ];
        let (_fixed, result) = run_probe(&constraints, HashMap::new());
        assert_eq!(result, ProbeResult::Unsatisfiable);

        // Cross-check against brute force.
        let instance = make_instance(2, constraints);
        let (models, _) = brute_force_models(&instance);
        assert!(models.is_empty(), "brute force must agree it is UNSAT");
    }

    #[test]
    fn test_probe_no_false_fixing_when_satisfiable_unconstrained() {
        // x1 + x2 >= 1: both polarities of each variable are feasible; probing
        // must NOT fix anything.
        let constraints = vec![ge(vec![term(1, lit(1)), term(1, lit(2))], 1)];
        let (fixed, result) = run_probe(&constraints, HashMap::new());
        assert_eq!(
            result,
            ProbeResult::Ok {
                found_fixings: false
            }
        );
        assert!(
            fixed.is_empty(),
            "probing must not fix any feasible variable"
        );
    }

    #[test]
    fn test_preprocess_probing_forces_fixing_end_to_end() {
        // Same forcing instance as the focused test, run through the full
        // preprocess pipeline: x1 must be fixed false and propagated away.
        let instance = make_instance(
            2,
            vec![
                ge(vec![term(1, neg(1)), term(1, lit(2))], 1),
                ge(vec![term(1, neg(1)), term(1, neg(2))], 1),
            ],
        );
        match preprocess(&instance) {
            PreprocessResult::Simplified { fixed_literals, .. } => {
                assert_eq!(
                    fixed_literals.get(&1),
                    Some(&false),
                    "preprocess must fix x1=false via probing"
                );
            }
            other => panic!("expected Simplified, got {other:?}"),
        }
    }

    /// Brute-force a small instance with explicit forced fixings applied, used
    /// to confirm probing-derived fixings are genuine logical consequences.
    fn models_consistent_with_fixings(instance: &PbInstance, fixed: &HashMap<u32, bool>) -> bool {
        let (models, _) = brute_force_models(instance);
        models.iter().all(|&mask| {
            fixed.iter().all(|(&var, &value)| {
                let bit = (mask >> (var - 1)) & 1 == 1;
                bit == value
            })
        })
    }

    #[test]
    fn test_probe_fixings_are_entailed_by_every_model() {
        // Every probing-forced fixing must hold in *every* satisfying model
        // (that is the definition of an entailed consequence).
        let constraints = vec![
            ge(vec![term(1, neg(1)), term(1, lit(2))], 1),
            ge(vec![term(1, neg(1)), term(1, neg(2))], 1),
            ge(vec![term(1, lit(2)), term(1, lit(3))], 1),
        ];
        let instance = make_instance(3, constraints.clone());
        let (models, _) = brute_force_models(&instance);
        assert!(!models.is_empty(), "instance should be satisfiable");

        let (fixed, result) = run_probe(&constraints, HashMap::new());
        assert!(matches!(result, ProbeResult::Ok { .. }));
        assert!(
            models_consistent_with_fixings(&instance, &fixed),
            "every probing fixing must be entailed by all models: fixed={fixed:?}"
        );
    }

    /// Generates a deterministic batch of small random PB instances for the
    /// differential test.
    fn differential_batch() -> Vec<PbInstance> {
        // A handcrafted but varied set: decision + optimization, with and
        // without forced literals, SAT and UNSAT.
        vec![
            // 1. Forcing decision instance (probing fires).
            make_instance(
                3,
                vec![
                    ge(vec![term(1, neg(1)), term(1, lit(2))], 1),
                    ge(vec![term(1, neg(1)), term(1, neg(2))], 1),
                    ge(vec![term(1, lit(2)), term(1, lit(3))], 1),
                ],
            ),
            // 2. UNSAT via double conflict.
            make_instance(
                2,
                vec![
                    ge(vec![term(1, neg(1)), term(1, lit(2))], 1),
                    ge(vec![term(1, neg(1)), term(1, neg(2))], 1),
                    ge(vec![term(1, lit(1)), term(1, lit(2))], 1),
                    ge(vec![term(1, lit(1)), term(1, neg(2))], 1),
                ],
            ),
            // 3. Optimization instance with a forcing structure.
            PbInstance {
                num_vars: 4,
                num_constraints: 0,
                constraints: vec![
                    ge(vec![term(1, neg(1)), term(1, lit(2))], 1),
                    ge(vec![term(1, neg(1)), term(1, neg(2))], 1),
                    ge(vec![term(1, lit(3)), term(1, lit(4))], 1),
                ],
                objective: Some(PbObjective {
                    terms: vec![term(1, lit(1)), term(2, lit(2)), term(1, lit(3))],
                }),
            },
            // 4. Pure satisfiable cardinality (no forcing).
            make_instance(
                4,
                vec![
                    ge(vec![term(1, lit(1)), term(1, lit(2)), term(1, lit(3))], 1),
                    ge(vec![term(1, lit(2)), term(1, lit(3)), term(1, lit(4))], 2),
                ],
            ),
            // 5. Weighted satisfiable, mild forcing.
            make_instance(
                4,
                vec![
                    ge(vec![term(3, lit(1)), term(2, lit(2)), term(1, lit(3))], 4),
                    ge(vec![term(1, neg(1)), term(1, lit(4))], 1),
                ],
            ),
            // 6. Equality constraints.
            make_instance(
                3,
                vec![
                    eq_constraint(vec![term(1, lit(1)), term(1, lit(2)), term(1, lit(3))], 2),
                    ge(vec![term(1, neg(1)), term(1, lit(2))], 1),
                ],
            ),
            // 7. Larger chain of implications forcing several fixings.
            make_instance(
                5,
                vec![
                    ge(vec![term(1, neg(1)), term(1, lit(2))], 1),
                    ge(vec![term(1, neg(2)), term(1, lit(3))], 1),
                    ge(vec![term(1, neg(3)), term(1, lit(4))], 1),
                    ge(vec![term(1, neg(4)), term(1, lit(5))], 1),
                    ge(vec![term(1, neg(5))], 1),
                    ge(vec![term(1, lit(1)), term(1, lit(2)), term(1, lit(3))], 1),
                ],
            ),
        ]
    }

    /// Computes the SAT/UNSAT/optimum verdict from a `PreprocessResult` by
    /// SAT/UNSAT/optimum verdict used by the differential probing test.
    #[derive(Debug, Clone, Copy, PartialEq, Eq)]
    enum Verdict {
        Unsat,
        SatDecision,
        Optimum(i128),
    }

    /// Computes the verdict from a `PreprocessResult` by applying the fixed
    /// literals and brute-forcing over the ORIGINAL instance's
    /// variables/objective. This also validates that the fixings are sound (they
    /// must not exclude all models of a satisfiable instance).
    fn verdict_from_preprocess(original: &PbInstance, result: &PreprocessResult) -> Verdict {
        match result {
            PreprocessResult::Unsatisfiable => Verdict::Unsat,
            PreprocessResult::Interrupted => panic!("unexpected interruption"),
            PreprocessResult::Simplified { fixed_literals, .. } => {
                // Brute-force the ORIGINAL instance but require the fixed
                // literals to hold; this validates the fixings too.
                let (models, _) = brute_force_models(original);
                let consistent: Vec<u64> = models
                    .into_iter()
                    .filter(|&mask| {
                        fixed_literals.iter().all(|(&var, &value)| {
                            let bit = (mask >> (var - 1)) & 1 == 1;
                            bit == value
                        })
                    })
                    .collect();
                if consistent.is_empty() {
                    // If preprocess says Simplified but no consistent model
                    // exists, the fixings would be UNSOUND unless the original is
                    // genuinely UNSAT.
                    let (orig_models, _) = brute_force_models(original);
                    assert!(
                        orig_models.is_empty(),
                        "preprocess fixings excluded all models but instance is SAT (unsound!)"
                    );
                    return Verdict::Unsat;
                }
                match &original.objective {
                    None => Verdict::SatDecision,
                    Some(obj) => {
                        let best = consistent
                            .iter()
                            .map(|&mask| {
                                obj.terms
                                    .iter()
                                    .map(|t| {
                                        let all_true = t.lits.iter().all(|lit| {
                                            let bit = (mask >> (lit.var - 1)) & 1 == 1;
                                            bit != lit.negated
                                        });
                                        if all_true {
                                            t.coeff
                                        } else {
                                            0
                                        }
                                    })
                                    .sum::<i128>()
                            })
                            .min()
                            .expect("non-empty consistent set has a minimum cost");
                        Verdict::Optimum(best)
                    }
                }
            }
        }
    }

    #[test]
    fn test_probing_never_changes_verdict_differential() {
        // For every instance in the batch, the ground-truth verdict (from brute
        // force) must equal the verdict implied by preprocess WITH probing, and
        // that verdict must also match preprocess WITHOUT probing.
        for (idx, instance) in differential_batch().into_iter().enumerate() {
            // Ground truth.
            let (gt_models, gt_opt) = brute_force_models(&instance);
            let ground_truth: Verdict = if gt_models.is_empty() {
                Verdict::Unsat
            } else {
                match instance.objective {
                    None => Verdict::SatDecision,
                    Some(_) => Verdict::Optimum(
                        gt_opt.expect("satisfiable optimization instance has an optimum"),
                    ),
                }
            };

            // With probing (the production path).
            let with_probing = preprocess(&instance);
            let with_verdict = verdict_from_preprocess(&instance, &with_probing);
            assert_eq!(
                with_verdict, ground_truth,
                "instance {idx}: probing verdict {with_verdict:?} != ground truth {ground_truth:?}"
            );

            // Without probing (run the pipeline with probing disabled by an
            // over-tight budget so the probe pass is a no-op).
            let without_probing = preprocess_no_probing(&instance);
            let without_verdict = verdict_from_preprocess(&instance, &without_probing);
            assert_eq!(
                without_verdict, ground_truth,
                "instance {idx}: no-probing verdict {without_verdict:?} != ground truth {ground_truth:?}"
            );

            // And the two preprocess verdicts must agree with each other.
            assert_eq!(
                with_verdict, without_verdict,
                "instance {idx}: probing changed the verdict vs no-probing"
            );
        }
    }

    /// Runs the preprocessing pipeline with probing effectively disabled (budget
    /// caps set so the probe pass never probes any variable), used as the
    /// no-probing reference in the differential test.
    fn preprocess_no_probing(instance: &PbInstance) -> PreprocessResult {
        // We reuse the public pipeline but cannot pass a budget through it; for
        // the differential reference we instead reconstruct the same pipeline
        // steps WITHOUT the probing call by directly normalizing + fixing +
        // subsuming. To stay faithful, we call preprocess and then strip any
        // probing-only fixings is not possible; instead, assert the simpler
        // invariant by disabling probing via a zero budget through a dedicated
        // entry point.
        preprocess_with_probe_budget(
            instance,
            ProbeBudget {
                max_vars: 0,
                max_constraints: 0,
                max_probes: 0,
                max_propagation_steps: 0,
            },
        )
    }

    // --- Single-residue GCD division tests ---

    #[test]
    fn test_gcd_residue_divides_row_with_one_odd_coefficient() {
        // 3x + 2y + 2z >= 3  ->  2x + y + z >= 2 (g=2 over {2,2}; the odd
        // coefficient 3 rounds to 2). Exact equivalence: x=1 satisfies both
        // for any y,z; x=0 requires y=z=1 in both.
        let mut c = ge(vec![term(3, lit(1)), term(2, lit(2)), term(2, lit(3))], 3);
        let mut stats = PreprocessStats::default();
        gcd_residue_strengthen(&mut c, &mut stats);
        assert_eq!(
            c,
            ge(vec![term(2, lit(1)), term(1, lit(2)), term(1, lit(3))], 2)
        );
        assert_eq!(stats.gcd_residue_strengthened, 1);
    }

    #[test]
    fn test_gcd_residue_rounds_to_cardinality() {
        // 5x + 3y + 3z >= 6  ->  x + y + z >= 2 (g=3; ceil(6/3)=2,
        // ceil(1/3)=1 so the odd coefficient becomes 1).
        let mut c = ge(vec![term(5, lit(1)), term(3, lit(2)), term(3, lit(3))], 6);
        let mut stats = PreprocessStats::default();
        gcd_residue_strengthen(&mut c, &mut stats);
        assert_eq!(
            c,
            ge(vec![term(1, lit(1)), term(1, lit(2)), term(1, lit(3))], 2)
        );
    }

    #[test]
    fn test_gcd_residue_drops_irrelevant_literal() {
        // x + 2y + 2z >= 2: x alone cannot help (ceil(2/2) == ceil(1/2)), so
        // the row is exactly y + z >= 1 and x drops out.
        let mut c = ge(vec![term(1, lit(1)), term(2, lit(2)), term(2, lit(3))], 2);
        let mut stats = PreprocessStats::default();
        gcd_residue_strengthen(&mut c, &mut stats);
        assert_eq!(c, ge(vec![term(1, lit(2)), term(1, lit(3))], 1));
    }

    #[test]
    fn test_gcd_residue_exhaustive_equivalence_small_rows() {
        // Brute-force equivalence over all assignments for a spread of rows
        // with exactly one non-divisible coefficient.
        let rows = vec![
            ge(vec![term(3, lit(1)), term(2, lit(2)), term(2, lit(3))], 3),
            ge(vec![term(5, lit(1)), term(3, lit(2)), term(3, lit(3))], 6),
            ge(vec![term(1, lit(1)), term(2, lit(2)), term(2, lit(3))], 2),
            ge(vec![term(7, lit(1)), term(4, neg(2)), term(6, lit(3))], 9),
            ge(vec![term(2, lit(1)), term(9, neg(2)), term(6, lit(3))], 8),
            ge(
                vec![term(4, lit(1)), term(10, lit(2)), term(15, lit(3))],
                12,
            ),
        ];
        for original in rows {
            let mut rewritten = original.clone();
            let mut stats = PreprocessStats::default();
            gcd_residue_strengthen(&mut rewritten, &mut stats);
            for mask in 0u64..8 {
                assert_eq!(
                    mask_satisfies(std::slice::from_ref(&original), mask),
                    mask_satisfies(std::slice::from_ref(&rewritten), mask),
                    "residue rewrite changed the row's truth table:\n\
                     original: {original:?}\nrewritten: {rewritten:?}\nmask: {mask:#b}"
                );
            }
        }
    }

    #[test]
    fn test_gcd_residue_skips_nonlinear_and_unit_rows() {
        let mut nonlinear = ge(vec![prod(2, vec![lit(1), lit(2)]), term(4, lit(3))], 3);
        let before = nonlinear.clone();
        let mut stats = PreprocessStats::default();
        gcd_residue_strengthen(&mut nonlinear, &mut stats);
        assert_eq!(nonlinear, before, "non-linear rows must be skipped");

        let mut all_unit = ge(vec![term(1, lit(1)), term(1, lit(2))], 1);
        let before = all_unit.clone();
        gcd_residue_strengthen(&mut all_unit, &mut stats);
        assert_eq!(all_unit, before, "gcd-1 rows have no residue divisor");
        assert_eq!(stats.gcd_residue_strengthened, 0);
    }

    #[test]
    fn test_gcd_residue_counter_counts_rows_not_applications() {
        // 2x + 4y + 9z >= 10 needs TWO residue applications to reach its
        // fixpoint (-> x + 2y + 4z >= 5 -> x + y + 2z >= 3), but the stats
        // field documents ROWS rewritten, so one sweep must count exactly 1.
        let mut c = ge(vec![term(2, lit(1)), term(4, lit(2)), term(9, lit(3))], 10);
        let mut stats = PreprocessStats::default();
        gcd_residue_strengthen(&mut c, &mut stats);
        assert_eq!(
            c,
            ge(vec![term(1, lit(1)), term(1, lit(2)), term(2, lit(3))], 3)
        );
        assert_eq!(
            stats.gcd_residue_strengthened, 1,
            "a multi-application fixpoint sweep on one row must count once"
        );
    }

    #[test]
    fn test_preprocess_one_shot_interruptible_returns_matching_stats() {
        // The interruptible one-shot twin must surface the same stats as the
        // non-interruptible entry point (it used to discard them).
        let instance = make_instance(
            3,
            vec![
                ge(vec![term(1, lit(1)), term(1, lit(2))], 1),
                ge(vec![term(1, lit(2)), term(1, lit(3))], 1),
            ],
        );
        let (result, stats) = preprocess_one_shot_interruptible(&instance, || false);
        let (expected_result, expected_stats) = preprocess_one_shot(&instance);
        assert_eq!(result, expected_result);
        assert_eq!(stats, expected_stats);
        assert!(
            stats.pure_fixed > 0,
            "test instance must exercise a counted pass (pure-literal fixing)"
        );
    }

    // --- Pure/monotone literal elimination tests ---

    #[test]
    fn test_pure_literal_decision_fixes_positive_polarity() {
        // x1..x3 appear only positively in >= rows with slack (no literal is
        // unit-forced and probing finds no conflicts): the pure pass fixes all
        // three true and every row is satisfied and removed.
        let instance = make_instance(
            3,
            vec![
                ge(vec![term(1, lit(1)), term(1, lit(2))], 1),
                ge(vec![term(1, lit(2)), term(1, lit(3))], 1),
            ],
        );
        match preprocess_one_shot(&instance).0 {
            PreprocessResult::Simplified {
                instance: result,
                fixed_literals,
            } => {
                assert!(result.constraints.is_empty());
                assert_eq!(fixed_literals.get(&1), Some(&true));
                assert_eq!(fixed_literals.get(&2), Some(&true));
                assert_eq!(fixed_literals.get(&3), Some(&true));
            }
            other => panic!("expected Simplified, got {other:?}"),
        }
    }

    #[test]
    fn test_pure_literal_negative_polarity_fixes_false() {
        let instance = make_instance(2, vec![ge(vec![term(1, neg(1)), term(1, neg(2))], 1)]);
        match preprocess_one_shot(&instance).0 {
            PreprocessResult::Simplified {
                instance: result,
                fixed_literals,
            } => {
                assert!(result.constraints.is_empty());
                assert_eq!(fixed_literals.get(&1), Some(&false));
                assert_eq!(fixed_literals.get(&2), Some(&false));
            }
            other => panic!("expected Simplified, got {other:?}"),
        }
    }

    #[test]
    fn test_pure_literal_blocked_by_objective_preference() {
        // x1 is pure-positive in the row, but the objective charges +5 for
        // x1=true, so fixing it true could overshoot the optimum: must skip.
        // (x2 keeps the row nontrivial; it is charged nothing and is fixed.)
        let instance = PbInstance {
            num_vars: 2,
            num_constraints: 1,
            constraints: vec![ge(vec![term(1, lit(1)), term(1, lit(2))], 1)],
            objective: Some(PbObjective {
                terms: vec![term(5, lit(1))],
            }),
        };
        match preprocess_one_shot(&instance).0 {
            PreprocessResult::Simplified { fixed_literals, .. } => {
                // x1 must NOT be fixed true by the pure-row rule (the
                // objective charges +5 for x1=true). After x2 (pure,
                // objective-free) is fixed true and the row is satisfied, x1
                // becomes objective-only and is fixed to its objective-minimal
                // polarity FALSE — the optimum (0) is preserved either way.
                assert_eq!(
                    fixed_literals.get(&1),
                    Some(&false),
                    "objective-averse pure literal must never be fixed true"
                );
                // x2 is pure and objective-free: fixed true, satisfying the row.
                assert_eq!(fixed_literals.get(&2), Some(&true));
            }
            other => panic!("expected Simplified, got {other:?}"),
        }
    }

    #[test]
    fn test_pure_literal_allowed_when_objective_prefers_fixed_polarity() {
        // x1 pure-positive and the objective PAYS for x1=true (negative
        // coefficient): fixing true is optimum-safe and removes the row.
        let instance = PbInstance {
            num_vars: 1,
            num_constraints: 1,
            constraints: vec![ge(vec![term(1, lit(1))], 0)],
            objective: Some(PbObjective {
                terms: vec![term(-3, lit(1))],
            }),
        };
        match preprocess_one_shot(&instance).0 {
            PreprocessResult::Simplified {
                instance: result,
                fixed_literals,
            } => {
                assert!(result.constraints.is_empty());
                assert_eq!(fixed_literals.get(&1), Some(&true));
            }
            other => panic!("expected Simplified, got {other:?}"),
        }
    }

    #[test]
    fn test_objective_only_variable_fixed_to_minimal_polarity() {
        // x2 appears in no row; the objective prefers x2=false (+4 if true).
        // x3 appears in no row; the objective prefers x3=true (-2 if true).
        let instance = PbInstance {
            num_vars: 3,
            num_constraints: 1,
            constraints: vec![ge(vec![term(1, lit(1)), term(1, neg(1))], 1)],
            objective: Some(PbObjective {
                terms: vec![term(4, lit(2)), term(-2, lit(3))],
            }),
        };
        match preprocess_one_shot(&instance).0 {
            PreprocessResult::Simplified { fixed_literals, .. } => {
                assert_eq!(fixed_literals.get(&2), Some(&false));
                assert_eq!(fixed_literals.get(&3), Some(&true));
            }
            other => panic!("expected Simplified, got {other:?}"),
        }
    }

    #[test]
    fn test_pure_literal_pass_skipped_on_nonlinear_rows() {
        // Any product term disables the pass entirely (fail closed): x2 would
        // otherwise be pure.
        let instance = make_instance(
            2,
            vec![
                ge(vec![prod(1, vec![lit(1), lit(2)])], 0),
                ge(vec![term(1, lit(2))], 0),
            ],
        );
        match preprocess_one_shot(&instance).0 {
            PreprocessResult::Simplified { fixed_literals, .. } => {
                assert!(
                    fixed_literals.is_empty(),
                    "non-linear rows must disable pure-literal elimination"
                );
            }
            other => panic!("expected Simplified, got {other:?}"),
        }
    }

    #[test]
    fn test_pure_literal_not_fixed_when_both_polarities_constrained() {
        let instance = make_instance(
            2,
            vec![
                ge(vec![term(1, lit(1)), term(1, lit(2))], 1),
                ge(vec![term(1, neg(1)), term(1, lit(2))], 1),
            ],
        );
        match preprocess_one_shot(&instance).0 {
            PreprocessResult::Simplified { fixed_literals, .. } => {
                // x1 occurs in both polarities: not pure. x2 is pure (fixed
                // true), which satisfies both rows; x1 is then unconstrained
                // and absent from the objective, so it may not be fixed at all
                // or fixed by a later pass — but never inconsistently.
                assert_eq!(fixed_literals.get(&2), Some(&true));
            }
            other => panic!("expected Simplified, got {other:?}"),
        }
    }

    // -----------------------------------------------------------------------
    // Randomized differential fuzz: the full preprocessing pipeline (including
    // weighted row dominance and pure-literal elimination) must preserve
    // SAT/UNSAT, the optimum value, and model reconstruction on random
    // instances, verified against a brute-force oracle over ALL assignments.
    // -----------------------------------------------------------------------

    /// Deterministic xorshift64* RNG so the fuzz batch is reproducible.
    struct XorShift(u64);

    impl XorShift {
        fn next(&mut self) -> u64 {
            let mut x = self.0;
            x ^= x >> 12;
            x ^= x << 25;
            x ^= x >> 27;
            self.0 = x;
            x.wrapping_mul(0x2545_F491_4F6C_DD1D)
        }

        fn below(&mut self, n: u64) -> u64 {
            self.next() % n
        }
    }

    /// Generates a small random PB instance exercising normalization (negative
    /// coefficients, equalities), dominance (duplicated superset rows), pure
    /// literals (sparse polarity coverage), and objectives (mixed-sign
    /// coefficients over both polarities).
    fn random_instance(rng: &mut XorShift) -> PbInstance {
        let num_vars = 3 + rng.below(5) as u32; // 3..=7
        let num_rows = 1 + rng.below(9) as usize; // 1..=9
        let mut constraints = Vec::new();

        let random_row = |rng: &mut XorShift| {
            let width = 1 + rng.below(3.min(u64::from(num_vars))) as usize;
            let mut vars: Vec<u32> = (1..=num_vars).collect();
            // Partial Fisher-Yates for a distinct random sample.
            for i in 0..width {
                let j = i + rng.below((vars.len() - i) as u64) as usize;
                vars.swap(i, j);
            }
            let terms: Vec<PbTerm> = (0..width)
                .map(|i| {
                    let coeff = match rng.below(10) {
                        0..=6 => 1 + rng.below(4) as i128,
                        7..=8 => -(1 + rng.below(4) as i128),
                        _ => 5 + rng.below(8) as i128,
                    };
                    let negated = rng.below(10) < 4;
                    // Rare product terms exercise the fail-closed non-linear
                    // gates (pure literals, probing, residue division).
                    let lits = if rng.below(20) == 0 {
                        let other = 1 + rng.below(u64::from(num_vars)) as u32;
                        if other == vars[i] {
                            vec![PbLit {
                                var: vars[i],
                                negated,
                            }]
                        } else {
                            vec![
                                PbLit {
                                    var: vars[i],
                                    negated,
                                },
                                PbLit {
                                    var: other,
                                    negated: rng.below(2) == 1,
                                },
                            ]
                        }
                    } else {
                        vec![PbLit {
                            var: vars[i],
                            negated,
                        }]
                    };
                    PbTerm { coeff, lits }
                })
                .collect();
            let max_sum: i128 = terms.iter().map(|t| t.coeff.max(0)).sum();
            if rng.below(4) == 0 {
                let rhs = rng.below((max_sum.unsigned_abs() as u64).max(1) + 1) as i128;
                eq_constraint(terms, rhs)
            } else {
                let rhs = rng.below(8) as i128 - 2; // -2..=5
                ge(terms, rhs)
            }
        };

        for _ in 0..num_rows {
            let row = random_row(rng);
            // Occasionally add a superset/scaled sibling to exercise dominance.
            if matches!(row.rel, PbRel::Ge) && rng.below(4) == 0 {
                let mut sibling = row.clone();
                let scale = 1 + rng.below(3) as i128;
                for term in &mut sibling.terms {
                    term.coeff = term.coeff.saturating_mul(scale);
                }
                let extra_var = 1 + rng.below(u64::from(num_vars)) as u32;
                sibling.terms.push(PbTerm {
                    coeff: 1 + rng.below(3) as i128,
                    lits: vec![PbLit {
                        var: extra_var,
                        negated: rng.below(2) == 1,
                    }],
                });
                sibling.rhs = sibling.rhs.saturating_mul(scale) - rng.below(3) as i128;
                constraints.push(sibling);
            }
            constraints.push(row);
        }

        let objective = if rng.below(2) == 0 {
            let width = 1 + rng.below(u64::from(num_vars)) as usize;
            let terms: Vec<PbTerm> = (0..width)
                .map(|_| {
                    let mut coeff = rng.below(12) as i128 - 5; // -5..=6
                    if coeff == 0 {
                        coeff = 1;
                    }
                    PbTerm {
                        coeff,
                        lits: vec![PbLit {
                            var: 1 + rng.below(u64::from(num_vars)) as u32,
                            negated: rng.below(10) < 3,
                        }],
                    }
                })
                .collect();
            Some(PbObjective { terms })
        } else {
            None
        };

        let num_constraints = constraints.len() as u32;
        PbInstance {
            num_vars,
            num_constraints,
            constraints,
            objective,
        }
    }

    /// Evaluates whether `mask` satisfies every constraint of `constraints`.
    fn mask_satisfies(constraints: &[PbConstraint], mask: u64) -> bool {
        constraints.iter().all(|c| {
            let lhs: i128 = c
                .terms
                .iter()
                .map(|t| {
                    let all_true = t.lits.iter().all(|lit| {
                        let bit = (mask >> (lit.var - 1)) & 1 == 1;
                        bit != lit.negated
                    });
                    if all_true {
                        t.coeff
                    } else {
                        0
                    }
                })
                .sum();
            match c.rel {
                PbRel::Ge => lhs >= c.rhs,
                PbRel::Eq => lhs == c.rhs,
            }
        })
    }

    /// Objective cost of `mask` under `objective`.
    fn mask_cost(objective: &PbObjective, mask: u64) -> i128 {
        objective
            .terms
            .iter()
            .map(|t| {
                let all_true = t.lits.iter().all(|lit| {
                    let bit = (mask >> (lit.var - 1)) & 1 == 1;
                    bit != lit.negated
                });
                if all_true {
                    t.coeff
                } else {
                    0
                }
            })
            .sum()
    }

    #[test]
    fn test_preprocess_randomized_differential_solution_set() {
        // Default pipeline: entailed-only (safe under later assumptions).
        run_randomized_differential(0x9E37_79B9_7F4A_7C15, preprocess);
    }

    #[test]
    fn test_preprocess_one_shot_randomized_differential_solution_set() {
        // One-shot pipeline: additionally applies choice reductions (pure
        // literals); must still preserve SAT/UNSAT + the optimum + round-trip.
        run_randomized_differential(0xDEAD_BEEF_0BAD_F00D, |instance| {
            preprocess_one_shot(instance).0
        });
    }

    fn run_randomized_differential(seed: u64, run: impl Fn(&PbInstance) -> PreprocessResult) {
        let mut rng = XorShift(seed);
        for case in 0..3000 {
            let instance = random_instance(&mut rng);
            let (original_models, original_opt) = brute_force_models(&instance);

            match run(&instance) {
                PreprocessResult::Interrupted => panic!("case {case}: unexpected interruption"),
                PreprocessResult::Unsatisfiable => {
                    assert!(
                        original_models.is_empty(),
                        "case {case}: preprocess claimed UNSAT on a satisfiable instance:\n{instance:?}"
                    );
                }
                PreprocessResult::Simplified {
                    instance: reduced,
                    fixed_literals,
                } => {
                    let space_vars = instance.num_vars.max(reduced.num_vars);
                    assert!(space_vars <= 20, "case {case}: fuzz instance too large");

                    // Enumerate every assignment consistent with the fixed
                    // literals that satisfies the REDUCED constraints — this is
                    // exactly the set of models the solver + witness
                    // reconstruction (fixed_literals overrides) can produce.
                    let mut reconstructed_sat = false;
                    let mut reconstructed_best: Option<i128> = None;
                    for mask in 0u64..(1u64 << space_vars) {
                        let consistent = fixed_literals
                            .iter()
                            .all(|(&var, &value)| ((mask >> (var - 1)) & 1 == 1) == value);
                        if !consistent || !mask_satisfies(&reduced.constraints, mask) {
                            continue;
                        }
                        reconstructed_sat = true;
                        // ROUND-TRIP: every reconstructed model must satisfy the
                        // ORIGINAL constraints (fail-closed reconstruction).
                        assert!(
                            mask_satisfies(&instance.constraints, mask),
                            "case {case}: reconstructed model {mask:#b} violates the original \
                             instance:\n{instance:?}\nreduced: {reduced:?}\nfixed: {fixed_literals:?}"
                        );
                        if let Some(objective) = &instance.objective {
                            let cost = mask_cost(objective, mask);
                            reconstructed_best =
                                Some(reconstructed_best.map_or(cost, |best| best.min(cost)));
                        }
                    }

                    // SAT/UNSAT must be preserved exactly.
                    assert_eq!(
                        reconstructed_sat,
                        !original_models.is_empty(),
                        "case {case}: preprocessing changed satisfiability:\n{instance:?}\n\
                         reduced: {reduced:?}\nfixed: {fixed_literals:?}"
                    );

                    // The optimum must be preserved exactly (choice fixings such
                    // as pure literals may shrink the model set but never past
                    // the optimum).
                    if instance.objective.is_some() && reconstructed_sat {
                        assert_eq!(
                            reconstructed_best, original_opt,
                            "case {case}: preprocessing changed the optimum:\n{instance:?}\n\
                             reduced: {reduced:?}\nfixed: {fixed_literals:?}"
                        );
                    }
                }
            }
        }
    }
}
