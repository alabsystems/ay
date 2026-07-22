// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Theory-specific solving routines.
//!
//! This module contains the `solve_*` implementations that power `check-sat` for
//! each supported logic/theory combination.
//!
//! Split into sub-modules by theory family:
//! - `propositional`: Pure SAT
//! - `euf`: EUF, DT, ArrayEUF
//! - `lra`: LRA (pure real arithmetic)
//! - `lia`: LIA, NIA (pure integer arithmetic)
//! - `combined`: UF+LRA, AUFLIA, AUFLRA, LIRA, AUFLIRA (combined theories)
//! - `bv`: BV, ABV, UFBV, AUFBV solve pipelines
//! - `bv_config`: BvSolveConfig parameterization for BV logic variants
//! - `bv_model`: BV model extraction from SAT assignments
//! - `bv_eval`: BV expression evaluation for model recovery
//! - `bv_axioms_array`: Array read-over-write axiom generation for QF_ABV/QF_AUFBV
//! - `bv_axioms_euf`: EUF congruence axiom generation for QF_UFBV/QF_AUFBV
//! - `lia_eval`: LIA model evaluation and recovery helpers
//! - `solve_harness_helpers`: Free helpers for assertion flattening and source tracking
//! - `model_helpers`: Model storage and proof building

pub(in crate::executor) mod bv;
mod bv_axioms_array;
mod bv_axioms_euf;
mod bv_axioms_non_bv;
mod bv_cegar_array;
pub(in crate::executor) mod bv_cnf_dump;
mod bv_config;
mod bv_delayed_ext;
mod bv_encoding;
mod bv_eval;
mod bv_eval_bool;
mod bv_finite_array;
mod bv_incremental;
mod bv_model;
mod combined;
mod euf;
#[cfg(test)]
mod incremental_conflict_gate_tests;
mod incremental_scope;
pub(crate) use euf::reachable_term_set;
mod fp;
mod fp_model;
// pub(in crate::executor): the model-validation pipeline re-runs the #A1
// LIA reconciliation passes after post-validation repair (#A1-repair-resync).
pub(in crate::executor) mod lia;
mod lia_eval;
mod lra;
mod map;
mod model_helpers;
mod multiset;
mod nra;
mod propositional;
mod seq;
mod set;
mod skolem_cache;
pub(in crate::executor) mod solve_harness;
mod solve_harness_helpers;
pub(crate) mod split_incremental;
mod strings;
mod strings_analysis;
mod strings_eval;
mod strings_lemma;
mod strings_lia;
mod strings_preregister;
mod strings_regex_len;
mod strings_w4;
mod strings_w5;
mod strings_w6;
mod strings_w7;
mod strings_word_eq;

pub(crate) use split_incremental::BoundRefinementReplayKey;
pub(crate) use split_incremental::{SharedRescuePairCounter, DEFAULT_RESCUE_PAIR_BUDGET};

use ay_core::term::{Symbol, TermData};
use ay_core::{Sort, TermId, TermStore};
use ay_sat::{Solver as SatSolver, Variable as SatVariable};

/// Result of array axiom generation for QF_ABV
pub(in crate::executor) struct ArrayAxiomResult {
    /// Generated CNF clauses
    pub(in crate::executor) clauses: Vec<ay_core::CnfClause>,
    /// Number of additional variables used
    pub(in crate::executor) num_vars: u32,
}

/// Result of EUF congruence axiom generation for QF_UFBV/QF_AUFBV
pub(in crate::executor) struct EufAxiomResult {
    /// Generated CNF clauses
    pub(in crate::executor) clauses: Vec<ay_core::CnfClause>,
    /// Number of additional variables used
    pub(in crate::executor) num_vars: u32,
}

/// Maximum branch-and-bound split iterations for pure integer arithmetic solvers.
///
/// QF_LIA is decidable, so we keep this high to reduce spurious `Unknown`
/// results on hard-but-finite problems (#2472/#2475).
pub(in crate::executor) const MAX_SPLITS_LIA: usize = 1_000_000;

/// Maximum branch-and-bound split iterations for mixed Int/Real solvers.
///
/// Mixed arithmetic can still require conservative guards to avoid runaway
/// split growth in combined-theory paths.
pub(in crate::executor) const MAX_SPLITS_MIXED: usize = 100_000;

/// Maximum disequality split iterations for pure real arithmetic (QF_LRA).
///
/// LRA only needs splits for disequalities (`x != c` → `x < c OR x > c`).
/// This is typically much smaller than LIA branch-and-bound.
pub(in crate::executor) const MAX_SPLITS_LRA: usize = 100_000;

/// Maximum model equality split iterations for Array+EUF solving (QF_AX).
///
/// The array theory is non-convex: satisfiability of array formulas may
/// require exploring multiple model equality case splits (e.g., whether
/// two array-sorted terms are equal or not). Previously set to 1, which
/// caused false Unknown on any SAT instance needing >1 split. Z3 handles
/// this via unlimited interface equality generation in final_check. We
/// use a bounded limit to prevent runaway splitting on pathological inputs.
pub(in crate::executor) const MAX_SPLITS_ARRAY_EUF: usize = 10_000;

/// Threshold for detecting unbounded variables in integer arithmetic.
/// Variables with absolute value exceeding this are considered potentially unbounded.
pub(in crate::executor) const UNBOUNDED_THRESHOLD: i32 = 20;

/// Maximum string lemma iterations for QF_S/QF_SLIA solving.
///
/// Each iteration adds one split lemma clause from the string theory solver.
/// CVC5 typically converges in <100 iterations even on complex benchmarks.
pub(in crate::executor) const MAX_STRING_LEMMA_ITERATIONS: usize = 10_000;

#[inline]
pub(in crate::executor::theories) fn debug_auflia_enabled() -> bool {
    crate::theory_debug_flags::debug_auflia()
}
#[inline]
pub(in crate::executor::theories) fn debug_ite_conditions_enabled() -> bool {
    crate::theory_debug_flags::debug_ite_conditions()
}
#[inline]
pub(in crate::executor::theories) fn debug_linking_enabled() -> bool {
    crate::theory_debug_flags::debug_linking()
}
#[inline]
pub(in crate::executor::theories) fn debug_preprocessed_enabled() -> bool {
    crate::theory_debug_flags::debug_preprocessed()
}

/// Freeze a SAT variable exactly once.
///
/// Incremental DPLL(T) reuses SAT instances across many check-sat calls. Theory-facing
/// variables (assertion roots, active atoms, split atoms) must remain available for
/// future clauses and model synchronization, so they must not be eliminated by BVE.
#[inline]
pub(in crate::executor::theories) fn freeze_var_if_needed(
    solver: &mut SatSolver,
    var: SatVariable,
) {
    if !solver.is_frozen(var) {
        solver.freeze(var);
    }
}

/// Freeze the SAT variables of ITE-condition guards (#8003/#8125).
///
/// The eager `TheoryExtension` treats ITE conditions as first-class search
/// objects: the #8003 branch of `suggest_decision` DECIDES them with priority,
/// and the #8125 branch-deferral machinery keeps theory atoms from inactive ITE
/// branches away from the theory until their guard variable is ASSIGNED. Both
/// assume the guard variable stays alive in the SAT solver. Unlike theory
/// atoms, ITE conditions are often plain Tseitin variables, so the theory-atom
/// freeze loop does not protect them — BVE/SCC/sweep inprocessing could remove
/// one, after which (a) `suggest_decision` panics `decide()` with "decided
/// removed variable" (hwbench fischer.7, proof mode), and (b) a removed guard
/// can never be assigned, so its deferred branch atoms would be withheld from
/// the theory for the rest of the solve.
///
/// Mirrors the guard resolution in `extension/construction.rs`: the condition's
/// own SAT variable, or the inner variable when the condition is `(not x)`.
pub(in crate::executor::theories) fn freeze_ite_condition_vars(
    solver: &mut SatSolver,
    terms: &TermStore,
    term_to_var: &ay_core::kani_compat::DetHashMap<TermId, u32>,
) {
    let num_vars = solver.user_num_vars() as u32;
    for term_id in terms.term_ids() {
        if let TermData::Ite(cond, _, _) = terms.get(term_id) {
            let cond_sat_var = if let Some(&sv) = term_to_var.get(cond) {
                sv
            } else if let TermData::Not(inner) = terms.get(*cond) {
                match term_to_var.get(inner) {
                    Some(&sv) => sv,
                    None => continue,
                }
            } else {
                continue;
            };
            if cond_sat_var < num_vars {
                freeze_var_if_needed(solver, SatVariable::new(cond_sat_var));
            }
        }
    }
}

pub(in crate::executor) fn parse_expression_split_disequality(
    terms: &TermStore,
    disequality_term: TermId,
) -> Option<(TermId, TermId, bool)> {
    match terms.get(disequality_term) {
        TermData::App(Symbol::Named(name), args) if name == "=" && args.len() == 2 => {
            Some((args[0], args[1], false))
        }
        TermData::App(Symbol::Named(name), args) if name == "distinct" && args.len() == 2 => {
            Some((args[0], args[1], true))
        }
        TermData::Not(inner) => match terms.get(*inner) {
            TermData::App(Symbol::Named(name), args) if name == "=" && args.len() == 2 => {
                // `distinct` is often normalized to `not (= ...)`, so treat `not` like `distinct`
                // for conditional split encoding: `~term OR ...`.
                Some((args[0], args[1], true))
            }
            _ => None,
        },
        _ => None,
    }
}

pub(in crate::executor) fn create_expression_split_atoms(
    terms: &mut TermStore,
    disequality_term: TermId,
) -> Option<(TermId, TermId, bool)> {
    let (lhs, rhs, is_distinct) = parse_expression_split_disequality(terms, disequality_term)?;
    let (left_atom, right_atom) = create_expression_split_pair_atoms(terms, lhs, rhs)?;
    Some((left_atom, right_atom, is_distinct))
}

/// Build the two mutually-exclusive branch atoms for a disequality `lhs ≠ rhs`.
///
/// The caller emits the clause `left ∨ right ∨ ⟨equality-guard⟩`, so `left ∨
/// right` must be logically equivalent to (or, for arrays, a
/// satisfiability-preserving witness of) `lhs ≠ rhs`.
///
/// * `Int`  → `lhs ≤ rhs-1` / `lhs ≥ rhs+1` (the two integer half-lines).
/// * `Real` → `lhs < rhs` / `lhs > rhs`.
/// * `Array` → **extensionality skolemization**. `A ≠ B ⟹ select(A,k) ≠
///   select(B,k)` for a FRESH difference index `k`. We mint that skolem (one
///   per array pair — the deterministic `__ext_diff_{a}_{b}` name is interned
///   by `mk_var`, so repeated splits on the same pair reuse the same witness
///   and `encode_and_add_split_clause`'s key-dedup keeps the clause count
///   bounded), form `select(A,k)` / `select(B,k)`, and RECURSE on that
///   (element-sorted) disequality. For the common `(Array I Int)` this
///   bottoms out immediately in the `Int` arm; nested arrays recurse one more
///   level each call. The emitted clause `(A=B) ∨ select(A,k) ≠ select(B,k)`
///   is exactly the array extensionality axiom the eager fixpoint already
///   trusts (`add_array_extensionality_axioms`), and is satisfiability-
///   preserving in both directions (a model with `A≠B` has a differing index
///   to interpret `k`; a model with `select(A,k)≠select(B,k)` has `A≠B`).
///
/// Returns `None` for sorts with no arithmetic/extensional split (e.g. Bool,
/// uninterpreted, or an array whose element sort is itself unsplittable) — the
/// caller then surfaces `Unknown(ExpressionSplit)` exactly as before.
fn create_expression_split_pair_atoms(
    terms: &mut TermStore,
    lhs: TermId,
    rhs: TermId,
) -> Option<(TermId, TermId)> {
    if terms.sort(lhs) != terms.sort(rhs) {
        return None;
    }

    match terms.sort(lhs).clone() {
        Sort::Real => {
            let lt_atom = terms.mk_lt(lhs, rhs);
            let gt_atom = terms.mk_gt(lhs, rhs);
            Some((lt_atom, gt_atom))
        }
        Sort::Int => {
            // For integers, use non-strict inequalities with adjusted bounds
            // to avoid fractional solutions in the LRA relaxation.
            // E != F becomes: E <= F-1 OR E >= F+1.
            let neg_one = terms.mk_int(num_bigint::BigInt::from(-1));
            let pos_one = terms.mk_int(num_bigint::BigInt::from(1));
            let rhs_minus_one = terms.mk_add(vec![rhs, neg_one]);
            let rhs_plus_one = terms.mk_add(vec![rhs, pos_one]);
            let le_atom = terms.mk_le(lhs, rhs_minus_one);
            let ge_atom = terms.mk_ge(lhs, rhs_plus_one);
            Some((le_atom, ge_atom))
        }
        Sort::Array(arr) => {
            // Extensionality expression-split for Array-sorted disequalities.
            // `create_expression_split_atoms` previously returned `None` here,
            // bailing `Unknown(ExpressionSplit)` on satisfiable AUFLIA bases
            // whose only unsplittable disequalities were between arrays
            // (`seq_array(s1) ≠ seq_array(s2)`, `seq_array(s) ≠ store(a,i,v)`).
            //
            // Mint the fresh difference index using the SAME `__ext_diff_{}_{}`
            // discipline as the eager fixpoint so the witness is shared/deduped,
            // then reduce to the element-sorted split (recurses for nested
            // arrays; bottoms out in Int/Real).
            let index_sort = arr.index_sort;
            let skolem_name = format!("__ext_diff_{}_{}", lhs.0, rhs.0);
            let diff_var = terms.mk_var(skolem_name, index_sort);
            let sel_lhs = terms.mk_select(lhs, diff_var);
            let sel_rhs = terms.mk_select(rhs, diff_var);
            create_expression_split_pair_atoms(terms, sel_lhs, sel_rhs)
        }
        _ => None,
    }
}

/// Same-array select/select disequality companion lemma (#array-index-split).
///
/// For `select(a, i) ≠ select(a, j)` returns the index equality atom
/// `(= i j)`, to be added NEGATED as the clause `⟨diseq guard⟩ ∨ ¬(= i j)`
/// (see `encode_and_add_negated_atom_lemma`) alongside the ordinary value
/// split. This is the ROW-congruence CONTRAPOSITIVE — `select(a,i) ≠
/// select(a,j) ⟹ i ≠ j` — so the clause is a valid array-theory lemma for
/// every model (same array only: with different arrays the index disequality
/// is NOT implied).
///
/// Why the value split alone converges slowly here: its branch atoms
/// (`sel_i ≤ sel_j - 1` / `sel_i ≥ sel_j + 1`) are LIA-only — EUF and the
/// array solver see them as opaque Booleans and never learn `i ≠ j`, so the
/// (undecided) index equality atom keeps flipping across refinement rounds
/// and ROW congruence re-merges the two selects on the flipped side. CDCL
/// eventually prunes each flip through theory conflicts, but only one
/// assignment at a time — expensive on the 2^64-guarded frame instances,
/// whose widened ground-candidate pool creates whole webs of nested-select
/// pairs (`j = select(a, k)`). BCP on this clause instead delivers `i ≠ j`
/// to EUF the moment the select disequality is asserted, EUF shares it with
/// the array solver, and the value split's branch sticks immediately.
/// (The outright LIVELOCK on those instances had a separate cause — split
/// clauses stored learned-tier were wiped by destructive arena rebuilds;
/// see the ORIGINAL-ledger note in `encode_and_add_split_clause`.)
///
/// The index equality is well-sorted by construction: `largs[0] == rargs[0]`
/// forces both indices to the shared array's domain sort.
pub(in crate::executor) fn array_select_index_diseq_lemma_atom(
    terms: &mut TermStore,
    disequality_term: TermId,
) -> Option<TermId> {
    let (lhs, rhs, _) = parse_expression_split_disequality(terms, disequality_term)?;
    let (i, j) = match (terms.get(lhs), terms.get(rhs)) {
        (TermData::App(ls, largs), TermData::App(rs, rargs))
            if ls.name() == "select"
                && rs.name() == "select"
                && largs.len() == 2
                && rargs.len() == 2
                && largs[0] == rargs[0]
                && largs[1] != rargs[1] =>
        {
            (largs[1], rargs[1])
        }
        _ => return None,
    };
    Some(terms.mk_eq(i, j))
}

#[cfg(test)]
mod tests;
