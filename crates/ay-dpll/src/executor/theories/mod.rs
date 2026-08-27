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
pub(in crate::executor) use incremental_scope::ProofCheckpointBudget;
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
mod rdl;
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
mod strings_word_prop;

pub(crate) use split_incremental::BoundRefinementReplayKey;
pub(crate) use split_incremental::{SharedRescuePairCounter, DEFAULT_RESCUE_PAIR_BUDGET};

use ay_core::term::{Symbol, TermData};
use ay_core::{Sort, TermId, TermStore};
use ay_sat::{Solver as SatSolver, Variable as SatVariable};

/// Reserved namespace for array-extensionality difference witnesses.
///
/// Names are freshly minted with `TermStore::mk_internal_symbol`; exact
/// pair-to-witness reuse is owned by `ArrayExtWitnessCache`, not by textual
/// interning. This makes every public decision query a fresh Skolem scope.
#[cfg(test)]
pub(in crate::executor) const ARRAY_EXT_WITNESS_PREFIX: &str = "__ay_ext_diff!";

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
enum ArrayExtWitnessKey {
    Pair(TermId, TermId),
    Deep(TermId, TermId, usize),
}

#[derive(Debug, Clone)]
struct ArrayExtWitnessIdentity {
    term: TermId,
    name: String,
    var_id: u32,
    sort: Sort,
}

/// Exact solver-recorded binding used to justify one generated
/// extensionality clause.
///
/// The cache only records a binding while `witness` is an exact active
/// identity. Consumers must still validate the clause schema; this registry
/// proves origin, not logical shape.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct ArrayExtWitnessBinding {
    pub(crate) witness: TermId,
    pub(crate) array_a: TermId,
    pub(crate) array_b: TermId,
}

/// A caller-authored root is unsafe to register or solve.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum ArrayExtWitnessRootViolation {
    /// The raw `TermId` is outside the owning store.
    InvalidTerm(TermId),
    /// The DAG captures an exact solver-generated witness identity.
    CapturedWitness(TermId),
}

impl ArrayExtWitnessIdentity {
    fn still_matches(&self, terms: &TermStore) -> bool {
        self.term.index() < terms.len()
            && terms.sort(self.term) == &self.sort
            && matches!(
                terms.get(self.term),
                TermData::Var(name, var_id)
                    if name == &self.name && var_id == &self.var_id
            )
    }
}

/// Per-public-query provenance and reuse table for array difference witnesses.
///
/// Active entries are shared by every generator and internal retry in one
/// public query. `begin_public_solve` retires them before the next query, so a
/// native caller cannot constrain an old raw `TermId` and make it the next
/// query's Skolem. Retired identities remain exact (name + Var id + sort), so a
/// speculative TermStore rollback that recycles a numeric `TermId` cannot
/// taint the replacement term.
#[derive(Debug, Clone, Default)]
pub(crate) struct ArrayExtWitnessCache {
    active: ay_core::kani_compat::DetHashMap<ArrayExtWitnessKey, ArrayExtWitnessIdentity>,
    retired: ay_core::kani_compat::DetHashMap<TermId, ArrayExtWitnessIdentity>,
    generated_clauses: ay_core::kani_compat::DetHashMap<TermId, Vec<ArrayExtWitnessBinding>>,
}

impl ArrayExtWitnessCache {
    fn ordered(lhs: TermId, rhs: TermId) -> (TermId, TermId) {
        if lhs.0 <= rhs.0 {
            (lhs, rhs)
        } else {
            (rhs, lhs)
        }
    }

    fn mint(&mut self, terms: &mut TermStore, sort: Sort) -> Option<ArrayExtWitnessIdentity> {
        let name = loop {
            let candidate = terms.mk_internal_symbol("ext_diff");
            if !terms.has_var_name(&candidate) {
                break candidate;
            }
        };
        let term = terms.mk_var(name.clone(), sort.clone());
        let TermData::Var(actual_name, var_id) = terms.get(term) else {
            return None;
        };
        if actual_name != &name || terms.sort(term) != &sort {
            return None;
        }
        Some(ArrayExtWitnessIdentity {
            term,
            name,
            var_id: *var_id,
            sort,
        })
    }

    fn get_or_mint(
        &mut self,
        terms: &mut TermStore,
        key: ArrayExtWitnessKey,
        sort: Sort,
    ) -> Option<TermId> {
        if let Some(existing) = self.active.get(&key).cloned() {
            if existing.still_matches(terms) {
                return (existing.sort == sort).then_some(existing.term);
            }
            // A speculative rollback recycled this numeric TermId. Drop the
            // stale cache entry before minting a new identity.
            self.active.remove(&key);
        }
        let witness = self.mint(terms, sort)?;
        let term = witness.term;
        self.active.insert(key, witness);
        Some(term)
    }

    fn pair(&mut self, terms: &mut TermStore, lhs: TermId, rhs: TermId) -> Option<TermId> {
        if terms.sort(lhs) != terms.sort(rhs) {
            return None;
        }
        let Sort::Array(array_sort) = terms.sort(lhs).clone() else {
            return None;
        };
        let (lhs, rhs) = Self::ordered(lhs, rhs);
        self.get_or_mint(
            terms,
            ArrayExtWitnessKey::Pair(lhs, rhs),
            array_sort.index_sort,
        )
    }

    fn deep(
        &mut self,
        terms: &mut TermStore,
        root_lhs: TermId,
        root_rhs: TermId,
        level: usize,
        index_sort: Sort,
    ) -> Option<TermId> {
        let (root_lhs, root_rhs) = Self::ordered(root_lhs, root_rhs);
        self.get_or_mint(
            terms,
            ArrayExtWitnessKey::Deep(root_lhs, root_rhs, level),
            index_sort,
        )
    }

    /// Retire the preceding public query's witnesses and clear pair reuse.
    pub(crate) fn begin_public_solve(&mut self, terms: &TermStore) {
        self.generated_clauses.clear();
        for witness in std::mem::take(&mut self.active).into_values() {
            if witness.still_matches(terms) {
                self.retired.insert(witness.term, witness);
            }
        }
    }

    /// Clear provenance when the owning `TermStore` is replaced by `(reset)`.
    pub(crate) fn clear(&mut self) {
        self.active.clear();
        self.retired.clear();
        self.generated_clauses.clear();
    }

    /// Whether `witness` is an exact identity minted in the current public
    /// query. Numeric `TermId` equality alone is deliberately insufficient.
    pub(crate) fn is_active_witness(&self, terms: &TermStore, witness: TermId) -> bool {
        self.active
            .values()
            .any(|identity| identity.term == witness && identity.still_matches(terms))
    }

    fn is_retired_witness(&self, terms: &TermStore, witness: TermId) -> bool {
        self.retired
            .get(&witness)
            .is_some_and(|identity| identity.still_matches(terms))
    }

    /// Record an extensionality clause and its ordered witness dependency
    /// chain at the generation site.
    ///
    /// Every witness must still be active with exact identity provenance. The
    /// proof layer independently recognizes the clause shape before consuming
    /// this record, so a malformed or stale record cannot certify a step.
    pub(crate) fn record_generated_clause(
        &mut self,
        terms: &TermStore,
        clause: TermId,
        bindings: Vec<ArrayExtWitnessBinding>,
    ) -> bool {
        if bindings.is_empty()
            || bindings
                .iter()
                .any(|binding| !self.is_active_witness(terms, binding.witness))
        {
            self.generated_clauses.remove(&clause);
            return false;
        }
        self.generated_clauses.insert(clause, bindings);
        true
    }

    /// Exact active bindings recorded for `clause`, if none became stale.
    pub(crate) fn generated_clause_bindings(
        &self,
        terms: &TermStore,
        clause: TermId,
    ) -> Option<&[ArrayExtWitnessBinding]> {
        let bindings = self.generated_clauses.get(&clause)?;
        bindings
            .iter()
            .all(|binding| self.is_active_witness(terms, binding.witness))
            .then_some(bindings.as_slice())
    }

    /// Exact active provenance for proof promotion.
    #[cfg(test)]
    pub(crate) fn matches_pair(
        &self,
        terms: &TermStore,
        witness: TermId,
        lhs: TermId,
        rhs: TermId,
    ) -> bool {
        let (lhs, rhs) = Self::ordered(lhs, rhs);
        self.active
            .get(&ArrayExtWitnessKey::Pair(lhs, rhs))
            .is_some_and(|identity| identity.term == witness && identity.still_matches(terms))
    }

    /// Pair-keyed companion of [`Self::generated_clause_bindings`].
    pub(crate) fn pair_witness(
        &self,
        terms: &TermStore,
        lhs: TermId,
        rhs: TermId,
    ) -> Option<TermId> {
        let (lhs, rhs) = Self::ordered(lhs, rhs);
        let identity = self.active.get(&ArrayExtWitnessKey::Pair(lhs, rhs))?;
        identity.still_matches(terms).then_some(identity.term)
    }

    fn violation_in_roots(
        &self,
        terms: &TermStore,
        roots: &[TermId],
        include_active: bool,
    ) -> Option<ArrayExtWitnessRootViolation> {
        let mut seen = ay_core::kani_compat::DetHashSet::default();
        let mut pending = roots.to_vec();
        while let Some(term) = pending.pop() {
            if !seen.insert(term) {
                continue;
            }
            if term.index() >= terms.len() {
                return Some(ArrayExtWitnessRootViolation::InvalidTerm(term));
            }
            if self.is_retired_witness(terms, term)
                || (include_active && self.is_active_witness(terms, term))
            {
                return Some(ArrayExtWitnessRootViolation::CapturedWitness(term));
            }
            pending.extend(terms.children(term));
        }
        None
    }

    /// Reject registration of caller-authored DAGs that capture either a
    /// current-query or prior-query witness.
    pub(crate) fn registration_violation(
        &self,
        terms: &TermStore,
        roots: &[TermId],
    ) -> Option<ArrayExtWitnessRootViolation> {
        self.violation_in_roots(terms, roots, true)
    }

    /// Reject a solve DAG that captures a witness retired at its public query
    /// boundary. Active witnesses belong to internal retries of this query.
    pub(crate) fn solve_violation(
        &self,
        terms: &TermStore,
        roots: &[TermId],
    ) -> Option<ArrayExtWitnessRootViolation> {
        self.violation_in_roots(terms, roots, false)
    }
}

/// Create or reuse the correctly-sorted witness for an unordered array pair.
pub(in crate::executor) fn array_extensionality_witness(
    terms: &mut TermStore,
    cache: &mut ArrayExtWitnessCache,
    lhs: TermId,
    rhs: TermId,
) -> Option<TermId> {
    cache.pair(terms, lhs, rhs)
}

/// Create or reuse one level of a nested-array deep witness chain.
pub(in crate::executor) fn deep_array_extensionality_witness(
    terms: &mut TermStore,
    cache: &mut ArrayExtWitnessCache,
    root_lhs: TermId,
    root_rhs: TermId,
    level: usize,
    index_sort: Sort,
) -> Option<TermId> {
    cache.deep(terms, root_lhs, root_rhs, level, index_sort)
}

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

/// Budget on consecutive theory-conflict rounds whose own SAT search recorded
/// ZERO propositional conflicts, i.e. rounds where none of the blocking clauses
/// accumulated so far became falsified during the search.
///
/// A long run of such rounds is the signature of the loop enumerating total
/// models with every blocking clause a point-block. `MAX_SPLITS_LIA` (1e6)
/// cannot bound that -- at the measured ~40 rounds/s it is ~7h -- so in practice
/// only the caller deadline or the memory watchdog ends the loop, which makes
/// the verdict host-dependent (#7956).
///
/// This is a fixture-calibrated BUDGET, not a proof of non-productivity. A
/// zero-conflict theory-conflict round is NOT evidence that the blocking
/// clauses prune nothing: converging certified refutations contain stretches of
/// exactly this signature. Two measured bounds fix the window (quiet host,
/// 2026-08-25):
///
/// * LOWER. `group_quantifiers` is 321/0 at budgets >= 24, and 319/2 at 20 and
///   16 (`array_frame_u64_guarded_witness_{,selfcheck_}discharges_unsat`). The
///   longest zero-conflict run measured in any certified frame refutation is
///   8 rounds.
/// * UPPER. On `QUANTIFIER_CONSUMER_EXT_EQ_TSEITIN` (#7956) the diverging split-loop
///   invocation reaches a 142-round run at split iteration ~991 (~6s) and does
///   not reach 160 until ~69s. Anything > 142 leaves that divergence unbounded.
///
/// 128 sits near the top of [24, 142]: maximum completeness margin (5.3x the
/// measured suite floor) while still firing on #7956, at the cost of only ~10%
/// efficacy headroom.
///
/// It bounds ONE split-loop invocation, NOT the whole check-sat: on perturbed
/// variants of the same fixture the guard fires once and the query still runs
/// 45-100s afterwards in post-Unknown quantifier-loop routing, which has no
/// deadline poll of its own (tracked separately). Exhausting the budget yields
/// `UnknownReason::SplitLimit` -- the same fail-closed `Unknown` the split cap
/// itself produces -- and the guard sits on the theory-conflict arm, where it
/// can neither reach the Sat handler nor let the SAT solver conclude UNSAT. The
/// cost is COMPLETENESS, never soundness.
pub(in crate::executor) const MAX_UNPRODUCTIVE_CONFLICT_ROUNDS: usize = 128;

/// Companion CUMULATIVE bound on unproductive rounds within one split-loop
/// invocation.
///
/// `MAX_UNPRODUCTIVE_CONFLICT_ROUNDS` counts CONSECUTIVE zero-conflict rounds,
/// so a single productive round anywhere in the stream resets it to zero. That
/// is the right signal for the #7956 fixture, whose enumeration is one
/// uninterrupted run -- but it is defeated by an enumeration that is merely
/// SPRINKLED with conflicts. Measured: adding one unused `(declare-const)` to
/// QUANTIFIER_CONSUMER_EXT_EQ_TSEITIN, a semantics-preserving perturbation, takes it from a
/// 16s `Unknown` to burning a 120s budget, with `split_rounds` growing steadily
/// while the consecutive counter keeps getting reset.
///
/// This bounds the TOTAL, so an enumeration cannot buy unbounded time with an
/// occasional conflict. It is deliberately 8x the consecutive bound: a
/// refutation that genuinely converges spends its unproductive rounds in short
/// runs (the longest measured in any certified frame refutation is 8), so
/// reaching 1024 of them in ONE invocation is already the enumeration
/// signature. Same fail-closed exit, same `UnknownReason::SplitLimit`, same
/// COMPLETENESS-not-soundness trade.
pub(in crate::executor) const MAX_TOTAL_UNPRODUCTIVE_ROUNDS: usize = 1024;

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
    witness_cache: &mut ArrayExtWitnessCache,
    disequality_term: TermId,
) -> Option<(TermId, TermId, bool)> {
    let (lhs, rhs, is_distinct) = parse_expression_split_disequality(terms, disequality_term)?;
    let mut bindings = Vec::new();
    let (left_atom, right_atom, leaf_lhs, leaf_rhs) =
        create_expression_split_pair_atoms(terms, witness_cache, lhs, rhs, &mut bindings)?;
    if !bindings.is_empty() {
        // Materialize the logical extensionality clause even though the split
        // encoder may lower it directly to SAT literals. Hash-consing lets a
        // proof reconstructed in this shape recover the exact generation-site
        // binding chain instead of trusting a symbol name.
        let root_eq = terms.mk_eq(lhs, rhs);
        let leaf_eq = terms.mk_eq(leaf_lhs, leaf_rhs);
        let not_leaf_eq = terms.mk_not(leaf_eq);
        let ext_clause = terms.mk_or(vec![root_eq, not_leaf_eq]);
        witness_cache.record_generated_clause(terms, ext_clause, bindings);
    }
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
///   per canonical array pair and public query — the witness cache owns exact
///   identity provenance, so repeated splits on the same pair reuse it
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
    witness_cache: &mut ArrayExtWitnessCache,
    lhs: TermId,
    rhs: TermId,
    bindings: &mut Vec<ArrayExtWitnessBinding>,
) -> Option<(TermId, TermId, TermId, TermId)> {
    if terms.sort(lhs) != terms.sort(rhs) {
        return None;
    }

    match terms.sort(lhs).clone() {
        Sort::Real => {
            let lt_atom = terms.mk_lt(lhs, rhs);
            let gt_atom = terms.mk_gt(lhs, rhs);
            Some((lt_atom, gt_atom, lhs, rhs))
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
            Some((le_atom, ge_atom, lhs, rhs))
        }
        Sort::Array(_) => {
            // Extensionality expression-split for Array-sorted disequalities.
            // `create_expression_split_atoms` previously returned `None` here,
            // bailing `Unknown(ExpressionSplit)` on satisfiable AUFLIA bases
            // whose only unsplittable disequalities were between arrays
            // (`seq_array(s1) ≠ seq_array(s2)`, `seq_array(s) ≠ store(a,i,v)`).
            //
            // Mint the fresh difference index using the SAME per-query canonical
            // pair cache as the eager fixpoint so it is shared/deduped,
            // then reduce to the element-sorted split (recurses for nested
            // arrays; bottoms out in Int/Real).
            let diff_var = array_extensionality_witness(terms, witness_cache, lhs, rhs)?;
            bindings.push(ArrayExtWitnessBinding {
                witness: diff_var,
                array_a: lhs,
                array_b: rhs,
            });
            let sel_lhs = terms.mk_select(lhs, diff_var);
            let sel_rhs = terms.mk_select(rhs, diff_var);
            create_expression_split_pair_atoms(terms, witness_cache, sel_lhs, sel_rhs, bindings)
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
