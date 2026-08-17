// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![forbid(unsafe_code)]

//! AY LIA - Linear Integer Arithmetic theory solver
//!
//! Implements branch-and-bound over LRA for integer arithmetic,
//! following the DPLL(T) approach where the SAT solver handles branching.
//!
//! ## Algorithm Overview
//!
//! The solver uses lazy branch-and-bound with cutting planes:
//!
//! 1. Solve the LRA (Linear Real Arithmetic) relaxation
//! 2. If UNSAT, return UNSAT (integers can't satisfy it either)
//! 3. If SAT, check if all integer variables have integer values
//! 4. If all integers are satisfied, return SAT
//! 5. Otherwise, try cutting planes (Gomory, then HNF)
//! 6. If no cuts, return a split request for branch-and-bound
//!
//! ## Cutting Planes
//!
//! - **Gomory cuts**: Derived from the simplex tableau. Fast but limited when
//!   the tableau involves slack variables (internal to simplex).
//! - **HNF cuts**: Derived from the original constraint matrix using Hermite
//!   Normal Form. Works even when Gomory cuts fail due to slack variables.
//!
//! The DPLL(T) framework handles the branching by backtracking on the conflict
//! and trying alternative Boolean assignments.

#![warn(missing_docs)]
#![warn(clippy::all)]
// Gaussian-elimination echelon loops index parallel `work` rows by position;
// the index form is the natural expression (mirrors the workspace lint policy).
#![allow(clippy::needless_range_loop)]

// Import safe_eprintln! from ay-core (non-panicking eprintln replacement)
#[macro_use]
extern crate ay_core;

mod affine_implication;
mod assertion_view;
mod bounds;
mod branching;
mod check;
mod cuts;
mod dioph;
mod dioph_bridge;
mod dioph_joint_case_split;
mod dioph_joint_case_split_support;
mod dioph_substitution;
mod dioph_tighten;
mod enumeration;
mod gcd;
mod gcd_accumulative;
mod gcd_tableau;
mod hnf;
pub mod instrument;
mod intsat_bridge;
mod linear_cache;
mod linear_collect;
mod modular;
mod modular_bounds;
mod nelson_oppen;
mod parsing;
mod poly_residual;
mod solver_support;
mod state;
mod theory_impl;
mod two_var;
mod types;

pub use check::{
    reset_probe_subset_hint, restore_probe_state, save_probe_state, ProbeStateSnapshot,
};
pub(crate) use types::{
    gcd_of_abs, lia_debug_flags, positive_mod, AlgebraicDetectStamp, CutScopeState,
    DirectEnumResult, EnumMatrix, EnumRrefCache, EnumRrefOutcome, IneqOp, LinearCoeffs,
    SubstitutionMap, SubstitutionTriple,
};
pub use types::{DiophState, HnfCutKey, LiaModel, LiaSolver, LiaTimings, StoredCut};

// #8529: Use deterministic hash maps in all builds.
use ay_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};
use ay_core::term::{Constant, Symbol, TermData, TermId, TermStore};
use ay_core::FarkasAnnotation;
use ay_core::{
    propagate_tight_bound_equalities, unwrap_not, DiscoveredDisequality, DiscoveredEquality,
    DisequalitySplitRequest, EqualityPropagationResult, Sort, SplitRequest, TheoryConflict,
    TheoryLit, TheoryPropagation, TheoryResult, TheorySolver,
};
use ay_lra::{Bound, GcdRowInfo, LraSolver};
use num_bigint::BigInt;
use num_integer::Integer;
use num_rational::BigRational;
use num_traits::{One, Signed, Zero};

impl<'a> LiaSolver<'a> {
    /// M-A2 lazy-persistent-combiner: rebind the borrowed term store to a
    /// SUPERSET (append-extended) store (ARRAY-PROCEDURE-CLOSER-BLUEPRINT §5 A2).
    ///
    /// SOUNDNESS: `terms` is the only `&'a`-bound field; all else is owned and
    /// `TermId`-keyed. The inner `LraSolver` reads terms through a re-pointable
    /// raw pointer (`set_terms`), which we also re-point here so it tracks the
    /// same store. Because the store is append-only, every previously-resolved
    /// `TermId` maps to identical `TermData`/`Sort` in `new_terms`, so every
    /// cache stays valid. Only sound when `new_terms` is a superset of the
    /// store this solver was built on. Debug-only (shadow arm).
    #[cfg(debug_assertions)]
    pub fn rebind_terms(&mut self, new_terms: &'a TermStore) {
        self.terms = new_terms;
        self.lra.set_terms(new_terms);
    }

    /// Create a new LIA solver
    #[must_use]
    pub fn new(terms: &'a TermStore) -> Self {
        let mut lra = LraSolver::new(terms);
        lra.set_integer_mode(true);
        LiaSolver {
            terms,
            lra,
            integer_vars: HashSet::default(),
            sorted_integer_vars: Vec::new(),
            int_bounds_dirty: HashSet::default(),
            // Conservative start (#C4): the first bounds-conflict check
            // always scans every integer variable.
            int_bounds_all_dirty: true,
            int_constant_terms: HashMap::default(),
            collect_int_vars_visited: HashSet::default(),
            asserted: Vec::new(),
            const_bool_conflicts: Vec::new(),
            in_search_phase: false,
            dioph_bcp_unproductive_streak: 0,
            scopes: Vec::new(),
            cut_scopes: Vec::new(),
            cut_state_scopes: Vec::new(),
            gomory_iterations: 0,
            // Keep Gomory as a quick first pass; avoid burning entire checks on cycling cuts.
            max_gomory_iterations: 8,
            hnf_iterations: 0,
            hnf_barren_fingerprint: None,
            max_hnf_iterations: 50, // HNF is more expensive, limit more
            seen_hnf_cuts: HashSet::default(),
            seen_hnf_cuts_trail: Vec::new(),
            learned_cuts: Vec::new(),
            dioph_equality_key: Vec::new(),
            dioph_needs_full_check: false,
            dioph_needs_revalidation: false,
            dioph_safe_dependent_vars: HashSet::default(),
            dioph_cached_substitutions: Vec::new(),
            dioph_cached_modular_gcds: Vec::new(),
            dioph_cached_reasons: Vec::new(),
            dioph_modified_bounds: false,
            dioph_bound_term_ids: HashSet::default(),
            pending_equalities: Vec::new(),
            propagated_equality_pairs: HashSet::default(),
            propagated_disequality_pairs: HashSet::default(),
            shared_equalities: Vec::new(),
            hidden_interface: false,
            shared_eq_seen: HashSet::default(),
            conflict_probe: false,
            probe_subset_cache: false,
            verify_only: false,
            shared_eq_revision: 0,
            detect_algebraic_cache: None,
            detect_algebraic_calls: 0,
            detect_algebraic_cache_hits: 0,
            probe_alg_incr: None,
            shared_disequalities: Vec::new(),
            pending_shared_eq_conflict: None,
            skip_shared_algebraic: false,
            timeout_callback: None,
            deadline: None,
            direct_enum_witness: None,
            enum_rref_cache: None,
            // #6359: Use process-level cached env vars (OnceLock) to avoid
            // syscalls on every DPLL(T) iteration.
            debug_lia: lia_debug_flags().debug_lia,
            debug_lia_branch: lia_debug_flags().debug_lia_branch,
            debug_lia_check: lia_debug_flags().debug_lia_check,
            debug_lia_nelson_oppen: lia_debug_flags().debug_lia_nelson_oppen,
            debug_patch: lia_debug_flags().debug_patch,
            debug_gcd: lia_debug_flags().debug_gcd,
            debug_gcd_tab: lia_debug_flags().debug_gcd_tab,
            debug_dioph: lia_debug_flags().debug_dioph,
            debug_hnf: lia_debug_flags().debug_hnf,
            debug_mod: lia_debug_flags().debug_mod,
            debug_enum: lia_debug_flags().debug_enum,
            assertion_view_cache: assertion_view::AssertionViewCache::default(),
            linear_cache: Default::default(),
            affine_cache: Default::default(),
            dioph_parse_cache: Default::default(),
            var_index_epoch: 0,
            // Per-theory runtime statistics (#4706)
            check_count: 0,
            conflict_count: 0,
            propagation_count: 0,
            affine_min_core_attempts: 0,
            affine_min_core_successes: 0,
            // Persistent buffers for augment_farkas (#8599)
            reachable_vars_buf: HashSet::default(),
            conflict_vars_buf: HashSet::default(),
            // Real per-phase timings (#8823). Populated during check().
            timings: LiaTimings::default(),
        }
    }

    /// Extract integer variables from a term and its subterms.
    /// Also collects integer constant terms for N-O propagation (#3581).
    ///
    /// Delegates to `collect_integer_vars_rec` with a reusable DAG-visited set
    /// so each hash-consed subterm is processed at most once per top-level
    /// call. Byte-identical to the naive recursion: every effect below is
    /// idempotent per term (set inserts / `or_insert` / dirty-marking), and the
    /// pre-order first-visit sequence — hence `integer_vars`/`sorted_integer_vars`
    /// insertion order and the `var_index_epoch` count — is unchanged; only the
    /// redundant re-descent into already-processed shared subterms is skipped.
    fn collect_integer_vars(&mut self, term: TermId) {
        let mut visited = std::mem::take(&mut self.collect_int_vars_visited);
        visited.clear();
        self.collect_integer_vars_rec(term, &mut visited);
        self.collect_int_vars_visited = visited;
    }

    fn collect_integer_vars_rec(&mut self, term: TermId, visited: &mut HashSet<TermId>) {
        // Hash-consed DAG: a subterm shared by many parents is walked once.
        if !visited.insert(term) {
            return;
        }
        match self.terms.get(term) {
            TermData::Const(Constant::Int(n)) => {
                // Track integer constants for Nelson-Oppen propagation (#3581).
                // These allow propagate_equalities to pair derived tight bounds
                // (e.g., f(1) = 0) with existing constant terms (TermId for 0).
                self.int_constant_terms.entry(n.clone()).or_insert(term);
            }
            TermData::Var(_, _) => {
                // Check the sort of this term to see if it's an integer
                if matches!(self.terms.sort(term), Sort::Int) {
                    // The enclosing literal/equality may (re)tighten this
                    // var's LRA bounds — mark for the next bounds scan (#C4).
                    self.mark_int_bound_dirty(term);
                    if self.integer_vars.insert(term) {
                        // Variable index changed → dioph parse rows stale (#C2).
                        self.var_index_epoch += 1;
                        Self::insert_sorted_integer_var(&mut self.sorted_integer_vars, term);
                    }
                }
            }
            TermData::App(sym, args) => {
                // Treat Int-sorted "opaque" arithmetic terms as integer variables.
                //
                // In AUFLIA/Nelson-Oppen, terms like (f x) : Int appear inside arithmetic
                // constraints (e.g., (< (f x) y)). The linear parser treats these terms as
                // atomic variables, so they must be tracked as integer vars for:
                // - direct enumeration (must not treat them as 0)
                // - integrality checks / branch-and-bound
                if matches!(self.terms.sort(term), Sort::Int) {
                    let is_atomic_var = match sym.name() {
                        // Linear arithmetic ops are decomposed into their arguments.
                        "+" | "-" => false,
                        "*" => {
                            // Match collect_linear_coeffs(): treat non-linear multiplication as
                            // an opaque variable; otherwise decompose.
                            let non_const_args = args
                                .iter()
                                .filter(|&&arg| {
                                    !matches!(
                                        self.terms.get(arg),
                                        TermData::Const(Constant::Int(_) | Constant::Rational(_))
                                    )
                                })
                                .count();
                            non_const_args > 1
                        }
                        // Everything else (UF apps, select, div/mod, etc) is opaque to linear LIA.
                        _ => true,
                    };
                    if is_atomic_var {
                        // Same dirty marking as the Var case above (#C4).
                        self.mark_int_bound_dirty(term);
                        if self.integer_vars.insert(term) {
                            // Variable index changed → dioph parse rows stale (#C2).
                            self.var_index_epoch += 1;
                            Self::insert_sorted_integer_var(&mut self.sorted_integer_vars, term);
                        }
                    }
                }
                for &arg in args {
                    self.collect_integer_vars_rec(arg, visited);
                }
            }
            TermData::Let(_, body) => {
                self.collect_integer_vars_rec(*body, visited);
            }
            TermData::Not(inner) => {
                self.collect_integer_vars_rec(*inner, visited);
            }
            TermData::Ite(cond, then_branch, else_branch) => {
                self.collect_integer_vars_rec(*cond, visited);
                self.collect_integer_vars_rec(*then_branch, visited);
                self.collect_integer_vars_rec(*else_branch, visited);
            }
            _ => {}
        }
    }

    /// Equality-dense systems benefit from deeper HNF exploration.
    /// We treat a system as dense once equalities cover at least half of variables.
    fn is_equality_dense(num_equalities: usize, num_vars: usize) -> bool {
        num_vars > 0 && num_equalities.saturating_mul(2) >= num_vars
    }

    fn hnf_iteration_budget(num_equalities: usize, num_vars: usize) -> usize {
        if Self::is_equality_dense(num_equalities, num_vars) {
            20
        } else {
            2
        }
    }

    /// Extract the current model if satisfiable
    ///
    /// Returns None if the last check was not SAT or if integer constraints
    /// are not satisfied.
    /// Terms that appear in a CROSS-THEORY equality LIA was told about
    /// (`assert_shared_equality`). LIA is the authority for these: the
    /// equality is a hard constraint the LRA relaxation of a sibling solver
    /// may never have received (Int-only equalities are routed to LIA
    /// alone). See `reconcile_lia_lra_values` (#reconcile-lia-authority).
    #[must_use]
    pub fn shared_equality_terms(&self) -> HashSet<TermId> {
        let mut out: HashSet<TermId> = HashSet::default();
        for (lhs, rhs, _) in &self.shared_equalities {
            out.insert(*lhs);
            out.insert(*rhs);
        }
        out
    }

    /// Extract an integer model for the current satisfiable state, preferring
    /// a direct enumeration witness when one was found.
    pub fn extract_model(&self) -> Option<LiaModel> {
        let debug = self.debug_lia;

        if let Some(model) = &self.direct_enum_witness {
            return Some(model.clone());
        }

        let lra_model = self.lra.extract_model();
        let mut values = HashMap::default();

        if debug {
            safe_eprintln!(
                "[LIA] extract_model: lra_model has {} values, integer_vars has {} entries",
                lra_model.values.len(),
                self.integer_vars.len()
            );
            for &term in &self.integer_vars {
                safe_eprintln!("[LIA] integer_var: term {}", term.0);
            }
        }

        // Convert rational values to integers, checking constraints
        for (&term, val) in &lra_model.values {
            if debug {
                safe_eprintln!(
                    "[LIA] checking term {}: in integer_vars={}",
                    term.0,
                    self.integer_vars.contains(&term)
                );
            }
            if self.integer_vars.contains(&term) {
                if Self::is_integer(val) {
                    if debug {
                        safe_eprintln!("[LIA] term {} -> int value {}", term.0, val.numer());
                    }
                    values.insert(term, val.numer().clone());
                } else {
                    // Integer constraint violated
                    if debug {
                        safe_eprintln!("[LIA] term {} has non-integer value {}", term.0, val);
                    }
                    return None;
                }
            }
        }

        if debug {
            safe_eprintln!("[LIA] final model has {} values", values.len());
        }
        // Every registered integer variable that appears in the LRA model should
        // have an integer value in our extracted model. Missing variables indicate
        // a term registration or model extraction bug.
        debug_assert!(
            self.integer_vars
                .iter()
                .all(|v| !lra_model.values.contains_key(v) || values.contains_key(v)),
            "BUG: extract_model: integer variable present in LRA model but missing from LIA model"
        );
        Some(LiaModel { values })
    }

    /// Get the underlying LRA solver
    pub fn lra_solver(&self) -> &LraSolver {
        &self.lra
    }

    /// Collect bound conflicts from the underlying LRA relaxation.
    pub fn collect_all_bound_conflicts(&self, skip_first: bool) -> Vec<TheoryConflict> {
        self.lra.collect_all_bound_conflicts(skip_first)
    }

    /// Get mutable access to the underlying LRA solver
    ///
    /// Used by NIA to add tangent plane constraints directly.
    pub fn lra_solver_mut(&mut self) -> &mut LraSolver {
        // External `&mut` access can tighten arbitrary bounds (e.g. NIA
        // tangent planes) — conservatively rescan everything (#C4).
        self.mark_int_bounds_all_dirty();
        &mut self.lra
    }

    /// Count integer variables that are currently fixed (lower bound == upper bound).
    ///
    /// Used by the iterative Dioph tightening loop to detect when tightening
    /// has fixed new variables, which signals that re-running the Dioph solver
    /// may discover new substitutions (Z3's continue_with_check pattern).
    fn count_fixed_integer_vars(&self) -> usize {
        let mut count = 0;
        for &term_id in &self.integer_vars {
            if let Some((Some(lb), Some(ub))) = self.lra.get_bounds(term_id) {
                if lb.value == ub.value {
                    count += 1;
                }
            }
        }
        count
    }

    /// Count the number of equality constraints in the asserted literals.
    ///
    /// Used to detect equality-dense problems where more aggressive HNF
    /// cut generation is beneficial. Served from the incremental view (#C1):
    /// `positive_equalities` contains exactly the `(= a b)` atoms asserted
    /// true (including repeats), matching the previous O(asserted) scan.
    fn count_equalities(&self) -> usize {
        self.assertion_view().positive_equalities.len()
    }

    /// Count asserted arithmetic relational atoms (any polarity): `=`, `<=`,
    /// `>=`, `<`, `>`. Used to recognize the "single isolated constraint" shape
    /// where pinning a concrete Diophantine witness is provably sound: when the
    /// only arithmetic atom in the system is one equality over exactly the free
    /// variables, no other constraint can rule the witness out.
    pub(crate) fn count_arith_atoms(&self) -> usize {
        let mut count = 0;
        for &(literal, _value) in &self.asserted {
            if let TermData::App(Symbol::Named(name), args) = self.terms.get(literal) {
                if matches!(name.as_str(), "=" | "<=" | ">=" | "<" | ">") && args.len() == 2 {
                    count += 1;
                }
            }
        }
        count
    }

    /// Stable, sorted, deduplicated key for the currently asserted equality
    /// atoms (#C5). Served from the incrementally maintained view instead of
    /// re-scanning and re-sorting `asserted` on every BCP-time check.
    ///
    /// Used to avoid re-running Diophantine solving when only inequalities
    /// change (common during branch-and-bound).
    fn equality_key(&self) -> &[TermId] {
        &self.assertion_view().equality_key
    }
}

#[cfg(kani)]
mod verification;

#[cfg(test)]
mod dioph_conflict_tests;
#[allow(clippy::panic)]
#[cfg(test)]
mod tests;
