// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! PropagateValues preprocessing pass
//!
//! Eliminates ground equalities of the form `(= EXPR CONST)` by building a
//! substitution table and rewriting all occurrences of `EXPR` to `CONST`.
//!
//! This is critical for QF_UFLIA benchmarks that define UF functions via
//! exhaustive lookup tables (e.g., `(= (Succ 0) 1)`, `(= (Sum 3 4) 7)`).
//! Without this pass, all ground UF equalities survive preprocessing and
//! become theory atoms, causing combinatorial explosion in DPLL(T).
//!
//! Two entry points with DIFFERENT contracts:
//! - [`PreprocessingPass::apply`] — the solve-pipeline pass: preserves defining
//!   equalities (EUF congruence closure needs them) and never drops formulas.
//! - [`PropagateValues::apply_goal`] — z3's `propagate-values` GOAL semantics
//!   for the tactic surface: also harvests asserted Boolean literals and
//!   `(= x c)` over variables, rewrites definers by each other (forward and
//!   backward sweeps), drops formulas that fold to `true`, and collapses a
//!   conflicting goal to `{false}`. Equivalence-preserving (see its docs).
//!
//! # Reference
//! - Z3: `reference/z3/src/ast/simplifiers/propagate_values.cpp`
//! - Design: the development design notes
//! - Issue: #5081

use super::PreprocessingPass;
// #8529: Use deterministic hash maps in all builds.
use ay_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};
use ay_core::term::{Symbol, TermData};
use ay_core::{Sort, TermId, TermStore};

/// Red zone size for `stacker::maybe_grow` in propagate_values recursion (#8414).
const PROPVAL_STACK_RED_ZONE: usize = 32 * 1024;

/// Stack segment size allocated by stacker for propagate_values recursion.
const PROPVAL_STACK_SIZE: usize = 1024 * 1024;

/// Maximum forward+backward rounds in goal mode (`apply_goal`). Matches z3's
/// bounded fixpoint in `propagate_values.cpp`; each round either changes a
/// formula or the loop stops, and substitution targets are always constants
/// (strictly reducing), so termination never depends on this bound in practice.
const GOAL_MODE_MAX_ROUNDS: usize = 4;

/// Propagates ground equalities `(= EXPR CONST)` through assertions.
///
/// Phase 1: Scan assertions for `(= EXPR CONST)` where CONST is a concrete
/// constant and EXPR is any non-constant term (including function applications).
///
/// Phase 2: Rewrite NON-DEFINING assertions by substituting EXPR -> CONST.
/// The defining equalities themselves are preserved because EUF needs them
/// to compute congruence closure on non-ground applications like `Succ(x)`.
///
/// This is important for correctness: removing `(= (Succ 0) 1)` from the
/// formula makes `Succ` truly uninterpreted, which can change satisfiability.
pub(crate) struct PropagateValues {
    /// Substitution map: expression TermId -> constant TermId
    value_map: HashMap<TermId, TermId>,
    /// Set of defining equality assertions (TermIds) to skip during rewriting
    defining_equalities: HashSet<TermId>,
    /// Rewrite cache for the current iteration
    cache: HashMap<TermId, TermId>,
}

impl PropagateValues {
    pub(crate) fn new() -> Self {
        Self {
            value_map: HashMap::default(),
            defining_equalities: HashSet::default(),
            cache: HashMap::default(),
        }
    }

    /// Seed the substitution map from an EXTERNALLY-supplied `key ↦ value` table
    /// (F6 ground-bridge fold), then rewrite terms with [`Self::rewrite_seeded`].
    ///
    /// The caller owns the map's soundness contract: every `key ↦ value` must be
    /// an asserted / entailed equality of the CURRENT problem (so substituting is
    /// an exact equivalence), and no key may be a variable that occurs under a
    /// surviving binder (`rewrite` passes `Forall`/`Exists`/`Let` through
    /// unchanged, so substitution is confined to ground positions — no capture).
    /// Values are typically constants, which are strictly reducing. This shares
    /// the folding dispatch (arith / BV / bv2nat / int2bv / Boolean / array), so a
    /// pin that turns a bridge argument constant collapses the whole term. Seed
    /// ONCE, then rewrite each assertion — the rewrite cache is keyed by term for
    /// the fixed map, so it is valid across every assertion of the same seed.
    pub(crate) fn seed_substitution(&mut self, subst: &HashMap<TermId, TermId>) {
        self.value_map = subst.clone();
        self.cache.clear();
    }

    /// Rewrite `term` under the map installed by [`Self::seed_substitution`].
    pub(crate) fn rewrite_seeded(&mut self, terms: &mut TermStore, term: TermId) -> TermId {
        self.rewrite(terms, term)
    }

    /// Check if a term is a concrete constant.
    fn is_constant(terms: &TermStore, term: TermId) -> bool {
        matches!(terms.get(term), TermData::Const(_))
    }

    /// Check if a term is ground (contains no free variables).
    ///
    /// Ground terms consist only of constants and function applications over
    /// other ground terms. Variables make a term non-ground.
    /// Uses `stacker::maybe_grow` for stack safety on deeply nested terms (#8414).
    ///
    /// Visited-set deduplication: the term store is a hash-consed DAG; without
    /// it this walk enumerates every tree PATH — exponential in sharing depth
    /// (the DAG→tree pathology; a large BMC instance hung here). Skipping a
    /// revisited node as `true` is sound: `all`/`&&` short-circuit on the first
    /// `false` and every `false` terminates ALL ancestors immediately, so any
    /// node the walk continues past evaluated `true`, and that value is fixed
    /// for the (immutable, interned) term table.
    fn is_ground(terms: &TermStore, term: TermId) -> bool {
        let mut visited: HashSet<TermId> = HashSet::default();
        Self::is_ground_inner(terms, term, &mut visited)
    }

    fn is_ground_inner(terms: &TermStore, term: TermId, visited: &mut HashSet<TermId>) -> bool {
        stacker::maybe_grow(PROPVAL_STACK_RED_ZONE, PROPVAL_STACK_SIZE, || {
            if !visited.insert(term) {
                return true;
            }
            match terms.get(term) {
                TermData::Const(_) => true,
                TermData::Var(_, _) => false,
                TermData::App(_, args) => args
                    .iter()
                    .all(|&a| Self::is_ground_inner(terms, a, visited)),
                TermData::Not(inner) => Self::is_ground_inner(terms, *inner, visited),
                TermData::Ite(c, t, e) => {
                    Self::is_ground_inner(terms, *c, visited)
                        && Self::is_ground_inner(terms, *t, visited)
                        && Self::is_ground_inner(terms, *e, visited)
                }
                _ => false,
            }
        }) // stacker::maybe_grow
    }

    /// Extract a value equality from an assertion: `(= EXPR CONST)` or `(= CONST EXPR)`.
    ///
    /// Returns `Some((expr, const))` if the assertion is a top-level equality
    /// where exactly one side is a concrete constant and the other is a ground
    /// (variable-free) non-constant term.
    fn extract_value_equality(terms: &TermStore, assertion: TermId) -> Option<(TermId, TermId)> {
        match terms.get(assertion) {
            TermData::App(sym, args) if sym.name() == "=" && args.len() == 2 => {
                let (lhs, rhs) = (args[0], args[1]);
                let lhs_const = Self::is_constant(terms, lhs);
                let rhs_const = Self::is_constant(terms, rhs);
                match (lhs_const, rhs_const) {
                    (false, true) if Self::is_ground(terms, lhs) => Some((lhs, rhs)),
                    (true, false) if Self::is_ground(terms, rhs) => Some((rhs, lhs)),
                    _ => None,
                }
            }
            _ => None,
        }
    }

    /// Rewrite a term by substituting known value mappings.
    ///
    /// Bottom-up: first rewrite all children, then check if the result
    /// matches a known value in `value_map`. Uses canonical constructors
    /// (mk_eq, mk_add, etc.) when rebuilding to trigger constant folding.
    /// Uses `stacker::maybe_grow` for stack safety on deeply nested terms (#8414).
    fn rewrite(&mut self, terms: &mut TermStore, term: TermId) -> TermId {
        stacker::maybe_grow(PROPVAL_STACK_RED_ZONE, PROPVAL_STACK_SIZE, || {
            if let Some(&cached) = self.cache.get(&term) {
                return cached;
            }

            // Check direct substitution first
            if let Some(&value) = self.value_map.get(&term) {
                self.cache.insert(term, value);
                return value;
            }

            let result = match terms.get(term).clone() {
                TermData::Const(_) | TermData::Var(_, _) => term,

                TermData::App(sym, args) => {
                    let new_args: Vec<TermId> =
                        args.iter().map(|&a| self.rewrite(terms, a)).collect();

                    if new_args == args {
                        term
                    } else {
                        // Rebuild using canonical constructors for constant folding.
                        // BV and array constructors do constant folding when all
                        // arguments are constants, which is critical for QF_ABV
                        // benchmarks where PropagateValues substitutes array
                        // select results with concrete BV constants.
                        let rebuilt = match sym.name() {
                            // Boolean / arithmetic
                            "=" if new_args.len() == 2 => {
                                terms.mk_eq_coerce(new_args[0], new_args[1])
                            }
                            "+" => terms.mk_add(new_args),
                            "-" => terms.mk_sub(new_args),
                            "*" => terms.mk_mul(new_args),
                            "<" if new_args.len() == 2 => terms.mk_lt(new_args[0], new_args[1]),
                            "<=" if new_args.len() == 2 => terms.mk_le(new_args[0], new_args[1]),
                            ">" if new_args.len() == 2 => terms.mk_gt(new_args[0], new_args[1]),
                            ">=" if new_args.len() == 2 => terms.mk_ge(new_args[0], new_args[1]),
                            "div" if new_args.len() == 2 => {
                                terms.mk_intdiv(new_args[0], new_args[1])
                            }
                            "mod" if new_args.len() == 2 => terms.mk_mod(new_args[0], new_args[1]),
                            "abs" if new_args.len() == 1 => terms.mk_abs(new_args[0]),

                            // Boolean connectives: the canonical constructors
                            // fold constants/complements/absorption (mk_or
                            // folds `(or false q)` → `q`), which is what makes
                            // a harvested literal actually simplify the goal.
                            // Pure equivalence-preserving folds, safe on both
                            // the goal-mode and solve-pipeline paths.
                            "or" => terms.mk_or(new_args),
                            "and" => terms.mk_and(new_args),
                            "=>" if new_args.len() == 2 => {
                                terms.mk_implies(new_args[0], new_args[1])
                            }
                            "xor" if new_args.len() == 2 => terms.mk_xor(new_args[0], new_args[1]),

                            // BV arithmetic (constant folding on all-constant args)
                            "bvadd" if new_args.len() == 2 => terms.mk_bvadd(new_args),
                            "bvsub" if new_args.len() == 2 => terms.mk_bvsub(new_args),
                            "bvmul" if new_args.len() == 2 => terms.mk_bvmul(new_args),

                            // BV bitwise
                            "bvand" if new_args.len() == 2 => terms.mk_bvand(new_args),
                            "bvor" if new_args.len() == 2 => terms.mk_bvor(new_args),
                            "bvxor" if new_args.len() == 2 => terms.mk_bvxor(new_args),
                            "bvnot" if new_args.len() == 1 => terms.mk_bvnot(new_args[0]),
                            "bvneg" if new_args.len() == 1 => terms.mk_bvneg(new_args[0]),
                            "bvnand" if new_args.len() == 2 => terms.mk_bvnand(new_args),
                            "bvnor" if new_args.len() == 2 => terms.mk_bvnor(new_args),
                            "bvxnor" if new_args.len() == 2 => terms.mk_bvxnor(new_args),

                            // BV shifts
                            "bvshl" if new_args.len() == 2 => terms.mk_bvshl(new_args),
                            "bvlshr" if new_args.len() == 2 => terms.mk_bvlshr(new_args),
                            "bvashr" if new_args.len() == 2 => terms.mk_bvashr(new_args),

                            // BV division
                            "bvudiv" if new_args.len() == 2 => terms.mk_bvudiv(new_args),
                            "bvurem" if new_args.len() == 2 => terms.mk_bvurem(new_args),
                            "bvsdiv" if new_args.len() == 2 => terms.mk_bvsdiv(new_args),
                            "bvsrem" if new_args.len() == 2 => terms.mk_bvsrem(new_args),
                            "bvsmod" if new_args.len() == 2 => terms.mk_bvsmod(new_args),

                            // BV comparisons
                            "bvult" if new_args.len() == 2 => {
                                terms.mk_bvult(new_args[0], new_args[1])
                            }
                            "bvule" if new_args.len() == 2 => {
                                terms.mk_bvule(new_args[0], new_args[1])
                            }
                            "bvugt" if new_args.len() == 2 => {
                                terms.mk_bvugt(new_args[0], new_args[1])
                            }
                            "bvuge" if new_args.len() == 2 => {
                                terms.mk_bvuge(new_args[0], new_args[1])
                            }
                            "bvslt" if new_args.len() == 2 => {
                                terms.mk_bvslt(new_args[0], new_args[1])
                            }
                            "bvsle" if new_args.len() == 2 => {
                                terms.mk_bvsle(new_args[0], new_args[1])
                            }
                            "bvsgt" if new_args.len() == 2 => {
                                terms.mk_bvsgt(new_args[0], new_args[1])
                            }
                            "bvsge" if new_args.len() == 2 => {
                                terms.mk_bvsge(new_args[0], new_args[1])
                            }
                            "bvcomp" if new_args.len() == 2 => {
                                terms.mk_bvcomp(new_args[0], new_args[1])
                            }

                            // BV concat/extract (extract uses indexed params)
                            "concat" if new_args.len() == 2 => terms.mk_bvconcat(new_args),

                            // BV<->Int bridge (F6): route through the folding
                            // constructors so a `bv2nat` over a now-constant BV,
                            // or an `int2bv` over a now-constant Int, collapses to
                            // its literal instead of surviving as an opaque app.
                            // `mk_bv2nat`/`mk_int2bv` are exact (SMT-LIB
                            // definitional), so this only strengthens folding.
                            "bv2nat" if new_args.len() == 1 => terms.mk_bv2nat(new_args[0]),
                            "int2bv" if new_args.len() == 1 => {
                                if let Symbol::Indexed(_, indices) = &sym {
                                    if indices.len() == 1 {
                                        terms.mk_int2bv(indices[0], new_args[0])
                                    } else {
                                        let sort = terms.sort(term).clone();
                                        terms.mk_app(sym.clone(), new_args, sort)
                                    }
                                } else {
                                    let sort = terms.sort(term).clone();
                                    terms.mk_app(sym.clone(), new_args, sort)
                                }
                            }

                            // Array operations (read-over-write simplification)
                            "select" if new_args.len() == 2 => {
                                terms.mk_select(new_args[0], new_args[1])
                            }
                            "store" if new_args.len() == 3 => {
                                terms.mk_store(new_args[0], new_args[1], new_args[2])
                            }

                            // Indexed BV operations: extract, zero_extend,
                            // sign_extend, repeat, rotate_left, rotate_right
                            "extract" if new_args.len() == 1 => {
                                if let Symbol::Indexed(_, indices) = &sym {
                                    if indices.len() == 2 {
                                        terms.mk_bvextract(indices[0], indices[1], new_args[0])
                                    } else {
                                        let sort = terms.sort(term).clone();
                                        terms.mk_app(sym.clone(), new_args, sort)
                                    }
                                } else {
                                    let sort = terms.sort(term).clone();
                                    terms.mk_app(sym.clone(), new_args, sort)
                                }
                            }
                            "zero_extend" if new_args.len() == 1 => {
                                if let Symbol::Indexed(_, indices) = &sym {
                                    if indices.len() == 1 {
                                        terms.mk_bvzero_extend(indices[0], new_args[0])
                                    } else {
                                        let sort = terms.sort(term).clone();
                                        terms.mk_app(sym.clone(), new_args, sort)
                                    }
                                } else {
                                    let sort = terms.sort(term).clone();
                                    terms.mk_app(sym.clone(), new_args, sort)
                                }
                            }
                            "sign_extend" if new_args.len() == 1 => {
                                if let Symbol::Indexed(_, indices) = &sym {
                                    if indices.len() == 1 {
                                        terms.mk_bvsign_extend(indices[0], new_args[0])
                                    } else {
                                        let sort = terms.sort(term).clone();
                                        terms.mk_app(sym.clone(), new_args, sort)
                                    }
                                } else {
                                    let sort = terms.sort(term).clone();
                                    terms.mk_app(sym.clone(), new_args, sort)
                                }
                            }
                            "repeat" if new_args.len() == 1 => {
                                if let Symbol::Indexed(_, indices) = &sym {
                                    if indices.len() == 1 {
                                        terms.mk_bvrepeat(indices[0], new_args[0])
                                    } else {
                                        let sort = terms.sort(term).clone();
                                        terms.mk_app(sym.clone(), new_args, sort)
                                    }
                                } else {
                                    let sort = terms.sort(term).clone();
                                    terms.mk_app(sym.clone(), new_args, sort)
                                }
                            }
                            "rotate_left" if new_args.len() == 1 => {
                                if let Symbol::Indexed(_, indices) = &sym {
                                    if indices.len() == 1 {
                                        terms.mk_bvrotate_left(indices[0], new_args[0])
                                    } else {
                                        let sort = terms.sort(term).clone();
                                        terms.mk_app(sym.clone(), new_args, sort)
                                    }
                                } else {
                                    let sort = terms.sort(term).clone();
                                    terms.mk_app(sym.clone(), new_args, sort)
                                }
                            }
                            "rotate_right" if new_args.len() == 1 => {
                                if let Symbol::Indexed(_, indices) = &sym {
                                    if indices.len() == 1 {
                                        terms.mk_bvrotate_right(indices[0], new_args[0])
                                    } else {
                                        let sort = terms.sort(term).clone();
                                        terms.mk_app(sym.clone(), new_args, sort)
                                    }
                                } else {
                                    let sort = terms.sort(term).clone();
                                    terms.mk_app(sym.clone(), new_args, sort)
                                }
                            }

                            _ => {
                                let sort = terms.sort(term).clone();
                                terms.mk_app(sym.clone(), new_args, sort)
                            }
                        };
                        // Check if the rebuilt term is now in value_map
                        if let Some(&value) = self.value_map.get(&rebuilt) {
                            value
                        } else {
                            rebuilt
                        }
                    }
                }

                TermData::Not(inner) => {
                    let new_inner = self.rewrite(terms, inner);
                    if new_inner == inner {
                        term
                    } else {
                        terms.mk_not(new_inner)
                    }
                }

                TermData::Ite(c, t, e) => {
                    let nc = self.rewrite(terms, c);
                    let nt = self.rewrite(terms, t);
                    let ne = self.rewrite(terms, e);
                    if nc == c && nt == t && ne == e {
                        term
                    } else {
                        terms.mk_ite(nc, nt, ne)
                    }
                }

                // Let, Forall, Exists — pass through (not needed for ground value propagation)
                TermData::Let(_, _) | TermData::Forall(_, _, _) | TermData::Exists(_, _, _) => term,
                // All current TermData variants are handled above.
                // This arm is required by #[non_exhaustive] and catches future variants.
                other => unreachable!("unhandled TermData variant in rewrite(): {other:?}"),
            };

            self.cache.insert(term, result);
            result
        }) // stacker::maybe_grow
    }

    /// Goal-mode value propagation — the transform behind the
    /// `(apply propagate-values)` tactic surface (z3's `propagate-values`
    /// GOAL semantics, distinct from the solve-pipeline
    /// [`PreprocessingPass::apply`], which must preserve defining equalities
    /// for EUF congruence closure).
    ///
    /// SOUNDNESS CONTRACT: this MUST be **equivalence-preserving** (every model
    /// preserved), not merely equisatisfiable — it also runs on live check-sat
    /// paths (`Z3_mk_solver_from_tactic("propagate-values")`,
    /// `Z3_solver_add_simplifier` and `TacticSolver::check_sat`), and a model
    /// produced after the transform must satisfy the ORIGINAL assertions.
    /// Every step is a conjunction equivalence:
    ///
    /// 1. substitutions are harvested only from top-level conjuncts of the same
    ///    goal — `F ∧ G[E] ≡ F ∧ G[c]` when `F ⊨ E = c` (and `F ∧ G[p] ≡
    ///    F ∧ G[true]` when `F` is the literal `p`);
    /// 2. a conjunct is never rewritten by its own harvest (rewrite BEFORE
    ///    harvest, with a FRESH map per sweep) — so a definition never erases
    ///    itself, while earlier/later definitions do rewrite it (fwd/bwd sweeps);
    /// 3. no substitution under binders (`rewrite` passes `Let`/`Forall`/
    ///    `Exists` through unchanged) — no capture;
    /// 4. map targets are always concrete `Const`s (plus the whole-formula
    ///    `f ↦ true` / `¬g ⇒ g ↦ false` literal rules) — acyclic, strictly
    ///    reducing;
    /// 5. rebuilds go through the canonical folding constructors;
    /// 6. dropping a `true` conjunct and collapsing a conjunction containing
    ///    `false` to `{false}` are equivalences of conjunctions.
    ///
    /// Returns whether the goal changed.
    pub(crate) fn apply_goal(&mut self, terms: &mut TermStore, fs: &mut Vec<TermId>) -> bool {
        let mut changed = false;
        for _round in 0..GOAL_MODE_MAX_ROUNDS {
            let forward = self.goal_sweep(terms, fs, true);
            let backward = self.goal_sweep(terms, fs, false);
            if !(forward || backward) {
                break;
            }
            changed = true;
        }

        // Post-pass (goal semantics, matching z3): a conflict collapses the
        // goal to the single literal `false`; otherwise formulas that folded
        // to `true` are dropped. Both are conjunction equivalences.
        let false_term = terms.false_term();
        let true_term = terms.true_term();
        if fs.contains(&false_term) {
            if fs.as_slice() != [false_term] {
                *fs = vec![false_term];
                changed = true;
            }
        } else {
            let before = fs.len();
            fs.retain(|&f| f != true_term);
            changed |= fs.len() != before;
        }
        changed
    }

    /// One goal-mode sweep (forward or backward) with a FRESH substitution map:
    /// each formula is rewritten under the facts harvested so far in THIS sweep,
    /// then harvested itself. Returns whether any formula changed.
    fn goal_sweep(&mut self, terms: &mut TermStore, fs: &mut [TermId], forward: bool) -> bool {
        // Fresh-state discipline: goal mode deliberately does NOT reuse
        // `reset()` (which preserves `value_map` for the solve pipeline). A
        // fresh map per sweep is what makes "rewrite before harvest" prevent a
        // definition from erasing itself; the rewrite cache is invalidated with
        // it (cache entries are keyed by term only, so they are only valid for
        // one map state). `defining_equalities` is a solve-pipeline concept and
        // is ignored here — in goal mode definers ARE rewritten by other
        // definers (z3 rewrites `(= (f (f 0)) 2)` under `(= (f 0) 1)`).
        self.value_map.clear();
        self.cache.clear();
        let mut changed = false;
        let len = fs.len();
        for step in 0..len {
            let i = if forward { step } else { len - 1 - step };
            let rewritten = self.rewrite(terms, fs[i]);
            if rewritten != fs[i] {
                fs[i] = rewritten;
                changed = true;
            }
            self.harvest_goal_formula(terms, rewritten);
        }
        changed
    }

    /// Harvest the facts an asserted goal formula `f` contributes (z3's
    /// `propagate_values` harvest):
    ///
    /// - `(= a b)` with exactly ONE `Const` side → `expr ↦ const` (NO
    ///   groundness gate in goal mode: `(= x 5)` over a `declare-const` and the
    ///   non-ground `(= (f y) 3)` are both harvested — capture-safe because
    ///   `rewrite` never substitutes under binders);
    /// - `(not g)` → `g ↦ false`;
    /// - any other Bool formula → `f ↦ true` (z3's general literal rule).
    fn harvest_goal_formula(&mut self, terms: &TermStore, f: TermId) {
        // A constant formula (`true`, or the `false` a conflict folded to)
        // contributes no substitution — and `Const` keys are banned from the
        // map (see `insert_goal_value`).
        if Self::is_constant(terms, f) {
            return;
        }
        let true_term = terms.true_term();
        let false_term = terms.false_term();
        match terms.get(f) {
            TermData::App(sym, args) if sym.name() == "=" && args.len() == 2 => {
                let (lhs, rhs) = (args[0], args[1]);
                let lhs_const = Self::is_constant(terms, lhs);
                let rhs_const = Self::is_constant(terms, rhs);
                match (lhs_const, rhs_const) {
                    (false, true) => self.insert_goal_value(terms, lhs, rhs),
                    (true, false) => self.insert_goal_value(terms, rhs, lhs),
                    // Zero (or two — impossible after mk_eq folding) const
                    // sides: still an asserted Bool atom, so the general
                    // `f ↦ true` rule applies.
                    _ => self.insert_goal_value(terms, f, true_term),
                }
            }
            TermData::Not(inner) => {
                let inner = *inner;
                self.insert_goal_value(terms, inner, false_term);
            }
            _ => {
                if terms.sort(f) == &Sort::Bool {
                    self.insert_goal_value(terms, f, true_term);
                }
            }
        }
    }

    /// The single goal-mode map insertion point: record `key ↦ value` and
    /// invalidate the rewrite cache (cache entries are keyed by term only, so
    /// any entry computed under the previous map state may be stale).
    ///
    /// INVARIANT (defensive gate): a `Const` key must NEVER enter `value_map` —
    /// `rewrite` consults the map BEFORE its `Const` pass-through arm, so e.g.
    /// a `true ↦ false` entry (constructible only via a raw `Not(Const)` proof
    /// literal, `mk_not_raw`; `mk_not` folds it away) would rewrite the
    /// constant `true` globally — a wrong-verdict machine.
    fn insert_goal_value(&mut self, terms: &TermStore, key: TermId, value: TermId) {
        if Self::is_constant(terms, key) {
            debug_assert!(
                false,
                "BUG: attempted to insert a Const key into the propagate-values map"
            );
            return;
        }
        if self.value_map.insert(key, value) != Some(value) {
            self.cache.clear();
        }
    }
}

impl Default for PropagateValues {
    fn default() -> Self {
        Self::new()
    }
}

impl PreprocessingPass for PropagateValues {
    fn apply(&mut self, terms: &mut TermStore, assertions: &mut Vec<TermId>) -> bool {
        // Phase 1: Scan assertions for ground equalities (= EXPR CONST)
        let mut new_entries = false;
        for &assertion in assertions.iter() {
            if let Some((expr, value)) = Self::extract_value_equality(terms, assertion) {
                // Only insert if not already known (avoid overwriting)
                if !self.value_map.contains_key(&expr) {
                    self.value_map.insert(expr, value);
                    self.defining_equalities.insert(assertion);
                    new_entries = true;
                }
            }
        }

        if self.value_map.is_empty() {
            return false;
        }

        // Phase 2: Rewrite NON-DEFINING assertions by substituting EXPR -> CONST.
        // Defining equalities like (= (Succ 0) 1) are preserved unchanged because
        // EUF needs them to compute congruence closure on non-ground applications.
        // Without them, Succ becomes truly uninterpreted and the formula changes.
        let mut modified = new_entries;
        for assertion in assertions.iter_mut() {
            if self.defining_equalities.contains(assertion) {
                continue;
            }
            let new = self.rewrite(terms, *assertion);
            if new != *assertion {
                *assertion = new;
                modified = true;
            }
        }

        // Note: We do NOT remove tautological assertions. The defining equalities
        // must remain for EUF correctness, and any tautological rewrites in
        // non-defining assertions are harmless (Tseitin encodes them trivially).

        modified
    }

    fn reset(&mut self) {
        // Clear rewrite cache between fixed-point iterations so new
        // substitutions from other passes can be picked up.
        self.cache.clear();
        // Preserve value_map and defining_equalities across iterations —
        // accumulated ground equalities remain valid.
    }
}

#[cfg(test)]
mod tests;
