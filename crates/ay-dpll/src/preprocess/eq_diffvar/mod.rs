// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! EqDiffVar preprocessing pass (#23 keystone, uncovered half / inc-14).
//!
//! Bool-guarded VAR-VAR equality chains — `(or (not g) (= x y))` networks and
//! BMC-unrolling `or`-of-`and` copy blocks — leave every equality atom over a
//! distinct variable pair. The DPLL(T) search then re-derives the same linear
//! facts on every guard branch: measured 187k decisions / 262k LIA
//! propagations without closing the MOESI blocking checks that z3 decides in
//! 0.08s (51 conflicts) via theory propagation.
//!
//! This pass reduces multi-variable equality atoms to single-variable
//! (var-CONST) atoms by definitional difference variables:
//!
//! 1. Normalize each nested Int equality atom `(= a b)` to the canonical
//!    integer linear form `lin = rhs` (`lin` = sign/gcd-normalized
//!    combination of >= 2 leaves, `rhs` an integer constant).
//! 2. Introduce ONE fresh Int variable `d := lin` per distinct `lin`
//!    (deduped across atoms, so `(= x y)` and `(= x (+ y 5))` share a `d`).
//! 3. Define `d` by the unconditional pair `(<= d lin)` / `(>= d lin)` and
//!    rewrite every occurrence of the atom to `(= d rhs)` in place.
//!
//! Atoms over the SAME difference variable (`(= d 0)` vs `(= d 5)`) now
//! conflict directly through `d`'s bounds, so guard branching is pruned by
//! the existing single-variable bound propagation instead of fresh LIA
//! derivations per branch. Measured on the inc-13 differential corpus
//! (32 dumped blocking checks): 0/21 hard files decided at any budget
//! before, 17/21 decided in 0.3-1.9s after, verdicts matching z3.
//!
//! # Soundness
//!
//! The transform is a definitional extension, hence exactly equisatisfiable
//! (and model-preserving over the original signature): `d` is FRESH, its
//! definition `d = lin` is asserted unconditionally, and every rewrite
//! replaces an atom by an atom equivalent under that definition
//! (`(= a b)  <=>  (= d rhs)` whenever `a - b` normalizes to `lin - rhs`).
//! Every model of the original formula extends uniquely (assign `d` the
//! value of `lin`); every model of the rewritten formula restricts to a
//! model of the original. All arithmetic is exact `BigRational`/`BigInt`.
//! Atoms whose canonical `rhs` is non-integral (e.g. `2x - 2y = 1`) are
//! SKIPPED, never folded.
//!
//! The definition is asserted as an inequality PAIR, not a unit equality:
//! a unit `(= d lin)` is indistinguishable from user input to downstream
//! unit-equality substitution (`VariableSubstitution`), which would inline
//! `d := lin` right back and undo the reduction (measured: the equality
//! form converts 4/18 MOESI dumps, the pair form 14/18).
//!
//! The wiring site (solve_harness `preprocess_lia_artifacts`) disables the
//! pass under proof production — fresh definitional variables detach
//! reconstructed proof leaves from original assertions — and honors the
//! per-run `(set-option :ay-eq-diffvar false)` opt-out. Provenance for
//! incremental sessions is widened exactly like the GuardedEqMining
//! keystone: rewritten assertions and definitional assertions are justified
//! by the union of all original source sets (the 171e87c lesson: rewritten
//! assertions with narrow positional provenance can outlive the scoped
//! assertions that justified them and produce wrong-unsat after pops).

use super::guarded_eq_mining::GuardedEqMining;
use super::PreprocessingPass;
// #8529: Use deterministic hash maps in all builds.
use ay_core::kani_compat::DetHashMap as HashMap;
use ay_core::term::TermData;
use ay_core::{Sort, TermId, TermStore};
use num_bigint::BigInt;
use num_integer::Integer;
use num_rational::BigRational;
use num_traits::{One, Signed, Zero};

/// Red zone size for `stacker::maybe_grow` in DAG recursion (#8414).
const DV_STACK_RED_ZONE: usize = 32 * 1024;

/// Stack segment size allocated by stacker for DAG recursion.
const DV_STACK_SIZE: usize = 1024 * 1024;

/// Caps keeping the pass cheap and bounded on shapes it cannot help.
const MAX_DIFF_VARS: usize = 1024;
const MAX_ROW_LEAVES: usize = 64;

/// Canonical integer linear form: sign/gcd-normalized coefficients over
/// leaf terms, sorted by `TermId`. The map key for difference-variable
/// dedup (the constant side is NOT part of the key, so atoms differing
/// only in the constant share one difference variable).
type CanonKey = Vec<(TermId, BigInt)>;

/// Difference-variable reduction pass. See module docs.
pub(crate) struct EqDiffVar {
    /// Rewrite cache for the folding phase.
    cache: HashMap<TermId, TermId>,
    /// Atom -> replacement atom `(= d rhs)` for the folding phase.
    fold_map: HashMap<TermId, TermId>,
    /// Stats: distinct difference variables introduced.
    pub(crate) diff_vars: u64,
    /// Stats: equality atoms rewritten to var-const form.
    pub(crate) rewritten_atoms: u64,
}

impl EqDiffVar {
    pub(crate) fn new() -> Self {
        Self {
            cache: HashMap::default(),
            fold_map: HashMap::default(),
            diff_vars: 0,
            rewritten_atoms: 0,
        }
    }

    /// Whether `term`'s subterm DAG contains an ITE.
    ///
    /// EqDiffVar must not fold an equality whose canonical linear row draws a
    /// leaf from an ITE — for example the `(ite bᵢ cᵢ 0)` indicators that a
    /// pseudo-boolean / cardinality constraint desugars to
    /// (`(cmp (Σ cᵢ·(ite bᵢ cᵢ 0)) k)`). Folding `(= (Σ …) k)` to `(= d k)`
    /// and defining the fresh `d` by the pair `(<= d lin)` / `(>= d lin)`
    /// DUPLICATES the ITE-bearing `lin` into two inequalities and detaches the
    /// reified selectors from the original atom, forcing the downstream LIA
    /// search into a per-branch Shannon expansion that thrashes to a (sound
    /// but battery-failing) `unknown` — whereas the untouched atom is reified
    /// linearly and decided in a couple of LIA checks (repro: negated
    /// `(_ pbeq …)` over six weighted Bools, `unknown` before / `sat` after).
    /// Skipping such rows is a pure RESTRICTION of this optional transform: it
    /// only ever leaves the atom in its original, equisatisfiable form, so it
    /// can never change a verdict (same argument as the `!has_uf` guard).
    fn contains_ite(terms: &TermStore, term: TermId) -> bool {
        stacker::maybe_grow(DV_STACK_RED_ZONE, DV_STACK_SIZE, || {
            match terms.get(term) {
                TermData::Ite(_, _, _) => true,
                TermData::Not(inner) => Self::contains_ite(terms, *inner),
                TermData::App(_, args) => args.iter().any(|&a| Self::contains_ite(terms, a)),
                TermData::Let(bindings, body) => {
                    Self::contains_ite(terms, *body)
                        || bindings.iter().any(|(_, t)| Self::contains_ite(terms, *t))
                }
                TermData::Forall(_, body, _) | TermData::Exists(_, body, _) => {
                    Self::contains_ite(terms, *body)
                }
                // `TermData` is `#[non_exhaustive]`; a leaf of an
                // unrecognized kind is treated as ITE-free (the pass then
                // proceeds exactly as before this guard existed, so a new kind
                // never regresses — the guard only ADDS skips for known ITEs).
                _ => false,
            }
        })
    }

    /// Canonicalize a parsed equality row into `(coeffs, rhs)` with integer
    /// coefficients, gcd 1, and a positive leading (lowest-`TermId`)
    /// coefficient. Returns `None` when the row is not a >=2-leaf integer
    /// row or when the normalized rhs is non-integral (such an atom is
    /// unsatisfiable over Int; deciding it is left to the solver).
    fn canonicalize(
        terms: &TermStore,
        row: &super::guarded_eq_mining::TermRow,
    ) -> Option<(CanonKey, BigInt)> {
        if row.coeffs.len() < 2 || row.coeffs.len() > MAX_ROW_LEAVES {
            return None;
        }
        // Int-sorted leaves only: the difference variable must be Int.
        // ITE-bearing leaves are also excluded (see `contains_ite`): folding
        // such a row detaches the reified selectors and thrashes the LIA search.
        for (leaf, _) in &row.coeffs {
            if *terms.sort(*leaf) != Sort::Int || Self::contains_ite(terms, *leaf) {
                return None;
            }
        }
        // Scale to integers: multiply by the lcm of coefficient denominators.
        let mut lcm = BigInt::one();
        for (_, c) in &row.coeffs {
            lcm = lcm.lcm(c.denom());
        }
        let scale = BigRational::from_integer(lcm);
        let mut ints: Vec<(TermId, BigInt)> = row
            .coeffs
            .iter()
            .map(|(t, c)| (*t, (c * &scale).to_integer()))
            .collect();
        // Divide by the gcd of the coefficients.
        let mut gcd = BigInt::zero();
        for (_, c) in &ints {
            gcd = gcd.gcd(c);
        }
        if gcd.is_zero() {
            return None;
        }
        // Sign-normalize on the lowest-TermId leaf.
        ints.sort_by_key(|(t, _)| t.index());
        let negate = ints[0].1.is_negative();
        let divisor = if negate { -gcd.clone() } else { gcd.clone() };
        for (_, c) in ints.iter_mut() {
            *c = &*c / &divisor;
        }
        let rhs = &row.rhs * scale / BigRational::from_integer(divisor);
        if !rhs.is_integer() {
            // e.g. `2x - 2y = 1`: unsatisfiable over Int; skip (never fold).
            return None;
        }
        Some((ints, rhs.to_integer()))
    }

    /// Build the linear term `sum coeff_i * leaf_i` for a canonical key.
    fn build_lin(terms: &mut TermStore, key: &CanonKey) -> TermId {
        let mut parts: Vec<TermId> = Vec::with_capacity(key.len());
        for (leaf, c) in key {
            let part = if c.is_one() {
                *leaf
            } else if (-c).is_one() {
                terms.mk_neg(*leaf)
            } else {
                let k = terms.mk_int(c.clone());
                terms.mk_mul(vec![k, *leaf])
            };
            parts.push(part);
        }
        if parts.len() == 1 {
            parts[0]
        } else {
            terms.mk_add(parts)
        }
    }

    /// Bottom-up rewrite applying the fold map. Mirrors
    /// `GuardedEqMining::fold`: check the fold map first, then rebuild
    /// through canonical constructors. Replacements are Bool atoms replacing
    /// Bool atoms, so no arithmetic ITE terms can be created (task #28
    /// constraint). Atoms under binders are never fold candidates (see
    /// `GuardedEqMining::collect_atoms`); `Let`/quantifier bodies are left
    /// untouched, which is sound because the rewrite is an equivalence —
    /// rewriting any subset of occurrences preserves the formula.
    fn fold(&mut self, terms: &mut TermStore, term: TermId) -> TermId {
        stacker::maybe_grow(DV_STACK_RED_ZONE, DV_STACK_SIZE, || {
            if let Some(&cached) = self.cache.get(&term) {
                return cached;
            }
            if let Some(&value) = self.fold_map.get(&term) {
                self.cache.insert(term, value);
                return value;
            }
            let result = match terms.get(term).clone() {
                TermData::Const(_) | TermData::Var(_, _) => term,
                TermData::App(sym, args) => {
                    let new_args: Vec<TermId> = args.iter().map(|&a| self.fold(terms, a)).collect();
                    if new_args == args {
                        term
                    } else {
                        match sym.name() {
                            "=" if new_args.len() == 2 => {
                                terms.mk_eq_coerce(new_args[0], new_args[1])
                            }
                            "and" => terms.mk_and(new_args),
                            "or" => terms.mk_or(new_args),
                            "not" if new_args.len() == 1 => terms.mk_not(new_args[0]),
                            "=>" if new_args.len() == 2 => {
                                terms.mk_implies(new_args[0], new_args[1])
                            }
                            "xor" if new_args.len() == 2 => terms.mk_xor(new_args[0], new_args[1]),
                            "distinct" => terms.mk_distinct(new_args),
                            "ite" if new_args.len() == 3 => {
                                terms.mk_ite(new_args[0], new_args[1], new_args[2])
                            }
                            _ => {
                                let sort = terms.sort(term).clone();
                                terms.mk_app(sym.clone(), new_args, sort)
                            }
                        }
                    }
                }
                TermData::Not(inner) => {
                    let new_inner = self.fold(terms, inner);
                    if new_inner == inner {
                        term
                    } else {
                        terms.mk_not(new_inner)
                    }
                }
                TermData::Ite(c, t, e) => {
                    let nc = self.fold(terms, c);
                    let nt = self.fold(terms, t);
                    let ne = self.fold(terms, e);
                    if nc == c && nt == t && ne == e {
                        term
                    } else {
                        terms.mk_ite(nc, nt, ne)
                    }
                }
                // Quantifiers / lets: leave untouched (their atoms are never
                // fold candidates; partial rewriting stays an equivalence).
                _ => term,
            };
            self.cache.insert(term, result);
            result
        })
    }

    /// Core of the pass; returns the definitional assertions appended
    /// (empty when nothing was rewritten).
    fn apply_inner(&mut self, terms: &mut TermStore, assertions: &mut Vec<TermId>) -> Vec<TermId> {
        // ---- Phase A: candidate atoms -----------------------------------
        // Only atoms that occur NESTED somewhere are worth rewriting: a
        // whole-assertion unit equality is already a fixed fact (and is
        // VariableSubstitution / mining food).
        let (atoms, nested) = GuardedEqMining::collect_atoms(terms, assertions);
        let mut canon: Vec<(TermId, CanonKey, BigInt)> = Vec::new();
        for atom in atoms {
            if !nested.contains(&atom) {
                continue;
            }
            let Some(row) = GuardedEqMining::parse_eq_atom(terms, atom) else {
                continue;
            };
            if let Some((key, rhs)) = Self::canonicalize(terms, &row) {
                canon.push((atom, key, rhs));
            }
        }
        if canon.is_empty() {
            return Vec::new();
        }

        // ---- Phase B: difference-variable assignment --------------------
        let mut dvar_of: HashMap<CanonKey, TermId> = HashMap::default();
        let mut dvar_order: Vec<(CanonKey, TermId)> = Vec::new();
        self.fold_map.clear();
        self.cache.clear();
        for (atom, key, rhs) in &canon {
            let dvar = match dvar_of.get(key) {
                Some(&d) => d,
                None => {
                    if dvar_order.len() >= MAX_DIFF_VARS {
                        continue;
                    }
                    let name = terms.mk_internal_symbol("eqdv");
                    let d = terms.mk_var(name, Sort::Int);
                    dvar_of.insert(key.clone(), d);
                    dvar_order.push((key.clone(), d));
                    d
                }
            };
            let rhs_term = terms.mk_int(rhs.clone());
            let replacement = terms.mk_eq_coerce(dvar, rhs_term);
            self.fold_map.insert(*atom, replacement);
        }
        if self.fold_map.is_empty() {
            return Vec::new();
        }

        // ---- Phase C: rewrite + definitional assertions -----------------
        for assertion in assertions.iter_mut() {
            *assertion = self.fold(terms, *assertion);
        }
        let mut defs: Vec<TermId> = Vec::with_capacity(dvar_order.len() * 2);
        for (key, dvar) in &dvar_order {
            let lin = Self::build_lin(terms, key);
            // Inequality PAIR, not a unit equality: see module docs (a unit
            // equality is inlined right back by VariableSubstitution).
            defs.push(terms.mk_le(*dvar, lin));
            defs.push(terms.mk_ge(*dvar, lin));
        }
        self.diff_vars = dvar_order.len() as u64;
        self.rewritten_atoms = self.fold_map.len() as u64;
        assertions.extend(defs.iter().copied());
        defs
    }
}

impl Default for EqDiffVar {
    fn default() -> Self {
        Self::new()
    }
}

impl PreprocessingPass for EqDiffVar {
    fn apply(&mut self, terms: &mut TermStore, assertions: &mut Vec<TermId>) -> bool {
        !self.apply_inner(terms, assertions).is_empty()
    }

    fn apply_with_sources(
        &mut self,
        terms: &mut TermStore,
        assertions: &mut Vec<TermId>,
        source_sets: &mut Vec<Vec<TermId>>,
    ) -> bool {
        debug_assert_eq!(assertions.len(), source_sets.len());
        // Provenance widening, mirroring GuardedEqMining (the 171e87c
        // must-fix lesson): a rewritten assertion's content references
        // difference variables whose definitions live in appended
        // assertions, so both sides must be justified by the union of all
        // original sources. With narrow positional provenance, incremental
        // sessions could keep a rewritten assertion (or a definition) past
        // the pop that retracts its justifiers — a latent wrong-unsat.
        let before: Vec<TermId> = assertions.clone();
        let defs = self.apply_inner(terms, assertions);
        if defs.is_empty() {
            debug_assert_eq!(assertions.len(), source_sets.len());
            return false;
        }
        let mut union_sources: Vec<TermId> = source_sets.iter().flatten().copied().collect();
        union_sources.sort_by_key(|t| t.index());
        union_sources.dedup();
        for (i, &old) in before.iter().enumerate() {
            if assertions[i] != old {
                let set = &mut source_sets[i];
                set.extend(union_sources.iter().copied());
                set.sort_by_key(|t| t.index());
                set.dedup();
            }
        }
        for _ in 0..defs.len() {
            source_sets.push(union_sources.clone());
        }
        debug_assert_eq!(assertions.len(), source_sets.len());
        true
    }

    fn reset(&mut self) {
        self.cache.clear();
        self.fold_map.clear();
    }
}

#[cfg(test)]
mod tests;
