// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Substitution application: applying discovered substitutions to terms.
//!
//! Handles quantifier scoping (shadow/restore), let-bindings, and
//! recursive term rewriting. Extracted from `mod.rs` to keep each file
//! under 500 lines.

use super::VariableSubstitution;
use ay_core::term::TermData;
use ay_core::{Sort, TermId, TermStore};

/// Red zone size for `stacker::maybe_grow` in variable substitution recursion (#8414).
const VAR_SUBST_STACK_RED_ZONE: usize = 32 * 1024;

/// Stack segment size allocated by stacker for variable substitution recursion.
const VAR_SUBST_STACK_SIZE: usize = 1024 * 1024;

impl VariableSubstitution {
    /// Shadow substitutions for bound variables when entering a quantifier scope.
    ///
    /// Clears `subst_cache` when any substitution is shadowed because compound
    /// terms containing the bound variable retain stale cache entries from the
    /// outer scope. Due to hash-consing, inner `(+ x y)` shares the same TermId
    /// as outer `(+ x y)`, so the cache would return wrong results (#5731).
    fn shadow_bound_vars(
        &mut self,
        terms: &mut TermStore,
        bound_vars: &[(String, Sort)],
    ) -> Vec<(TermId, Option<TermId>)> {
        let mut shadowed = Vec::new();
        let mut any_shadowed = false;
        for (name, sort) in bound_vars {
            let var_id = terms.mk_var(name.clone(), sort.clone());
            let old = self.substitutions.remove(&var_id);
            if old.is_some() {
                any_shadowed = true;
            }
            shadowed.push((var_id, old));
        }
        if any_shadowed {
            self.subst_cache.clear();
        }
        shadowed
    }

    /// Restore previously-shadowed substitutions when leaving a quantifier scope.
    fn restore_shadowed(&mut self, shadowed: Vec<(TermId, Option<TermId>)>) {
        let mut any_restored = false;
        for (var_id, old_subst) in shadowed {
            if let Some(replacement) = old_subst {
                self.substitutions.insert(var_id, replacement);
                any_restored = true;
            }
        }
        if any_restored {
            self.subst_cache.clear();
        }
    }

    /// Apply existing substitutions to a single term without discovering new substitutions.
    ///
    /// Used by the LIA assumption preprocessing path (#6728) to apply assertion-derived
    /// substitutions to assumption terms while preserving original assumption identity.
    pub(crate) fn apply_to_term(&mut self, terms: &mut TermStore, term: TermId) -> TermId {
        self.substitute_term(terms, term)
    }

    /// Substitute inside a quantifier body, shadowing bound variables (#5731).
    ///
    /// Returns `Some(new_term)` if the body or triggers changed, `None` otherwise.
    fn substitute_quantifier(
        &mut self,
        terms: &mut TermStore,
        vars: &[(String, Sort)],
        body: TermId,
        triggers: &[Vec<TermId>],
        is_forall: bool,
    ) -> Option<TermId> {
        let shadowed = self.shadow_bound_vars(terms, vars);
        let new_body = self.substitute_term(terms, body);
        let new_triggers: Vec<Vec<TermId>> = triggers
            .iter()
            .map(|trig| {
                trig.iter()
                    .map(|&t| self.substitute_term(terms, t))
                    .collect()
            })
            .collect();
        self.restore_shadowed(shadowed);
        if new_body == body && new_triggers == triggers {
            return None;
        }
        Some(if is_forall {
            terms.mk_forall_with_triggers(vars.to_vec(), new_body, new_triggers)
        } else {
            terms.mk_exists_with_triggers(vars.to_vec(), new_body, new_triggers)
        })
    }

    /// Substitute inside a let-binding, recursing into values and body.
    ///
    /// Let-bound variables shadow outer substitutions in the body (#5731 variant).
    fn substitute_let(
        &mut self,
        terms: &mut TermStore,
        bindings: &[(String, TermId)],
        body: TermId,
        term: TermId,
    ) -> TermId {
        // Substitute in binding values (outer scope — no shadowing yet)
        let new_bindings: Vec<(String, TermId)> = bindings
            .iter()
            .map(|(name, val)| (name.clone(), self.substitute_term(terms, *val)))
            .collect();
        // Shadow let-bound names before substituting in body
        let bound_vars: Vec<(String, Sort)> = bindings
            .iter()
            .map(|(name, val)| (name.clone(), terms.sort(*val).clone()))
            .collect();
        let shadowed = self.shadow_bound_vars(terms, &bound_vars);
        let new_body = self.substitute_term(terms, body);
        self.restore_shadowed(shadowed);
        if new_bindings
            .iter()
            .zip(bindings.iter())
            .all(|((_, nv), (_, ov))| nv == ov)
            && new_body == body
        {
            term
        } else {
            terms.mk_let(new_bindings, new_body)
        }
    }

    /// Apply substitutions to a term, returning the substituted term.
    /// Uses `stacker::maybe_grow` for stack safety on deeply nested terms (#8414).
    pub(super) fn substitute_term(&mut self, terms: &mut TermStore, term: TermId) -> TermId {
        stacker::maybe_grow(VAR_SUBST_STACK_RED_ZONE, VAR_SUBST_STACK_SIZE, || {
            // Check cache first
            if let Some(&cached) = self.subst_cache.get(&term) {
                return cached;
            }

            // Check if this term is a variable that should be substituted
            if let Some(&replacement) = self.substitutions.get(&term) {
                // Recursively substitute in the replacement (for transitive chains)
                let result = self.substitute_term(terms, replacement);
                self.subst_cache.insert(term, result);
                return result;
            }

            // Recursively substitute in subterms
            let result = match terms.get(term).clone() {
                TermData::Const(_) | TermData::Var(_, _) => term,

                TermData::App(sym, args) => {
                    let new_args: Vec<TermId> = args
                        .iter()
                        .map(|&arg| self.substitute_term(terms, arg))
                        .collect();

                    if new_args == args {
                        term
                    } else if let Some(folded) = (new_args.len() == 1)
                        .then(|| terms.try_fold_datatype_selector(sym.name(), new_args[0]))
                        .flatten()
                    {
                        // Datatype selector-over-constructor/ite fold. After a
                        // datatype variable is substituted by its (ite of)
                        // constructor definition, `(fld_x (ite c (C ..) ..))` must
                        // collapse to the concrete field; otherwise an SSA datatype
                        // reconstruction (a Parser/Vec post-state) stays an opaque
                        // selector over a giant ite-tree and the field/len reads
                        // never reduce. A selector is always unary, so this can
                        // never shadow the multi-arg operators below. (#dt-selector-subst)
                        folded
                    } else {
                        // Dispatch to canonical constructors for special operators.
                        // This ensures flattening, constant folding (#1708, #2767),
                        // and read-over-write simplification for arrays (#8140).
                        match sym.name() {
                            "=" if new_args.len() == 2 => {
                                terms.mk_eq_coerce_no_ite_expand(new_args[0], new_args[1])
                            }
                            "+" => terms.mk_add(new_args),
                            "-" => terms.mk_sub(new_args),
                            "*" => terms.mk_mul(new_args),
                            // Array canonical constructors: mk_select does read-over-write
                            // simplification (select(store(a, i, v), i) -> v), mk_store
                            // does squash-store and constant-array no-op elimination.
                            // Critical for QF_ABV after array variable substitution
                            // collapses chains like array_Q_22 -> store(array_Q_21, ...).
                            "select" if new_args.len() == 2 => {
                                terms.mk_select(new_args[0], new_args[1])
                            }
                            "store" if new_args.len() == 3 => {
                                terms.mk_store(new_args[0], new_args[1], new_args[2])
                            }
                            // Arithmetic comparisons and Int/Real bridge ops:
                            // dispatch through the canonical constructors so the
                            // to_real-integrality rewrites (#to-real-bridge) fire
                            // after a substitution exposes them (e.g. r := to_real(n)
                            // turns `0 < r < 1` into `0 < to_real(n) < 1`, which the
                            // constructors tighten to the unsatisfiable `n >= 1 &&
                            // n <= 0`). Guarded on the argument sorts the
                            // constructors' debug_asserts require; anything else
                            // falls through to the raw rebuild unchanged.
                            "<" | "<=" | ">" | ">="
                                if new_args.len() == 2
                                    && matches!(
                                        terms.sort(new_args[0]),
                                        Sort::Int | Sort::Real
                                    )
                                    && terms.sort(new_args[0]) == terms.sort(new_args[1]) =>
                            {
                                match sym.name() {
                                    "<" => terms.mk_lt(new_args[0], new_args[1]),
                                    "<=" => terms.mk_le(new_args[0], new_args[1]),
                                    ">" => terms.mk_gt(new_args[0], new_args[1]),
                                    _ => terms.mk_ge(new_args[0], new_args[1]),
                                }
                            }
                            "is_int"
                                if new_args.len() == 1
                                    && *terms.sort(new_args[0]) == Sort::Real =>
                            {
                                terms.mk_is_int(new_args[0])
                            }
                            "to_int"
                                if new_args.len() == 1
                                    && *terms.sort(new_args[0]) == Sort::Real =>
                            {
                                terms.mk_to_int(new_args[0])
                            }
                            _ => {
                                let sort = terms.sort(term).clone();
                                terms.mk_app(sym.clone(), new_args, sort)
                            }
                        }
                    }
                }

                TermData::Not(inner) => {
                    let new_inner = self.substitute_term(terms, inner);
                    if new_inner == inner {
                        term
                    } else {
                        terms.mk_not(new_inner)
                    }
                }

                TermData::Ite(c, t, e) => {
                    let new_c = self.substitute_term(terms, c);
                    let new_t = self.substitute_term(terms, t);
                    let new_e = self.substitute_term(terms, e);
                    if new_c == c && new_t == t && new_e == e {
                        term
                    } else {
                        if crate::theory_debug_flags::debug_var_subst() && new_c != c {
                            safe_eprintln!("[var_subst] ITE cond {:?} -> {:?}", c, new_c);
                        }
                        terms.mk_ite(new_c, new_t, new_e)
                    }
                }

                TermData::Let(bindings, body) => self.substitute_let(terms, &bindings, body, term),
                TermData::Forall(v, b, t) => self
                    .substitute_quantifier(terms, &v, b, &t, true)
                    .unwrap_or(term),
                TermData::Exists(v, b, t) => self
                    .substitute_quantifier(terms, &v, b, &t, false)
                    .unwrap_or(term),
                // All current TermData variants are handled above.
                // This arm is required by #[non_exhaustive] and catches future variants.
                other => unreachable!("unhandled TermData variant in substitute_term(): {other:?}"),
            };

            self.subst_cache.insert(term, result);
            result
        }) // stacker::maybe_grow
    }
}
