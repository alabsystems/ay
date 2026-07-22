// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Skolemization for existential quantifiers.
//!
//! Skolemization replaces existentially-bound variables with fresh witnesses,
//! eliminating the quantifier while preserving satisfiability:
//!
//! - Positive `Exists([x], body)` → `body[x := sk_x]` where `sk_x` is fresh.
//! - Negative `Forall([x], body)` → `¬body[x := sk_x]` is wrong; instead,
//!   `¬(∀x. body)` ≡ `∃x. ¬body` → `(¬body)[x := sk_x]`.
//!
//! Nested existentials under universals use Skolem functions:
//!
//! - `forall y. exists x. P(x, y)` → `forall y. P(sk_x(y), y)`
//!
//! This matches Z3's `q_solver::skolemize()` for top-level existentials and
//! its NNF skolemizer for nested existential dependencies.
//!
//! Finite domain expansion lives in `finite_domain`.
//!
//! # References
//!
//! - Z3: `reference/z3/src/sat/smt/q_solver.cpp:143-148`
//! - Design: the development design notes

mod finite_domain;
pub(crate) use finite_domain::{
    bounded_expansion_grounds_all_quantifiers, derived_bound_unlocks_expansion,
    expand_finite_domain_subterms, finite_domain_expand_with_instances,
    set_bool_ground_instantiation_candidates, set_derived_consts,
};
// Production goes through `expand_finite_domain_subterms`; the single-term
// entry point is exercised directly by the skolemize tests.
#[cfg(test)]
pub(crate) use finite_domain::finite_domain_expand;

// #8529: Use deterministic hash maps in all builds.
use ay_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};
use ay_core::term::Symbol;
use ay_core::{Sort, TermData, TermId, TermStore};

use crate::ematching::subst_vars;

/// Exact source mapping produced while eliminating a negative, single-binder
/// `forall` with a dependency-free fresh constant.
///
/// This is proof authority, not a name heuristic: the three terms are captured
/// at the one site that creates the witness and performs the substitution.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct ForallSkolemProvenance {
    pub(crate) quantified: TermId,
    pub(crate) instance: TermId,
    pub(crate) witness: TermId,
}

/// Red zone size for `stacker::maybe_grow` in skolemization recursion (#8414).
const SKOLEM_STACK_RED_ZONE: usize = 32 * 1024;

/// Stack segment size allocated by stacker for skolemization recursion.
const SKOLEM_STACK_SIZE: usize = 1024 * 1024;

/// Skolemize a quantifier if it is an existential target.
///
/// Returns `Some(body_with_skolem_constants)` if Skolemization applies:
/// - `negated = false` and the term is `Exists(vars, body, _)`: replace vars with fresh constants.
/// - `negated = true` and the term is `Forall(vars, body, _)`: negate body, replace vars.
///
/// Returns `None` if the quantifier is not a Skolemization target (e.g., positive Forall
/// or negative Exists — those go to E-matching).
#[cfg(test)]
pub(crate) fn skolemize(
    terms: &mut TermStore,
    quantifier_id: TermId,
    negated: bool,
) -> Option<TermId> {
    skolemize_with_env(terms, quantifier_id, negated, &[], &mut Vec::new())
}

fn skolemize_with_env(
    terms: &mut TermStore,
    quantifier_id: TermId,
    negated: bool,
    universal_env: &[String],
    provenance: &mut Vec<ForallSkolemProvenance>,
) -> Option<TermId> {
    let body = match terms.get(quantifier_id).clone() {
        TermData::Forall(_, _, _) if negated => {
            // ¬(∀x. P) ≡ ∃x. ¬P → Skolemize with ¬P as body
            let (instance, witnesses) =
                skolemize_quantifier_body(terms, quantifier_id, universal_env)?;
            if let [witness] = witnesses.as_slice() {
                if matches!(terms.get(*witness), TermData::Var(..)) {
                    provenance.push(ForallSkolemProvenance {
                        quantified: quantifier_id,
                        instance,
                        witness: *witness,
                    });
                }
            }
            terms.mk_not(instance)
        }
        TermData::Exists(_, _, _) if !negated => {
            skolemize_quantifier_body(terms, quantifier_id, universal_env)?.0
        }
        _ => return None, // Not a Skolemization target
    };

    Some(body)
}

fn skolemize_quantifier_body(
    terms: &mut TermStore,
    quantifier_id: TermId,
    universal_env: &[String],
) -> Option<(TermId, Vec<TermId>)> {
    let (vars, body) = match terms.get(quantifier_id).clone() {
        TermData::Forall(v, b, _) | TermData::Exists(v, b, _) => (v, b),
        _ => return None,
    };

    let dependencies = collect_skolem_dependencies(terms, body, &vars, universal_env);

    // Create fresh Skolem constants/functions for each bound variable.
    // Every minted symbol name is registered in the TermStore-side Skolem
    // registry (`mark_skolem_symbol`): the names are globally fresh, so registry
    // membership is exact provenance, which the quantified-CE-lemma
    // de-Skolemizer relies on to reconstruct the pre-Skolemization body.
    let mut subst: HashMap<String, TermId> = Default::default();
    let mut witnesses = Vec::with_capacity(vars.len());
    for (name, sort) in &vars {
        let skolem = if dependencies.is_empty() {
            let skolem = terms.mk_fresh_var(&format!("sk!{name}"), sort.clone());
            if let TermData::Var(fresh_name, _) = terms.get(skolem) {
                let fresh_name = fresh_name.clone();
                terms.mark_skolem_symbol(fresh_name);
            }
            skolem
        } else {
            let symbol_name = terms.mk_internal_symbol(&format!("sk_{name}"));
            terms.mark_skolem_symbol(symbol_name.clone());
            let symbol = Symbol::named(symbol_name);
            terms.mk_app(symbol, dependencies.clone(), sort.clone())
        };
        subst.insert(name.clone(), skolem);
        witnesses.push(skolem);
    }

    // Substitute Skolem constants into the body
    Some((subst_vars(terms, body, &subst), witnesses))
}

fn extend_universal_env(universal_env: &[String], vars: &[(String, Sort)]) -> Vec<String> {
    let shadowed: HashSet<String> = vars.iter().map(|(name, _)| name.clone()).collect();
    let mut extended: Vec<String> = universal_env
        .iter()
        .filter(|name| !shadowed.contains(name.as_str()))
        .cloned()
        .collect();
    extended.extend(vars.iter().map(|(name, _)| name.clone()));
    extended
}

/// Uses `stacker::maybe_grow` for stack safety on deeply nested terms (#8414).
fn collect_used_universal_terms(
    terms: &TermStore,
    term: TermId,
    visible_universals: &HashSet<String>,
    bound: &mut HashSet<String>,
    used: &mut HashMap<String, TermId>,
) {
    stacker::maybe_grow(SKOLEM_STACK_RED_ZONE, SKOLEM_STACK_SIZE, || {
        match terms.get(term).clone() {
            TermData::Var(name, _)
                if visible_universals.contains(name.as_str()) && !bound.contains(name.as_str()) =>
            {
                used.entry(name).or_insert(term);
            }
            TermData::Const(_) => {}
            TermData::App(_, args) => {
                for arg in args {
                    collect_used_universal_terms(terms, arg, visible_universals, bound, used);
                }
            }
            TermData::Not(inner) => {
                collect_used_universal_terms(terms, inner, visible_universals, bound, used);
            }
            TermData::Ite(cond, then_br, else_br) => {
                collect_used_universal_terms(terms, cond, visible_universals, bound, used);
                collect_used_universal_terms(terms, then_br, visible_universals, bound, used);
                collect_used_universal_terms(terms, else_br, visible_universals, bound, used);
            }
            TermData::Let(bindings, body) => {
                for (_, value) in &bindings {
                    collect_used_universal_terms(terms, *value, visible_universals, bound, used);
                }
                let mut inserted = Vec::with_capacity(bindings.len());
                for (name, _) in &bindings {
                    if bound.insert(name.clone()) {
                        inserted.push(name.clone());
                    }
                }
                collect_used_universal_terms(terms, body, visible_universals, bound, used);
                for name in inserted {
                    bound.remove(name.as_str());
                }
            }
            TermData::Forall(vars, body, _) | TermData::Exists(vars, body, _) => {
                let mut inserted = Vec::with_capacity(vars.len());
                for (name, _) in &vars {
                    if bound.insert(name.clone()) {
                        inserted.push(name.clone());
                    }
                }
                collect_used_universal_terms(terms, body, visible_universals, bound, used);
                for name in inserted {
                    bound.remove(name.as_str());
                }
            }
            _ => {}
        }
    }) // stacker::maybe_grow
}

fn collect_skolem_dependencies(
    terms: &TermStore,
    body: TermId,
    vars: &[(String, Sort)],
    universal_env: &[String],
) -> Vec<TermId> {
    if universal_env.is_empty() {
        return Vec::new();
    }

    let visible_universals: HashSet<String> = universal_env.iter().cloned().collect();
    let mut bound: HashSet<String> = vars.iter().map(|(name, _)| name.clone()).collect();
    let mut used: HashMap<String, TermId> = Default::default();
    collect_used_universal_terms(terms, body, &visible_universals, &mut bound, &mut used);

    universal_env
        .iter()
        .filter_map(|name| used.get(name).copied())
        .collect()
}

/// Uses `stacker::maybe_grow` for stack safety on deeply nested terms (#8414).
fn rewrite_nnf_with_skolem(
    terms: &mut TermStore,
    term: TermId,
    positive: bool,
    universal_env: &[String],
    provenance: &mut Vec<ForallSkolemProvenance>,
) -> TermId {
    stacker::maybe_grow(SKOLEM_STACK_RED_ZONE, SKOLEM_STACK_SIZE, || {
        match terms.get(term).clone() {
            // Positive exists: replace bound vars, then continue rewriting in-place.
            TermData::Exists(..) if positive => {
                let skolemized = skolemize_with_env(terms, term, false, universal_env, provenance)
                    .expect("Exists must have a Skolemizable body");
                rewrite_nnf_with_skolem(terms, skolemized, true, universal_env, provenance)
            }

            // Negative forall: ¬(forall x. P) ≡ ¬P[sk/x], so continue under negative polarity.
            TermData::Forall(..) if !positive => {
                let skolemized = skolemize_with_env(terms, term, true, universal_env, provenance)
                    .expect("Forall must have a Skolemizable body");
                rewrite_nnf_with_skolem(terms, skolemized, true, universal_env, provenance)
            }

            // Negative exists: ¬(∃x. P) ≡ ∀x. ¬P — convert to Forall for CEGQI/E-matching.
            // Without this, ¬∃ leaves a NOT(Exists(...)) that the quantifier pipeline
            // cannot match, causing nested quantifiers to return Unknown (#7150).
            TermData::Exists(vars, body, triggers) if !positive => {
                let extended_env = extend_universal_env(universal_env, &vars);
                let negated_body =
                    rewrite_nnf_with_skolem(terms, body, false, &extended_env, provenance);
                terms.mk_forall_with_triggers(vars, negated_body, triggers)
            }

            // Positive forall keeps universal scope. Recurse so nested existentials
            // can build Skolem functions from the visible universal environment.
            TermData::Forall(vars, body, triggers) if positive => {
                let extended_env = extend_universal_env(universal_env, &vars);
                let new_body =
                    rewrite_nnf_with_skolem(terms, body, true, &extended_env, provenance);
                if new_body == body {
                    term
                } else {
                    terms.mk_forall_with_triggers(vars, new_body, triggers)
                }
            }

            // Push negation inward through the remaining Boolean structure.
            TermData::Not(inner) => {
                rewrite_nnf_with_skolem(terms, inner, !positive, universal_env, provenance)
            }

            // Rebuild conjunction/disjunction in the polarity-correct connective.
            TermData::App(ref sym, ref args) if sym.name() == "and" || sym.name() == "or" => {
                let sym_name = sym.name().to_string();
                let rewritten: Vec<TermId> = args
                    .iter()
                    .copied()
                    .map(|arg| {
                        rewrite_nnf_with_skolem(terms, arg, positive, universal_env, provenance)
                    })
                    .collect();
                match (sym_name.as_str(), positive) {
                    ("and", true) => terms.mk_and(rewritten),
                    ("and", false) => terms.mk_or(rewritten),
                    ("or", true) => terms.mk_or(rewritten),
                    ("or", false) => terms.mk_and(rewritten),
                    _ => unreachable!("guard ensures a Boolean n-ary connective"),
                }
            }

            // Handle raw implication terms that may still exist in internal formulas.
            TermData::App(ref sym, ref args) if sym.name() == "=>" && args.len() == 2 => {
                let lhs_positive = !positive;
                let rhs_positive = positive;
                let lhs = rewrite_nnf_with_skolem(
                    terms,
                    args[0],
                    lhs_positive,
                    universal_env,
                    provenance,
                );
                let rhs = rewrite_nnf_with_skolem(
                    terms,
                    args[1],
                    rhs_positive,
                    universal_env,
                    provenance,
                );
                if positive {
                    terms.mk_or(vec![lhs, rhs])
                } else {
                    terms.mk_and(vec![lhs, rhs])
                }
            }

            // ITE is conservative: keep the condition opaque, but rewrite branches.
            // Under negative polarity this becomes `ite c (not t) (not e)`.
            TermData::Ite(cond, then_br, else_br) => {
                let then_br =
                    rewrite_nnf_with_skolem(terms, then_br, positive, universal_env, provenance);
                let else_br =
                    rewrite_nnf_with_skolem(terms, else_br, positive, universal_env, provenance);
                terms.mk_ite(cond, then_br, else_br)
            }

            // Ground leaf or unsupported Boolean subtree.
            _ => {
                if positive {
                    term
                } else {
                    terms.mk_not(term)
                }
            }
        }
    }) // stacker::maybe_grow
}

/// Polarity-aware deep Skolemization: walk through Boolean connectives and
/// Skolemize existentials at positive polarity and universals at negative polarity.
///
/// This handles formulas like `(and (exists ((x Int)) (= x 5)) (> y 0))` where
/// the existential is nested inside a conjunction. Z3's NNF Skolemizer does the
/// same walk (reference/z3/src/ast/normal_forms/nnf.cpp:407).
///
/// Returns `None` if no Skolemization was performed (term unchanged).
#[cfg(test)]
pub(crate) fn skolemize_deep(
    terms: &mut TermStore,
    term: TermId,
    positive: bool,
) -> Option<TermId> {
    skolemize_deep_with_provenance(terms, term, positive).0
}

/// Proof-aware deep Skolemization. The returned mappings are minted by the
/// actual skolemization operation and therefore bind a source `forall` to its
/// exact fresh witness and exact substituted body.
pub(crate) fn skolemize_deep_with_provenance(
    terms: &mut TermStore,
    term: TermId,
    positive: bool,
) -> (Option<TermId>, Vec<ForallSkolemProvenance>) {
    let mut provenance = Vec::new();
    let rewritten = rewrite_nnf_with_skolem(terms, term, positive, &[], &mut provenance);
    ((rewritten != term).then_some(rewritten), provenance)
}

#[cfg(test)]
mod tests;
