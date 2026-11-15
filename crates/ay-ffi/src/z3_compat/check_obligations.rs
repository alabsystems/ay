// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Fail-closed obligations of a decision goal that the context's shared
//! engine cannot see by itself (T5 P0.2 quarantine, implementer Y).
//!
//! * **Loose bound variables (Q2).** A de Bruijn variable (`Z3_mk_bound`)
//!   that no binder of the goal binds is a free `__db{k}` constant to the
//!   engine, which then answered `sat` with `__db0 = 2`. libz3 5.1.0 answers
//!   `unknown` with [`UNBOUND_VARIABLES_REASON`] instead.
//! * **Lossy binder sorts (Q12).** `Char` and finite-domain values lower to
//!   engine `Int`s. A binder of exactly such a sort is relativized to its
//!   carrier where the quantifier is built; a binder whose sort holds one
//!   anywhere else (an array, a sequence, a datatype field) ranges over engine
//!   values that are not public values, so the goal is refused.
//! * **Well-formedness guards (Q12, design §2.10).** A free symbol whose
//!   value holds such a sort gets its guard at declaration (`wf_guards`).
//!   Guards are asserted only for the symbols a goal reaches, so they never
//!   add quantifiers to unrelated checks.
//! * **Reachable recursive definitions (Q9).** An Optimize goal asserts only
//!   the recursive-definition axioms its own constraints reach.

use std::collections::{BTreeSet, HashMap, HashSet};

use ay_dpll::api::{de_bruijn_index, Sort, Term, TermKind};

use super::wf_guards::{eager_guards, mentions_bounded_scalar, wf_obligations};
pub(crate) use super::wf_guards::{
    recheck_due, register_constant_wf_guard, register_function_wf_guard, validate_wf_model,
    WfGuard, WfObligations, WfPhase, WfVerdict,
};
use super::{bounded_sort_hi, lookup_ast_sort, term_to_ast, Z3Context};

/// libz3 5.1.0's reason for a goal holding a loose bound variable: the check
/// of `s.add(Var(0, IntSort()) > 1)` answers `unknown` with this text, and an
/// assumption or an Optimize constraint holding one is an error with this
/// message (`Z3_EXCEPTION`).
pub(crate) const UNBOUND_VARIABLES_REASON: &str = "Formulas should not contain unbound variables";

/// Whether a de Bruijn variable occurs free (bound by no enclosing
/// quantifier, `let` or lambda) in `roots`. Fails closed: roots the engine
/// cannot walk count as holding one.
pub(crate) fn has_loose_bound_variable(ctx: &Z3Context, roots: &[Term]) -> bool {
    match ctx.solver.declared_symbols_in(roots) {
        Ok(names) => names.iter().any(|name| de_bruijn_index(name).is_some()),
        Err(_) => true,
    }
}

/// Whether `sort` is a sort AY lowers to a bounded engine `Int` (`Char`, a
/// finite domain).
fn is_bounded_scalar(sort: &Sort) -> bool {
    bounded_sort_hi(sort).is_some()
}

/// Whether a binder of `sort` ranges over engine values that are not public
/// values: a `Char` / finite-domain component below the top level.
pub(crate) fn is_lossy_binder_sort(sort: &Sort) -> bool {
    !is_bounded_scalar(sort) && mentions_bounded_scalar(sort, &mut HashSet::new())
}

/// The refusal for the first quantifier of `roots` that binds a variable of a
/// lossy sort (see [`is_lossy_binder_sort`]), if any.
pub(crate) fn lossy_binder_refusal(ctx: &Z3Context, roots: &[Term]) -> Option<String> {
    if ctx.quantifier_public_bound_terms.is_empty() {
        return None;
    }
    let mut seen: HashSet<Term> = HashSet::new();
    let mut stack: Vec<Term> = roots.to_vec();
    while let Some(term) = stack.pop() {
        if !seen.insert(term) {
            continue;
        }
        if let Some(bound) = ctx.quantifier_public_bound_terms.get(&term) {
            for &var in bound {
                if ctx.bounded_sort_lost.contains(&var) {
                    return Some(
                        "a quantifier binds a Char or finite-domain constant whose sort AY \
                         lost when its handle was reused (Z3_mk_char_to_int returns its \
                         argument), so the binder may range over unbounded Ints; the goal \
                         is not decided"
                            .to_string(),
                    );
                }
                if let Some(sort) = lookup_ast_sort(ctx, term_to_ast(ctx, var)) {
                    if is_lossy_binder_sort(sort) {
                        return Some(format!(
                            "a quantifier binds a variable of sort {sort}, whose Char or \
                             finite-domain component AY lowers to an unbounded Int; the \
                             quantifier would range over values that are not values of \
                             the sort, so the goal is not decided"
                        ));
                    }
                }
            }
        }
        stack.extend(ctx.solver.term_children(term));
    }
    None
}

/// Every application symbol and variable name occurring in `roots`, inside
/// binders too (an over-approximation of the symbols the goal reaches), and
/// whether a binder (quantifier or lambda) occurs. Ordered, so the guards and
/// axioms a goal reaches are asserted, and a refusal is named, in the same
/// order on every run.
fn occurring_names(ctx: &Z3Context, roots: &[Term]) -> (BTreeSet<String>, bool) {
    let mut seen: HashSet<Term> = HashSet::new();
    let mut names: BTreeSet<String> = BTreeSet::new();
    let mut binder = false;
    let mut stack: Vec<Term> = roots.to_vec();
    while let Some(term) = stack.pop() {
        if !seen.insert(term) {
            continue;
        }
        match ctx.solver.term_kind(term) {
            TermKind::App { name, .. } => {
                binder |= name == "lambda-array";
                names.insert(name);
            }
            TermKind::Var { name } => {
                names.insert(name);
            }
            TermKind::Forall | TermKind::Exists => binder = true,
            _ => {}
        }
        stack.extend(ctx.solver.term_children(term));
    }
    (names, binder)
}

/// The well-formedness obligations of the symbols `roots` reach (see
/// [`WfObligations`]), or the refusal for a reached symbol whose guard could
/// not be built.
pub(crate) fn reachable_wf_obligations(
    ctx: &Z3Context,
    roots: &[Term],
) -> Result<WfObligations, String> {
    if ctx.wf_guards.is_empty() {
        return wf_obligations(ctx, &BTreeSet::new(), false);
    }
    let (names, binder) = occurring_names(ctx, roots);
    wf_obligations(ctx, &names, binder)
}

/// Every well-formedness guard of the symbols `roots` reach, or the refusal
/// for a reached symbol without one: what a query that cannot validate its
/// model asserts (see `wf_guards::eager_guards`).
pub(crate) fn reachable_wf_guards(ctx: &Z3Context, roots: &[Term]) -> Result<Vec<Term>, String> {
    if ctx.wf_guards.is_empty() {
        return Ok(Vec::new());
    }
    Ok(eager_guards(&reachable_wf_obligations(ctx, roots)?))
}

/// Assert [`reachable_wf_guards`] of `roots` on the shared engine.
pub(crate) fn assert_reachable_wf_guards(
    ctx: &mut Z3Context,
    roots: &[Term],
) -> Result<(), String> {
    for guard in reachable_wf_guards(ctx, roots)? {
        ctx.solver
            .try_assert_term(guard)
            .map_err(|e| e.to_string())?;
    }
    Ok(())
}

/// The recursive-definition axioms the goal `roots` reaches, closed through
/// the definitions' own bodies.
pub(crate) fn reachable_rec_def_axioms(ctx: &Z3Context, roots: &[Term]) -> Vec<Term> {
    if ctx.rec_def_axiom_index.is_empty() {
        return Vec::new();
    }
    let index: &HashMap<String, usize> = &ctx.rec_def_axiom_index;
    let mut reached: HashSet<String> = HashSet::new();
    let mut axioms: Vec<Term> = Vec::new();
    let mut frontier: Vec<String> = occurring_names(ctx, roots)
        .0
        .into_iter()
        .filter(|name| index.contains_key(name))
        .collect();
    while let Some(name) = frontier.pop() {
        if !reached.insert(name.clone()) {
            continue;
        }
        let Some(&axiom) = index
            .get(&name)
            .and_then(|&slot| ctx.global_definition_axioms.get(slot))
        else {
            continue;
        };
        axioms.push(axiom);
        frontier.extend(
            occurring_names(ctx, &[axiom])
                .0
                .into_iter()
                .filter(|other| index.contains_key(other) && !reached.contains(other)),
        );
    }
    axioms
}

/// The theory-internal axioms of an Optimize check over the goal `roots`: the
/// context's background axioms, the recursive-definition axioms the goal
/// reaches (asserting every definition stalled unrelated objectives; libz3
/// 5.1.0 answers `maximize x` under `x <= 7` beside an unrelated recursive
/// function at once with 7), the reachable finite-set axioms and the
/// reachable well-formedness guards `phase` asserts. Returns the goal's
/// well-formedness obligations, which an optimum's model is validated
/// against.
pub(crate) fn assert_optimize_obligations(
    ctx: &mut Z3Context,
    roots: &[Term],
    phase: &mut WfPhase,
) -> Result<WfObligations, String> {
    let rec_axioms = reachable_rec_def_axioms(ctx, roots);
    let mut axioms = ctx.background_axioms.clone();
    axioms.extend(rec_axioms.iter().copied());
    for axiom in axioms {
        ctx.solver
            .try_assert_term(axiom)
            .map_err(|e| e.to_string())?;
    }
    super::assert_reachable_finite_set_axioms(ctx, roots)?;
    let mut wf_roots = roots.to_vec();
    wf_roots.extend(rec_axioms);
    let obligations = reachable_wf_obligations(ctx, &wf_roots)?;
    for guard in phase.guards(&obligations) {
        ctx.solver
            .try_assert_term(guard)
            .map_err(|e| e.to_string())?;
    }
    Ok(obligations)
}
