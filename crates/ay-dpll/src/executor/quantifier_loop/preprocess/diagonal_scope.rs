// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Which universals the diagonal-instance pass takes.

use ay_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};
use ay_core::{Sort, TermData, TermId, TermStore};

/// What the input said about instantiating its quantifiers, as far as the
/// diagonal pass is concerned.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum Instantiation {
    /// The input left model-based instantiation on: it is the default, and
    /// `(set-option :smt.mbqi true)` says the same. The input expects the
    /// solver to look for instances its patterns do not lead to, and this
    /// pass is one of the places that does.
    Unrestricted,
    /// `(set-option :smt.mbqi false)`: a quantifier that carries a pattern is
    /// to be instantiated where the pattern matches, and nowhere else.
    TriggersOnly,
}

/// Where the pass found a universal.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum Standing {
    /// The universal is an assertion by itself: an axiom of the input.
    Asserted,
    /// The universal is an entailed part of a larger assertion, such as a
    /// hypothesis inside a goal. An asserted `(not (exists ..))` counts here
    /// too: the universal the pass reads out of it is not the asserted term.
    PartOfAnAssertion,
}

/// Whether `add_diagonal_forall_instances` instantiates a universal over the
/// same-sort binders `vars` with body `body` and user patterns `triggers`.
///
/// The pass exists for EPR/UF formulas whose refutation needs the self-pair
/// `x = y = c`, which trigger matching never produces when the ground problem
/// only holds off-diagonal tuples. It takes a universal when either
///
/// * the body is function-free over the binders: every non-Boolean subterm
///   that mentions a binder is a binder. An instance then only relates
///   existing ground terms through predicates and equalities, exactly as in
///   EPR, whatever the sort; or
/// * the binder sort is uninterpreted and the input does not keep the
///   universal from it. An [`Instantiation::Unrestricted`] input keeps none.
///   An [`Instantiation::TriggersOnly`] input keeps every universal that
///   carries a pattern and is [`Standing::Asserted`].
///
/// It skips a universal whose body applies a function or an arithmetic
/// operator to a binder when
///
/// * the sort is interpreted (`Int`, `Real`, bit-vectors, datatypes). Each of
///   its diagonal instances mints fresh ground terms — for a definition such
///   as `(Mul x y) = (* x y)`, the products `(* c c)` for every constant `c` —
///   which feed E-matching further instances and can move the query into a
///   nonlinear theory mix with no combined decision procedure, or stall the
///   NIA lane. Trigger-annotated input carries many such axioms: every Verus
///   query asserts two dozen same-sort `Int`/`Real` prelude definitions; or
/// * the sort is uninterpreted, the universal carries a pattern and is an
///   assertion by itself, and the input asked for triggers only. A diagonal
///   instance mints the functions
///   of the body at every ground term of the sort, `(f c c)` and whatever is
///   built from it, and each minted term matches further axioms. Program
///   verifiers box every value into one uninterpreted sort, ship a library
///   of binary definitions over it with each query, and send the option with
///   them. Where the query applies a definition's function, its pattern
///   matches and trigger matching supplies the instance; the pass would add
///   one more batch per definition and ground term on top, for the
///   definitions the query uses and for those it does not. The reference
///   solver, given the option, makes none of these instances.
///
/// Why the last skip waits for the option. On an input that leaves
/// model-based instantiation on, the instance at `(c, c)` is often the only
/// one a universal gets that no trigger reaches, and small formulas are
/// decided by it: the instance refutes the ground facts, or mints the terms
/// the pattern then matches. Withholding it there, from the unreached
/// universals alone, was measured on 600 random patterned formulas over one
/// uninterpreted sort: 37 answers became `unknown`. Those inputs keep the
/// pass as it was.
///
/// Why the last skip stops at assertions. A universal that is only part of
/// a larger assertion is a hypothesis of one goal, not a library: there are a
/// few per query, and refutations rest on their instances. Measured on a
/// program verifier's queries: the goal assumes `forall c j. ens(f, c, j) =>
/// ...` and calls `f` twice, the second time under a branch. The instance the
/// second call needs is reached only through an equality that holds in that
/// branch, which trigger matching here does not see; the diagonal batch of
/// the hypothesis mints the term it is matched on. Without the batch three
/// tests that passed reported errors on correct programs.
///
/// Skipping a universal only withholds consequences of an asserted formula: it
/// can cost a refutation, but it removes nothing a `sat` model is checked
/// against.
pub(super) fn takes_diagonal_instances(
    terms: &TermStore,
    vars: &[(String, Sort)],
    body: TermId,
    triggers: &[Vec<TermId>],
    instantiation: Instantiation,
    standing: Standing,
) -> bool {
    let Some((_, sort)) = vars.first() else {
        return false;
    };
    let bound: HashSet<&str> = vars.iter().map(|(name, _)| name.as_str()).collect();
    if body_is_function_free(terms, body, &bound) {
        return true;
    }
    if !matches!(sort, Sort::Uninterpreted(_)) {
        return false;
    }
    match instantiation {
        Instantiation::Unrestricted => true,
        Instantiation::TriggersOnly => {
            triggers.is_empty() || standing == Standing::PartOfAnAssertion
        }
    }
}

/// Whether every non-Boolean subterm of `body` that mentions a variable named
/// in `bound` is such a variable itself. A nested binder that reuses a name is
/// treated as the outer one, which can only make the answer `false`.
fn body_is_function_free(terms: &TermStore, body: TermId, bound: &HashSet<&str>) -> bool {
    // Post-order walk; `mentions` records, per finished subterm, whether it
    // mentions a bound variable.
    let mut mentions: HashMap<TermId, bool> = HashMap::default();
    let mut stack: Vec<(TermId, bool)> = vec![(body, false)];
    while let Some((id, children_done)) = stack.pop() {
        if mentions.contains_key(&id) {
            continue;
        }
        match terms.get(id) {
            TermData::Var(name, _) => {
                mentions.insert(id, bound.contains(name.as_str()));
                continue;
            }
            TermData::Let(..) => return false,
            _ => {}
        }
        let children = terms.children(id);
        if !children_done {
            stack.push((id, true));
            stack.extend(
                children
                    .into_iter()
                    .filter(|child| !mentions.contains_key(child))
                    .map(|child| (child, false)),
            );
            continue;
        }
        let mentions_bound = children
            .iter()
            .any(|child| mentions.get(child).copied().unwrap_or(false));
        if mentions_bound && *terms.sort(id) != Sort::Bool {
            return false;
        }
        mentions.insert(id, mentions_bound);
    }
    true
}

#[cfg(test)]
#[path = "diagonal_scope_tests.rs"]
mod tests;
