// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The quantifier-body walk of the RoundingMode domain pass.

use ay_core::kani_compat::DetHashSet as HashSet;
use ay_core::term::TermData;
use ay_core::{TermId, TermStore};

use super::{
    fp_rounding_mode_operand, is_rm_literal, is_rm_sort, subtree_mentions_rm_sort, RmLiteralAtoms,
};

/// Walk a quantifier body classifying its RoundingMode mentions.
///
/// Returns `true` when every RM mention is handled soundly:
/// * an RM literal in an FP rounding-op mode slot — benign, ignored (this is
///   the standard quantified-FP pattern, e.g. `forall i. … (fp.add RNE …)`);
/// * an RM literal in a domain position — sets `literal_domain_mention` so
///   the distinct-5 axiom (ground, valid) constrains every instantiation, and
///   collects any different-mode literal equality into `literal_atoms`: the
///   atom is GROUND (both operands are mode literals), so instantiation leaves
///   it untouched and a top-level pin on it is both valid and effective;
/// * a plain RM-sorted `Var` that is NOT a bound variable of any enclosing
///   binder — a GLOBAL constant (bound-variable-carrying terms are never
///   plain global Vars), so the ground coverage disjunction reaches it:
///   collected into `needs_coverage`.
///
/// Returns `false` (caller MUST fail closed) for every other shape: an
/// RM-sorted binder of a nested quantifier, an RM-sorted Var that shadows an
/// enclosing binder name, any RM-sorted application/ite (it may carry bound
/// variables — asserting ground coverage over it would be ill-formed), and
/// any `let` whose subtree mentions the sort (binding structure makes
/// groundness analysis unreliable; rare, conservative).
///
/// `scope.walked` holds the subterms already walked to `true` under the
/// current binder names; every effect of a walk (coverage, the literal-domain
/// flag, the literal atoms) is idempotent, so a second walk of one of them
/// changes nothing and is skipped. A nested quantifier gets a fresh set,
/// because the binder names are the context the answer depends on. Without
/// it the walk re-walked shared subterms once per path: on AUFBV Alive2
/// `gcc__081_gcc` the `--z3-mode` run was still inside this walk 9-12 s into
/// a `-T:10` run (sampled), polling no stop, and ended in the watchdog's hard
/// exit.
pub(super) fn walk_quantifier_body(
    terms: &TermStore,
    body: TermId,
    scope: &mut BinderScope,
    needs_coverage: &mut Vec<TermId>,
    coverage_set: &mut HashSet<TermId>,
    literal_domain_mention: &mut bool,
    literal_atoms: &mut RmLiteralAtoms,
) -> bool {
    if scope.walked.contains(&body) {
        return true;
    }
    let ok = walk_quantifier_body_uncached(
        terms,
        body,
        scope,
        needs_coverage,
        coverage_set,
        literal_domain_mention,
        literal_atoms,
    );
    if ok {
        scope.walked.insert(body);
    }
    ok
}

/// The binder names in force during [`walk_quantifier_body`], and the
/// subterms already walked to `true` under exactly those names.
pub(super) struct BinderScope {
    names: Vec<String>,
    walked: HashSet<TermId>,
}

impl BinderScope {
    pub(super) fn new(names: Vec<String>) -> Self {
        Self {
            names,
            walked: HashSet::default(),
        }
    }
}

fn walk_quantifier_body_uncached(
    terms: &TermStore,
    body: TermId,
    scope: &mut BinderScope,
    needs_coverage: &mut Vec<TermId>,
    coverage_set: &mut HashSet<TermId>,
    literal_domain_mention: &mut bool,
    literal_atoms: &mut RmLiteralAtoms,
) -> bool {
    let data = terms.get(body).clone();
    if is_rm_sort(terms.sort(body)) && !is_rm_literal(terms, body) {
        match &data {
            TermData::Var(name, _) => {
                if scope.names.iter().any(|b| b == name) {
                    return false; // bound RM var (or shadowing) — fail closed
                }
                if coverage_set.insert(body) {
                    needs_coverage.push(body);
                }
            }
            _ => return false, // RM-valued app/ite/let under a binder
        }
    }
    match data {
        TermData::App(sym, args) => {
            literal_atoms.record(terms, body, &sym, &args);
            let mode_slot = fp_rounding_mode_operand(sym.name(), &args);
            for (i, &a) in args.iter().enumerate() {
                let in_mode_slot = i == 0 && mode_slot == Some(a);
                if is_rm_literal(terms, a) {
                    if !in_mode_slot {
                        *literal_domain_mention = true;
                    }
                    continue;
                }
                if !walk_quantifier_body(
                    terms,
                    a,
                    scope,
                    needs_coverage,
                    coverage_set,
                    literal_domain_mention,
                    literal_atoms,
                ) {
                    return false;
                }
            }
            true
        }
        TermData::Not(inner) => walk_quantifier_body(
            terms,
            inner,
            scope,
            needs_coverage,
            coverage_set,
            literal_domain_mention,
            literal_atoms,
        ),
        TermData::Ite(c, th, el) => [c, th, el].into_iter().all(|x| {
            if is_rm_literal(terms, x) {
                *literal_domain_mention = true;
                return true;
            }
            walk_quantifier_body(
                terms,
                x,
                scope,
                needs_coverage,
                coverage_set,
                literal_domain_mention,
                literal_atoms,
            )
        }),
        // `let` under a binder: fail closed iff its subtree mentions RM at
        // all (conservative — see doc comment).
        TermData::Let(..) => !subtree_mentions_rm_sort(terms, body),
        TermData::Forall(vars, b, _) | TermData::Exists(vars, b, _) => {
            if vars.iter().any(|(_, s)| is_rm_sort(s)) {
                return false;
            }
            let added = vars.len();
            scope.names.extend(vars.iter().map(|(n, _)| n.clone()));
            let outer_walked = std::mem::take(&mut scope.walked);
            let ok = walk_quantifier_body(
                terms,
                b,
                scope,
                needs_coverage,
                coverage_set,
                literal_domain_mention,
                literal_atoms,
            );
            scope.names.truncate(scope.names.len() - added);
            scope.walked = outer_walked;
            ok
        }
        // Constants and non-RM vars carry no RM structure.
        _ => true,
    }
}
