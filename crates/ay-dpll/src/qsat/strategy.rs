// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The ∃ player's winning strategy, read off a `sat` run.
//!
//! Every ∀ lemma `¬P_i` was learned when ∃ had the move `x := t_i` at an
//! existential level `k_i` into a position ∀ loses from: `P_i ⇒ (φ ∨
//! ⋁_{j<i} P_j)[x := t_i]`, with `P_i` and `t_i` over lower levels. The run
//! ends with `C₀ ⇒ φ ∨ ⋁_i P_i` for a level-0 cube `C₀` true in the witness.
//!
//! STRATEGY: at level `k`, play `t_i` for the FIRST (lowest-index) lemma `i`
//! of level `k` whose region holds. It wins: if some play ended with `φ`
//! false, the set `T` of lemmas true at the end is non-empty (the level-0
//! implication); its least element `m` was true when level `k_m` was played
//! (its region is over lower levels), so the strategy played `t_m` there —
//! any smaller candidate at that level would also be true at the end and
//! contradict minimality. Then `φ ∨ ⋁_{j<m} P_j` holds at the end, so some
//! `j < m` is in `T`: contradiction.
//!
//! The certificate is DATA for the quantified model gate, which re-walks the
//! authored conjunct itself, replaces universal binders by fresh constants
//! and existential binders by these terms (checking they mention only
//! enclosing universal binders and free constants), and confirms by a
//! checked ground refutation of the negation. A wrong strategy can only be
//! refused.

use ay_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};
use ay_core::term::Symbol;
use ay_core::{Sort, TermId, TermStore};
use num_bigint::BigInt;
use num_rational::BigRational;
use num_traits::Zero;

use super::game::Run;
use super::lin::Val;
use super::mbp::substitute;
use super::prenex::Game;

/// One authored quantifier occurrence in the certificate.
#[derive(Clone, Debug)]
pub(crate) struct OccurrenceCert {
    pub(crate) universal: bool,
    /// Engine variables, one per binder: the gate's fresh constants for a
    /// universal occurrence, the names strategies refer to otherwise.
    pub(crate) vars: Vec<TermId>,
    /// Existential occurrences: one term per binder, over free constants and
    /// the engine variables of other occurrences.
    pub(crate) strategy: Vec<TermId>,
}

/// `(authored quantifier, positive) -> occurrence`.
#[derive(Clone, Debug, Default)]
pub(crate) struct StrategyCert {
    pub(crate) occurrences: HashMap<(TermId, bool), OccurrenceCert>,
}

fn default_term(terms: &mut TermStore, sort: &Sort) -> TermId {
    match sort {
        Sort::Bool => terms.mk_bool(false),
        Sort::Int => terms.mk_int(BigInt::zero()),
        _ => terms.mk_rational(BigRational::zero()),
    }
}

fn value_term(terms: &mut TermStore, sort: &Sort, v: Option<&Val>) -> TermId {
    match (sort, v) {
        (Sort::Bool, Some(Val::Bool(b))) => terms.mk_bool(*b),
        (Sort::Int, Some(Val::Num(n))) if n.is_integer() => terms.mk_int(n.to_integer()),
        (Sort::Real, Some(Val::Num(n))) => terms.mk_rational(n.clone()),
        _ => default_term(terms, sort),
    }
}

/// Build the certificate of a `sat` run, or `None` when an occurrence key
/// is ambiguous (one authored quantifier placed twice at one polarity).
pub(crate) fn extract(terms: &mut TermStore, game: &Game, run: &Run) -> Option<StrategyCert> {
    let mut seen: HashSet<(TermId, bool)> = HashSet::default();
    for occ in &game.occurrences {
        if !seen.insert((occ.quantifier, occ.positive)) {
            return None;
        }
    }
    // Level-0 existential variables that are not authored constants take
    // their witness value; purification variables their definitions.
    let free: HashSet<TermId> = game.free.iter().copied().collect();
    let mut base: Vec<(TermId, TermId)> = Vec::new();
    for occ in &game.occurrences {
        if occ.level == 0 && !occ.universal {
            for &v in &occ.vars {
                let sort = terms.sort(v).clone();
                let t = value_term(terms, &sort, run.model.vals.get(&v));
                base.push((v, t));
            }
        }
    }
    let mut purified = game.purified.clone();
    purified.sort_by_key(|p| p.level);
    for p in &purified {
        if free.contains(&p.var) {
            continue;
        }
        let def = substitute(terms, p.def, &base);
        base.push((p.var, def));
    }
    let mut cert = StrategyCert::default();
    for occ in &game.occurrences {
        let mut strategy = Vec::new();
        if !occ.universal {
            for &v in &occ.vars {
                let sort = terms.sort(v).clone();
                let t = if occ.level == 0 {
                    value_term(terms, &sort, run.model.vals.get(&v))
                } else {
                    // Decision list in lemma order: first region wins.
                    let mut arms: Vec<(TermId, TermId)> = Vec::new();
                    for lemma in &run.lemmas {
                        if !lemma.forall_owned || lemma.level != occ.level {
                            continue;
                        }
                        let Some(&(_, t)) = lemma.subst.iter().find(|(x, _)| *x == v) else {
                            continue;
                        };
                        let lits: Vec<TermId> = lemma
                            .region
                            .iter()
                            .map(|&(a, val)| if val { a } else { terms.mk_not_raw(a) })
                            .collect();
                        let cond = match lits.as_slice() {
                            [] => terms.mk_bool(true),
                            [one] => *one,
                            _ => terms.mk_app(Symbol::named("and"), lits, Sort::Bool),
                        };
                        arms.push((cond, t));
                    }
                    let mut acc = default_term(terms, &sort);
                    for (cond, t) in arms.into_iter().rev() {
                        acc = terms.mk_ite_raw(cond, t, acc);
                    }
                    acc
                };
                strategy.push(substitute(terms, t, &base));
            }
        }
        cert.occurrences.insert(
            (occ.quantifier, occ.positive),
            OccurrenceCert {
                universal: occ.universal,
                vars: occ.vars.clone(),
                strategy,
            },
        );
    }
    Some(cert)
}

/// The ∀ player's strategy of an `unsat` run: for every variable of a
/// universal level `k > 0`, the decision list over the ∃ player's lemmas that
/// projected level `k` (first region wins, default `0`/`false`). The terms
/// are over engine variables of lower levels. The same minimality argument
/// as for the ∃ strategy (module docs) shows it wins, from the final level-0
/// refutation of `φ ∧ ⋀¬Pᵢ`; the consequence replay's ground probe decides
/// the expansion regardless.
pub(crate) fn forall_strategy(
    terms: &mut TermStore,
    game: &Game,
    run: &Run,
) -> HashMap<TermId, TermId> {
    let mut out = HashMap::default();
    for occ in &game.occurrences {
        if !occ.universal {
            continue;
        }
        for &v in &occ.vars {
            let sort = terms.sort(v).clone();
            let mut arms: Vec<(TermId, TermId)> = Vec::new();
            for lemma in &run.lemmas {
                if lemma.forall_owned || lemma.level != occ.level {
                    continue;
                }
                let Some(&(_, t)) = lemma.subst.iter().find(|(x, _)| *x == v) else {
                    continue;
                };
                let lits: Vec<TermId> = lemma
                    .region
                    .iter()
                    .map(|&(a, val)| if val { a } else { terms.mk_not_raw(a) })
                    .collect();
                let cond = match lits.as_slice() {
                    [] => terms.mk_bool(true),
                    [one] => *one,
                    _ => terms.mk_app(Symbol::named("and"), lits, Sort::Bool),
                };
                arms.push((cond, t));
            }
            let mut acc = default_term(terms, &sort);
            for (cond, t) in arms.into_iter().rev() {
                acc = if matches!(
                    terms.get(cond),
                    ay_core::term::TermData::Const(ay_core::term::Constant::Bool(true))
                ) {
                    t
                } else {
                    terms.mk_ite_raw(cond, t, acc)
                };
            }
            out.insert(v, acc);
        }
    }
    out
}
