// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Model-preserving midpoint selection (plan §3.4 steps 2–3).
//!
//! Given a model `I` of `¬φ[k, e⃗]` and an implicant `L` of `¬φ` true in `I`,
//! eliminate `e_1..e_n` in binder order:
//!
//! * a solved equality `e_i = s` gives `t_i = s`;
//! * otherwise, with `ℓ*` the lower bound of largest value in `I` and `u*` the
//!   upper bound of smallest value (strict wins ties): `t_i = (ℓ*+u*)/2`, or
//!   `ℓ*` when both are non-strict and equal in `I`, `ℓ*+1` with only a lower
//!   bound, `u*−1` with only an upper bound, `0` with none;
//! * a disequality is read as the strict bound on the side `I` places `e_i`;
//! * a Bool binder takes its model value.
//!
//! MODEL PRESERVATION. `I(t_i)` satisfies every bound on `e_i`, so each
//! literal of `L[e_i := t_i]` is still true in `I`; the implementation
//! RE-CHECKS this after every step and declines on any violation. After the
//! forward pass the tuple is back-substituted so every `t_i` is over the
//! problem constants only (the `#cegqi-ce-var-selection` invariant), and
//! `L[e⃗ := t⃗] = L_n` is true in `I`, hence `I ⊨ ¬φ[k, t⃗]`.
//!
//! FINITENESS. Every `t_i` is a midpoint/±1 combination of bound terms drawn
//! from the finitely many atoms of `φ`.

use ay_core::kani_compat::DetHashMap as HashMap;
use ay_core::{Sort, TermId, TermStore};
use num_rational::BigRational;
use num_traits::{One, Signed, Zero};

use super::implicant::{lit_holds, Assignment, LinLit, Walker};
use crate::qe::cooper::Rel;
use crate::qe::linrat::LinRat;

/// Why a selection declined.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum SelectDecline {
    /// The body left linear real arithmetic over Bool connectives, or the
    /// model did not evaluate it to `false`.
    Implicant,
    /// A counterexample constant has no model value.
    Unassigned,
    /// A post-substitution literal was false in the model (defensive).
    ModelPreservation,
    /// A selected term still mentions a counterexample constant (defensive).
    CeLeak,
}

struct Bound {
    term: LinRat,
    value: BigRational,
    strict: bool,
}

/// The selected tuple as linear forms over problem constants (Real binders)
/// or constants (Bool binders), before term construction.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum Selected {
    Real(LinRat),
    Bool(bool),
}

fn value_of(lin: &LinRat, reals: &HashMap<TermId, BigRational>) -> Option<BigRational> {
    let assign: std::collections::HashMap<TermId, BigRational> = lin
        .coeffs
        .keys()
        .filter_map(|v| Some((*v, reals.get(v)?.clone())))
        .collect();
    lin.eval(&assign)
}

/// `a·e + r ⋈ 0` read as a bound on `e`: `(bound term, is_lower, strict)` or
/// `None` for an equality (handled by the caller).
fn as_bound(
    rel: Rel,
    lin: &LinRat,
    var: TermId,
    reals: &HashMap<TermId, BigRational>,
) -> Option<Option<(Bound, bool)>> {
    let a = lin.coeff_of(var);
    let mut term = lin.without(var);
    term.scale(&(-a.recip()));
    let value = value_of(&term, reals)?;
    let current = reals.get(&var)?.clone();
    let (lower, strict) = match rel {
        Rel::Eq => return Some(None),
        Rel::Le => (a.is_negative(), false),
        Rel::Lt => (a.is_negative(), true),
        Rel::Ne => (current > value, true),
    };
    Some(Some((
        Bound {
            term,
            value,
            strict,
        },
        lower,
    )))
}

/// Pick `t` for `var` from the literals mentioning it.
fn choose(lits: &[LinLit], var: TermId, reals: &HashMap<TermId, BigRational>) -> Option<LinRat> {
    let mut lower: Option<Bound> = None;
    let mut upper: Option<Bound> = None;
    for (rel, lin) in lits {
        if lin.coeff_of(var).is_zero() {
            continue;
        }
        let Some((bound, is_lower)) = as_bound(*rel, lin, var, reals)? else {
            // Solved equality: e = -rest/a.
            let mut term = lin.without(var);
            term.scale(&(-lin.coeff_of(var).recip()));
            return Some(term);
        };
        let slot = if is_lower { &mut lower } else { &mut upper };
        let better = match slot {
            None => true,
            Some(best) if is_lower => {
                bound.value > best.value
                    || (bound.value == best.value && bound.strict && !best.strict)
            }
            Some(best) => {
                bound.value < best.value
                    || (bound.value == best.value && bound.strict && !best.strict)
            }
        };
        if better {
            *slot = Some(bound);
        }
    }
    let one = LinRat {
        coeffs: Default::default(),
        constant: BigRational::one(),
    };
    Some(match (lower, upper) {
        (Some(l), Some(u)) if l.value == u.value => l.term,
        (Some(l), Some(u)) => {
            let mut mid = l.term;
            mid.add(&u.term);
            mid.scale(&BigRational::new(1.into(), 2.into()));
            mid
        }
        (Some(l), None) => {
            let mut t = l.term;
            t.add(&one);
            t
        }
        (None, Some(u)) => {
            let mut t = u.term;
            t.sub(&one);
            t
        }
        (None, None) => LinRat::zero(),
    })
}

/// Select a tuple for binders `ce_vars` (sorts `sorts`) from a model of
/// `¬ce_body`. Returns the tuple over problem constants.
pub(crate) fn select_tuple(
    terms: &TermStore,
    ce_body: TermId,
    ce_vars: &[TermId],
    sorts: &[Sort],
    model: &Assignment,
    max_work: usize,
) -> Result<Vec<Selected>, SelectDecline> {
    select_tuple_for(terms, ce_body, false, ce_vars, sorts, model, max_work)
}

/// Select a tuple for binders `ce_vars` from a model in which `formula`
/// evaluates to `want`: the implicant is taken of `formula = want`, and the
/// tuple keeps `formula[e⃗ := t⃗] = want` true in the model. A universal's
/// counterexample asks for `want = false`, an existential's witness for
/// `want = true`.
pub(crate) fn select_tuple_for(
    terms: &TermStore,
    formula: TermId,
    want: bool,
    ce_vars: &[TermId],
    sorts: &[Sort],
    model: &Assignment,
    max_work: usize,
) -> Result<Vec<Selected>, SelectDecline> {
    let mut walker = Walker {
        terms,
        model,
        ce_vars,
        work: 0,
        max_work,
    };
    let mut lits: Vec<LinLit> = Vec::new();
    walker
        .implicant(formula, want, &mut lits)
        .ok_or(SelectDecline::Implicant)?;
    let mut reals = model.reals.clone();
    let mut chosen: Vec<Selected> = Vec::with_capacity(ce_vars.len());
    for (&var, sort) in ce_vars.iter().zip(sorts) {
        // A binder the (folded) body never mentions has no model value and
        // constrains nothing: any value, here the default, is model-preserving.
        if matches!(sort, Sort::Bool) {
            let value = model.bools.get(&var).copied().unwrap_or(false);
            chosen.push(Selected::Bool(value));
            continue;
        }
        reals.entry(var).or_insert_with(BigRational::zero);
        let t = choose(&lits, var, &reals).ok_or(SelectDecline::Unassigned)?;
        for lit in &mut lits {
            lit.1 = lit.1.substitute(var, &t);
        }
        let t_value = value_of(&t, &reals).ok_or(SelectDecline::Unassigned)?;
        reals.insert(var, t_value);
        if lits.iter().any(|lit| lit_holds(lit, &reals) != Some(true)) {
            return Err(SelectDecline::ModelPreservation);
        }
        chosen.push(Selected::Real(t));
    }
    back_substitute(&mut chosen, ce_vars);
    for selected in &chosen {
        if let Selected::Real(lin) = selected {
            if lin.coeffs.keys().any(|v| ce_vars.contains(v)) {
                return Err(SelectDecline::CeLeak);
            }
        }
    }
    Ok(chosen)
}

/// `t_i := t_i[e_j := t_j]` for `j > i`, last to first, so every entry is over
/// problem constants only.
fn back_substitute(chosen: &mut [Selected], ce_vars: &[TermId]) {
    for i in (0..chosen.len()).rev() {
        for j in (i + 1)..chosen.len() {
            let Selected::Real(later) = chosen[j].clone() else {
                continue;
            };
            if let Selected::Real(lin) = &mut chosen[i] {
                *lin = lin.substitute(ce_vars[j], &later);
            }
        }
    }
}

/// Build the tuple's terms.
pub(crate) fn tuple_terms(terms: &mut TermStore, chosen: &[Selected]) -> Vec<TermId> {
    chosen
        .iter()
        .map(|selected| match selected {
            Selected::Real(lin) => lin.to_term(terms),
            Selected::Bool(b) => terms.mk_bool(*b),
        })
        .collect()
}
