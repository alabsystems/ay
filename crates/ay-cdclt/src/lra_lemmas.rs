// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The lemmas the LRA plug-in adds in place of the lanes' requests (design
//! §3.5). Each one is T-valid whatever the current assignment (K4), and each
//! carries the lemma kind the checker validates (P1).

use ay_core::TheorySolver;
use ay_core::{
    ModelEqualityRequest, Sort, TermData, TermId, TermStore, TheoryConflict, TheoryLemmaKind,
    TheoryLit, TheoryResult,
};
use ay_lra::{LraSolver, TermCut};
use num_rational::BigRational;
use num_traits::One;

use crate::atoms::eq_atom;
use crate::plugin::{Conflict, Ctx, GiveUp, Lemma, LemmaTier, ProofHint};

pub(crate) fn farkas_conflict(conflict: TheoryConflict) -> Conflict {
    Conflict {
        lits: conflict.literals,
        hint: conflict.farkas.map_or_else(
            || ProofHint::kind(TheoryLemmaKind::Generic),
            ProofHint::farkas,
        ),
    }
}

/// A bound axiom `l1 ∨ l2` when a fresh simplex over the reals refutes
/// `¬l1 ∧ ¬l2`, with the refutation's Farkas certificate as its hint; `None`
/// when it does not, and the pair is dropped. Real validity implies integer
/// validity, so one check serves both plug-in modes.
///
/// The lemma is the negation of the refuted literals in the refutation's own
/// order, so a Farkas hint stays aligned with its clause (`ProofHint`); a
/// refutation naming any literal but `¬l1`, `¬l2` drops the pair.
pub(crate) fn bound_axiom(terms: &TermStore, clause: [TheoryLit; 2]) -> Option<Lemma> {
    let mut check = LraSolver::new(terms);
    for lit in &clause {
        check.assert_literal(lit.term, !lit.value);
    }
    let result = check.check();
    check.unset_terms();
    let conflict = match result {
        TheoryResult::UnsatWithFarkas(conflict) => farkas_conflict(conflict),
        TheoryResult::Unsat(lits) => Conflict {
            lits,
            hint: ProofHint::kind(TheoryLemmaKind::Generic),
        },
        _ => return None,
    };
    let refuted: Vec<TheoryLit> = conflict
        .lits
        .iter()
        .map(|l| TheoryLit::new(l.term, !l.value))
        .collect();
    if refuted.is_empty() || refuted.iter().any(|l| !clause.contains(l)) {
        return None;
    }
    Some(Lemma {
        clause: refuted,
        tier: LemmaTier::Redundant,
        hint: conflict.hint,
    })
}

/// `lt ∨ gt ∨ eq`: trichotomy, T-valid over Int and Real (K4), in the
/// literal order `ArithDisequalitySplit` validates (branches, then guard).
pub(crate) fn trichotomy(lt: TermId, gt: TermId, eq: TermId) -> Lemma {
    Lemma {
        clause: vec![
            TheoryLit::new(lt, true),
            TheoryLit::new(gt, true),
            TheoryLit::new(eq, true),
        ],
        tier: LemmaTier::Redundant,
        hint: ProofHint::kind(TheoryLemmaKind::ArithDisequalitySplit),
    }
}

fn arithmetic(terms: &TermStore, term: TermId) -> Result<(), GiveUp> {
    match terms.sort(term) {
        Sort::Real | Sort::Int => Ok(()),
        other => Err(GiveUp::new(format!(
            "lra: a split over sort {other:?} is not arithmetic"
        ))),
    }
}

/// Whether a model-equality answer only repeats guesses whose atoms exist and
/// are assigned.
pub(crate) fn hints_exhausted(ctx: &Ctx<'_>, result: &TheoryResult) -> bool {
    let requests = match result {
        TheoryResult::NeedModelEquality(request) => std::slice::from_ref(request),
        TheoryResult::NeedModelEqualities(requests) => requests.as_slice(),
        _ => return false,
    };
    requests.iter().all(|r| {
        ctx.terms()
            .find_eq(r.lhs, r.rhs)
            .and_then(|eq| ctx.value(eq))
            .is_some()
    })
}

/// A speculative model equality (design H3): mint `(= a b)`, add its
/// trichotomy lemma so the atom exists and a false decision can still split,
/// and ask the search to try it true first. `implied` requests carry a theory
/// reason (the ITE link lemmas are of this kind), so `¬reason ∨ (= a b)` is
/// added as well.
pub(crate) fn model_equality(
    ctx: &mut Ctx<'_>,
    request: &ModelEqualityRequest,
) -> Result<(), GiveUp> {
    let terms = ctx.terms_mut();
    arithmetic(terms, request.lhs)?;
    let eq = eq_atom(terms, request.lhs, request.rhs);
    let lt = terms.mk_lt(request.lhs, request.rhs);
    let gt = terms.mk_gt(request.lhs, request.rhs);
    ctx.lemma(trichotomy(lt, gt, eq));
    if request.implied {
        let mut clause: Vec<TheoryLit> = request
            .reason
            .iter()
            .map(|r| TheoryLit::new(r.term, !r.value))
            .collect();
        clause.push(TheoryLit::new(eq, true));
        let kind = if is_ite_branch_projection(ctx.terms(), &clause) {
            TheoryLemmaKind::IteBranchProjection
        } else {
            TheoryLemmaKind::Generic
        };
        ctx.lemma(Lemma {
            clause,
            tier: LemmaTier::Redundant,
            hint: ProofHint::kind(kind),
        });
    }
    ctx.prefer(TheoryLit::new(eq, true));
    Ok(())
}

/// The link definitions of an arithmetic `ite` `t = (ite c a b)`:
/// `¬c ∨ (= t a)` and `c ∨ (= t b)`, the clauses the LRA lane requests as
/// implied model equalities. The kernel starts every search with them: the
/// lane asks only for links whose equalities the term store does not hold
/// yet, and a store shared across checks can hold them from an earlier check
/// whose clauses this search never had (the `ite` was then a free variable).
/// Definitional, so a reduction never drops one the lane will not ask again.
pub(crate) fn ite_links(terms: &mut TermStore, ite: TermId) -> Vec<Lemma> {
    let TermData::Ite(c, then_branch, else_branch) = *terms.get(ite) else {
        return Vec::new();
    };
    [(false, then_branch), (true, else_branch)]
        .into_iter()
        .map(|(cond_value, branch)| {
            let eq = eq_atom(terms, ite, branch);
            let clause = vec![TheoryLit::new(c, cond_value), TheoryLit::new(eq, true)];
            let kind = if is_ite_branch_projection(terms, &clause) {
                TheoryLemmaKind::IteBranchProjection
            } else {
                TheoryLemmaKind::Generic
            };
            Lemma {
                clause,
                tier: LemmaTier::Definitional,
                hint: ProofHint::kind(kind),
            }
        })
        .collect()
}

/// Whether `[¬c, (= (ite c a b) a)]` or `[c, (= (ite c a b) b)]` is the
/// clause (either side of the equality may be the `ite`): the ITE link lemma
/// LRA asks for, which the checker validates as `IteBranchProjection`.
fn is_ite_branch_projection(terms: &TermStore, clause: &[TheoryLit]) -> bool {
    let [cond, eq] = clause else {
        return false;
    };
    if !eq.value {
        return false;
    }
    let TermData::App(sym, args) = terms.get(eq.term) else {
        return false;
    };
    let (&[left, right], "=") = (args.as_slice(), sym.name()) else {
        return false;
    };
    let (mut cond_term, mut cond_value) = (cond.term, cond.value);
    while let TermData::Not(inner) = terms.get(cond_term) {
        cond_term = *inner;
        cond_value = !cond_value;
    }
    [(left, right), (right, left)]
        .into_iter()
        .any(|(ite, other)| {
            let TermData::Ite(c, then_branch, else_branch) = terms.get(ite) else {
                return false;
            };
            let projected = if cond_value {
                *else_branch
            } else {
                *then_branch
            };
            *c == cond_term && other == projected
        })
}

/// Split `x ≠ c` for the request's variable and excluded value.
pub(crate) fn value_split(
    terms: &mut TermStore,
    request: &ay_core::DisequalitySplitRequest,
) -> Result<Lemma, GiveUp> {
    arithmetic(terms, request.variable)?;
    let c = if terms.sort(request.variable) == &Sort::Int {
        if !request.excluded_value.is_integer() {
            // An Int never equals a fraction; the vertex just sits on it,
            // so move it off with the branch-and-bound split around it.
            return Ok(branch_lemma(
                terms,
                request.variable,
                &request.excluded_value,
            ));
        }
        terms.mk_int(request.excluded_value.to_integer())
    } else {
        terms.mk_rational(request.excluded_value.clone())
    };
    let eq = eq_atom(terms, request.variable, c);
    let lt = terms.mk_lt(request.variable, c);
    let gt = terms.mk_gt(request.variable, c);
    Ok(trichotomy(lt, gt, eq))
}

/// Split a violated binary disequality `(not (= a b))` / `(distinct a b)`.
pub(crate) fn term_split(terms: &mut TermStore, diseq: TermId) -> Result<Lemma, GiveUp> {
    let (a, b) = binary_equality_sides(terms, diseq)
        .ok_or_else(|| GiveUp::new("lra: expression split on a non-binary disequality"))?;
    arithmetic(terms, a)?;
    let eq = eq_atom(terms, a, b);
    let lt = terms.mk_lt(a, b);
    let gt = terms.mk_gt(a, b);
    Ok(trichotomy(lt, gt, eq))
}

fn binary_equality_sides(terms: &TermStore, mut term: TermId) -> Option<(TermId, TermId)> {
    while let TermData::Not(inner) = terms.get(term) {
        term = *inner;
    }
    let TermData::App(sym, args) = terms.get(term) else {
        return None;
    };
    match (sym.name(), args.as_slice()) {
        ("=" | "distinct", &[a, b]) => Some((a, b)),
        _ => None,
    }
}

/// Branch and bound in the search (design §3.5): for an Int term whose value
/// `v` is fractional, `x ≤ ⌊v⌋ ∨ x ≥ ⌊v⌋ + 1`. T-valid over Int;
/// `IntBoundsTautology` is the kind the checker validates for a
/// branch-and-bound cover clause.
pub(crate) fn branch_lemma(terms: &mut TermStore, term: TermId, value: &BigRational) -> Lemma {
    let floor = BigRational::floor(value).to_integer();
    let lo = terms.mk_int(floor.clone());
    let hi = terms.mk_int(floor + 1);
    let le = terms.mk_le(term, lo);
    let ge = terms.mk_ge(term, hi);
    Lemma {
        clause: vec![TheoryLit::new(le, true), TheoryLit::new(ge, true)],
        tier: LemmaTier::Redundant,
        hint: ProofHint::kind(TheoryLemmaKind::IntBoundsTautology),
    }
}

/// A Gomory cut as a guarded lemma (design §3.5, K4): `¬r₁ ∨ … ∨ ¬rₖ ∨
/// (Σ aᵢ·tᵢ ≥ b)`, T-valid over Int because the reasons are the complete
/// justification of every bound the cut used. The cut atom is minted by the
/// kernel. `None` when the cut folds to a constant.
pub(crate) fn cut_lemma(terms: &mut TermStore, cut: TermCut) -> Option<Lemma> {
    let summands: Vec<TermId> = cut
        .coeffs
        .iter()
        .map(|(term, a)| {
            if a.is_one() {
                *term
            } else {
                let k = terms.mk_int(a.clone());
                terms.mk_mul(vec![k, *term])
            }
        })
        .collect();
    let lhs = match summands.as_slice() {
        [single] => *single,
        _ => terms.mk_add(summands),
    };
    let rhs = terms.mk_int(cut.bound);
    let atom = terms.mk_ge(lhs, rhs);
    if matches!(terms.get(atom), TermData::Const(_)) {
        return None;
    }
    let mut clause: Vec<TheoryLit> = cut
        .reasons
        .iter()
        .map(|&(term, value)| TheoryLit::new(term, !value))
        .collect();
    clause.push(TheoryLit::new(atom, true));
    Some(Lemma {
        clause,
        tier: LemmaTier::Redundant,
        hint: ProofHint::kind(TheoryLemmaKind::LiaGeneric),
    })
}
