// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Exact structural alignment of a search term with its authored-surface
//! counterpart.
//!
//! A search term differs from the authored-surface term at the same position
//! only where the search placed one of its own constants (a counterexample
//! constant or a Skolem constant of the rewritten roots): the surface has the
//! enclosing occurrence's instance value or registered witness there. Every
//! other node — symbols, binder lists, triggers, bound and free variables,
//! constants — must be identical. [`bind`] reads the constant → surface-term
//! map off that alignment and refuses any other difference; [`apply`] then
//! transports a logged instance tuple onto the surface.
//!
//! Nothing here is authority: a mis-aligned map yields surface terms the
//! strict checker's `forall_inst` / `sko` validators re-derive from the
//! authored quantifier alone.

use ay_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};
use ay_core::term::TermData;
use ay_core::{TermId, TermStore};

use super::lemma_plan::PlanDecline;

/// Node pairs one alignment may visit.
const MAX_ALIGN_WORK: usize = 1 << 21;

/// Search constant → surface term.
pub(super) type Sigma = HashMap<TermId, TermId>;

/// Align `search` with `surface`, binding every `pattern` constant of
/// `search` to the surface term at the same position.
pub(super) fn bind(
    terms: &TermStore,
    pattern: &HashSet<TermId>,
    search: TermId,
    surface: TermId,
) -> Result<Sigma, PlanDecline> {
    let mut sigma = Sigma::default();
    let mut seen: HashSet<(TermId, TermId)> = HashSet::default();
    let mut stack = vec![(search, surface)];
    while let Some((s, c)) = stack.pop() {
        if !seen.insert((s, c)) {
            continue;
        }
        if seen.len() > MAX_ALIGN_WORK {
            return Err(PlanDecline::Cap);
        }
        if pattern.contains(&s) {
            match sigma.get(&s) {
                Some(&bound) if bound != c => return Err(PlanDecline::Alignment),
                Some(_) => {}
                None => {
                    sigma.insert(s, c);
                }
            }
            continue;
        }
        if s == c {
            continue;
        }
        if terms.sort(s) != terms.sort(c) {
            return Err(PlanDecline::Alignment);
        }
        match (terms.get(s), terms.get(c)) {
            (TermData::App(fs, sa), TermData::App(fc, ca)) if fs == fc && sa.len() == ca.len() => {
                stack.extend(sa.iter().copied().zip(ca.iter().copied()));
            }
            (TermData::Not(a), TermData::Not(b)) => stack.push((*a, *b)),
            (TermData::Ite(sc, sa, sb), TermData::Ite(cc, ca, cb)) => {
                stack.extend([(*sc, *cc), (*sa, *ca), (*sb, *cb)]);
            }
            (TermData::Forall(bs, sb, ts), TermData::Forall(bc, cb, tc))
            | (TermData::Exists(bs, sb, ts), TermData::Exists(bc, cb, tc))
                if bs == bc && ts.len() == tc.len() =>
            {
                stack.push((*sb, *cb));
                for (group_s, group_c) in ts.iter().zip(tc) {
                    if group_s.len() != group_c.len() {
                        return Err(PlanDecline::Alignment);
                    }
                    stack.extend(group_s.iter().copied().zip(group_c.iter().copied()));
                }
            }
            _ => return Err(PlanDecline::Alignment),
        }
    }
    Ok(sigma)
}

/// `term` with every `pattern` constant replaced through `sigma`. The term is
/// a quantifier-free instance value; a pattern constant `sigma` does not bind
/// has no surface counterpart ([`PlanDecline::Unbound`]).
pub(super) fn apply(
    terms: &mut TermStore,
    pattern: &HashSet<TermId>,
    sigma: &Sigma,
    term: TermId,
    memo: &mut HashMap<TermId, TermId>,
) -> Result<TermId, PlanDecline> {
    if let Some(&done) = memo.get(&term) {
        return Ok(done);
    }
    let out = match terms.get(term).clone() {
        TermData::Var(..) if pattern.contains(&term) => {
            *sigma.get(&term).ok_or(PlanDecline::Unbound)?
        }
        TermData::Var(..) | TermData::Const(_) => term,
        TermData::App(symbol, args) => {
            let mut rewritten = Vec::with_capacity(args.len());
            for &arg in &args {
                rewritten.push(apply(terms, pattern, sigma, arg, memo)?);
            }
            if rewritten == args {
                term
            } else {
                let sort = terms.sort(term).clone();
                terms.mk_app(symbol, rewritten, sort)
            }
        }
        TermData::Not(inner) => {
            let rewritten = apply(terms, pattern, sigma, inner, memo)?;
            if rewritten == inner {
                term
            } else {
                terms.mk_not_raw(rewritten)
            }
        }
        TermData::Ite(c, a, b) => {
            let c2 = apply(terms, pattern, sigma, c, memo)?;
            let a2 = apply(terms, pattern, sigma, a, memo)?;
            let b2 = apply(terms, pattern, sigma, b, memo)?;
            if (c2, a2, b2) == (c, a, b) {
                term
            } else {
                terms.mk_ite_raw(c2, a2, b2)
            }
        }
        _ => return Err(PlanDecline::Alignment),
    };
    memo.insert(term, out);
    Ok(out)
}

/// Whether any of `roots` mentions a `pattern` constant (bounded; an
/// exhausted scan answers `true`, which declines).
pub(super) fn mentions_any(terms: &TermStore, pattern: &HashSet<TermId>, roots: &[TermId]) -> bool {
    let mut seen: HashSet<TermId> = HashSet::default();
    let mut stack: Vec<TermId> = roots.to_vec();
    while let Some(t) = stack.pop() {
        if !seen.insert(t) {
            continue;
        }
        if seen.len() > MAX_ALIGN_WORK || pattern.contains(&t) {
            return true;
        }
        match terms.get(t) {
            TermData::App(_, args) => stack.extend(args.iter().copied()),
            TermData::Not(inner) => stack.push(*inner),
            TermData::Ite(c, a, b) => stack.extend([*c, *a, *b]),
            TermData::Forall(_, body, triggers) | TermData::Exists(_, body, triggers) => {
                stack.push(*body);
                stack.extend(triggers.iter().flatten().copied());
            }
            TermData::Let(bindings, body) => {
                stack.extend(bindings.iter().map(|(_, v)| *v));
                stack.push(*body);
            }
            _ => {}
        }
    }
    false
}
