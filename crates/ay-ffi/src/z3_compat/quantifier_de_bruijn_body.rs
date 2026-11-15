// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The de Bruijn form of a quantifier's body (`Z3_get_quantifier_body`).

use std::collections::HashMap;

use ay_dpll::api::{de_bruijn_index, Sort, Term, TermKind};

use super::super::provenance::LAMBDA_ARRAY;
use super::super::quantifiers::{de_bruijn_public_sort, de_bruijn_var_at};
use super::super::Z3Context;
use super::quantifier_bound_public_sort;

/// `body` of the quantifier `quantifier` in de Bruijn form.
///
/// AY binds by name, and its de Bruijn variables `__db{k}` are anchored at
/// the root of the term they occur in: a named binder in between does not
/// shift them (`Z3_mk_quantifier` resolves a `(:var k)` at any depth, and
/// `substitute_vars` replaces `__db{k}` wherever it occurs). So binder `i` of
/// `n` becomes `__db{n-1-i}` wherever it occurs in the body, and a loose
/// `__db{k}` of the quantifier becomes `__db{k+n}` of its body. A nested
/// quantifier's body adds its own binders the same way, which gives z3's
/// indices: the body of `ForAll x. Exists y. x < y` is `Exists y. __db0 < y`,
/// and that one's body is `__db1 < __db0`, z3's `(< (:var 1) (:var 0))`
/// (libz3 5.1.0, `t5x/body_pins.py`). Indexing a binder by its depth (z3's
/// relative indices) instead made `substitute_vars(q.body(), ..)` miss the
/// variable, and leaving a loose `__db{k}` unshifted let the body's own
/// binder capture it.
///
/// `None` (the caller returns the body as stored) when a binder inside the
/// body has a de Bruijn spelling, which the shift would rename, or a `let`
/// hides its bound names.
pub(super) fn de_bruijn_body(ctx: &mut Z3Context, quantifier: Term, body: Term) -> Option<Term> {
    let vars = ctx.solver.quantifier_bound_vars(quantifier)?;
    let n = vars.len();
    let mut binders = HashMap::with_capacity(n);
    for (i, (name, engine)) in vars.into_iter().enumerate() {
        let public = quantifier_bound_public_sort(ctx, quantifier, i).unwrap_or(engine);
        binders.insert(name, (n - 1 - i, public));
    }
    let mut memo = HashMap::new();
    rebuild_de_bruijn(ctx, body, &binders, n, &mut memo)
}

/// The quantifier's binders still in scope, by name: their de Bruijn index
/// in the body and their public sort.
type DeBruijnBinders = HashMap<String, (usize, Sort)>;

fn rebuild_de_bruijn(
    ctx: &mut Z3Context,
    term: Term,
    binders: &DeBruijnBinders,
    shift: usize,
    memo: &mut HashMap<(Term, Vec<String>), Term>,
) -> Option<Term> {
    let mut in_scope: Vec<String> = binders.keys().cloned().collect();
    in_scope.sort_unstable();
    let key = (term, in_scope);
    if let Some(&done) = memo.get(&key) {
        return Some(done);
    }
    let result = match ctx.solver.term_kind(term) {
        TermKind::Const => term,
        TermKind::Var { name } => match binders.get(&name) {
            Some((index, public)) => {
                let (index, public) = (*index, public.clone());
                let engine = ctx.solver.term_sort(term);
                de_bruijn_var_at(ctx, index, engine, &public).ok()?
            }
            None => match de_bruijn_index(&name) {
                Some(loose) => {
                    let public = de_bruijn_public_sort(ctx, term);
                    let engine = ctx.solver.term_sort(term);
                    de_bruijn_var_at(ctx, loose.checked_add(shift)?, engine, &public).ok()?
                }
                None => term,
            },
        },
        TermKind::Forall | TermKind::Exists => {
            let inner = ctx.solver.quantifier_bound_vars(term)?;
            if inner
                .iter()
                .any(|(name, _)| de_bruijn_index(name).is_some())
            {
                return None;
            }
            let mut shadowed = binders.clone();
            for (name, _) in &inner {
                shadowed.remove(name);
            }
            rebuild_children(ctx, term, &shadowed, shift, memo)?
        }
        TermKind::App { name, .. } if name == LAMBDA_ARRAY => {
            // A lambda's slot (its first child) is a named binder too.
            let children = ctx.solver.term_children(term);
            let mut shadowed = binders.clone();
            if let Some(&slot) = children.first() {
                if let TermKind::Var { name } = ctx.solver.term_kind(slot) {
                    if de_bruijn_index(&name).is_some() {
                        return None;
                    }
                    shadowed.remove(&name);
                }
            }
            rebuild_children(ctx, term, &shadowed, shift, memo)?
        }
        TermKind::Let => return None,
        _ => rebuild_children(ctx, term, binders, shift, memo)?,
    };
    memo.insert(key, result);
    Some(result)
}

/// `term` with each child rebuilt by [`rebuild_de_bruijn`].
fn rebuild_children(
    ctx: &mut Z3Context,
    term: Term,
    binders: &DeBruijnBinders,
    shift: usize,
    memo: &mut HashMap<(Term, Vec<String>), Term>,
) -> Option<Term> {
    let children = ctx.solver.term_children(term);
    let mut rebuilt = Vec::with_capacity(children.len());
    for &child in &children {
        rebuilt.push(rebuild_de_bruijn(ctx, child, binders, shift, memo)?);
    }
    if rebuilt == children {
        Some(term)
    } else {
        ctx.solver.try_update_term(term, &rebuilt).ok()
    }
}
