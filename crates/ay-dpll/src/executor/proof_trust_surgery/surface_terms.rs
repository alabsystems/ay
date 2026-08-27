// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Surface-term equivalence and capture-safe let expansion.

use super::*;

pub(super) fn eq_flip_equivalent(terms: &ay_core::TermStore, a: TermId, b: TermId) -> bool {
    if a == b {
        return true;
    }
    match (terms.get(a), terms.get(b)) {
        (TermData::Not(x), TermData::Not(y)) => {
            let (x, y) = (*x, *y);
            eq_flip_equivalent(terms, x, y)
        }
        (TermData::App(sa, xa), TermData::App(sb, xb)) => {
            if sa != sb || xa.len() != xb.len() {
                return false;
            }
            let (sa, xa, xb) = (sa.clone(), xa.clone(), xb.clone());
            let straight = xa
                .iter()
                .zip(xb.iter())
                .all(|(&x, &y)| eq_flip_equivalent(terms, x, y));
            if straight {
                return true;
            }
            matches!(sa, Symbol::Named(ref n) if n == "=")
                && xa.len() == 2
                && eq_flip_equivalent(terms, xa[0], xb[1])
                && eq_flip_equivalent(terms, xa[1], xb[0])
        }
        _ => false,
    }
}

/// Fully expand `let` bindings in a surface term (SMT-LIB parallel-binding
/// semantics: binding values are expanded in the OUTER environment). Returns
/// `None` fail-closed on any binder that could capture (`forall`/`exists`/
/// `lambda`/`match` under a non-empty environment) so no incorrect
/// substitution is ever produced.
pub(super) fn expand_surface_lets(
    term: &FrontendTerm,
    env: &std::collections::HashMap<String, FrontendTerm>,
) -> Option<FrontendTerm> {
    match term {
        FrontendTerm::Let(bindings, body) => {
            let mut inner = env.clone();
            for (name, value) in bindings {
                let expanded = expand_surface_lets(value, env)?;
                inner.insert(name.clone(), expanded);
            }
            expand_surface_lets(body, &inner)
        }
        FrontendTerm::Symbol(name) => Some(match env.get(name) {
            Some(bound) => bound.clone(),
            None => term.clone(),
        }),
        FrontendTerm::App(head, args) => {
            let args = args
                .iter()
                .map(|a| expand_surface_lets(a, env))
                .collect::<Option<Vec<_>>>()?;
            Some(FrontendTerm::App(head.clone(), args))
        }
        FrontendTerm::IndexedApp(name, indices, args) => {
            let args = args
                .iter()
                .map(|arg| expand_surface_lets(arg, env))
                .collect::<Option<Vec<_>>>()?;
            Some(FrontendTerm::IndexedApp(
                name.clone(),
                indices.clone(),
                args,
            ))
        }
        FrontendTerm::QualifiedApp(identifier, sort, args) => {
            let args = args
                .iter()
                .map(|arg| expand_surface_lets(arg, env))
                .collect::<Option<Vec<_>>>()?;
            Some(FrontendTerm::QualifiedApp(
                identifier.clone(),
                sort.clone(),
                args,
            ))
        }
        FrontendTerm::Annotated(inner, notes) => {
            let inner = expand_surface_lets(inner, env)?;
            Some(FrontendTerm::Annotated(Box::new(inner), notes.clone()))
        }
        FrontendTerm::Const(_) => Some(term.clone()),
        _ => {
            // Binders (and any future variant) under an active environment
            // could capture: fail closed. Without bindings in scope the term
            // needs no expansion.
            env.is_empty().then(|| term.clone())
        }
    }
}
