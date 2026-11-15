// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The names a skipped subterm may read, so that only the bindings it names
//! are stood in for when it is checked.

use ay_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};
use ay_core::Sort;

use crate::command::{MatchPattern, QualifiedIdentifier, Term as ParsedTerm};
use crate::sexp::SExpr;

/// Every name `root` may look up in its environment, and more: each symbol it
/// mentions as a term, a function head, a `match` pattern or inside an
/// attribute value, whether or not a binder inside `root` shadows it. A name
/// outside this set is never read when `root` is elaborated.
pub(super) fn mentioned_names(root: &ParsedTerm) -> HashSet<String> {
    let mut names = HashSet::default();
    let mut terms = vec![root];
    let mut attribute_values: Vec<&SExpr> = Vec::new();
    while let Some(term) = terms.pop() {
        match term {
            ParsedTerm::Const(_) => {}
            ParsedTerm::Symbol(name) => {
                names.insert(name.clone());
            }
            ParsedTerm::App(name, args) | ParsedTerm::IndexedApp(name, _, args) => {
                names.insert(name.clone());
                terms.extend(args.iter());
            }
            ParsedTerm::QualifiedApp(identifier, _, args) => {
                if let QualifiedIdentifier::Symbol(name) = identifier {
                    names.insert(name.clone());
                }
                terms.extend(args.iter());
            }
            ParsedTerm::Let(bindings, body) => {
                terms.extend(bindings.iter().map(|(_, value)| value));
                terms.push(body);
            }
            ParsedTerm::Forall(_, body)
            | ParsedTerm::Exists(_, body)
            | ParsedTerm::Lambda(_, body) => terms.push(body),
            ParsedTerm::Annotated(inner, attributes) => {
                terms.push(inner);
                attribute_values.extend(attributes.iter().map(|(_, value)| value));
            }
            ParsedTerm::Match(scrutinee, cases) => {
                terms.push(scrutinee);
                for (pattern, body) in cases {
                    match pattern {
                        MatchPattern::Symbol(name) | MatchPattern::Constructor(name, _) => {
                            names.insert(name.clone());
                        }
                    }
                    terms.push(body);
                }
            }
        }
    }
    while let Some(value) = attribute_values.pop() {
        match value {
            SExpr::Symbol(name) => {
                names.insert(name.clone());
            }
            SExpr::List(items) => attribute_values.extend(items.iter()),
            _ => {}
        }
    }
    names
}

/// The entries of `binders` that `term` names, in name order. Only these are
/// stood in for when `term` is checked: every earlier dead binding of a `let`
/// chain is in scope for each dead value, and standing all of them in for
/// every value made the work and the scratch copy's term store grow with the
/// square of the chain's length.
pub(super) fn binders_named_in(
    term: &ParsedTerm,
    binders: &HashMap<String, Sort>,
) -> Vec<(String, Sort)> {
    if binders.is_empty() {
        return Vec::new();
    }
    let mut named: Vec<(String, Sort)> = mentioned_names(term)
        .into_iter()
        .filter_map(|name| {
            let sort = binders.get(&name)?.clone();
            Some((name, sort))
        })
        .collect();
    named.sort_by(|left, right| left.0.cmp(&right.0));
    named
}
