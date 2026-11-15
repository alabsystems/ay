// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Conservative namespace guard for preferred scalar ITE naming.

use ay_core::kani_compat::DetHashSet;
use ay_core::{Sort, TermData, TermId, TermStore};

/// Bound both the contextual DAG walk and its pending work, including repeated
/// edges. Declining leaves the baseline exact Shannon encoding available.
const SHARING_SCAN_WORK: usize = 16_384;

/// Linear naming preserves an ITE shared inside a UF argument. An arithmetic
/// ITE outside such an argument keeps the existing Shannon encoding, whose
/// branch-local arithmetic propagation does not need that sharing.
pub(super) fn has_uf_argument_ite(
    terms: &TermStore,
    roots: &[TermId],
    should_stop: &impl Fn() -> bool,
) -> bool {
    scan_uf_argument_ites(terms, roots, should_stop) == Some(true)
}

/// Distinguish a complete negative inventory from a declined scan. Callers
/// excluding the shared-ITE fragment must not interpret an incomplete scan as
/// evidence that no such argument exists.
pub(in crate::executor::theories) fn scan_uf_argument_ites(
    terms: &TermStore,
    roots: &[TermId],
    should_stop: &impl Fn() -> bool,
) -> Option<bool> {
    if roots.len() > SHARING_SCAN_WORK {
        return None;
    }
    let mut pending: Vec<_> = roots.iter().map(|&term| (term, false)).collect();
    let mut seen = DetHashSet::default();
    let mut work = 0;
    let mut found = false;
    while let Some((term, under_uf_argument)) = pending.pop() {
        work += 1;
        if work > SHARING_SCAN_WORK || should_stop() {
            return None;
        }
        if !seen.insert((term, under_uf_argument)) {
            continue;
        }
        match terms.get(term) {
            TermData::Forall(..) | TermData::Exists(..) | TermData::Let(..) => return None,
            TermData::App(symbol, args) => {
                if pending.len().saturating_add(args.len()) > SHARING_SCAN_WORK {
                    return None;
                }
                let context = under_uf_argument
                    || (!args.is_empty()
                        && !crate::features::is_builtin_symbol_name(symbol.name()));
                pending.extend(args.iter().copied().map(|child| (child, context)));
            }
            TermData::Not(inner) => pending.push((*inner, under_uf_argument)),
            TermData::Ite(condition, then_term, else_term) => {
                found |= under_uf_argument && *terms.sort(term) != Sort::Bool;
                if pending.len().saturating_add(3) > SHARING_SCAN_WORK {
                    return None;
                }
                pending.extend(
                    [*condition, *then_term, *else_term].map(|child| (child, under_uf_argument)),
                );
            }
            TermData::Var(..) | TermData::Const(..) => {}
            _ => return None,
        }
    }
    Some(found)
}

/// The naming helper uses `__ay_ite_def_<TermId>`. Ordinary declarations reject
/// that namespace, but low-level/translated terms can still contain it. Decline
/// this optimization when the incoming problem uses any such name; retain the
/// exact Shannon path instead of risking an alias with an authored symbol.
pub(super) fn contains_definition_symbol(terms: &TermStore, roots: &[TermId]) -> bool {
    let mut seen = DetHashSet::default();
    let mut pending = roots.to_vec();
    while let Some(term) = pending.pop() {
        if !seen.insert(term) {
            continue;
        }
        let name = match terms.get(term) {
            TermData::Var(name, _) => Some(name.as_str()),
            TermData::App(symbol, _) => Some(symbol.name()),
            _ => None,
        };
        if name.is_some_and(|name| name.starts_with("__ay_ite_def_")) {
            return true;
        }
        pending.extend(terms.children(term));
    }
    false
}

#[cfg(test)]
mod tests {
    use super::*;
    use ay_core::{Sort, Symbol};

    #[test]
    fn authored_generated_variable_name_declines_naming() {
        let mut terms = TermStore::new();
        let condition = terms.mk_var("condition", Sort::Bool);
        let one = terms.mk_int(1.into());
        let two = terms.mk_int(2.into());
        let ite = terms.mk_ite(condition, one, two);
        let authored = terms.mk_var(format!("__ay_ite_def_{}", ite.0), Sort::Int);
        let root = terms.mk_eq(authored, two);
        assert!(contains_definition_symbol(&terms, &[ite, root]));
    }

    #[test]
    fn translated_nullary_function_name_also_declines_naming() {
        let mut terms = TermStore::new();
        let authored = terms.mk_app(Symbol::named("__ay_ite_def_42"), [], Sort::Int);
        assert!(contains_definition_symbol(&terms, &[authored]));
    }

    #[test]
    fn ordinary_user_symbols_allow_naming() {
        let mut terms = TermStore::new();
        let value = terms.mk_var("value", Sort::Int);
        let call = terms.mk_app(Symbol::named("f"), [value], Sort::Int);
        assert!(!contains_definition_symbol(&terms, &[call]));
    }

    #[test]
    fn preserves_uf_argument_ite_even_when_seen_first_outside_the_argument() {
        let mut terms = TermStore::new();
        let condition = terms.mk_var("condition", Sort::Bool);
        let one = terms.mk_int(1.into());
        let two = terms.mk_int(2.into());
        let ite = terms.mk_ite(condition, one, two);
        let call = terms.mk_app(Symbol::named("f"), [ite], Sort::Int);
        assert!(has_uf_argument_ite(&terms, &[call, ite], &|| false));
        assert!(!has_uf_argument_ite(&terms, &[call], &|| true));
        assert_eq!(scan_uf_argument_ites(&terms, &[call], &|| true), None);
        assert!(!has_uf_argument_ite(
            &terms,
            &vec![call; SHARING_SCAN_WORK + 1],
            &|| false
        ));
        assert_eq!(
            scan_uf_argument_ites(&terms, &vec![call; SHARING_SCAN_WORK + 1], &|| false),
            None
        );
    }

    #[test]
    fn arithmetic_ite_and_separate_uf_call_keep_shannon() {
        let mut terms = TermStore::new();
        let condition = terms.mk_var("condition", Sort::Bool);
        let x = terms.mk_var("x", Sort::Int);
        let one = terms.mk_int(1.into());
        let ite = terms.mk_ite(condition, x, one);
        let call = terms.mk_app(Symbol::named("f"), [x], Sort::Int);
        assert!(!has_uf_argument_ite(&terms, &[call, ite], &|| false));
        let sum = terms.mk_add(vec![x, ite]);
        let nested = terms.mk_app(Symbol::named("f"), [sum], Sort::Int);
        assert!(has_uf_argument_ite(&terms, &[nested], &|| false));
    }
}
