// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Syntactic walks over parsed terms for `:named` labels.

use ay_core::kani_compat::DetHashSet as HashSet;

use super::{node_address, LabelSlot, NAMED};
use crate::command::{MatchPattern, QualifiedIdentifier, Term as ParsedTerm};
use crate::sexp::{SExpr, PARSE_STACK_RED_ZONE, PARSE_STACK_SIZE};

/// Whether an attribute value mentions `:named` anywhere.
fn sexpr_mentions_named(value: &SExpr) -> bool {
    let mut stack = vec![value];
    while let Some(item) = stack.pop() {
        match item {
            SExpr::Keyword(keyword) if keyword == NAMED => return true,
            SExpr::List(items) => stack.extend(items.iter()),
            _ => {}
        }
    }
    false
}

/// Bare symbols the elaborator resolves to a builtin constant.
pub(super) fn is_builtin_bare_symbol(name: &str) -> bool {
    matches!(
        name,
        "true"
            | "false"
            | "re.none"
            | "re.all"
            | "re.allchar"
            | "RNE"
            | "RNA"
            | "RTP"
            | "RTN"
            | "RTZ"
            | "roundNearestTiesToEven"
            | "roundNearestTiesToAway"
            | "roundTowardPositive"
            | "roundTowardNegative"
            | "roundTowardZero"
    ) || name
        .strip_prefix('-')
        .is_some_and(|rest| rest.starts_with(|c: char| c.is_ascii_digit()))
}

/// Every `:named` attribute in `root`, and whether all of them are reached
/// in z3's parse order (see [`LabelJournal::in_parse_order`]).
pub(super) fn authored_label_slots(root: &ParsedTerm) -> (HashSet<LabelSlot>, bool) {
    let mut slots = HashSet::default();
    let mut in_parse_order = true;
    // (term, whether it sits in a position elaborated out of parse order)
    let mut stack = vec![(root, false)];
    while let Some((term, reordered)) = stack.pop() {
        match term {
            ParsedTerm::Const(_) | ParsedTerm::Symbol(_) => {}
            ParsedTerm::App(_, args)
            | ParsedTerm::IndexedApp(_, _, args)
            | ParsedTerm::QualifiedApp(_, _, args) => {
                stack.extend(args.iter().map(|arg| (arg, reordered)));
            }
            ParsedTerm::Let(bindings, body) => {
                stack.extend(bindings.iter().map(|(_, value)| (value, true)));
                stack.push((body, reordered));
            }
            ParsedTerm::Forall(_, body)
            | ParsedTerm::Exists(_, body)
            | ParsedTerm::Lambda(_, body) => stack.push((body, reordered)),
            ParsedTerm::Annotated(inner, annotations) => {
                for (index, (keyword, value)) in annotations.iter().enumerate() {
                    if keyword == NAMED {
                        slots.insert((node_address(term), index));
                        in_parse_order &= !reordered;
                    } else if sexpr_mentions_named(value) {
                        in_parse_order = false;
                    }
                }
                stack.push((inner, reordered));
            }
            ParsedTerm::Match(scrutinee, cases) => {
                stack.push((scrutinee, true));
                stack.extend(cases.iter().map(|(_, body)| (body, true)));
            }
        }
    }
    (slots, in_parse_order)
}

/// Whether `term` contains a `:named` annotation anywhere.
#[must_use]
pub fn term_has_named_label(term: &ParsedTerm) -> bool {
    let (slots, in_parse_order) = authored_label_slots(term);
    !slots.is_empty() || !in_parse_order
}

/// Names occurring free in `term`, application heads included, respecting
/// quantifier, lambda, `let` and `match` binders.
pub(in crate::elaborate) fn free_term_names(term: &ParsedTerm) -> HashSet<String> {
    let mut out = HashSet::default();
    collect_free_names(term, &mut Vec::new(), &mut out);
    out
}

fn collect_free_names(term: &ParsedTerm, bound: &mut Vec<String>, out: &mut HashSet<String>) {
    stacker::maybe_grow(PARSE_STACK_RED_ZONE, PARSE_STACK_SIZE, || match term {
        ParsedTerm::Const(_) => {}
        ParsedTerm::Symbol(name) => {
            if !bound.iter().any(|b| b == name) {
                out.insert(name.clone());
            }
        }
        // An application's head counts too: a variable of that name in scope
        // shadows the function, and the elaborator rejects the application.
        ParsedTerm::App(name, args) => {
            if !bound.iter().any(|b| b == name) {
                out.insert(name.clone());
            }
            for arg in args {
                collect_free_names(arg, bound, out);
            }
        }
        ParsedTerm::IndexedApp(_, _, args) => {
            for arg in args {
                collect_free_names(arg, bound, out);
            }
        }
        ParsedTerm::QualifiedApp(identifier, _, args) => {
            if let QualifiedIdentifier::Symbol(name) = identifier {
                if !bound.iter().any(|b| b == name) {
                    out.insert(name.clone());
                }
            }
            for arg in args {
                collect_free_names(arg, bound, out);
            }
        }
        ParsedTerm::Let(bindings, body) => {
            for (_, value) in bindings {
                collect_free_names(value, bound, out);
            }
            let mark = bound.len();
            bound.extend(bindings.iter().map(|(name, _)| name.clone()));
            collect_free_names(body, bound, out);
            bound.truncate(mark);
        }
        ParsedTerm::Forall(vars, body)
        | ParsedTerm::Exists(vars, body)
        | ParsedTerm::Lambda(vars, body) => {
            let mark = bound.len();
            bound.extend(vars.iter().map(|(name, _)| name.clone()));
            collect_free_names(body, bound, out);
            bound.truncate(mark);
        }
        ParsedTerm::Annotated(inner, _) => collect_free_names(inner, bound, out),
        ParsedTerm::Match(scrutinee, cases) => {
            collect_free_names(scrutinee, bound, out);
            for (pattern, body) in cases {
                let mark = bound.len();
                match pattern {
                    MatchPattern::Symbol(name) => bound.push(name.clone()),
                    MatchPattern::Constructor(_, fields) => bound.extend(fields.iter().cloned()),
                }
                collect_free_names(body, bound, out);
                bound.truncate(mark);
            }
        }
    });
}

/// `term` with every `:named` attribute removed. The labels inside a labeled
/// term are bound before the outer one, so the outer definition must not bind
/// them again each time it is expanded.
pub(super) fn strip_named(term: &ParsedTerm) -> ParsedTerm {
    stacker::maybe_grow(PARSE_STACK_RED_ZONE, PARSE_STACK_SIZE, || match term {
        ParsedTerm::Const(_) | ParsedTerm::Symbol(_) => term.clone(),
        ParsedTerm::App(name, args) => {
            ParsedTerm::App(name.clone(), args.iter().map(strip_named).collect())
        }
        ParsedTerm::IndexedApp(name, indices, args) => ParsedTerm::IndexedApp(
            name.clone(),
            indices.clone(),
            args.iter().map(strip_named).collect(),
        ),
        ParsedTerm::QualifiedApp(identifier, sort, args) => ParsedTerm::QualifiedApp(
            identifier.clone(),
            sort.clone(),
            args.iter().map(strip_named).collect(),
        ),
        ParsedTerm::Let(bindings, body) => ParsedTerm::Let(
            bindings
                .iter()
                .map(|(name, value)| (name.clone(), strip_named(value)))
                .collect(),
            Box::new(strip_named(body)),
        ),
        ParsedTerm::Forall(vars, body) => {
            ParsedTerm::Forall(vars.clone(), Box::new(strip_named(body)))
        }
        ParsedTerm::Exists(vars, body) => {
            ParsedTerm::Exists(vars.clone(), Box::new(strip_named(body)))
        }
        ParsedTerm::Lambda(vars, body) => {
            ParsedTerm::Lambda(vars.clone(), Box::new(strip_named(body)))
        }
        ParsedTerm::Annotated(inner, annotations) => {
            let kept: Vec<_> = annotations
                .iter()
                .filter(|(keyword, _)| keyword != NAMED)
                .cloned()
                .collect();
            let inner = strip_named(inner);
            if kept.is_empty() {
                inner
            } else {
                ParsedTerm::Annotated(Box::new(inner), kept)
            }
        }
        ParsedTerm::Match(scrutinee, cases) => ParsedTerm::Match(
            Box::new(strip_named(scrutinee)),
            cases
                .iter()
                .map(|(pattern, body)| (pattern.clone(), strip_named(body)))
                .collect(),
        ),
    })
}
