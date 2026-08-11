// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Proof-surface numeral realification without annotation-payload cloning.

use ay_frontend::command::{Constant as FrontendConstant, Term as FrontendTerm};
use ay_frontend::Context;

use super::{parsed_term_is_binder_free, strip_frontend_annotations};

fn subterm_is_real_sorted(ctx: &mut Context, term: &FrontendTerm) -> bool {
    parsed_term_is_binder_free(term)
        && ctx
            .elaborate_surface_subterm(term)
            .is_some_and(|id| *ctx.terms.sort(id) == ay_core::Sort::Real)
}

/// Rewrite Int numerals in Real arithmetic positions. Annotation metadata is
/// never proof-visible here, so it is dropped recursively instead of cloned.
pub(super) fn realify_real_context_numerals(
    ctx: &mut Context,
    term: &FrontendTerm,
    real_ctx: bool,
    let_env: &mut Vec<(String, bool)>,
) -> FrontendTerm {
    match term {
        FrontendTerm::Annotated(inner, _) => {
            realify_real_context_numerals(ctx, inner, real_ctx, let_env)
        }
        FrontendTerm::Const(FrontendConstant::Numeral(n)) if real_ctx => {
            FrontendTerm::Const(FrontendConstant::Decimal(format!("{n}.0")))
        }
        FrontendTerm::App(op, args) => {
            let arg_ctx: Vec<bool> = match op.as_str() {
                "/" => vec![true; args.len()],
                "+" | "-" | "*" => {
                    let real =
                        real_ctx || args.iter().any(|arg| surface_is_real(ctx, arg, let_env));
                    vec![real; args.len()]
                }
                "<" | "<=" | ">" | ">=" | "=" | "distinct" => {
                    let real = args.iter().any(|arg| surface_is_real(ctx, arg, let_env));
                    vec![real; args.len()]
                }
                "ite" if args.len() == 3 => {
                    let real = real_ctx
                        || args[1..]
                            .iter()
                            .any(|arg| surface_is_real(ctx, arg, let_env));
                    vec![false, real, real]
                }
                _ => vec![false; args.len()],
            };
            FrontendTerm::App(
                op.clone(),
                args.iter()
                    .zip(arg_ctx)
                    .map(|(arg, real)| realify_real_context_numerals(ctx, arg, real, let_env))
                    .collect(),
            )
        }
        FrontendTerm::IndexedApp(name, indices, args) => FrontendTerm::IndexedApp(
            name.clone(),
            indices.clone(),
            args.iter()
                .map(|arg| realify_real_context_numerals(ctx, arg, false, let_env))
                .collect(),
        ),
        FrontendTerm::QualifiedApp(identifier, sort, args) => FrontendTerm::QualifiedApp(
            identifier.clone(),
            sort.clone(),
            args.iter()
                .map(|arg| realify_real_context_numerals(ctx, arg, false, let_env))
                .collect(),
        ),
        FrontendTerm::Let(bindings, body) => {
            let mut rebound = Vec::with_capacity(bindings.len());
            let mut entries = Vec::with_capacity(bindings.len());
            for (name, value) in bindings {
                entries.push((name.clone(), surface_is_real(ctx, value, let_env)));
                rebound.push((
                    name.clone(),
                    realify_real_context_numerals(ctx, value, false, let_env),
                ));
            }
            let depth = let_env.len();
            let_env.extend(entries);
            let new_body = realify_real_context_numerals(ctx, body, real_ctx, let_env);
            let_env.truncate(depth);
            FrontendTerm::Let(rebound, Box::new(new_body))
        }
        FrontendTerm::Forall(bindings, body) => {
            FrontendTerm::Forall(bindings.clone(), Box::new(clone_without_annotations(body)))
        }
        FrontendTerm::Exists(bindings, body) => {
            FrontendTerm::Exists(bindings.clone(), Box::new(clone_without_annotations(body)))
        }
        FrontendTerm::Lambda(bindings, body) => {
            FrontendTerm::Lambda(bindings.clone(), Box::new(clone_without_annotations(body)))
        }
        FrontendTerm::Match(scrutinee, cases) => FrontendTerm::Match(
            Box::new(clone_without_annotations(scrutinee)),
            cases
                .iter()
                .map(|(pattern, body)| (pattern.clone(), clone_without_annotations(body)))
                .collect(),
        ),
        FrontendTerm::Const(constant) => FrontendTerm::Const(constant.clone()),
        FrontendTerm::Symbol(symbol) => FrontendTerm::Symbol(symbol.clone()),
        other => other.clone(),
    }
}

fn clone_without_annotations(term: &FrontendTerm) -> FrontendTerm {
    match term {
        FrontendTerm::Annotated(inner, _) => clone_without_annotations(inner),
        FrontendTerm::Const(constant) => FrontendTerm::Const(constant.clone()),
        FrontendTerm::Symbol(symbol) => FrontendTerm::Symbol(symbol.clone()),
        FrontendTerm::App(name, args) => FrontendTerm::App(
            name.clone(),
            args.iter().map(clone_without_annotations).collect(),
        ),
        FrontendTerm::IndexedApp(name, indices, args) => FrontendTerm::IndexedApp(
            name.clone(),
            indices.clone(),
            args.iter().map(clone_without_annotations).collect(),
        ),
        FrontendTerm::QualifiedApp(identifier, sort, args) => FrontendTerm::QualifiedApp(
            identifier.clone(),
            sort.clone(),
            args.iter().map(clone_without_annotations).collect(),
        ),
        FrontendTerm::Let(bindings, body) => FrontendTerm::Let(
            bindings
                .iter()
                .map(|(name, value)| (name.clone(), clone_without_annotations(value)))
                .collect(),
            Box::new(clone_without_annotations(body)),
        ),
        FrontendTerm::Forall(bindings, body) => {
            FrontendTerm::Forall(bindings.clone(), Box::new(clone_without_annotations(body)))
        }
        FrontendTerm::Exists(bindings, body) => {
            FrontendTerm::Exists(bindings.clone(), Box::new(clone_without_annotations(body)))
        }
        FrontendTerm::Lambda(bindings, body) => {
            FrontendTerm::Lambda(bindings.clone(), Box::new(clone_without_annotations(body)))
        }
        FrontendTerm::Match(scrutinee, cases) => FrontendTerm::Match(
            Box::new(clone_without_annotations(scrutinee)),
            cases
                .iter()
                .map(|(pattern, body)| (pattern.clone(), clone_without_annotations(body)))
                .collect(),
        ),
        other => other.clone(),
    }
}

fn surface_is_real(ctx: &mut Context, term: &FrontendTerm, let_env: &[(String, bool)]) -> bool {
    match strip_frontend_annotations(term) {
        FrontendTerm::Symbol(name) => {
            if let Some((_, is_real)) = let_env.iter().rev().find(|(bound, _)| bound == name) {
                return *is_real;
            }
            subterm_is_real_sorted(ctx, term)
        }
        FrontendTerm::App(op, args) => match op.as_str() {
            "/" => true,
            "+" | "-" | "*" | "abs" => args
                .iter()
                .any(|argument| surface_is_real(ctx, argument, let_env)),
            "ite" if args.len() == 3 => args[1..]
                .iter()
                .any(|argument| surface_is_real(ctx, argument, let_env)),
            _ => subterm_is_real_sorted(ctx, term),
        },
        other => subterm_is_real_sorted(ctx, other),
    }
}

#[cfg(test)]
mod tests {
    use ay_frontend::command::Sort as FrontendSort;
    use ay_frontend::SExpr;

    use super::*;

    #[test]
    fn nested_annotation_payload_is_not_cloned_into_the_echo() {
        let parsed = FrontendTerm::Forall(
            vec![("x".to_string(), FrontendSort::Simple("Int".to_string()))],
            Box::new(FrontendTerm::Annotated(
                Box::new(FrontendTerm::Symbol("x".to_string())),
                vec![(
                    ":large".to_string(),
                    SExpr::String("unrendered".repeat(128 * 1024)),
                )],
            )),
        );
        let mut ctx = Context::new();
        let echo = realify_real_context_numerals(&mut ctx, &parsed, false, &mut Vec::new());
        let FrontendTerm::Forall(_, body) = &echo else {
            panic!("quantifier shape must remain visible")
        };
        assert!(matches!(body.as_ref(), FrontendTerm::Symbol(_)));
    }
}
