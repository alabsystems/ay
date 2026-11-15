// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Proof-surface numeral realification without annotation-payload cloning.

use ay_core::term::TermData;
use ay_frontend::command::{
    Constant as FrontendConstant, Sort as FrontendSort, Term as FrontendTerm,
};
use ay_frontend::Context;

use super::{parsed_term_is_binder_free, strip_frontend_annotations};

fn subterm_is_real_sorted(ctx: &mut Context, term: &FrontendTerm) -> bool {
    parsed_term_is_binder_free(term)
        && ctx
            .elaborate_surface_subterm(term)
            .is_some_and(|id| *ctx.terms.sort(id) == ay_core::Sort::Real)
}

/// Which arguments of an application of the DECLARED function `op` sit at a
/// `Real` parameter, read off the application as the elaborator built it
/// (which already resolved overloads and coerced `2` to `2.0` there).
///
/// REGRESSION (measured 2026-10-09, pinned Carcara 1.1.0 git 9a352ee): with
/// `(declare-fun f (Real) Real)`, `(assert (> (f -2) 1.0))` echoed as
/// `(assume t0 (> (f -2) 1.0))`, a hole-free document Carcara refuses ("sort
/// error: expected 'Real', got 'Int'"); `(f 2)` the same on main. It now
/// echoes `(f -2.0)`, as the problem's `(= x -2)` already echoes `-2.0`.
/// Builtin operators keep their own rules above; a macro, which elaborates to
/// its body, or a shape the elaborator rewrote reads as no `Real` parameter.
fn declared_real_parameters(ctx: &mut Context, op: &str, args: &[FrontendTerm]) -> Vec<bool> {
    let mut real = vec![false; args.len()];
    if args.is_empty()
        || ay_frontend::is_builtin_operator_name(op)
        || !args.iter().any(holds_ground_numeral)
    {
        return real;
    }
    let application = FrontendTerm::App(op.to_string(), args.to_vec());
    if !parsed_term_is_binder_free(&application) {
        return real;
    }
    let Some(id) = ctx.elaborate_surface_subterm(&application) else {
        return real;
    };
    let TermData::App(_, elaborated) = ctx.terms.get(id) else {
        return real;
    };
    if elaborated.len() != args.len() {
        return real;
    }
    for (slot, &arg) in real.iter_mut().zip(elaborated.iter()) {
        *slot = *ctx.terms.sort(arg) == ay_core::Sort::Real;
    }
    real
}

/// `true` when `term` holds an integer numeral outside every binder: the only
/// spellings a `Real` parameter context can change.
fn holds_ground_numeral(term: &FrontendTerm) -> bool {
    match term {
        FrontendTerm::Annotated(inner, _) => holds_ground_numeral(inner),
        FrontendTerm::Const(FrontendConstant::Numeral(_)) => true,
        FrontendTerm::App(_, args)
        | FrontendTerm::IndexedApp(_, _, args)
        | FrontendTerm::QualifiedApp(_, _, args) => args.iter().any(holds_ground_numeral),
        _ => false,
    }
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
                _ => declared_real_parameters(ctx, op, args),
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

/// `true` when `term` holds an integer numeral this module never realifies
/// while `Real` arithmetic is in play: a numeral inside a `forall`, `exists`
/// or `lambda` body or a `match` (whose subterms
/// [`realify_real_context_numerals`] copies verbatim), with `real_in_play`
/// set by the caller (the logic or a declared symbol) or a `Real` binder,
/// decimal, `/`, `to_real` or `(as _ Real)` in `term` itself.
///
/// Pinned carcara reads a numeral as `Real` only in a real-only logic's
/// PROBLEM, never in the proof (`interpret_ints_as_reals`), so such an
/// authored spelling, `(forall ((x Real)) (= (+ x 1) x))`, is a sort error
/// at its `assume` ("parser error"). A caller that may decline to print it
/// asks here first. Over-approximate by design: an `Int` numeral in a
/// problem that also involves `Real` reads as `true`.
pub(in crate::executor) fn holds_numeral_beyond_realify(
    term: &FrontendTerm,
    real_in_play: bool,
) -> bool {
    let mut real = real_in_play;
    let mut unreached_numeral = false;
    let mut stack: Vec<(&FrontendTerm, bool)> = vec![(term, false)];
    while let Some((node, under_binder)) = stack.pop() {
        match node {
            FrontendTerm::Annotated(inner, _) => stack.push((inner, under_binder)),
            FrontendTerm::Const(FrontendConstant::Numeral(_)) => {
                unreached_numeral |= under_binder;
            }
            FrontendTerm::Const(FrontendConstant::Decimal(_)) => real = true,
            FrontendTerm::Const(_) | FrontendTerm::Symbol(_) => {}
            FrontendTerm::App(op, args) => {
                real |= matches!(op.as_str(), "/" | "to_real");
                stack.extend(args.iter().map(|arg| (arg, under_binder)));
            }
            FrontendTerm::IndexedApp(_, _, args) => {
                stack.extend(args.iter().map(|arg| (arg, under_binder)));
            }
            FrontendTerm::QualifiedApp(_, sort, args) => {
                real |= frontend_sort_mentions_real(sort);
                stack.extend(args.iter().map(|arg| (arg, under_binder)));
            }
            FrontendTerm::Let(bindings, body) => {
                stack.extend(bindings.iter().map(|(_, value)| (value, under_binder)));
                stack.push((body, under_binder));
            }
            FrontendTerm::Forall(bindings, body)
            | FrontendTerm::Exists(bindings, body)
            | FrontendTerm::Lambda(bindings, body) => {
                real |= bindings
                    .iter()
                    .any(|(_, sort)| frontend_sort_mentions_real(sort));
                stack.push((body, true));
            }
            FrontendTerm::Match(scrutinee, cases) => {
                stack.push((scrutinee, true));
                stack.extend(cases.iter().map(|(_, body)| (body, true)));
            }
            // A term shape this walk does not know: judge it unreached.
            _ => unreached_numeral = true,
        }
    }
    unreached_numeral && real
}

fn frontend_sort_mentions_real(sort: &FrontendSort) -> bool {
    match sort {
        FrontendSort::Simple(name) => name == "Real",
        FrontendSort::Parameterized(_, args) => args.iter().any(frontend_sort_mentions_real),
        FrontendSort::Indexed(..) => false,
        _ => true,
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
    use ay_frontend::SExpr;

    use super::*;

    fn term(text: &str) -> FrontendTerm {
        let sexp = ay_frontend::sexp::parse_sexp(text).expect("test term parses");
        FrontendTerm::from_sexp(&sexp).expect("test term is a term")
    }

    /// The spelling pinned carcara's proof parser refuses: `1` is `Int`
    /// beside the `Real` binder, and the realify lane copies binder bodies
    /// verbatim.
    #[test]
    fn a_numeral_in_a_real_binder_body_is_beyond_realify() {
        for text in [
            "(forall ((x Real)) (= (+ x 1) x))",
            "(forall ((x Real)) (= (+ x 2) (+ x 1)))",
            "(exists ((x Real)) (< x 0))",
            "(! (forall ((x Real)) (< x 0)) :named a)",
            "(forall ((a (Array Int Real))) (= (select a k) 1))",
            "(forall ((x Int)) (< (to_real x) 1))",
            "(forall ((x Int)) (< (/ x 2) 1))",
        ] {
            assert!(holds_numeral_beyond_realify(&term(text), false), "{text}");
        }
    }

    /// The realify lane reaches ground positions, a decimal needs nothing,
    /// and a binder body free of numerals has nothing to realify.
    #[test]
    fn reached_or_numeral_free_terms_are_not_beyond_realify() {
        for text in [
            "(forall ((q Bool)) q)",
            "(forall ((q Bool)) (and q q))",
            "(forall ((x Real)) (= (+ x 1.0) x))",
            "(< (+ c 1) 0)",
            "(and p (forall ((q Bool)) q))",
            "(forall ((x Real)) (< x y))",
        ] {
            assert!(!holds_numeral_beyond_realify(&term(text), true), "{text}");
        }
    }

    /// `Int`-only binders are judged by the caller's `real_in_play`, and
    /// read as beyond realify when `Real` is in play elsewhere (fail-closed).
    #[test]
    fn an_int_binder_numeral_depends_on_real_being_in_play() {
        let int_only = term("(forall ((x Int)) (> x 1))");
        assert!(!holds_numeral_beyond_realify(&int_only, false));
        assert!(holds_numeral_beyond_realify(&int_only, true));
        let bool_over_real = term("(forall ((q Bool)) (or q (< c 1)))");
        assert!(!holds_numeral_beyond_realify(&bool_over_real, false));
        assert!(holds_numeral_beyond_realify(&bool_over_real, true));
    }

    /// A numeral at a declared `Real` parameter is spelled `Real`; one at an
    /// `Int` parameter, or under a builtin with no `Real` operand, is kept.
    #[test]
    fn a_numeral_at_a_declared_real_parameter_is_realified() {
        let mut ctx = Context::new();
        for command in ay_frontend::parse(
            "(set-logic QF_UFLIRA)
             (declare-fun f (Real) Real)
             (declare-fun g (Int Real) Real)
             (declare-fun h (Int) Int)",
        )
        .expect("parse")
        {
            ctx.process_command(&command).expect("declare");
        }
        let echo = realify_real_context_numerals(
            &mut ctx,
            &term("(and (> (f -2) (g 3 4)) (> (h -1) 0) (= (f (+ 1 2)) 1.5))"),
            false,
            &mut Vec::new(),
        );
        assert_eq!(
            echo,
            term("(and (> (f -2.0) (g 3 4.0)) (> (h -1) 0) (= (f (+ 1.0 2.0)) 1.5))")
        );
    }

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
