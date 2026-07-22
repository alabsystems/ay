// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Surface-syntax preservation helpers for Alethe proof export.

// #8529: Use deterministic hash maps in all builds.
use ay_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};
use ay_core::term::TermData;
use ay_core::{quote_symbol, TermId};
use ay_frontend::command::{
    Constant as FrontendConstant, MatchPattern as FrontendMatchPattern, Sort as FrontendSort,
    Term as FrontendTerm,
};
use ay_frontend::Context;

pub(super) fn strip_frontend_annotations(term: &FrontendTerm) -> &FrontendTerm {
    match term {
        FrontendTerm::Annotated(inner, _) => strip_frontend_annotations(inner),
        other => other,
    }
}

pub(super) fn collect_surface_term_overrides(
    ctx: &mut Context,
    canonical: TermId,
    parsed: &FrontendTerm,
    overrides: &mut HashMap<TermId, String>,
) {
    let parsed = strip_frontend_annotations(parsed);
    let echo = realify_real_context_numerals(ctx, parsed, false);
    overrides.insert(canonical, format_frontend_term(&echo));

    if let (FrontendTerm::App(op, args), TermData::Not(inner)) = (parsed, ctx.terms.get(canonical))
    {
        if op == "not" && args.len() == 1 {
            let inner = *inner;
            collect_surface_term_overrides(ctx, inner, &args[0], overrides);
            return;
        }
    }

    // Certified `sko_forall` export must use one surface identity for the
    // quantified body, its Hilbert-choice predicate, and the instantiated
    // body.  The generic collector intentionally skips open subterms, but here
    // the already-elaborated binder gives us the exact local environment, so
    // descending is deterministic and does not create a fresh quantifier.
    if let (
        FrontendTerm::Forall(parsed_bindings, parsed_body),
        TermData::Forall(canonical_bindings, canonical_body, _),
    ) = (parsed, ctx.terms.get(canonical).clone())
    {
        if parsed_bindings.len() == canonical_bindings.len() {
            let mut env = Vec::with_capacity(parsed_bindings.len());
            let mut recovered_all_bindings = true;
            for ((surface_name, _), (canonical_name, canonical_sort)) in
                parsed_bindings.iter().zip(&canonical_bindings)
            {
                let Some(canonical_var) =
                    find_bound_var(ctx, canonical_body, canonical_name, canonical_sort)
                else {
                    recovered_all_bindings = false;
                    break;
                };
                env.push((surface_name.clone(), canonical_var));
            }
            // A provenance-preserving preprocessing pass may have rewritten
            // the canonical body while retaining this authored quantifier as
            // its source (integer `<` normalization is the boundary case).
            // The whole bodies then need not have the same TermId. Descend
            // anyway: each individual surface subterm is re-elaborated under
            // the exact recovered binder and is attached only to its own
            // hash-consed TermId. The printer subsequently accepts a mapping
            // only through exact Boolean-complement structure in the checked
            // proof.
            if recovered_all_bindings {
                collect_bound_surface_overrides(ctx, parsed_body, &env, overrides);
            }
        }
        return;
    }

    collect_subterm_surface_overrides(ctx, parsed, overrides);
}

/// Recover the exact fresh variable identity used by an elaborated binder.
///
/// Quantifier variables are deliberately not entered in `TermStore`'s global
/// name table, so `mk_var(canonical_name, ..)` would create a distinct Var
/// with the same printed name. Search the already-elaborated body instead and
/// fail closed if preprocessing somehow left two identities ambiguous.
fn find_bound_var(
    ctx: &Context,
    body: TermId,
    canonical_name: &str,
    canonical_sort: &ay_core::Sort,
) -> Option<TermId> {
    let mut stack = vec![body];
    let mut visited = HashSet::default();
    let mut found = None;
    while let Some(term) = stack.pop() {
        if !visited.insert(term) {
            continue;
        }
        if matches!(ctx.terms.get(term), TermData::Var(name, _) if name == canonical_name)
            && ctx.terms.sort(term) == canonical_sort
        {
            if found.is_some_and(|prior| prior != term) {
                return None;
            }
            found = Some(term);
        }
        stack.extend(ctx.terms.children(term));
    }
    found
}

/// Collect exact surface spellings below an already-elaborated binder.
///
/// Unlike the closed-term collector, every node is re-elaborated with the
/// caller-provided local environment.  This is restricted to the body of a
/// binder whose canonical `TermId` was already matched above, so a failure at
/// any child is simply skipped and can never authorize a proof step.
fn collect_bound_surface_overrides(
    ctx: &mut Context,
    parsed: &FrontendTerm,
    env: &[(String, TermId)],
    overrides: &mut HashMap<TermId, String>,
) {
    let parsed = strip_frontend_annotations(parsed);
    if let Some(canonical) = ctx.elaborate_surface_subterm_with_bindings(parsed, env) {
        let echo = realify_real_context_numerals(ctx, parsed, false);
        overrides
            .entry(canonical)
            .or_insert_with(|| format_frontend_term(&echo));
    }
    match parsed {
        FrontendTerm::App(_, args)
        | FrontendTerm::IndexedApp(_, _, args)
        | FrontendTerm::QualifiedApp(_, _, args) => {
            for arg in args {
                collect_bound_surface_overrides(ctx, arg, env, overrides);
            }
        }
        // The certified Skolem lane rejects nested binders/lets.  Do not try
        // to approximate their shadowing here; the strict checker fails them
        // closed before printing.
        FrontendTerm::Const(_) | FrontendTerm::Symbol(_) => {}
        _ => {}
    }
}

/// Connectives whose surface subterms are safe to re-elaborate for override
/// collection: pure logical structure with no fresh-variable or
/// side-constraint elaboration paths.
fn is_override_descent_connective(op: &str) -> bool {
    matches!(
        op,
        "not" | "and" | "or" | "=>" | "implies" | "xor" | "=" | "distinct" | "ite"
    )
}

/// `true` when the parsed term contains no binding construct, so it is closed
/// at the top level and re-elaborates (deterministically, via hash-consing)
/// to the exact canonical `TermId` it produced when originally asserted.
fn parsed_term_is_binder_free(term: &FrontendTerm) -> bool {
    let mut stack: Vec<&FrontendTerm> = vec![term];
    while let Some(t) = stack.pop() {
        match strip_frontend_annotations(t) {
            FrontendTerm::Const(_) | FrontendTerm::Symbol(_) => {}
            FrontendTerm::App(_, args)
            | FrontendTerm::IndexedApp(_, _, args)
            | FrontendTerm::QualifiedApp(_, _, args) => stack.extend(args.iter()),
            _ => return false,
        }
    }
    true
}

/// Recurse through pure connective structure, mapping each composite surface
/// subterm back to its canonical `TermId` (by re-elaboration — exact even
/// when canonicalization reordered or desugared it, e.g. `(=> a b)` stored as
/// `(or (not a) b)`, or commutative-argument sorting) and recording its
/// surface rendering. This keeps nested occurrences of an assertion's
/// subterms printing with the problem file's own syntax, so steps like
/// `equiv_pos2` over `(= c (=> a b))` print the implication — not the
/// internal or-term — and stay consistent with the `assume` of the source
/// assertion.
///
/// Child overrides never overwrite an existing entry: the first surface
/// spelling encountered stays authoritative, and the top-level assertion
/// override (inserted unconditionally above) keeps its original precedence.
fn collect_subterm_surface_overrides(
    ctx: &mut Context,
    parsed: &FrontendTerm,
    overrides: &mut HashMap<TermId, String>,
) {
    let FrontendTerm::App(op, args) = parsed else {
        return;
    };
    if !is_override_descent_connective(op) {
        return;
    }
    for arg in args {
        let arg = strip_frontend_annotations(arg);
        // Only composite subterms can print differently from their surface
        // form; symbols and constants already render identically.
        if !matches!(arg, FrontendTerm::App(..)) {
            continue;
        }
        if !parsed_term_is_binder_free(arg) {
            continue;
        }
        let Some(child) = ctx.elaborate_surface_subterm(arg) else {
            continue;
        };
        if !overrides.contains_key(&child) {
            let echo = realify_real_context_numerals(ctx, arg, false);
            overrides.insert(child, format_frontend_term(&echo));
        }
        collect_subterm_surface_overrides(ctx, arg, overrides);
    }
}

/// Deep override collection for the trust-surgery ite-lift: unlike the
/// connective-only descent above, this walks through arithmetic operators,
/// comparisons, and `ite` so that TERM-level subterms of an atomic assertion
/// (the lifted `(ite c u v)` and its condition) also print with the problem
/// file's syntax. Restricted to pure, side-constraint-free operators —
/// everything here re-elaborates deterministically via hash-consing.
pub(super) fn collect_deep_arith_surface_overrides(
    ctx: &mut Context,
    parsed: &FrontendTerm,
    overrides: &mut HashMap<TermId, String>,
) {
    let FrontendTerm::App(op, args) = strip_frontend_annotations(parsed) else {
        return;
    };
    if !is_override_descent_connective(op)
        && !matches!(op.as_str(), "<" | "<=" | ">" | ">=" | "+" | "-" | "*")
    {
        return;
    }
    for arg in args {
        let arg = strip_frontend_annotations(arg);
        if !matches!(arg, FrontendTerm::App(..)) {
            continue;
        }
        if !parsed_term_is_binder_free(arg) {
            continue;
        }
        if let Some(child) = ctx.elaborate_surface_subterm(arg) {
            if !overrides.contains_key(&child) {
                let echo = realify_real_context_numerals(ctx, arg, false);
                overrides.insert(child, format_frontend_term(&echo));
            }
        }
        collect_deep_arith_surface_overrides(ctx, arg, overrides);
    }
}

/// `true` when the parsed subterm is binder-free and elaborates to a
/// Real-sorted canonical term (elaboration is hash-consed, so this only
/// re-interns terms the assertion already created).
fn subterm_is_real_sorted(ctx: &mut Context, term: &FrontendTerm) -> bool {
    if !parsed_term_is_binder_free(term) {
        return false;
    }
    ctx.elaborate_surface_subterm(term)
        .is_some_and(|id| *ctx.terms.sort(id) == ay_core::Sort::Real)
}

/// Rewrite Int numerals that occur in Real arithmetic positions of a surface
/// term into their decimal spelling (`5` → `5.0`).
///
/// Alethe checkers (Carcara) type a bare numeral leniently — `(>= x 3)` with
/// `x : Real` parses — but type a compound all-numeral application as `Int`
/// and reject it in a Real position: `(/ 5 2)` and `(< x (- 3 1))` both fail
/// with "sort error: expected 'Real', got 'Int'". Since the surface-override
/// echo reproduces the problem file's spelling verbatim, any such assertion
/// used to produce an unparseable proof. This pass realifies exactly the
/// numerals in Real context and leaves everything else — in particular every
/// pure-Int assertion — byte-identical.
///
/// Real context is established by:
/// - `/` (SMT-LIB real division): argument positions are always Real;
/// - `+`, `-`, `*`: Real when inherited from the parent or when any sibling
///   argument elaborates to a Real-sorted term;
/// - comparisons / (dis)equality: Real when any argument elaborates to Real;
/// - `ite`: branch positions inherit / infer Real; the condition never does.
///
/// Terms under binders are left unchanged (their subterms cannot be
/// re-elaborated in the global environment, so no Real context is inferred).
fn realify_real_context_numerals(
    ctx: &mut Context,
    term: &FrontendTerm,
    real_ctx: bool,
) -> FrontendTerm {
    match term {
        FrontendTerm::Annotated(inner, annotations) => FrontendTerm::Annotated(
            Box::new(realify_real_context_numerals(ctx, inner, real_ctx)),
            annotations.clone(),
        ),
        FrontendTerm::Const(FrontendConstant::Numeral(n)) if real_ctx => {
            FrontendTerm::Const(FrontendConstant::Decimal(format!("{n}.0")))
        }
        FrontendTerm::App(op, args) => {
            let arg_ctx: Vec<bool> = match op.as_str() {
                "/" => vec![true; args.len()],
                "+" | "-" | "*" => {
                    let rc = real_ctx || args.iter().any(|a| subterm_is_real_sorted(ctx, a));
                    vec![rc; args.len()]
                }
                "<" | "<=" | ">" | ">=" | "=" | "distinct" => {
                    let rc = args.iter().any(|a| subterm_is_real_sorted(ctx, a));
                    vec![rc; args.len()]
                }
                "ite" if args.len() == 3 => {
                    let rc = real_ctx || args[1..].iter().any(|a| subterm_is_real_sorted(ctx, a));
                    vec![false, rc, rc]
                }
                _ => vec![false; args.len()],
            };
            FrontendTerm::App(
                op.clone(),
                args.iter()
                    .zip(arg_ctx)
                    .map(|(a, rc)| realify_real_context_numerals(ctx, a, rc))
                    .collect(),
            )
        }
        other => other.clone(),
    }
}

pub(super) fn format_frontend_term(term: &FrontendTerm) -> String {
    match strip_frontend_annotations(term) {
        FrontendTerm::Const(c) => format_frontend_constant(c),
        FrontendTerm::Symbol(name) => format_frontend_symbol(name),
        FrontendTerm::App(name, args) => format_frontend_application(name, args),
        FrontendTerm::IndexedApp(name, indices, args) => {
            format_frontend_head_application(&format_indexed_head(name, indices), args)
        }
        FrontendTerm::QualifiedApp(name, sort, args) => {
            format_frontend_head_application(&format_qualified_head(name, sort), args)
        }
        FrontendTerm::Let(bindings, body) => format_frontend_let(bindings, body),
        FrontendTerm::Forall(bindings, body) => {
            format_frontend_quantifier("forall", bindings, body)
        }
        FrontendTerm::Exists(bindings, body) => {
            format_frontend_quantifier("exists", bindings, body)
        }
        FrontendTerm::Lambda(bindings, body) => {
            format_frontend_quantifier("lambda", bindings, body)
        }
        FrontendTerm::Match(scrutinee, cases) => format_frontend_match(scrutinee, cases),
        FrontendTerm::Annotated(_, _) => unreachable!("annotations stripped above"),
        other => unreachable!("unsupported frontend term in proof export override: {other:?}"),
    }
}

fn format_frontend_match(
    scrutinee: &FrontendTerm,
    cases: &[(FrontendMatchPattern, FrontendTerm)],
) -> String {
    let rendered_cases: Vec<String> = cases
        .iter()
        .map(|(pattern, body)| {
            format!(
                "({} {})",
                format_frontend_match_pattern(pattern),
                format_frontend_term(body)
            )
        })
        .collect();
    format!(
        "(match {} ({}))",
        format_frontend_term(scrutinee),
        rendered_cases.join(" ")
    )
}

fn format_frontend_match_pattern(pattern: &FrontendMatchPattern) -> String {
    match pattern {
        FrontendMatchPattern::Symbol(name) => format_frontend_symbol(name),
        FrontendMatchPattern::Constructor(ctor, vars) => {
            let rendered_vars: Vec<String> =
                vars.iter().map(|v| format_frontend_symbol(v)).collect();
            if rendered_vars.is_empty() {
                format!("({})", format_frontend_symbol(ctor))
            } else {
                format!(
                    "({} {})",
                    format_frontend_symbol(ctor),
                    rendered_vars.join(" ")
                )
            }
        }
        other => unreachable!("unsupported frontend match pattern in proof export: {other:?}"),
    }
}

fn format_frontend_application(name: &str, args: &[FrontendTerm]) -> String {
    format_frontend_head_application(&format_frontend_symbol(name), args)
}

fn format_frontend_head_application(head: &str, args: &[FrontendTerm]) -> String {
    if args.is_empty() {
        head.to_string()
    } else {
        let rendered_args: Vec<String> = args.iter().map(format_frontend_term).collect();
        format!("({head} {})", rendered_args.join(" "))
    }
}

fn format_indexed_head(name: &str, indices: &[String]) -> String {
    format!("(_ {} {})", format_frontend_symbol(name), indices.join(" "))
}

fn format_qualified_head(name: &str, sort: &FrontendSort) -> String {
    format!(
        "(as {} {})",
        format_frontend_symbol(name),
        format_frontend_sort(sort)
    )
}

fn format_frontend_let(bindings: &[(String, FrontendTerm)], body: &FrontendTerm) -> String {
    let rendered_bindings: Vec<String> = bindings
        .iter()
        .map(|(name, value)| format!("({} {})", quote_symbol(name), format_frontend_term(value)))
        .collect();
    format!(
        "(let ({}) {})",
        rendered_bindings.join(" "),
        format_frontend_term(body)
    )
}

fn format_frontend_quantifier(
    keyword: &str,
    bindings: &[(String, FrontendSort)],
    body: &FrontendTerm,
) -> String {
    let rendered_bindings: Vec<String> = bindings
        .iter()
        .map(|(name, sort)| format!("({} {})", quote_symbol(name), format_frontend_sort(sort)))
        .collect();
    format!(
        "({keyword} ({}) {})",
        rendered_bindings.join(" "),
        format_frontend_term(body)
    )
}

fn format_frontend_symbol(name: &str) -> String {
    if name.starts_with('(') {
        name.to_string()
    } else {
        quote_symbol(name)
    }
}

fn format_frontend_sort(sort: &FrontendSort) -> String {
    match sort {
        FrontendSort::Simple(name) => format_frontend_symbol(name),
        FrontendSort::Parameterized(name, params) => {
            let rendered_params: Vec<String> = params.iter().map(format_frontend_sort).collect();
            format!(
                "({} {})",
                format_frontend_symbol(name),
                rendered_params.join(" ")
            )
        }
        FrontendSort::Indexed(name, indices) => {
            format!("(_ {} {})", format_frontend_symbol(name), indices.join(" "))
        }
        other => unreachable!("unsupported frontend sort in proof export override: {other:?}"),
    }
}

fn format_frontend_constant(constant: &FrontendConstant) -> String {
    match constant {
        FrontendConstant::True => "true".to_string(),
        FrontendConstant::False => "false".to_string(),
        FrontendConstant::Numeral(n)
        | FrontendConstant::Decimal(n)
        | FrontendConstant::Hexadecimal(n)
        | FrontendConstant::Binary(n) => n.clone(),
        FrontendConstant::String(s) => format!("\"{}\"", s.replace('\"', "\"\"")),
        other => unreachable!("unsupported frontend constant in proof export override: {other:?}"),
    }
}
