// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Capture-safe quantified surface substitution and binder reconstruction.

use super::*;

pub(super) fn surface_subst_ground(
    term: &FrontendTerm,
    subst: &HashMap<String, FrontendTerm>,
) -> Option<FrontendTerm> {
    match term {
        FrontendTerm::Annotated(inner, _) => surface_subst_ground(inner, subst),
        FrontendTerm::Const(_) => Some(term.clone()),
        FrontendTerm::Symbol(name) => {
            Some(subst.get(name).cloned().unwrap_or_else(|| term.clone()))
        }
        FrontendTerm::App(head, args) => {
            let new_args = args
                .iter()
                .map(|a| surface_subst_ground(a, subst))
                .collect::<Option<Vec<_>>>()?;
            Some(FrontendTerm::App(head.clone(), new_args))
        }
        FrontendTerm::IndexedApp(name, indices, args) => {
            let new_args = args
                .iter()
                .map(|a| surface_subst_ground(a, subst))
                .collect::<Option<Vec<_>>>()?;
            Some(FrontendTerm::IndexedApp(
                name.clone(),
                indices.clone(),
                new_args,
            ))
        }
        FrontendTerm::QualifiedApp(name, sort, args) => {
            let new_args = args
                .iter()
                .map(|a| surface_subst_ground(a, subst))
                .collect::<Option<Vec<_>>>()?;
            Some(FrontendTerm::QualifiedApp(
                name.clone(),
                sort.clone(),
                new_args,
            ))
        }
        _ => None,
    }
}

/// Reconstruct a raw quantified body from its raw ground surface instance.
///
/// `surface_subst_ground` records exactly where each binder was replaced.
/// Walking the original and substituted surface trees alongside the raw
/// ground term lets us reverse only those binder-origin positions.  Equal
/// ground constants elsewhere are untouched, avoiding the unsound global
/// `value -> variable` reverse substitution.  Only binder-free QF body shapes
/// supported by `raw_intern_surface` are admitted; every mismatch fails closed.
pub(super) fn lift_surface_binders_from_ground(
    terms: &mut ay_core::TermStore,
    source: &FrontendTerm,
    substituted: &FrontendTerm,
    ground: TermId,
    bound_vars: &HashMap<String, TermId>,
) -> Option<TermId> {
    if let FrontendTerm::Annotated(inner, _) = source {
        return lift_surface_binders_from_ground(terms, inner, substituted, ground, bound_vars);
    }
    if let FrontendTerm::Annotated(inner, _) = substituted {
        return lift_surface_binders_from_ground(terms, source, inner, ground, bound_vars);
    }
    match (source, substituted) {
        (FrontendTerm::Symbol(name), _) if bound_vars.contains_key(name) => {
            bound_vars.get(name).copied()
        }
        (FrontendTerm::Symbol(source_name), FrontendTerm::Symbol(substituted_name))
            if source_name == substituted_name =>
        {
            Some(ground)
        }
        (FrontendTerm::Const(source_const), FrontendTerm::Const(substituted_const))
            if source_const == substituted_const =>
        {
            Some(ground)
        }
        (
            FrontendTerm::App(source_head, source_args),
            FrontendTerm::App(substituted_head, substituted_args),
        ) if source_head == substituted_head && source_args.len() == substituted_args.len() => {
            // `ground` was built by `raw_intern_surface` and authenticated
            // byte-exactly by `build_raw_ematching_forall_source` before this
            // reverse lift. Preserve its exact core symbol: a declaration whose
            // legal surface spelling collides with a builtin deliberately has a
            // private identity, and rebuilding from `source_head` would silently
            // turn that UF back into the builtin during proof repair.
            let (ground_symbol, ground_args): (Option<Symbol>, Vec<TermId>) =
                match terms.get(ground) {
                    TermData::Not(inner) if source_head == "not" && source_args.len() == 1 => {
                        (None, vec![*inner])
                    }
                    TermData::Ite(cond, then_term, else_term)
                        if source_head == "ite" && source_args.len() == 3 =>
                    {
                        (None, vec![*cond, *then_term, *else_term])
                    }
                    TermData::App(symbol, args) if source_head != "not" && source_head != "ite" => {
                        (Some(symbol.clone()), args.clone())
                    }
                    _ => return None,
                };
            if ground_args.len() != source_args.len() {
                return None;
            }
            let rebuilt = source_args
                .iter()
                .zip(substituted_args)
                .zip(ground_args)
                .map(|((source_arg, substituted_arg), ground_arg)| {
                    lift_surface_binders_from_ground(
                        terms,
                        source_arg,
                        substituted_arg,
                        ground_arg,
                        bound_vars,
                    )
                })
                .collect::<Option<Vec<_>>>()?;
            if source_head == "not" {
                return Some(terms.mk_not_raw(rebuilt[0]));
            }
            if source_head == "ite" {
                return Some(terms.mk_ite_raw(rebuilt[0], rebuilt[1], rebuilt[2]));
            }
            let sort = terms.sort(ground).clone();
            Some(terms.mk_app(ground_symbol?, rebuilt, sort))
        }
        (
            FrontendTerm::IndexedApp(source_name, source_indices, source_args),
            FrontendTerm::IndexedApp(substituted_name, substituted_indices, substituted_args),
        ) if source_name == substituted_name
            && source_indices == substituted_indices
            && source_args.len() == substituted_args.len() =>
        {
            let TermData::App(symbol, ground_args) = terms.get(ground).clone() else {
                return None;
            };
            if ground_args.len() != source_args.len() {
                return None;
            }
            let rebuilt = source_args
                .iter()
                .zip(substituted_args)
                .zip(ground_args)
                .map(|((source_arg, substituted_arg), ground_arg)| {
                    lift_surface_binders_from_ground(
                        terms,
                        source_arg,
                        substituted_arg,
                        ground_arg,
                        bound_vars,
                    )
                })
                .collect::<Option<Vec<_>>>()?;
            let sort = terms.sort(ground).clone();
            Some(terms.mk_app(symbol, rebuilt, sort))
        }
        (
            FrontendTerm::QualifiedApp(source_name, source_sort, source_args),
            FrontendTerm::QualifiedApp(substituted_name, substituted_sort, substituted_args),
        ) if source_name == substituted_name
            && source_sort == substituted_sort
            && source_args.len() == substituted_args.len() =>
        {
            let TermData::App(symbol, ground_args) = terms.get(ground).clone() else {
                return None;
            };
            if ground_args.len() != source_args.len() {
                return None;
            }
            let rebuilt = source_args
                .iter()
                .zip(substituted_args)
                .zip(ground_args)
                .map(|((source_arg, substituted_arg), ground_arg)| {
                    lift_surface_binders_from_ground(
                        terms,
                        source_arg,
                        substituted_arg,
                        ground_arg,
                        bound_vars,
                    )
                })
                .collect::<Option<Vec<_>>>()?;
            let sort = terms.sort(ground).clone();
            Some(terms.mk_app(symbol, rebuilt, sort))
        }
        _ => None,
    }
}

/// Check one simultaneous substitution without rebuilding through AY's
/// simplifying constructors.  This deliberately mirrors the structural
/// contract of the strict `forall_inst` checker: a raw surface comparison
/// such as `(> (f x) 0)` must remain `>` after substituting `x`, rather than
/// being canonicalized to `(< 0 (f x))` by the ordinary term builders.
pub(super) fn raw_instance_matches_substitution(
    terms: &ay_core::TermStore,
    pattern: TermId,
    instance: TermId,
    substitutions: &HashMap<String, TermId>,
) -> bool {
    let mut visited = HashSet::default();
    let mut stack = vec![(pattern, instance)];
    let mut work = 0usize;
    while let Some((expected, actual)) = stack.pop() {
        if !visited.insert((expected, actual)) {
            continue;
        }
        work = work.saturating_add(1);
        if work > 100_000 || terms.sort(expected) != terms.sort(actual) {
            return false;
        }
        match terms.get(expected) {
            TermData::Var(name, _) => {
                if let Some(&replacement) = substitutions.get(name) {
                    if actual != replacement {
                        return false;
                    }
                } else if expected != actual {
                    return false;
                }
            }
            TermData::Const(..) => {
                if expected != actual {
                    return false;
                }
            }
            TermData::Not(inner) => {
                let TermData::Not(actual_inner) = terms.get(actual) else {
                    return false;
                };
                stack.push((*inner, *actual_inner));
            }
            TermData::Ite(condition, then_branch, else_branch) => {
                let TermData::Ite(actual_condition, actual_then, actual_else) = terms.get(actual)
                else {
                    return false;
                };
                stack.extend([
                    (*condition, *actual_condition),
                    (*then_branch, *actual_then),
                    (*else_branch, *actual_else),
                ]);
            }
            TermData::App(symbol, args) => {
                let TermData::App(actual_symbol, actual_args) = terms.get(actual) else {
                    return false;
                };
                if symbol != actual_symbol || args.len() != actual_args.len() {
                    return false;
                }
                stack.extend(args.iter().copied().zip(actual_args.iter().copied()));
            }
            TermData::Let(..) | TermData::Forall(..) | TermData::Exists(..) => return false,
            _ => return false,
        }
    }
    true
}

/// Surface spelling of a ground binder value (Int and Bool only — the
/// finite-domain sorts whose derivations are validated end-to-end).
/// Negative integers spell as `(- k)`, the SMT-LIB surface form.
pub(super) fn value_to_surface(terms: &ay_core::TermStore, value: TermId) -> Option<FrontendTerm> {
    use ay_frontend::command::Constant as SurfaceConstant;
    match terms.get(value) {
        TermData::Const(ay_core::term::Constant::Bool(b)) => Some(FrontendTerm::Const(if *b {
            SurfaceConstant::True
        } else {
            SurfaceConstant::False
        })),
        TermData::Const(ay_core::term::Constant::Int(n)) => {
            if n.sign() == num_bigint::Sign::Minus {
                Some(FrontendTerm::App(
                    "-".to_string(),
                    vec![FrontendTerm::Const(SurfaceConstant::Numeral(
                        (-n).to_string(),
                    ))],
                ))
            } else {
                Some(FrontendTerm::Const(SurfaceConstant::Numeral(n.to_string())))
            }
        }
        _ => None,
    }
}
