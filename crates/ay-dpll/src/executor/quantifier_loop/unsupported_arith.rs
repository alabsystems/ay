// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Bounded recognition of arithmetic that CEGQI cannot refine reliably.

use ay_core::kani_compat::DetHashSet as HashSet;
use ay_core::{Sort, TermData, TermId, TermStore};

use crate::cegqi::CegqiInstantiator;

pub(super) fn unsupported_arith_mentions_ce_var(
    terms: &TermStore,
    roots: &[TermId],
    cegqi_state: &[(TermId, CegqiInstantiator)],
) -> bool {
    unsupported_arith_mentions_ce_var_in_mode(
        terms,
        roots,
        cegqi_state,
        UnsupportedArithmeticMode::Any,
    )
}

/// Whether a symbolic (or literal-zero) integer div/mod/rem operation depends
/// on a CEGQI counterexample variable.
///
/// Unlike [`unsupported_arith_mentions_ce_var`], this deliberately ignores
/// nonlinear multiplication and real division. The pre-dispatch liveness gate
/// uses this narrower predicate after logic detection has widened a source LIA
/// problem to NIA: unrelated ground div/mod must not make an otherwise supported
/// nonlinear CEGQI obligation fail closed.
pub(in crate::executor) fn unsupported_int_div_mod_mentions_ce_var(
    terms: &TermStore,
    roots: &[TermId],
    cegqi_state: &[(TermId, CegqiInstantiator)],
) -> bool {
    unsupported_arith_mentions_ce_var_in_mode(
        terms,
        roots,
        cegqi_state,
        UnsupportedArithmeticMode::IntDivMod,
    )
}

#[derive(Clone, Copy)]
enum UnsupportedArithmeticMode {
    Any,
    IntDivMod,
}

fn unsupported_arith_mentions_ce_var_in_mode(
    terms: &TermStore,
    roots: &[TermId],
    cegqi_state: &[(TermId, CegqiInstantiator)],
    mode: UnsupportedArithmeticMode,
) -> bool {
    let ce_vars: HashSet<TermId> = cegqi_state
        .iter()
        .flat_map(|(_, inst)| inst.ce_variables().values().copied())
        .collect();
    if ce_vars.is_empty() {
        return false;
    }

    let mut visited = HashSet::default();
    roots
        .iter()
        .any(|&root| unsupported_arith_mentions_any(terms, root, &ce_vars, &mut visited, mode))
}

fn unsupported_arith_mentions_any(
    terms: &TermStore,
    term: TermId,
    ce_vars: &HashSet<TermId>,
    visited: &mut HashSet<TermId>,
    mode: UnsupportedArithmeticMode,
) -> bool {
    if !visited.insert(term) {
        return false;
    }

    match terms.get(term) {
        TermData::App(sym, args) => {
            let name = sym.name();
            let unsupported_int_div_mod =
                if matches!(name, "div" | "mod" | "rem") && matches!(terms.sort(term), Sort::Int) {
                    // Nonzero constant divisors are eliminated exactly. Symbolic
                    // or literal-zero divisors keep the fail-closed bail because
                    // their case-split auxiliaries prevent CEGQI convergence.
                    let nonzero_constant_divisor = args.len() == 2
                        && terms
                            .extract_integer_constant(args[1])
                            .is_some_and(|c| !num_traits::Zero::is_zero(&c));
                    !nonzero_constant_divisor
                        && args
                            .iter()
                            .any(|&arg| term_mentions_any(terms, arg, ce_vars))
                } else {
                    false
                };
            let unsupported_here = unsupported_int_div_mod
                || (matches!(mode, UnsupportedArithmeticMode::Any)
                    && if name == "*" && args.len() >= 2 {
                        let non_const_count = args
                            .iter()
                            .filter(|&&arg| !matches!(terms.get(arg), TermData::Const(_)))
                            .count();
                        non_const_count >= 2
                            && args
                                .iter()
                                .any(|&arg| term_mentions_any(terms, arg, ce_vars))
                    } else if name == "/" && args.len() >= 2 {
                        !matches!(terms.get(args[1]), TermData::Const(_))
                            && args
                                .iter()
                                .any(|&arg| term_mentions_any(terms, arg, ce_vars))
                    } else {
                        false
                    });
            unsupported_here
                || args
                    .iter()
                    .any(|&arg| unsupported_arith_mentions_any(terms, arg, ce_vars, visited, mode))
        }
        TermData::Not(inner) => {
            unsupported_arith_mentions_any(terms, *inner, ce_vars, visited, mode)
        }
        TermData::Ite(cond, then_term, else_term) => {
            unsupported_arith_mentions_any(terms, *cond, ce_vars, visited, mode)
                || unsupported_arith_mentions_any(terms, *then_term, ce_vars, visited, mode)
                || unsupported_arith_mentions_any(terms, *else_term, ce_vars, visited, mode)
        }
        TermData::Let(bindings, body) => {
            bindings.iter().any(|(_, value)| {
                unsupported_arith_mentions_any(terms, *value, ce_vars, visited, mode)
            }) || unsupported_arith_mentions_any(terms, *body, ce_vars, visited, mode)
        }
        TermData::Forall(_, body, _) | TermData::Exists(_, body, _) => {
            unsupported_arith_mentions_any(terms, *body, ce_vars, visited, mode)
        }
        TermData::Const(_) | TermData::Var(_, _) => false,
        _ => false,
    }
}

pub(super) fn term_mentions_any(
    terms: &TermStore,
    root: TermId,
    targets: &HashSet<TermId>,
) -> bool {
    let mut visited = HashSet::default();
    let mut stack = vec![root];
    while let Some(term) = stack.pop() {
        if !visited.insert(term) {
            continue;
        }
        if targets.contains(&term) {
            return true;
        }
        match terms.get(term) {
            TermData::App(_, args) => stack.extend(args.iter().copied()),
            TermData::Not(inner) => stack.push(*inner),
            TermData::Ite(cond, then_term, else_term) => {
                stack.push(*cond);
                stack.push(*then_term);
                stack.push(*else_term);
            }
            TermData::Let(bindings, body) => {
                for (_, value) in bindings {
                    stack.push(*value);
                }
                stack.push(*body);
            }
            TermData::Forall(_, body, _) | TermData::Exists(_, body, _) => stack.push(*body),
            TermData::Const(_) | TermData::Var(_, _) => {}
            _ => {}
        }
    }
    false
}
