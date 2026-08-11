// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Exact validation for a bounded total-order / term-ITE tautology fragment.
//!
//! Numeric leaves are uninterpreted Int or Real variables. Numeric expressions
//! may only be `ite` trees selecting those leaves; Boolean expressions may only
//! compare the resulting values and combine comparisons propositionally.
//! Consequently a formula's truth depends solely on the finite total preorder
//! of its numeric variables. Every total preorder on `n` labelled variables has
//! a representative assignment in `{0, .., n-1}^n`, so exhaustive evaluation
//! of that finite domain is a complete decision procedure for this fragment.
//!
//! This deliberately rejects numeric constants, arithmetic, UFs, Boolean
//! variables, quantifiers, and large inputs. Those need their own certificates;
//! accepting them here would invalidate the finite-preorder argument.

use ay_core::{Constant, ProofId, Sort, Symbol, TermData, TermId, TermStore};

use super::ProofCheckError;

const MAX_ORDER_VARIABLES: usize = 6;
const MAX_REACHABLE_TERMS: usize = 512;
const MAX_EVAL_DEPTH: usize = 128;

/// Return whether `clause` is a tautology in the exact bounded total-order /
/// term-`ite` fragment accepted by `OrderIteTautology` proof steps.
///
/// Every reachable term must belong to the fragment; unsupported content is
/// rejected even when it occurs in a semantically dead `ite` branch.
#[must_use]
pub fn recognize_order_ite_tautology(terms: &TermStore, clause: &[TermId]) -> bool {
    validate_order_ite_tautology(terms, ProofId(0), clause).is_ok()
}

pub(crate) fn validate_order_ite_tautology(
    terms: &TermStore,
    step: ProofId,
    clause: &[TermId],
) -> Result<(), ProofCheckError> {
    let invalid = |reason: String| ProofCheckError::InvalidTheoryLemma {
        step,
        reason: format!("invalid order-ITE tautology: {reason}"),
    };
    if clause.is_empty() {
        return Err(invalid("clause is empty".to_string()));
    }
    if clause
        .iter()
        .any(|&literal| terms.sort(literal) != &Sort::Bool)
    {
        return Err(invalid(
            "every clause literal must have sort Bool".to_string(),
        ));
    }

    let mut seen = Vec::new();
    let mut variables = Vec::new();
    for &literal in clause {
        validate_fragment(terms, literal, 0, &mut seen, &mut variables).map_err(&invalid)?;
    }
    variables.sort_unstable();
    variables.dedup();
    if variables.len() > MAX_ORDER_VARIABLES {
        return Err(invalid(format!(
            "{} numeric variables exceed the {MAX_ORDER_VARIABLES}-variable bound",
            variables.len()
        )));
    }

    let domain = variables.len().max(1);
    let assignment_count = if variables.is_empty() {
        1
    } else {
        domain.pow(variables.len() as u32)
    };
    let mut values = vec![0usize; variables.len()];
    for mut code in 0..assignment_count {
        for value in &mut values {
            *value = code % domain;
            code /= domain;
        }
        let mut cache = EvalCache::default();
        let mut satisfied = false;
        for &literal in clause {
            let value = eval_bool(terms, literal, &variables, &values, &mut cache, 0)
                .ok_or_else(|| invalid("formula is outside the certified fragment".to_string()))?;
            satisfied |= value;
        }
        if !satisfied {
            return Err(invalid(format!(
                "counterexample total-preorder representative {values:?}"
            )));
        }
    }
    Ok(())
}

fn validate_fragment(
    terms: &TermStore,
    term: TermId,
    depth: usize,
    seen: &mut Vec<TermId>,
    variables: &mut Vec<TermId>,
) -> Result<(), String> {
    if depth > MAX_EVAL_DEPTH {
        return Err(format!("term nesting exceeds {MAX_EVAL_DEPTH}"));
    }
    if seen.contains(&term) {
        return Ok(());
    }
    if seen.len() >= MAX_REACHABLE_TERMS {
        return Err(format!(
            "reachable term count exceeds {MAX_REACHABLE_TERMS}"
        ));
    }
    seen.push(term);

    match (terms.sort(term), terms.get(term)) {
        (Sort::Int | Sort::Real, TermData::Var(_, _)) => variables.push(term),
        (sort @ (Sort::Int | Sort::Real), TermData::Ite(condition, then_term, else_term)) => {
            if terms.sort(*condition) != &Sort::Bool
                || terms.sort(*then_term) != sort
                || terms.sort(*else_term) != sort
            {
                return Err("ill-sorted numeric ite".to_string());
            }
            for child in [*condition, *then_term, *else_term] {
                validate_fragment(terms, child, depth + 1, seen, variables)?;
            }
        }
        (Sort::Bool, TermData::Const(Constant::Bool(_))) => {}
        (Sort::Bool, TermData::Not(inner)) => {
            if terms.sort(*inner) != &Sort::Bool {
                return Err("ill-sorted Boolean negation".to_string());
            }
            validate_fragment(terms, *inner, depth + 1, seen, variables)?;
        }
        (Sort::Bool, TermData::Ite(condition, then_term, else_term)) => {
            if [*condition, *then_term, *else_term]
                .iter()
                .any(|&child| terms.sort(child) != &Sort::Bool)
            {
                return Err("ill-sorted Boolean ite".to_string());
            }
            for child in [*condition, *then_term, *else_term] {
                validate_fragment(terms, child, depth + 1, seen, variables)?;
            }
        }
        (Sort::Bool, TermData::App(Symbol::Named(operator), args)) => {
            let valid_shape = match operator.as_str() {
                "and" | "or" => args.iter().all(|&arg| terms.sort(arg) == &Sort::Bool),
                "=>" | "xor" => {
                    args.len() == 2 && args.iter().all(|&arg| terms.sort(arg) == &Sort::Bool)
                }
                "=" => {
                    args.len() == 2
                        && terms.sort(args[0]) == terms.sort(args[1])
                        && matches!(terms.sort(args[0]), Sort::Bool | Sort::Int | Sort::Real)
                }
                "<" | "<=" | ">" | ">=" => {
                    args.len() == 2
                        && terms.sort(args[0]) == terms.sort(args[1])
                        && matches!(terms.sort(args[0]), Sort::Int | Sort::Real)
                }
                _ => false,
            };
            if !valid_shape {
                return Err(format!("unsupported or ill-sorted operator `{operator}`"));
            }
            for &child in args {
                validate_fragment(terms, child, depth + 1, seen, variables)?;
            }
        }
        _ => {
            return Err(format!(
                "term {term:?} is outside the pure total-order / ite fragment"
            ));
        }
    }
    Ok(())
}

#[derive(Default)]
struct EvalCache {
    bool_values: Vec<(TermId, bool)>,
    numeric_values: Vec<(TermId, usize)>,
}

fn eval_numeric(
    terms: &TermStore,
    term: TermId,
    variables: &[TermId],
    values: &[usize],
    cache: &mut EvalCache,
    depth: usize,
) -> Option<usize> {
    if depth > MAX_EVAL_DEPTH || !matches!(terms.sort(term), Sort::Int | Sort::Real) {
        return None;
    }
    if let Some(value) = cache
        .numeric_values
        .iter()
        .find_map(|&(cached, value)| (cached == term).then_some(value))
    {
        return Some(value);
    }
    let result = match terms.get(term) {
        TermData::Var(_, _) => variables
            .iter()
            .position(|&variable| variable == term)
            .map(|index| values[index]),
        TermData::Ite(condition, then_term, else_term) => {
            let branch = if eval_bool(terms, *condition, variables, values, cache, depth + 1)? {
                *then_term
            } else {
                *else_term
            };
            eval_numeric(terms, branch, variables, values, cache, depth + 1)
        }
        _ => None,
    }?;
    cache.numeric_values.push((term, result));
    Some(result)
}

fn eval_bool(
    terms: &TermStore,
    term: TermId,
    variables: &[TermId],
    values: &[usize],
    cache: &mut EvalCache,
    depth: usize,
) -> Option<bool> {
    if depth > MAX_EVAL_DEPTH || terms.sort(term) != &Sort::Bool {
        return None;
    }
    if let Some(value) = cache
        .bool_values
        .iter()
        .find_map(|&(cached, value)| (cached == term).then_some(value))
    {
        return Some(value);
    }
    let result = match terms.get(term) {
        TermData::Const(Constant::Bool(value)) => Some(*value),
        TermData::Not(inner) => Some(!eval_bool(
            terms,
            *inner,
            variables,
            values,
            cache,
            depth + 1,
        )?),
        TermData::Ite(condition, then_term, else_term) => {
            let branch = if eval_bool(terms, *condition, variables, values, cache, depth + 1)? {
                *then_term
            } else {
                *else_term
            };
            eval_bool(terms, branch, variables, values, cache, depth + 1)
        }
        TermData::App(Symbol::Named(operator), args) => match operator.as_str() {
            "and" => args.iter().try_fold(true, |value, &arg| {
                let next = eval_bool(terms, arg, variables, values, cache, depth + 1)?;
                Some(value && next)
            }),
            "or" => args.iter().try_fold(false, |value, &arg| {
                let next = eval_bool(terms, arg, variables, values, cache, depth + 1)?;
                Some(value || next)
            }),
            "=>" if args.len() == 2 => {
                let lhs = eval_bool(terms, args[0], variables, values, cache, depth + 1)?;
                let rhs = eval_bool(terms, args[1], variables, values, cache, depth + 1)?;
                Some(!lhs || rhs)
            }
            "xor" if args.len() == 2 => {
                let lhs = eval_bool(terms, args[0], variables, values, cache, depth + 1)?;
                let rhs = eval_bool(terms, args[1], variables, values, cache, depth + 1)?;
                Some(lhs != rhs)
            }
            "=" if args.len() == 2 && terms.sort(args[0]) == terms.sort(args[1]) => {
                match terms.sort(args[0]) {
                    Sort::Bool => Some(
                        eval_bool(terms, args[0], variables, values, cache, depth + 1)?
                            == eval_bool(terms, args[1], variables, values, cache, depth + 1)?,
                    ),
                    Sort::Int | Sort::Real => Some(
                        eval_numeric(terms, args[0], variables, values, cache, depth + 1)?
                            == eval_numeric(terms, args[1], variables, values, cache, depth + 1)?,
                    ),
                    _ => None,
                }
            }
            "<" | "<=" | ">" | ">="
                if args.len() == 2 && terms.sort(args[0]) == terms.sort(args[1]) =>
            {
                let lhs = eval_numeric(terms, args[0], variables, values, cache, depth + 1)?;
                let rhs = eval_numeric(terms, args[1], variables, values, cache, depth + 1)?;
                Some(match operator.as_str() {
                    "<" => lhs < rhs,
                    "<=" => lhs <= rhs,
                    ">" => lhs > rhs,
                    ">=" => lhs >= rhs,
                    _ => unreachable!(),
                })
            }
            _ => None,
        },
        _ => None,
    }?;
    cache.bool_values.push((term, result));
    Some(result)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn cmp(terms: &mut TermStore, op: &str, lhs: TermId, rhs: TermId) -> TermId {
        terms.mk_app(Symbol::named(op), [lhs, rhs], Sort::Bool)
    }

    fn sorting_network_post(terms: &mut TermStore, a: TermId, b: TermId, c: TermId) -> TermId {
        let a_gt_b = cmp(terms, ">", a, b);
        let a1 = terms.mk_ite_raw(a_gt_b, b, a);
        let b1 = terms.mk_ite_raw(a_gt_b, a, b);
        let b1_gt_c = cmp(terms, ">", b1, c);
        let b2 = terms.mk_ite_raw(b1_gt_c, c, b1);
        let c2 = terms.mk_ite_raw(b1_gt_c, b1, c);
        let a1_gt_b2 = cmp(terms, ">", a1, b2);
        let a3 = terms.mk_ite_raw(a1_gt_b2, b2, a1);
        let b3 = terms.mk_ite_raw(a1_gt_b2, a1, b2);
        let a3_le_b3 = cmp(terms, "<=", a3, b3);
        let b3_le_c2 = cmp(terms, "<=", b3, c2);
        let a3_le_c2 = cmp(terms, "<=", a3, c2);
        terms.mk_app(
            Symbol::named("and"),
            [a3_le_b3, b3_le_c2, a3_le_c2],
            Sort::Bool,
        )
    }

    #[test]
    fn accepts_three_input_sorting_network() {
        let mut terms = TermStore::new();
        let a = terms.mk_var("a", Sort::Int);
        let b = terms.mk_var("b", Sort::Int);
        let c = terms.mk_var("c", Sort::Int);
        let post = sorting_network_post(&mut terms, a, b, c);
        validate_order_ite_tautology(&terms, ProofId(0), &[post])
            .expect("the three-comparator network sorts every total preorder");
    }

    #[test]
    fn rejects_non_tautology_and_unsupported_arithmetic() {
        let mut terms = TermStore::new();
        let a = terms.mk_var("a", Sort::Int);
        let b = terms.mk_var("b", Sort::Int);
        let a_le_b = cmp(&mut terms, "<=", a, b);
        assert!(validate_order_ite_tautology(&terms, ProofId(0), &[a_le_b]).is_err());

        let sum = terms.mk_app(Symbol::named("+"), [a, b], Sort::Int);
        let self_eq = terms.mk_app(Symbol::named("="), [sum, sum], Sort::Bool);
        assert!(
            validate_order_ite_tautology(&terms, ProofId(0), &[self_eq]).is_err(),
            "even a true arithmetic formula is outside this proof lane"
        );
    }

    #[test]
    fn rejects_boolean_atoms_and_oversized_variable_sets() {
        let mut terms = TermStore::new();
        let p = terms.mk_var("p", Sort::Bool);
        let not_p = terms.mk_not_raw(p);
        let excluded_middle = terms.mk_app(Symbol::named("or"), [p, not_p], Sort::Bool);
        assert!(
            validate_order_ite_tautology(&terms, ProofId(0), &[excluded_middle]).is_err(),
            "Boolean atoms need the ordinary BoolTautology checker"
        );

        let vars: Vec<TermId> = (0..=MAX_ORDER_VARIABLES)
            .map(|index| terms.mk_var(format!("x{index}"), Sort::Int))
            .collect();
        let equalities: Vec<TermId> = vars
            .iter()
            .map(|&variable| terms.mk_app(Symbol::named("="), [variable, variable], Sort::Bool))
            .collect();
        let conjunction = terms.mk_app(Symbol::named("and"), equalities, Sort::Bool);
        assert!(validate_order_ite_tautology(&terms, ProofId(0), &[conjunction]).is_err());
    }

    #[test]
    fn rejects_unsupported_content_in_dead_ite_branch() {
        let mut terms = TermStore::new();
        let true_term = terms.mk_bool(true);
        let a = terms.mk_var("a", Sort::Int);
        let b = terms.mk_var("b", Sort::Int);
        let sum = terms.mk_app(Symbol::named("+"), [a, b], Sort::Int);
        let selected = terms.mk_ite_raw(true_term, a, sum);
        let equality = terms.mk_app(Symbol::named("="), [selected, a], Sort::Bool);
        assert!(
            validate_order_ite_tautology(&terms, ProofId(0), &[equality]).is_err(),
            "unsupported terms must not hide in a semantically dead branch"
        );
    }
}
