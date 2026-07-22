// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Model-completion certificates for restored skipped quantifiers.
//!
//! This module is deliberately narrow.  It recognizes QuantifierConsumer's opaque sequence
//! library axioms over `(Seq Int)`, whose skipped universal constraints can be
//! satisfied by extending the interpretation of the sequence helper functions
//! (`seq_len`, `seq_concat`, `seq_get`, etc.) to list semantics after all ground
//! assertions have already been validated.

use ay_core::{Constant, Sort, TermData, TermId, TermStore};
use num_traits::Zero;

/// Return true when every quantified assertion in `assertions` is one of the
/// QuantifierConsumer `(Seq Int)` helper axioms for which a total list-model extension is
/// known to exist.
pub(super) fn skipped_quantifiers_have_quantifier_consumer_seq_model_completion(
    terms: &TermStore,
    assertions: &[TermId],
) -> bool {
    let mut quantifiers = Vec::new();
    for &assertion in assertions {
        collect_quantifiers(terms, assertion, &mut quantifiers);
    }

    !quantifiers.is_empty()
        && quantifiers
            .into_iter()
            .all(|q| is_quantifier_consumer_seq_model_completion_quantifier(terms, q))
}

/// Return true when `term` is one of QuantifierConsumer's opaque sequence axioms.
pub(super) fn is_quantifier_consumer_seq_model_completion_quantifier(
    terms: &TermStore,
    term: TermId,
) -> bool {
    let TermData::Forall(vars, body, triggers) = terms.get(term) else {
        return false;
    };

    matches_select_bridge(terms, vars, *body, triggers)
        || matches_len_nonnegative(terms, vars, *body, triggers)
        || matches_get_in_bounds(terms, vars, *body, triggers)
        || matches_get_out_of_bounds(terms, vars, *body, triggers)
        || matches_contains_empty(terms, vars, *body, triggers)
        || matches_contains_push_back(terms, vars, *body, triggers)
        || matches_concat_len(terms, vars, *body, triggers)
        || matches_concat_left_index(terms, vars, *body, triggers)
        || matches_concat_right_index(terms, vars, *body, triggers)
        || matches_concat_assoc(terms, vars, *body, triggers)
        || matches_concat_left_identity(terms, vars, *body, triggers)
        || matches_concat_right_identity(terms, vars, *body, triggers)
        || matches_push_front_definition(terms, vars, *body, triggers)
        || matches_push_back_definition(terms, vars, *body, triggers)
}

fn collect_quantifiers(terms: &TermStore, term: TermId, out: &mut Vec<TermId>) {
    match terms.get(term) {
        TermData::Forall(..) | TermData::Exists(..) => out.push(term),
        TermData::App(_, args) => {
            for &arg in args {
                collect_quantifiers(terms, arg, out);
            }
        }
        TermData::Not(inner) => collect_quantifiers(terms, *inner, out),
        TermData::Ite(c, a, b) => {
            collect_quantifiers(terms, *c, out);
            collect_quantifiers(terms, *a, out);
            collect_quantifiers(terms, *b, out);
        }
        TermData::Let(bindings, body) => {
            for (_, value) in bindings {
                collect_quantifiers(terms, *value, out);
            }
            collect_quantifiers(terms, *body, out);
        }
        TermData::Const(_) | TermData::Var(_, _) => {}
        _ => {}
    }
}

fn matches_select_bridge(
    terms: &TermStore,
    vars: &[(String, Sort)],
    body: TermId,
    triggers: &[Vec<TermId>],
) -> bool {
    let Some((s, i)) = seq_int_var_pair(vars) else {
        return false;
    };
    trigger_tops_allowed(terms, triggers, &["seq_index_logic"])
        && is_eq_between(
            terms,
            body,
            |t| is_select_seq_array_at_offset_plus(terms, t, s, i),
            |t| is_seq_index_logic(terms, t, s, i),
        )
}

fn matches_len_nonnegative(
    terms: &TermStore,
    vars: &[(String, Sort)],
    body: TermId,
    triggers: &[Vec<TermId>],
) -> bool {
    let Some(s) = single_seq_int_var(vars) else {
        return false;
    };
    trigger_tops_allowed(terms, triggers, &["seq_len"])
        && app_args(terms, body, "<=", 2)
            .is_some_and(|args| is_zero_int(terms, args[0]) && is_seq_len(terms, args[1], s))
}

fn matches_get_in_bounds(
    terms: &TermStore,
    vars: &[(String, Sort)],
    body: TermId,
    triggers: &[Vec<TermId>],
) -> bool {
    let Some((s, i)) = seq_int_var_pair(vars) else {
        return false;
    };
    let Some(args) = app_args(terms, body, "or", 3) else {
        return false;
    };
    trigger_tops_allowed(terms, triggers, &["seq_get"])
        && args.iter().any(|&arg| {
            is_eq_between(
                terms,
                arg,
                |t| is_seq_get(terms, t, s, i),
                |t| {
                    app_args(terms, t, "logic_Some", 1)
                        .is_some_and(|some_args| is_seq_index_logic(terms, some_args[0], s, i))
                },
            )
        })
        && args.iter().any(|&arg| is_not_le_zero_var(terms, arg, i))
        && args
            .iter()
            .any(|&arg| is_not_lt_var_seq_len(terms, arg, i, s))
}

fn matches_get_out_of_bounds(
    terms: &TermStore,
    vars: &[(String, Sort)],
    body: TermId,
    triggers: &[Vec<TermId>],
) -> bool {
    let Some((s, i)) = seq_int_var_pair(vars) else {
        return false;
    };
    let Some(args) = app_args(terms, body, "or", 2) else {
        return false;
    };
    trigger_tops_allowed(terms, triggers, &["seq_get"])
        && args.iter().any(|&arg| {
            is_eq_between(
                terms,
                arg,
                |t| is_seq_get(terms, t, s, i),
                |t| is_logic_none(terms, t),
            )
        })
        && args.iter().any(|&arg| {
            app_args(terms, arg, "and", 2).is_some_and(|and_args| {
                and_args.iter().any(|&a| is_not_lt_var_zero(terms, a, i))
                    && and_args
                        .iter()
                        .any(|&a| is_not_le_seq_len_var(terms, a, s, i))
            })
        })
}

fn matches_contains_empty(
    terms: &TermStore,
    vars: &[(String, Sort)],
    body: TermId,
    triggers: &[Vec<TermId>],
) -> bool {
    let Some(x) = single_int_var(vars) else {
        return false;
    };
    trigger_tops_allowed(terms, triggers, &["seq_contains"])
        && not_arg(terms, body).is_some_and(|inner| {
            app_args(terms, inner, "seq_contains", 2)
                .is_some_and(|args| is_seq_empty(terms, args[0]) && is_var(terms, args[1], x))
        })
}

fn matches_contains_push_back(
    terms: &TermStore,
    vars: &[(String, Sort)],
    body: TermId,
    triggers: &[Vec<TermId>],
) -> bool {
    let Some((s, value, x)) = seq_int_int_var_triple(vars) else {
        return false;
    };
    trigger_tops_allowed(terms, triggers, &["seq_contains"])
        && is_eq_between(
            terms,
            body,
            |t| {
                app_args(terms, t, "seq_contains", 2).is_some_and(|args| {
                    is_seq_push_back(terms, args[0], s, value) && is_var(terms, args[1], x)
                })
            },
            |t| {
                app_args(terms, t, "or", 2).is_some_and(|args| {
                    args.iter().any(|&arg| is_eq_vars(terms, arg, value, x))
                        && args.iter().any(|&arg| {
                            app_args(terms, arg, "seq_contains", 2).is_some_and(|contains| {
                                is_var(terms, contains[0], s) && is_var(terms, contains[1], x)
                            })
                        })
                })
            },
        )
}

fn matches_concat_len(
    terms: &TermStore,
    vars: &[(String, Sort)],
    body: TermId,
    triggers: &[Vec<TermId>],
) -> bool {
    let Some((lhs, rhs)) = two_seq_int_vars(vars) else {
        return false;
    };
    trigger_tops_allowed(terms, triggers, &["seq_concat"])
        && is_eq_between(
            terms,
            body,
            |t| {
                app_args(terms, t, "seq_len", 1)
                    .is_some_and(|args| is_seq_concat(terms, args[0], lhs, rhs))
            },
            |t| is_add_seq_lens(terms, t, lhs, rhs),
        )
}

fn matches_concat_left_index(
    terms: &TermStore,
    vars: &[(String, Sort)],
    body: TermId,
    triggers: &[Vec<TermId>],
) -> bool {
    let Some((s1, s2, i)) = seq_seq_int_var_triple(vars) else {
        return false;
    };
    let Some(args) = app_args(terms, body, "or", 3) else {
        return false;
    };
    trigger_tops_allowed(terms, triggers, &["seq_index_logic"])
        && args.iter().any(|&arg| {
            is_eq_between(
                terms,
                arg,
                |t| is_seq_index_logic_concat(terms, t, s1, s2, i),
                |t| is_seq_index_logic(terms, t, s1, i),
            )
        })
        && args.iter().any(|&arg| is_not_le_zero_var(terms, arg, i))
        && args
            .iter()
            .any(|&arg| is_not_lt_var_seq_len(terms, arg, i, s1))
}

fn matches_concat_right_index(
    terms: &TermStore,
    vars: &[(String, Sort)],
    body: TermId,
    triggers: &[Vec<TermId>],
) -> bool {
    let Some((s1, s2, i)) = seq_seq_int_var_triple(vars) else {
        return false;
    };
    let Some(args) = app_args(terms, body, "or", 3) else {
        return false;
    };
    trigger_tops_allowed(terms, triggers, &["seq_index_logic"])
        && args.iter().any(|&arg| {
            is_eq_between(
                terms,
                arg,
                |t| is_seq_index_logic_concat_at_len_plus(terms, t, s1, s2, i),
                |t| is_seq_index_logic(terms, t, s2, i),
            )
        })
        && args.iter().any(|&arg| is_not_le_zero_var(terms, arg, i))
        && args
            .iter()
            .any(|&arg| is_not_lt_var_seq_len(terms, arg, i, s2))
}

fn matches_concat_assoc(
    terms: &TermStore,
    vars: &[(String, Sort)],
    body: TermId,
    triggers: &[Vec<TermId>],
) -> bool {
    let Some((s1, s2, s3)) = three_seq_int_vars(vars) else {
        return false;
    };
    trigger_tops_allowed(terms, triggers, &["seq_concat"])
        && is_eq_between(
            terms,
            body,
            |t| is_seq_concat_left_assoc(terms, t, s1, s2, s3),
            |t| is_seq_concat_right_assoc(terms, t, s1, s2, s3),
        )
}

fn matches_concat_left_identity(
    terms: &TermStore,
    vars: &[(String, Sort)],
    body: TermId,
    triggers: &[Vec<TermId>],
) -> bool {
    let Some(s) = single_seq_int_var(vars) else {
        return false;
    };
    trigger_tops_allowed(terms, triggers, &["seq_concat"])
        && is_eq_between(
            terms,
            body,
            |t| is_var(terms, t, s),
            |t| {
                app_args(terms, t, "seq_concat", 2)
                    .is_some_and(|args| is_seq_empty(terms, args[0]) && is_var(terms, args[1], s))
            },
        )
}

fn matches_concat_right_identity(
    terms: &TermStore,
    vars: &[(String, Sort)],
    body: TermId,
    triggers: &[Vec<TermId>],
) -> bool {
    let Some(s) = single_seq_int_var(vars) else {
        return false;
    };
    trigger_tops_allowed(terms, triggers, &["seq_concat"])
        && is_eq_between(
            terms,
            body,
            |t| is_var(terms, t, s),
            |t| {
                app_args(terms, t, "seq_concat", 2)
                    .is_some_and(|args| is_var(terms, args[0], s) && is_seq_empty(terms, args[1]))
            },
        )
}

fn matches_push_front_definition(
    terms: &TermStore,
    vars: &[(String, Sort)],
    body: TermId,
    triggers: &[Vec<TermId>],
) -> bool {
    let Some((s, x)) = seq_int_var_pair(vars) else {
        return false;
    };
    trigger_tops_allowed(terms, triggers, &["seq_push_front", "seq_concat"])
        && is_eq_between(
            terms,
            body,
            |t| is_seq_push_front(terms, t, s, x),
            |t| {
                app_args(terms, t, "seq_concat", 2).is_some_and(|args| {
                    is_seq_singleton(terms, args[0], x) && is_var(terms, args[1], s)
                })
            },
        )
}

fn matches_push_back_definition(
    terms: &TermStore,
    vars: &[(String, Sort)],
    body: TermId,
    triggers: &[Vec<TermId>],
) -> bool {
    let Some((s, x)) = seq_int_var_pair(vars) else {
        return false;
    };
    trigger_tops_allowed(terms, triggers, &["seq_push_back", "seq_concat"])
        && is_eq_between(
            terms,
            body,
            |t| is_seq_push_back(terms, t, s, x),
            |t| {
                app_args(terms, t, "seq_concat", 2).is_some_and(|args| {
                    is_var(terms, args[0], s) && is_seq_singleton(terms, args[1], x)
                })
            },
        )
}

fn trigger_tops_allowed(terms: &TermStore, triggers: &[Vec<TermId>], allowed: &[&str]) -> bool {
    !triggers.is_empty()
        && triggers.iter().flatten().any(|_| true)
        && triggers
            .iter()
            .flatten()
            .all(|&trigger| app_name(terms, trigger).is_some_and(|name| allowed.contains(&name)))
}

fn single_seq_int_var(vars: &[(String, Sort)]) -> Option<&str> {
    if vars.len() == 1 && is_seq_int_sort(&vars[0].1) {
        Some(vars[0].0.as_str())
    } else {
        None
    }
}

fn single_int_var(vars: &[(String, Sort)]) -> Option<&str> {
    if vars.len() == 1 && vars[0].1 == Sort::Int {
        Some(vars[0].0.as_str())
    } else {
        None
    }
}

fn seq_int_var_pair(vars: &[(String, Sort)]) -> Option<(&str, &str)> {
    if vars.len() == 2 && is_seq_int_sort(&vars[0].1) && vars[1].1 == Sort::Int {
        Some((vars[0].0.as_str(), vars[1].0.as_str()))
    } else {
        None
    }
}

fn two_seq_int_vars(vars: &[(String, Sort)]) -> Option<(&str, &str)> {
    if vars.len() == 2 && is_seq_int_sort(&vars[0].1) && is_seq_int_sort(&vars[1].1) {
        Some((vars[0].0.as_str(), vars[1].0.as_str()))
    } else {
        None
    }
}

fn seq_int_int_var_triple(vars: &[(String, Sort)]) -> Option<(&str, &str, &str)> {
    if vars.len() == 3
        && is_seq_int_sort(&vars[0].1)
        && vars[1].1 == Sort::Int
        && vars[2].1 == Sort::Int
    {
        Some((vars[0].0.as_str(), vars[1].0.as_str(), vars[2].0.as_str()))
    } else {
        None
    }
}

fn seq_seq_int_var_triple(vars: &[(String, Sort)]) -> Option<(&str, &str, &str)> {
    if vars.len() == 3
        && is_seq_int_sort(&vars[0].1)
        && is_seq_int_sort(&vars[1].1)
        && vars[2].1 == Sort::Int
    {
        Some((vars[0].0.as_str(), vars[1].0.as_str(), vars[2].0.as_str()))
    } else {
        None
    }
}

fn three_seq_int_vars(vars: &[(String, Sort)]) -> Option<(&str, &str, &str)> {
    if vars.len() == 3
        && is_seq_int_sort(&vars[0].1)
        && is_seq_int_sort(&vars[1].1)
        && is_seq_int_sort(&vars[2].1)
    {
        Some((vars[0].0.as_str(), vars[1].0.as_str(), vars[2].0.as_str()))
    } else {
        None
    }
}

fn is_seq_int_sort(sort: &Sort) -> bool {
    matches!(sort, Sort::Seq(elem) if matches!(elem.as_ref(), Sort::Int))
}

fn app_name(terms: &TermStore, term: TermId) -> Option<&str> {
    match terms.get(term) {
        TermData::App(sym, _) => Some(sym.name()),
        _ => None,
    }
}

fn app_args<'a>(
    terms: &'a TermStore,
    term: TermId,
    name: &str,
    arity: usize,
) -> Option<&'a [TermId]> {
    match terms.get(term) {
        TermData::App(sym, args) if sym.name() == name && args.len() == arity => {
            Some(args.as_slice())
        }
        _ => None,
    }
}

fn eq_args(terms: &TermStore, term: TermId) -> Option<(TermId, TermId)> {
    app_args(terms, term, "=", 2).map(|args| (args[0], args[1]))
}

fn is_eq_between<L, R>(terms: &TermStore, term: TermId, lhs: L, rhs: R) -> bool
where
    L: Fn(TermId) -> bool,
    R: Fn(TermId) -> bool,
{
    let Some((a, b)) = eq_args(terms, term) else {
        return false;
    };
    (lhs(a) && rhs(b)) || (lhs(b) && rhs(a))
}

fn not_arg(terms: &TermStore, term: TermId) -> Option<TermId> {
    match terms.get(term) {
        TermData::Not(inner) => Some(*inner),
        TermData::App(sym, args) if sym.name() == "not" && args.len() == 1 => Some(args[0]),
        _ => None,
    }
}

fn is_var(terms: &TermStore, term: TermId, name: &str) -> bool {
    matches!(terms.get(term), TermData::Var(var_name, _) if var_name == name)
}

fn is_seq_empty(terms: &TermStore, term: TermId) -> bool {
    matches!(terms.get(term), TermData::Var(name, _) if name == "seq_empty")
}

fn is_zero_int(terms: &TermStore, term: TermId) -> bool {
    matches!(terms.get(term), TermData::Const(Constant::Int(value)) if value.is_zero())
}

fn is_logic_none(terms: &TermStore, term: TermId) -> bool {
    matches!(terms.get(term), TermData::Var(name, _) if name == "logic_None")
        || app_args(terms, term, "logic_None", 0).is_some()
}

fn is_seq_len(terms: &TermStore, term: TermId, seq: &str) -> bool {
    app_args(terms, term, "seq_len", 1).is_some_and(|args| is_var(terms, args[0], seq))
}

fn is_seq_get(terms: &TermStore, term: TermId, seq: &str, index: &str) -> bool {
    app_args(terms, term, "seq_get", 2)
        .is_some_and(|args| is_var(terms, args[0], seq) && is_var(terms, args[1], index))
}

fn is_seq_index_logic(terms: &TermStore, term: TermId, seq: &str, index: &str) -> bool {
    app_args(terms, term, "seq_index_logic", 2)
        .is_some_and(|args| is_var(terms, args[0], seq) && is_var(terms, args[1], index))
}

fn is_seq_concat(terms: &TermStore, term: TermId, lhs: &str, rhs: &str) -> bool {
    app_args(terms, term, "seq_concat", 2)
        .is_some_and(|args| is_var(terms, args[0], lhs) && is_var(terms, args[1], rhs))
}

fn is_seq_push_back(terms: &TermStore, term: TermId, seq: &str, value: &str) -> bool {
    app_args(terms, term, "seq_push_back", 2)
        .is_some_and(|args| is_var(terms, args[0], seq) && is_var(terms, args[1], value))
}

fn is_seq_push_front(terms: &TermStore, term: TermId, seq: &str, value: &str) -> bool {
    app_args(terms, term, "seq_push_front", 2)
        .is_some_and(|args| is_var(terms, args[0], seq) && is_var(terms, args[1], value))
}

fn is_seq_singleton(terms: &TermStore, term: TermId, value: &str) -> bool {
    app_args(terms, term, "seq_singleton", 1).is_some_and(|args| is_var(terms, args[0], value))
}

fn is_select_seq_array_at_offset_plus(
    terms: &TermStore,
    term: TermId,
    seq: &str,
    index: &str,
) -> bool {
    app_args(terms, term, "select", 2).is_some_and(|args| {
        app_args(terms, args[0], "seq_array", 1)
            .is_some_and(|array_args| is_var(terms, array_args[0], seq))
            && is_plus_seq_offset_var(terms, args[1], seq, index)
    })
}

fn is_plus_seq_offset_var(terms: &TermStore, term: TermId, seq: &str, index: &str) -> bool {
    app_args(terms, term, "+", 2).is_some_and(|args| {
        (is_seq_offset(terms, args[0], seq) && is_var(terms, args[1], index))
            || (is_var(terms, args[0], index) && is_seq_offset(terms, args[1], seq))
    })
}

fn is_seq_offset(terms: &TermStore, term: TermId, seq: &str) -> bool {
    app_args(terms, term, "seq_offset", 1).is_some_and(|args| is_var(terms, args[0], seq))
}

fn is_not_le_zero_var(terms: &TermStore, term: TermId, var: &str) -> bool {
    not_arg(terms, term).is_some_and(|inner| {
        app_args(terms, inner, "<=", 2)
            .is_some_and(|args| is_zero_int(terms, args[0]) && is_var(terms, args[1], var))
    })
}

fn is_not_lt_var_seq_len(terms: &TermStore, term: TermId, var: &str, seq: &str) -> bool {
    not_arg(terms, term).is_some_and(|inner| {
        app_args(terms, inner, "<", 2)
            .is_some_and(|args| is_var(terms, args[0], var) && is_seq_len(terms, args[1], seq))
    })
}

fn is_not_lt_var_zero(terms: &TermStore, term: TermId, var: &str) -> bool {
    not_arg(terms, term).is_some_and(|inner| {
        app_args(terms, inner, "<", 2)
            .is_some_and(|args| is_var(terms, args[0], var) && is_zero_int(terms, args[1]))
    })
}

fn is_not_le_seq_len_var(terms: &TermStore, term: TermId, seq: &str, var: &str) -> bool {
    not_arg(terms, term).is_some_and(|inner| {
        app_args(terms, inner, "<=", 2)
            .is_some_and(|args| is_seq_len(terms, args[0], seq) && is_var(terms, args[1], var))
    })
}

fn is_eq_vars(terms: &TermStore, term: TermId, a: &str, b: &str) -> bool {
    is_eq_between(
        terms,
        term,
        |t| is_var(terms, t, a),
        |t| is_var(terms, t, b),
    )
}

fn is_add_seq_lens(terms: &TermStore, term: TermId, lhs: &str, rhs: &str) -> bool {
    app_args(terms, term, "+", 2).is_some_and(|args| {
        (is_seq_len(terms, args[0], lhs) && is_seq_len(terms, args[1], rhs))
            || (is_seq_len(terms, args[0], rhs) && is_seq_len(terms, args[1], lhs))
    })
}

fn is_seq_index_logic_concat(
    terms: &TermStore,
    term: TermId,
    lhs: &str,
    rhs: &str,
    index: &str,
) -> bool {
    app_args(terms, term, "seq_index_logic", 2).is_some_and(|args| {
        is_seq_concat(terms, args[0], lhs, rhs) && is_var(terms, args[1], index)
    })
}

fn is_seq_index_logic_concat_at_len_plus(
    terms: &TermStore,
    term: TermId,
    lhs: &str,
    rhs: &str,
    index: &str,
) -> bool {
    app_args(terms, term, "seq_index_logic", 2).is_some_and(|args| {
        is_seq_concat(terms, args[0], lhs, rhs)
            && app_args(terms, args[1], "+", 2).is_some_and(|plus| {
                (is_seq_len(terms, plus[0], lhs) && is_var(terms, plus[1], index))
                    || (is_var(terms, plus[0], index) && is_seq_len(terms, plus[1], lhs))
            })
    })
}

fn is_seq_concat_left_assoc(terms: &TermStore, term: TermId, s1: &str, s2: &str, s3: &str) -> bool {
    app_args(terms, term, "seq_concat", 2)
        .is_some_and(|args| is_seq_concat(terms, args[0], s1, s2) && is_var(terms, args[1], s3))
}

fn is_seq_concat_right_assoc(
    terms: &TermStore,
    term: TermId,
    s1: &str,
    s2: &str,
    s3: &str,
) -> bool {
    app_args(terms, term, "seq_concat", 2)
        .is_some_and(|args| is_var(terms, args[0], s1) && is_seq_concat(terms, args[1], s2, s3))
}
