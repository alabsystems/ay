// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Pattern synthesis, trigger grouping, and term-to-pattern conversion helpers.
//!
//! Standalone helper functions extracted from `pattern.rs` for code health (#5970).

// #8529: Use deterministic hash maps in all builds.
use ay_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};
use ay_core::term::{Symbol, TermData};
use ay_core::{TermId, TermStore};

use super::pattern::{EMatchArg, EMatchPattern, TriggerGroup};
use super::{EMATCH_STACK_RED_ZONE, EMATCH_STACK_SIZE};

#[derive(Clone, Copy)]
struct LetAlias {
    term: TermId,
    visible_scope_count: usize,
}

type LetScopeFrame = HashMap<String, LetAlias>;

/// Synthesize trigger groups from auto-extracted patterns (#3325 item 2b).
///
/// If any single pattern covers all bound variables, returns those as single triggers.
/// Otherwise, combines partial-coverage patterns into multi-trigger groups:
/// tries pairs first (O(n^2)), then triples (O(n^3)), capped at 8 groups.
/// Falls back to returning partial patterns as singles if no combination covers all vars.
pub(super) struct SynthesizedTriggerGroups {
    pub(super) primary: Vec<TriggerGroup>,
    pub(super) fallback: Vec<TriggerGroup>,
}

pub(super) fn synthesize_trigger_groups_with_fallback(
    patterns: Vec<(EMatchPattern, Vec<String>)>,
    num_vars: usize,
    var_names: &[String],
) -> SynthesizedTriggerGroups {
    let var_names_vec: Vec<String> = var_names.to_vec();

    // Compute variable coverage for each pattern
    let coverages: Vec<HashSet<usize>> = patterns
        .iter()
        .map(|(pat, _)| pattern_covered_vars(pat))
        .collect();

    // Separate full-coverage patterns (single triggers) from partial-coverage
    let mut full_coverage: Vec<&EMatchPattern> = Vec::new();
    let mut partial: Vec<(usize, &EMatchPattern)> = Vec::new();

    for (i, (pat, _)) in patterns.iter().enumerate() {
        if coverages[i].len() == num_vars {
            full_coverage.push(pat);
        } else if !coverages[i].is_empty() {
            partial.push((i, pat));
        }
    }

    if !full_coverage.is_empty() {
        let max_specificity = full_coverage
            .iter()
            .map(|pat| pattern_specificity(pat))
            .max()
            .unwrap_or(0);
        let mut primary = Vec::new();
        let mut fallback = Vec::new();

        for pat in full_coverage {
            let group = TriggerGroup {
                patterns: vec![pat.clone()],
                var_names: var_names_vec.clone(),
            };
            if pattern_specificity(pat) == max_specificity {
                primary.push(group);
            } else {
                fallback.push(group);
            }
        }

        return SynthesizedTriggerGroups { primary, fallback };
    }

    // No single pattern covers all vars — combine partial-coverage patterns.
    let multi = synthesize_multi_triggers(&partial, &coverages, num_vars, &var_names_vec);
    if !multi.is_empty() {
        return SynthesizedTriggerGroups {
            primary: multi,
            fallback: vec![],
        };
    }

    // Fallback: return partial patterns as singles (they'll fail to match all vars
    // but enumerative instantiation will handle the quantifier)
    let primary = patterns
        .into_iter()
        .map(|(pat, vn)| TriggerGroup {
            patterns: vec![pat],
            var_names: vn,
        })
        .collect();
    SynthesizedTriggerGroups {
        primary,
        fallback: vec![],
    }
}

fn pattern_specificity(pattern: &EMatchPattern) -> usize {
    1 + pattern
        .args
        .iter()
        .map(|arg| match arg {
            EMatchArg::Nested(nested) => pattern_specificity(nested),
            EMatchArg::Var(_) | EMatchArg::Ground(_) => 0,
        })
        .sum::<usize>()
}

/// Combine partial-coverage patterns into multi-trigger groups that together
/// cover all bound variables. Tries pairs first, then triples.
///
/// Max 8 multi-trigger groups to avoid combinatorial explosion.
fn synthesize_multi_triggers(
    partial: &[(usize, &EMatchPattern)],
    coverages: &[HashSet<usize>],
    num_vars: usize,
    var_names: &[String],
) -> Vec<TriggerGroup> {
    let mut result: Vec<TriggerGroup> = Vec::new();
    let max_multi = 8;

    // Try pairs (most common case: 2-variable quantifiers with unary patterns)
    for i in 0..partial.len() {
        if result.len() >= max_multi {
            break;
        }
        for j in (i + 1)..partial.len() {
            if result.len() >= max_multi {
                break;
            }
            let combined: HashSet<usize> = coverages[partial[i].0]
                .union(&coverages[partial[j].0])
                .copied()
                .collect();
            if combined.len() == num_vars {
                result.push(TriggerGroup {
                    patterns: vec![partial[i].1.clone(), partial[j].1.clone()],
                    var_names: var_names.to_vec(),
                });
            }
        }
    }

    if !result.is_empty() {
        return result;
    }

    // Try triples if pairs don't cover (3-variable quantifiers with 3 unary patterns)
    if num_vars >= 3 && partial.len() >= 3 {
        'triple: for i in 0..partial.len() {
            for j in (i + 1)..partial.len() {
                for k in (j + 1)..partial.len() {
                    let combined: HashSet<usize> = coverages[partial[i].0]
                        .union(&coverages[partial[j].0])
                        .copied()
                        .chain(coverages[partial[k].0].iter().copied())
                        .collect();
                    if combined.len() == num_vars {
                        result.push(TriggerGroup {
                            patterns: vec![
                                partial[i].1.clone(),
                                partial[j].1.clone(),
                                partial[k].1.clone(),
                            ],
                            var_names: var_names.to_vec(),
                        });
                        if result.len() >= max_multi {
                            break 'triple;
                        }
                    }
                }
            }
        }
    }

    result
}

/// Collect the set of bound variable indices covered by a pattern.
pub(super) fn pattern_covered_vars(pattern: &EMatchPattern) -> HashSet<usize> {
    let mut vars = HashSet::default();
    collect_pattern_vars(pattern, &mut vars);
    vars
}

fn collect_pattern_vars(pattern: &EMatchPattern, out: &mut HashSet<usize>) {
    for arg in &pattern.args {
        match arg {
            EMatchArg::Var(idx) => {
                out.insert(*idx);
            }
            EMatchArg::Nested(nested) => {
                collect_pattern_vars(nested, out);
            }
            EMatchArg::Ground(_) => {}
        }
    }
}

/// Convert a multi-trigger (group of trigger terms) into a TriggerGroup.
/// All patterns in the group must match with consistent bindings for the
/// trigger to fire. Returns None if no valid patterns are extracted.
pub(super) fn user_pattern_to_ematch(
    terms: &TermStore,
    multi_trigger: &[TermId],
    var_indices: &HashMap<String, usize>,
    actual_var_names: &[String],
) -> Option<TriggerGroup> {
    let patterns: Vec<EMatchPattern> = multi_trigger
        .iter()
        .filter_map(|&trigger_term| {
            let TermData::App(sym, args) = terms.get(trigger_term) else {
                // Non-function triggers are silently skipped (Z3 compatibility).
                return None;
            };

            let contains_bound_var = args
                .iter()
                .any(|&arg| term_has_bound_var(terms, arg, var_indices));

            if !contains_bound_var || is_builtin_symbol(sym) {
                return None;
            }

            let pattern_args: Vec<EMatchArg> = args
                .iter()
                .map(|&arg| term_to_pattern_arg(terms, arg, var_indices))
                .collect();

            Some(EMatchPattern {
                symbol: sym.clone(),
                args: pattern_args,
            })
        })
        .collect();

    if patterns.is_empty() {
        None
    } else {
        Some(TriggerGroup {
            patterns,
            var_names: actual_var_names.to_vec(),
        })
    }
}

pub(super) fn collect_patterns_from_term(
    terms: &TermStore,
    term: TermId,
    var_indices: &HashMap<String, usize>,
    actual_var_names: &[String],
    no_patterns: &[TermId],
    out: &mut Vec<(EMatchPattern, Vec<String>)>,
) {
    let let_scopes = Vec::new();
    collect_patterns_from_term_with_let_scopes(
        terms,
        term,
        var_indices,
        actual_var_names,
        &let_scopes,
        no_patterns,
        out,
    );
}

fn collect_patterns_from_term_with_let_scopes(
    terms: &TermStore,
    term: TermId,
    var_indices: &HashMap<String, usize>,
    actual_var_names: &[String],
    let_scopes: &[LetScopeFrame],
    no_patterns: &[TermId],
    out: &mut Vec<(EMatchPattern, Vec<String>)>,
) {
    stacker::maybe_grow(EMATCH_STACK_RED_ZONE, EMATCH_STACK_SIZE, || {
        match terms.get(term) {
            TermData::App(sym, args) => {
                let contains_bound_var = args.iter().any(|&arg| {
                    term_has_bound_var_in_let_scope(terms, arg, var_indices, let_scopes)
                });

                // Z3's pattern inference rejects an exact `:no-pattern` node as
                // a candidate but still visits its children, so only suppress
                // this one push; do not prune the traversal.
                if contains_bound_var && !is_builtin_symbol(sym) && !no_patterns.contains(&term) {
                    let pattern_args: Vec<EMatchArg> = args
                        .iter()
                        .map(|&arg| {
                            term_to_pattern_arg_in_let_scope(terms, arg, var_indices, let_scopes)
                        })
                        .collect();

                    out.push((
                        EMatchPattern {
                            symbol: sym.clone(),
                            args: pattern_args,
                        },
                        actual_var_names.to_vec(),
                    ));
                }

                for &arg in args {
                    collect_patterns_from_term_with_let_scopes(
                        terms,
                        arg,
                        var_indices,
                        actual_var_names,
                        let_scopes,
                        no_patterns,
                        out,
                    );
                }
            }
            TermData::Not(inner) => {
                collect_patterns_from_term_with_let_scopes(
                    terms,
                    *inner,
                    var_indices,
                    actual_var_names,
                    let_scopes,
                    no_patterns,
                    out,
                );
            }
            TermData::Ite(c, t, e) => {
                collect_patterns_from_term_with_let_scopes(
                    terms,
                    *c,
                    var_indices,
                    actual_var_names,
                    let_scopes,
                    no_patterns,
                    out,
                );
                collect_patterns_from_term_with_let_scopes(
                    terms,
                    *t,
                    var_indices,
                    actual_var_names,
                    let_scopes,
                    no_patterns,
                    out,
                );
                collect_patterns_from_term_with_let_scopes(
                    terms,
                    *e,
                    var_indices,
                    actual_var_names,
                    let_scopes,
                    no_patterns,
                    out,
                );
            }
            TermData::Let(bindings, body) => {
                let inner_scopes = extend_let_scopes(let_scopes, bindings);
                collect_patterns_from_term_with_let_scopes(
                    terms,
                    *body,
                    var_indices,
                    actual_var_names,
                    &inner_scopes,
                    no_patterns,
                    out,
                );
            }
            _ => {}
        }
    })
}

/// Convert a term to a pattern argument.
/// - If the term is a bound variable, returns EMatchArg::Var
/// - If the term is ground (no bound variables), returns EMatchArg::Ground
/// - If the term is an App containing bound variables, returns EMatchArg::Nested
fn term_to_pattern_arg(
    terms: &TermStore,
    term: TermId,
    var_indices: &HashMap<String, usize>,
) -> EMatchArg {
    let let_scopes = Vec::new();
    term_to_pattern_arg_in_let_scope(terms, term, var_indices, &let_scopes)
}

/// Uses `stacker::maybe_grow` for stack safety on deeply nested terms (#8414).
fn term_to_pattern_arg_in_let_scope(
    terms: &TermStore,
    term: TermId,
    var_indices: &HashMap<String, usize>,
    let_scopes: &[LetScopeFrame],
) -> EMatchArg {
    stacker::maybe_grow(EMATCH_STACK_RED_ZONE, EMATCH_STACK_SIZE, || {
        // Case 1: Direct bound variable
        if let TermData::Var(name, _) = terms.get(term) {
            if let Some(alias) = lookup_let_alias(name, let_scopes) {
                return term_to_pattern_arg_in_let_scope(
                    terms,
                    alias.term,
                    var_indices,
                    visible_let_scopes(let_scopes, alias.visible_scope_count),
                );
            }
            if let Some(&idx) = var_indices.get(name) {
                return EMatchArg::Var(idx);
            }
        }

        // Case 2: Ground term (no bound variables) - match exactly
        if !term_has_bound_var_in_let_scope(terms, term, var_indices, let_scopes) {
            return EMatchArg::Ground(term);
        }

        // Case 3: Non-variable term containing bound variables -> nested pattern
        match terms.get(term) {
            TermData::App(sym, args) => {
                let nested_args: Vec<EMatchArg> = args
                    .iter()
                    .map(|&arg| {
                        term_to_pattern_arg_in_let_scope(terms, arg, var_indices, let_scopes)
                    })
                    .collect();
                EMatchArg::Nested(Box::new(EMatchPattern {
                    symbol: sym.clone(),
                    args: nested_args,
                }))
            }
            TermData::Let(bindings, body) => {
                let inner_scopes = extend_let_scopes(let_scopes, bindings);
                term_to_pattern_arg_in_let_scope(terms, *body, var_indices, &inner_scopes)
            }
            // Fallback: treat as ground (shouldn't happen for well-formed terms)
            _ => EMatchArg::Ground(term),
        }
    }) // stacker::maybe_grow
}

fn term_has_bound_var(
    terms: &TermStore,
    term: TermId,
    var_indices: &HashMap<String, usize>,
) -> bool {
    let let_scopes = Vec::new();
    term_has_bound_var_in_let_scope(terms, term, var_indices, &let_scopes)
}

/// Uses `stacker::maybe_grow` for stack safety on deeply nested terms (#8414).
fn term_has_bound_var_in_let_scope(
    terms: &TermStore,
    term: TermId,
    var_indices: &HashMap<String, usize>,
    let_scopes: &[LetScopeFrame],
) -> bool {
    stacker::maybe_grow(EMATCH_STACK_RED_ZONE, EMATCH_STACK_SIZE, || {
        match terms.get(term) {
            TermData::Var(name, _) => lookup_let_alias(name, let_scopes)
                .map(|alias| {
                    term_has_bound_var_in_let_scope(
                        terms,
                        alias.term,
                        var_indices,
                        visible_let_scopes(let_scopes, alias.visible_scope_count),
                    )
                })
                .unwrap_or_else(|| var_indices.contains_key(name)),
            TermData::App(_, args) => args
                .iter()
                .any(|&arg| term_has_bound_var_in_let_scope(terms, arg, var_indices, let_scopes)),
            TermData::Not(inner) => {
                term_has_bound_var_in_let_scope(terms, *inner, var_indices, let_scopes)
            }
            TermData::Ite(c, t, e) => {
                term_has_bound_var_in_let_scope(terms, *c, var_indices, let_scopes)
                    || term_has_bound_var_in_let_scope(terms, *t, var_indices, let_scopes)
                    || term_has_bound_var_in_let_scope(terms, *e, var_indices, let_scopes)
            }
            TermData::Let(bindings, body) => {
                let inner_scopes = extend_let_scopes(let_scopes, bindings);
                term_has_bound_var_in_let_scope(terms, *body, var_indices, &inner_scopes)
            }
            _ => false,
        }
    }) // stacker::maybe_grow
}

fn extend_let_scopes(
    let_scopes: &[LetScopeFrame],
    bindings: &[(String, TermId)],
) -> Vec<LetScopeFrame> {
    if bindings.is_empty() {
        return let_scopes.to_vec();
    }

    let mut inner_scopes = let_scopes.to_vec();
    let visible_scope_count = let_scopes.len();
    let frame: LetScopeFrame = bindings
        .iter()
        .map(|(name, term)| {
            (
                name.clone(),
                LetAlias {
                    term: *term,
                    visible_scope_count,
                },
            )
        })
        .collect();
    inner_scopes.push(frame);
    inner_scopes
}

fn lookup_let_alias(name: &str, let_scopes: &[LetScopeFrame]) -> Option<LetAlias> {
    for scope in let_scopes.iter().rev() {
        if let Some(alias) = scope.get(name) {
            return Some(*alias);
        }
    }
    None
}

fn visible_let_scopes(
    let_scopes: &[LetScopeFrame],
    visible_scope_count: usize,
) -> &[LetScopeFrame] {
    let_scopes.get(..visible_scope_count).unwrap_or(let_scopes)
}

fn is_builtin_symbol(sym: &Symbol) -> bool {
    match sym {
        Symbol::Named(name) => matches!(
            name.as_str(),
            "+" | "-"
                | "*"
                | "/"
                | "div"
                | "mod"
                | "abs"
                | "and"
                | "or"
                | "not"
                | "=>"
                | "="
                | "<"
                | "<="
                | ">"
                | ">="
                | "distinct"
                | "ite"
        ),
        Symbol::Indexed(_, _) => false,
        // Future Symbol variants: not builtin.
        _ => false,
    }
}
