// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Exact, capture-safe validation for premiseless `forall_inst`.

use super::*;

type MatchFrame = (TermId, TermId, HashSet<String>);

fn invalid_forall_inst(step: ProofId, reason: impl Into<String>) -> ProofCheckError {
    invalid_rule(step, "forall_inst", reason)
}

struct SubstitutionMatcher<'a, 's, 'w> {
    terms: &'a TermStore,
    substitutions: &'s HashMap<&'a str, TermId>,
    matched_var_ids: HashMap<String, u32>,
    work: &'w mut usize,
    stack: Vec<MatchFrame>,
}

impl SubstitutionMatcher<'_, '_, '_> {
    fn run(&mut self, pattern: TermId, instance: TermId) -> Option<bool> {
        self.stack
            .push((pattern, instance, HashSet::<String>::default()));
        while let Some((expected, actual, blocked)) = self.stack.pop() {
            if !self.match_node(expected, actual, blocked)? {
                return Some(false);
            }
        }
        Some(true)
    }

    fn match_node(
        &mut self,
        expected: TermId,
        actual: TermId,
        blocked: HashSet<String>,
    ) -> Option<bool> {
        if *self.work >= SKOLEM_TERM_WORK_LIMIT {
            return None;
        }
        *self.work += 1;
        if self.terms.sort(expected) != self.terms.sort(actual) {
            return Some(false);
        }
        match self.terms.get(expected) {
            TermData::Var(name, id) => {
                Some(self.match_variable(name, *id, expected, actual, &blocked))
            }
            TermData::Const(..) => Some(expected == actual),
            TermData::Not(inner) => {
                let TermData::Not(actual_inner) = self.terms.get(actual) else {
                    return Some(false);
                };
                self.stack.push((*inner, *actual_inner, blocked));
                Some(true)
            }
            TermData::Ite(condition, then_branch, else_branch) => {
                let TermData::Ite(actual_condition, actual_then, actual_else) =
                    self.terms.get(actual)
                else {
                    return Some(false);
                };
                self.stack.extend([
                    (*condition, *actual_condition, blocked.clone()),
                    (*then_branch, *actual_then, blocked.clone()),
                    (*else_branch, *actual_else, blocked),
                ]);
                Some(true)
            }
            TermData::App(symbol, args) => self.match_app(symbol, args, actual, blocked),
            TermData::Forall(bindings, body, triggers)
            | TermData::Exists(bindings, body, triggers) => {
                self.match_quantifier(expected, actual, bindings, *body, triggers, blocked)
            }
            TermData::Let(..) => Some(false),
            _ => Some(false),
        }
    }

    fn match_variable(
        &mut self,
        name: &str,
        id: u32,
        expected: TermId,
        actual: TermId,
        blocked: &HashSet<String>,
    ) -> bool {
        if blocked.contains(name) {
            return expected == actual;
        }
        let Some(&replacement) = self.substitutions.get(name) else {
            return expected == actual;
        };
        match self.matched_var_ids.get(name) {
            Some(&seen) if seen != id => return false,
            Some(_) => {}
            None => {
                self.matched_var_ids.insert(name.to_owned(), id);
            }
        }
        actual == replacement
    }

    fn match_app(
        &mut self,
        symbol: &Symbol,
        args: &[TermId],
        actual: TermId,
        blocked: HashSet<String>,
    ) -> Option<bool> {
        let TermData::App(actual_symbol, actual_args) = self.terms.get(actual) else {
            return Some(false);
        };
        if symbol != actual_symbol || args.len() != actual_args.len() {
            return Some(false);
        }
        self.stack.extend(
            args.iter()
                .copied()
                .zip(actual_args.iter().copied())
                .map(|(left, right)| (left, right, blocked.clone())),
        );
        Some(true)
    }

    fn match_quantifier(
        &mut self,
        expected: TermId,
        actual: TermId,
        bindings: &[(String, Sort)],
        body: TermId,
        triggers: &[Vec<TermId>],
        mut blocked: HashSet<String>,
    ) -> Option<bool> {
        let same_polarity = matches!(
            (self.terms.get(expected), self.terms.get(actual)),
            (TermData::Forall(..), TermData::Forall(..))
                | (TermData::Exists(..), TermData::Exists(..))
        );
        let (actual_bindings, actual_body, actual_triggers) = match self.terms.get(actual) {
            TermData::Forall(bindings, body, triggers)
            | TermData::Exists(bindings, body, triggers) => (bindings, body, triggers),
            _ => return Some(false),
        };
        if !same_polarity
            || bindings != actual_bindings
            || triggers.len() != actual_triggers.len()
            || triggers
                .iter()
                .zip(actual_triggers)
                .any(|(left, right)| left.len() != right.len())
        {
            return Some(false);
        }
        blocked.extend(bindings.iter().map(|(name, _)| name.clone()));
        self.stack.push((body, *actual_body, blocked.clone()));
        for (left, right) in triggers.iter().zip(actual_triggers) {
            self.stack.extend(
                left.iter()
                    .copied()
                    .zip(right.iter().copied())
                    .map(|(left, right)| (left, right, blocked.clone())),
            );
        }
        Some(true)
    }
}

fn matches_substitution<'a>(
    terms: &'a TermStore,
    pattern: TermId,
    instance: TermId,
    substitutions: &HashMap<&'a str, TermId>,
    work: &mut usize,
) -> Option<bool> {
    SubstitutionMatcher {
        terms,
        substitutions,
        matched_var_ids: HashMap::default(),
        work,
        stack: Vec::new(),
    }
    .run(pattern, instance)
}

fn nested_binder_names(
    terms: &TermStore,
    root: TermId,
    work: &mut usize,
) -> Option<HashSet<String>> {
    let mut names = HashSet::default();
    let mut seen = HashSet::default();
    let mut stack = vec![root];
    while let Some(term) = stack.pop() {
        if !seen.insert(term) {
            continue;
        }
        if *work >= SKOLEM_TERM_WORK_LIMIT {
            return None;
        }
        *work += 1;
        match terms.get(term) {
            TermData::Forall(bindings, body, triggers)
            | TermData::Exists(bindings, body, triggers) => {
                names.extend(bindings.iter().map(|(name, _)| name.clone()));
                stack.push(*body);
                stack.extend(triggers.iter().flatten().copied());
            }
            TermData::App(_, args) => stack.extend(args.iter().copied()),
            TermData::Not(inner) => stack.push(*inner),
            TermData::Ite(condition, then_branch, else_branch) => {
                stack.extend([*condition, *then_branch, *else_branch]);
            }
            TermData::Let(..) => return None,
            _ => {}
        }
    }
    Some(names)
}

fn argument_has_free_name_in(
    terms: &TermStore,
    root: TermId,
    forbidden: &HashSet<String>,
    work: &mut usize,
) -> Option<bool> {
    let mut seen = HashSet::default();
    let mut stack = vec![root];
    while let Some(term) = stack.pop() {
        if !seen.insert(term) {
            continue;
        }
        if *work >= SKOLEM_TERM_WORK_LIMIT {
            return None;
        }
        *work += 1;
        match terms.get(term) {
            TermData::Var(name, _) if forbidden.contains(name) => return Some(true),
            TermData::App(_, args) => stack.extend(args.iter().copied()),
            TermData::Not(inner) => stack.push(*inner),
            TermData::Ite(condition, then_branch, else_branch) => {
                stack.extend([*condition, *then_branch, *else_branch]);
            }
            TermData::Let(..) | TermData::Forall(..) | TermData::Exists(..) => return Some(true),
            _ => {}
        }
    }
    Some(false)
}

pub(super) fn matches_single_substitution(
    terms: &TermStore,
    pattern: TermId,
    instance: TermId,
    binder: &str,
    witness: TermId,
    work: &mut usize,
) -> Option<bool> {
    let mut substitutions = HashMap::default();
    substitutions.insert(binder, witness);
    matches_substitution(terms, pattern, instance, &substitutions, work)
}

fn argument_is_ground_for(
    terms: &TermStore,
    root: TermId,
    binder_names: &HashSet<&str>,
    work: &mut usize,
) -> Option<bool> {
    let mut visited = HashSet::default();
    let mut stack = vec![root];
    while let Some(term) = stack.pop() {
        if !visited.insert(term) {
            continue;
        }
        if *work >= SKOLEM_TERM_WORK_LIMIT {
            return None;
        }
        *work += 1;
        match terms.get(term) {
            TermData::Var(name, _) if binder_names.contains(name.as_str()) => return Some(false),
            TermData::Var(..) | TermData::Const(..) => {}
            TermData::Not(inner) => stack.push(*inner),
            TermData::Ite(condition, then_branch, else_branch) => {
                stack.extend([*condition, *then_branch, *else_branch]);
            }
            TermData::App(_, args) => stack.extend(args.iter().copied()),
            TermData::Let(..) | TermData::Forall(..) | TermData::Exists(..) => return Some(false),
            _ => return Some(false),
        }
    }
    Some(true)
}

fn decode_forall_inst_shape<'a>(
    terms: &'a TermStore,
    step: ProofId,
    clause: &[TermId],
    premise_count: usize,
    args: &[TermId],
) -> Result<(&'a [(String, Sort)], TermId, TermId), ProofCheckError> {
    if premise_count != 0 {
        return Err(invalid_forall_inst(step, "must not have premises"));
    }
    let [implication] = clause else {
        return Err(invalid_forall_inst(
            step,
            "conclusion must be one or-wrapped implication",
        ));
    };
    let TermData::App(Symbol::Named(or_name), disjuncts) = terms.get(*implication) else {
        return Err(invalid_forall_inst(step, "conclusion must be an or term"));
    };
    if terms.sort(*implication) != &Sort::Bool || or_name != "or" || disjuncts.len() != 2 {
        return Err(invalid_forall_inst(
            step,
            "conclusion must be exactly a Boolean (or (not forall) instance)",
        ));
    }
    let TermData::Not(quantified) = terms.get(disjuncts[0]) else {
        return Err(invalid_forall_inst(
            step,
            "first disjunct must be the negated source forall",
        ));
    };
    let TermData::Forall(bindings, body, _) = terms.get(*quantified) else {
        return Err(invalid_forall_inst(step, "negated source must be a forall"));
    };
    if bindings.is_empty() || args.len() != bindings.len() {
        return Err(invalid_forall_inst(
            step,
            "positional argument count must equal the non-empty binder count",
        ));
    }
    Ok((bindings, *body, disjuncts[1]))
}

fn checked_substitutions<'a>(
    terms: &'a TermStore,
    step: ProofId,
    bindings: &'a [(String, Sort)],
    body: TermId,
    args: &[TermId],
    work: &mut usize,
) -> Result<HashMap<&'a str, TermId>, ProofCheckError> {
    let binder_names = bindings
        .iter()
        .map(|(name, _)| name.as_str())
        .collect::<HashSet<_>>();
    if binder_names.len() != bindings.len() {
        return Err(invalid_forall_inst(
            step,
            "source forall contains duplicate binder names",
        ));
    }
    let nested_names = nested_binder_names(terms, body, work).ok_or_else(|| {
        invalid_forall_inst(
            step,
            format!(
                "nested-binder scan exceeds {SKOLEM_TERM_WORK_LIMIT} distinct terms or encounters let"
            ),
        )
    })?;
    let mut substitutions = HashMap::default();
    for ((name, sort), &argument) in bindings.iter().zip(args) {
        if terms.sort(argument) != sort {
            return Err(invalid_forall_inst(
                step,
                "argument sort does not match its positional binder",
            ));
        }
        if argument_is_ground_for(terms, argument, &binder_names, work) != Some(true) {
            return Err(invalid_forall_inst(
                step,
                "argument is not a bounded ground term for the source binders",
            ));
        }
        if argument_has_free_name_in(terms, argument, &nested_names, work) != Some(false) {
            return Err(invalid_forall_inst(
                step,
                "argument is unbounded or may be captured by a nested binder",
            ));
        }
        substitutions.insert(name.as_str(), argument);
    }
    Ok(substitutions)
}

/// Validate AY's premiseless, exact structural `forall_inst` representation.
pub(crate) fn validate_forall_inst(
    terms: &TermStore,
    step: ProofId,
    clause: &[TermId],
    premise_count: usize,
    args: &[TermId],
) -> Result<(), ProofCheckError> {
    let (bindings, body, instance) =
        decode_forall_inst_shape(terms, step, clause, premise_count, args)?;
    let mut work = 0usize;
    let substitutions = checked_substitutions(terms, step, bindings, body, args, &mut work)?;
    if terms.sort(instance) != &Sort::Bool {
        return Err(invalid_forall_inst(
            step,
            "instantiated body must be Boolean",
        ));
    }
    match matches_substitution(terms, body, instance, &substitutions, &mut work) {
        Some(true) => Ok(()),
        Some(false) => Err(invalid_forall_inst(
            step,
            "instance is not the exact simultaneous binder substitution",
        )),
        None => Err(invalid_forall_inst(
            step,
            format!("substitution check exceeds {SKOLEM_TERM_WORK_LIMIT} distinct term pairs"),
        )),
    }
}
