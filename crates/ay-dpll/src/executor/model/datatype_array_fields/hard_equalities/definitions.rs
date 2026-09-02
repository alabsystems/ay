// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Unique hard array-definition selection under an aggregate replay budget.

use super::*;

impl Executor {
    /// Unique authored hard definition of one exact array term. Duplicate
    /// equalities naming the same value agree; distinct values are ambiguous.
    pub(in crate::executor::model::datatype_array_fields) fn authored_array_definition(
        &self,
        source: TermId,
        expected_sort: &Sort,
        excluded: &HashSet<TermId>,
        work: &mut usize,
    ) -> AuthoredArrayDefinition {
        let Some(equalities) = self.datatype_array_hard_equalities() else {
            return AuthoredArrayDefinition::Rejected;
        };
        self.authored_array_definition_from(source, expected_sort, &equalities, excluded, work)
    }

    pub(super) fn authored_array_definition_from(
        &self,
        source: TermId,
        expected_sort: &Sort,
        equalities: &[AuthoredHardEquality],
        excluded: &HashSet<TermId>,
        work: &mut usize,
    ) -> AuthoredArrayDefinition {
        if self.ctx.terms.entry_stamp(source).is_none()
            || self.ctx.terms.sort(source) != expected_sort
            || !matches!(expected_sort, Sort::Array(_))
            || !matches!(self.ctx.terms.get(source), TermData::Var(_, _))
        {
            return AuthoredArrayDefinition::Rejected;
        }

        let mut aliases: HashMap<TermId, Vec<(TermId, TermId)>> = HashMap::default();
        let mut terminals: HashMap<TermId, Vec<(TermId, TermId)>> = HashMap::default();
        let mut unsupported = HashSet::default();
        for equality in equalities {
            if !charge_work(work, 1) {
                return AuthoredArrayDefinition::Rejected;
            }
            if self.ctx.terms.entry_stamp(equality.root).is_none()
                || self.ctx.terms.entry_stamp(equality.lhs).is_none()
                || self.ctx.terms.entry_stamp(equality.rhs).is_none()
            {
                return AuthoredArrayDefinition::Rejected;
            }
            if self.ctx.terms.sort(equality.lhs) != expected_sort
                || self.ctx.terms.sort(equality.rhs) != expected_sort
            {
                continue;
            }
            let lhs_var = matches!(self.ctx.terms.get(equality.lhs), TermData::Var(_, _));
            let rhs_var = matches!(self.ctx.terms.get(equality.rhs), TermData::Var(_, _));
            match (lhs_var, rhs_var) {
                (true, true) => {
                    if !charge_work(work, 2) {
                        return AuthoredArrayDefinition::Rejected;
                    }
                    aliases
                        .entry(equality.lhs)
                        .or_default()
                        .push((equality.rhs, equality.root));
                    aliases
                        .entry(equality.rhs)
                        .or_default()
                        .push((equality.lhs, equality.root));
                }
                (true, false) | (false, true) => {
                    if !charge_work(work, 1) {
                        return AuthoredArrayDefinition::Rejected;
                    }
                    let (variable, value) = if lhs_var {
                        (equality.lhs, equality.rhs)
                    } else {
                        (equality.rhs, equality.lhs)
                    };
                    if self.authored_array_definition_value_shape(value, expected_sort) {
                        terminals
                            .entry(variable)
                            .or_default()
                            .push((value, equality.root));
                    } else {
                        unsupported.insert(variable);
                    }
                }
                (false, false) => {}
            }
        }

        let mut component = HashSet::default();
        let mut stack = vec![source];
        let mut support = HashSet::default();
        while let Some(variable) = stack.pop() {
            if variable != source && excluded.contains(&variable) {
                return AuthoredArrayDefinition::Rejected;
            }
            if !component.insert(variable) {
                continue;
            }
            if component.len() > MAX_EXACT_ARRAY_FIELD_TERMS {
                return AuthoredArrayDefinition::Rejected;
            }
            if unsupported.contains(&variable) {
                return AuthoredArrayDefinition::Rejected;
            }
            for &(neighbor, equality) in aliases.get(&variable).into_iter().flatten() {
                support.insert(equality);
                if !component.contains(&neighbor) {
                    stack.push(neighbor);
                }
            }
        }

        let mut selected = None;
        for &variable in &component {
            for &(value, equality) in terminals.get(&variable).into_iter().flatten() {
                let depends = self.array_definition_references_component(
                    value,
                    expected_sort,
                    &component,
                    work,
                );
                if excluded.contains(&value) || depends.is_none_or(|depends| depends) {
                    return AuthoredArrayDefinition::Rejected;
                }
                match selected {
                    Some(old) if old != value => return AuthoredArrayDefinition::Rejected,
                    Some(_) => {}
                    None => selected = Some(value),
                }
                support.insert(equality);
            }
        }
        let Some(value) = selected else {
            return AuthoredArrayDefinition::Absent;
        };
        let mut equalities: Vec<_> = support.into_iter().collect();
        equalities.sort_by_key(|term| term.index());
        AuthoredArrayDefinition::Exact { equalities, value }
    }

    /// Scan the full structural DAG under one aggregate bound. Although scalar
    /// store keys/cells and ITE conditions cannot themselves have
    /// `expected_sort`, an application below them may still mention a component
    /// array as an argument; accepting that hidden cycle would make the source
    /// replay depend on the value it is meant to authenticate.
    fn array_definition_references_component(
        &self,
        value: TermId,
        expected_sort: &Sort,
        component: &HashSet<TermId>,
        work: &mut usize,
    ) -> Option<bool> {
        if !self.authored_array_definition_value_shape(value, expected_sort) {
            return None;
        }
        let mut stack = vec![(value, 0_u32)];
        let mut seen = HashSet::default();
        while let Some((term, depth)) = stack.pop() {
            if depth > super::super::MAX_TYPED_ARRAY_DEPTH
                || !charge_work(work, 1)
                || self.ctx.terms.entry_stamp(term).is_none()
            {
                return None;
            }
            if !seen.insert(term) {
                continue;
            }
            if component.contains(&term) {
                return Some(true);
            }
            if self.ctx.terms.sort(term) == expected_sort
                && !self.authored_array_definition_value_shape(term, expected_sort)
            {
                return None;
            }
            let next_depth = depth.checked_add(1)?;
            match self.ctx.terms.get(term) {
                TermData::Const(_) | TermData::Var(_, _) => {}
                TermData::App(_, args) => {
                    for &child in args.iter().rev() {
                        if stack.len() >= MAX_EXACT_ARRAY_FIELD_TERMS {
                            return None;
                        }
                        stack.push((child, next_depth));
                    }
                }
                TermData::Let(bindings, body) => {
                    if stack.len().checked_add(bindings.len())? >= MAX_EXACT_ARRAY_FIELD_TERMS {
                        return None;
                    }
                    stack.push((*body, next_depth));
                    for (_, child) in bindings.iter().rev() {
                        stack.push((*child, next_depth));
                    }
                }
                TermData::Not(child) => {
                    if stack.len() >= MAX_EXACT_ARRAY_FIELD_TERMS {
                        return None;
                    }
                    stack.push((*child, next_depth));
                }
                TermData::Ite(condition, then_term, else_term) => {
                    if stack.len().checked_add(3)? > MAX_EXACT_ARRAY_FIELD_TERMS {
                        return None;
                    }
                    stack.push((*else_term, next_depth));
                    stack.push((*then_term, next_depth));
                    stack.push((*condition, next_depth));
                }
                TermData::Forall(_, body, triggers) | TermData::Exists(_, body, triggers) => {
                    let trigger_count = triggers
                        .iter()
                        .try_fold(0usize, |count, pattern| count.checked_add(pattern.len()))?;
                    if stack.len().checked_add(trigger_count)?.checked_add(1)?
                        > MAX_EXACT_ARRAY_FIELD_TERMS
                    {
                        return None;
                    }
                    for &child in triggers.iter().rev().flatten().rev() {
                        stack.push((child, next_depth));
                    }
                    stack.push((*body, next_depth));
                }
                _ => return None,
            }
        }
        Some(false)
    }
}
