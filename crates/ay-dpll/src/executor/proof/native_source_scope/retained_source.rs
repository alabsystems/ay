// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Bind checked retained data to the exact live, frozen source identities.
//! This is the same-arena diagnostic boundary; fresh-context alpha remapping
//! must be independently authenticated and is not inferred here from names.

use super::*;
use ay_proof::{ProofCheckError, RetainedProofSourceView};

impl NativeProofSourceScope {
    pub(crate) fn matches_retained_source_with_progress(
        &self,
        executor: &Executor,
        view: &RetainedProofSourceView<'_>,
        progress: &mut dyn FnMut(usize, usize) -> bool,
    ) -> Result<bool, ProofCheckError> {
        if !self
            .diagnostic_applications_are_declared_with_progress(executor, progress)
            .ok_or(ProofCheckError::ResourceLimit)?
        {
            return Ok(false);
        }
        let mut control = codec::Control::new(progress);
        let mut bind = || -> Option<bool> {
            for &root in view.obligations() {
                control.charge(self.roots.len(), 0)?;
                if !self.roots.contains(&root) {
                    return Some(false);
                }
            }
            if !name_table_matches(
                self.datatypes.declarations(),
                view.datatype_declarations(),
                &mut control,
            )? || !name_table_matches(
                self.datatypes.selectors(),
                view.constructor_selectors(),
                &mut control,
            )? {
                return Some(false);
            }
            let expected = self.datatypes.signatures();
            let actual = view.datatype_member_signatures();
            control.charge(expected.len().checked_add(actual.len())?, 0)?;
            if expected.len() != actual.len() {
                return Some(false);
            }
            for (expected, actual) in expected.iter().zip(actual) {
                control.charge(
                    expected.identity.len().checked_add(actual.identity.len())?,
                    0,
                )?;
                if expected.identity != actual.identity
                    || expected.nullary_term != actual.nullary_term
                    || expected.argument_sorts.len() != actual.argument_sorts.len()
                {
                    return Some(false);
                }
                for (left, right) in expected
                    .argument_sorts
                    .iter()
                    .zip(&actual.argument_sorts)
                    .chain(std::iter::once((
                        &expected.result_sort,
                        &actual.result_sort,
                    )))
                {
                    codec::validate_sort(left, 32, false, &mut control)?;
                    codec::validate_sort(right, 32, false, &mut control)?;
                    if left != right {
                        return Some(false);
                    }
                }
            }
            Some(true)
        };
        if !bind().ok_or(ProofCheckError::ResourceLimit)? {
            return Ok(false);
        }
        if view.term_count() > MAX_SOURCE_TERMS {
            return Ok(false);
        }
        for index in 0..view.term_count() {
            control.charge(1, 0).ok_or(ProofCheckError::ResourceLimit)?;
            let id = TermId(u32::try_from(index).map_err(|_| ProofCheckError::ResourceLimit)?);
            let Some((data, sort)) = view.term(id) else {
                return Ok(false);
            };
            self.datatypes
                .admits_sort(sort, &mut control)
                .ok_or(ProofCheckError::ResourceLimit)?;
            if !self
                .diagnostic_application_matches(
                    executor,
                    data,
                    sort,
                    |child| view.term(child).map(|(_, sort)| sort),
                    &mut control,
                )
                .ok_or(ProofCheckError::ResourceLimit)?
            {
                return Ok(false);
            }
        }
        for &(id, entry) in &self.source_entries {
            control.charge(1, 0).ok_or(ProofCheckError::ResourceLimit)?;
            if executor.ctx.terms.entry_stamp(id) != Some(entry) {
                return Ok(false);
            }
            if !view.term_matches_with_resource_control(
                id,
                (executor.ctx.terms.get(id), executor.ctx.terms.sort(id)),
                &mut |w, b| control.charge(w, b).is_some(),
            )? {
                return Ok(false);
            }
        }
        control.charge(0, 0).ok_or(ProofCheckError::ResourceLimit)?;
        Ok(true)
    }

    /// One actual declaration/signature rule shared by live input admission
    /// and independently decoded proof terms. Unknown proof-private functions
    /// decline in this first slice rather than acquiring authority from names.
    pub(super) fn diagnostic_application_matches<'a>(
        &self,
        executor: &Executor,
        data: &ay_core::TermData,
        sort: &Sort,
        child_sort: impl Fn(TermId) -> Option<&'a Sort>,
        control: &mut codec::Control<'_>,
    ) -> Option<bool> {
        let ay_core::TermData::App(symbol, args) = data else {
            return Some(true);
        };
        control.charge(
            self.declarations
                .len()
                .checked_add(self.datatypes.signatures().len())?,
            0,
        )?;
        let mut lookup_work = symbol.name().len().checked_add(args.len())?;
        for declaration in &self.declarations {
            lookup_work = lookup_work.checked_add(declaration.symbol.name().len())?;
        }
        for member in self.datatypes.signatures() {
            lookup_work = lookup_work.checked_add(member.identity.len())?;
        }
        control.charge(lookup_work, 0)?;
        let member = self
            .datatypes
            .signatures()
            .iter()
            .find(|member| member.identity == symbol.name());
        let ordinary = self.declarations.iter().find(|decl| decl.symbol == *symbol);
        let signature = member
            .map(|m| (m.argument_sorts.as_slice(), &m.result_sort))
            .or_else(|| ordinary.map(|d| (d.domain.as_ref(), &d.range)));
        if let Some((domain, range)) = signature {
            if !matches!(symbol, Symbol::Named(_)) || domain.len() != args.len() {
                return Some(false);
            }
            // The independent snapshot checker has no source-level overload
            // environment. A source UF cannot become a builtin solely by
            // carrying a reserved operator spelling in the retained table.
            if ordinary.is_some()
                && ay_frontend::is_canonical_theory_operator_identity(symbol.name())
            {
                return Some(false);
            }
            codec::validate_sort(range, 32, false, control)?;
            codec::validate_sort(sort, 32, false, control)?;
            if range != sort {
                return Some(false);
            }
            for (expected, &id) in domain.iter().zip(args) {
                let Some(actual) = child_sort(id) else {
                    return Some(false);
                };
                codec::validate_sort(expected, 32, false, control)?;
                codec::validate_sort(actual, 32, false, control)?;
                if expected != actual {
                    return Some(false);
                }
            }
            Some(true)
        } else {
            Some(
                matches!(symbol, Symbol::Named(_))
                    && executor
                        .ctx
                        .canonical_operator_binding_is_unambiguous(symbol.name()),
            )
        }
    }
}

fn name_table_matches(
    expected: &[(String, Vec<String>)],
    actual: &[(String, Vec<String>)],
    control: &mut codec::Control<'_>,
) -> Option<bool> {
    control.charge(expected.len().checked_add(actual.len())?, 0)?;
    if expected.len() != actual.len() {
        return Some(false);
    }
    for ((left, left_children), (right, right_children)) in expected.iter().zip(actual) {
        control.charge(left.len().checked_add(right.len())?, 0)?;
        if left != right || left_children.len() != right_children.len() {
            return Some(false);
        }
        control.charge(left_children.len(), 0)?;
        for (left, right) in left_children.iter().zip(right_children) {
            control.charge(left.len().checked_add(right.len())?, 0)?;
            if left != right {
                return Some(false);
            }
        }
    }
    Some(true)
}
