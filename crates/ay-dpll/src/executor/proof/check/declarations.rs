// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Owning declaration inventories, admitted before copying from sticky registries.
//!
//! These are data collectors, not proof or source-authority grants. Their caller
//! must share its cumulative callback with bundle construction and checking; a
//! later copy is another debit. Legacy unmetered collectors remain unchanged.

#[path = "declarations/storage.rs"]
mod storage;
#[cfg(test)]
#[path = "declarations/tests.rs"]
mod tests;

use ay_core::Sort;
use ay_proof::{DatatypeMemberSignature, ProofCheckError};

use crate::executor::Executor;

pub(in crate::executor::proof) use storage::Control;

pub(crate) type ProofDeclarationInventories = (
    Vec<(String, Vec<String>)>,
    Vec<(String, Vec<String>)>,
    Vec<DatatypeMemberSignature>,
);

type Collected<T> = Result<T, ProofCheckError>;

impl Executor {
    /// Copy the exact legacy datatype inventory under the caller's envelope.
    pub(crate) fn datatype_decls_for_strict_proof_with_progress(
        &self,
        progress: &mut dyn FnMut(usize, usize) -> bool,
    ) -> Collected<Vec<(String, Vec<String>)>> {
        Control::new(progress).run(|control| {
            let count = count(self.ctx.datatype_iter(), control)?;
            copy_registry(count, self.ctx.datatype_iter(), control)
        })
    }

    /// Preserve constructor iteration and field order, including retained scopes.
    pub(crate) fn ctor_selector_decls_for_strict_proof_with_progress(
        &self,
        progress: &mut dyn FnMut(usize, usize) -> bool,
    ) -> Collected<Vec<(String, Vec<String>)>> {
        Control::new(progress).run(|control| {
            let count = count(self.ctx.ctor_selectors_iter(), control)?;
            copy_registry(
                count,
                self.ctx
                    .ctor_selectors_iter()
                    .map(|(name, fields)| (name.as_str(), fields.as_slice())),
                control,
            )
        })
    }

    /// Preserve the legacy exact sticky identity lookup; a missing signature is
    /// absent inventory, never an omitted declaration or a weaker context.
    pub(crate) fn datatype_member_signatures_for_strict_proof_with_progress(
        &self,
        progress: &mut dyn FnMut(usize, usize) -> bool,
    ) -> Collected<Option<Vec<DatatypeMemberSignature>>> {
        Control::new(progress).run(|control| {
            let Some(count) = self.member_inventory_len(control)? else {
                return Ok(None);
            };
            let mut output = control.vector(count)?;
            for (_, constructors) in self.ctx.datatype_iter() {
                control.charge(1, 0)?;
                for constructor in constructors {
                    control.charge(1, 0)?;
                    control.charge(constructor.len(), 0)?;
                    let Some(fields) = self.ctx.constructor_selectors(constructor) else {
                        return Ok(None);
                    };
                    let tester_len = constructor
                        .len()
                        .checked_add(3)
                        .ok_or(ProofCheckError::ResourceLimit)?;
                    control.charge(tester_len, tester_len)?;
                    let mut tester = String::new();
                    tester
                        .try_reserve_exact(tester_len)
                        .map_err(|_| ProofCheckError::ResourceLimit)?;
                    tester.push_str("is-");
                    tester.push_str(constructor);
                    for identity in std::iter::once(constructor.as_str())
                        .chain(std::iter::once(tester.as_str()))
                        .chain(fields.iter().map(String::as_str))
                    {
                        control.charge(1, 0)?;
                        control.charge(identity.len(), 0)?;
                        let Some(info) = self.ctx.exact_datatype_member_info(identity) else {
                            return Ok(None);
                        };
                        output.push(copy_signature(
                            identity,
                            &info.arg_sorts,
                            &info.sort,
                            info.term,
                            control,
                        )?);
                    }
                }
            }
            Ok(Some(output))
        })
    }

    fn member_inventory_len(&self, control: &mut Control<'_>) -> Collected<Option<usize>> {
        let mut count = 0usize;
        for (_, constructors) in self.ctx.datatype_iter() {
            control.charge(1, 0)?;
            for constructor in constructors {
                control.charge(1, 0)?;
                control.charge(constructor.len(), 0)?;
                let Some(fields) = self.ctx.constructor_selectors(constructor) else {
                    return Ok(None);
                };
                count = count
                    .checked_add(fields.len())
                    .and_then(|n| n.checked_add(2))
                    .ok_or(ProofCheckError::ResourceLimit)?;
            }
        }
        Ok(Some(count))
    }
}

fn count<I: Iterator>(values: I, control: &mut Control<'_>) -> Collected<usize> {
    let mut count = 0usize;
    for _ in values {
        control.charge(1, 0)?;
        count = count.checked_add(1).ok_or(ProofCheckError::ResourceLimit)?;
    }
    Ok(count)
}

pub(in crate::executor::proof) fn copy_registry<'a>(
    count: usize,
    rows: impl Iterator<Item = (&'a str, &'a [String])>,
    control: &mut Control<'_>,
) -> Collected<Vec<(String, Vec<String>)>> {
    let mut output = control.vector(count)?;
    for (name, fields) in rows {
        if output.len() == count {
            return Err(ProofCheckError::ResourceLimit);
        }
        let name = control.string(name)?;
        let mut copied = control.vector(fields.len())?;
        for field in fields {
            copied.push(control.string(field)?);
        }
        output.push((name, copied));
    }
    if output.len() != count {
        return Err(ProofCheckError::ResourceLimit);
    }
    Ok(output)
}

pub(in crate::executor::proof) fn copy_signatures(
    signatures: &[DatatypeMemberSignature],
    control: &mut Control<'_>,
) -> Collected<Vec<DatatypeMemberSignature>> {
    let mut output = control.vector(signatures.len())?;
    for signature in signatures {
        output.push(copy_signature(
            &signature.identity,
            &signature.argument_sorts,
            &signature.result_sort,
            signature.nullary_term,
            control,
        )?);
    }
    Ok(output)
}

fn copy_signature(
    identity: &str,
    arguments: &[Sort],
    result: &Sort,
    nullary_term: Option<ay_core::TermId>,
    control: &mut Control<'_>,
) -> Collected<DatatypeMemberSignature> {
    let identity = control.string(identity)?;
    let mut argument_sorts = control.vector(arguments.len())?;
    for sort in arguments {
        control.sort(sort, 0)?;
        argument_sorts.push(sort.clone());
    }
    control.sort(result, 0)?;
    Ok(DatatypeMemberSignature {
        identity,
        argument_sorts,
        result_sort: result.clone(),
        nullary_term,
    })
}
