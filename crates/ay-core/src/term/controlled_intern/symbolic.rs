// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Bounded structural nodes for total symbolic-model bodies. This API checks
//! handles and copy/hash safety, never an operator meaning or source grant.

use super::*;
use crate::term::Symbol;
use std::mem::size_of;

#[cfg(test)]
mod tests;

impl TermStore {
    /// Physical allowance for a caller-metered declaration-identity lookup.
    /// Retired identities remain registered after source pop. This count is
    /// resource metadata only and grants no declaration or operator meaning.
    #[doc(hidden)]
    pub fn declared_function_lookup_work(&self, incoming_bytes: usize) -> Option<usize> {
        crate::kani_compat::hash_table_cost::string_lookup::<(String, ())>(
            self.declared_functions.allocation_size(),
            self.declared_functions.len(),
            incoming_bytes,
        )
    }

    /// Intern a bounded Bool/Int/Real/Array model-body node under the SAME
    /// caller-owned allowance. Variables/freshness and binders are separate;
    /// no caller numeric variable identity, indexed head or datatype descriptor
    /// is admitted. Node typing and source/model semantics remain the caller's
    /// responsibility. Refusal may retain inert reservation/arena history.
    pub fn try_intern_symbolic_with_progress(
        &mut self,
        term: &TermData,
        sort: &Sort,
        progress: &mut dyn FnMut(usize, usize) -> bool,
    ) -> std::result::Result<TermId, ControlledTermInternError> {
        let mut admission = Admission {
            progress,
            refused: false,
        };
        admission.pay(0, 0)?;
        let result = (|| {
            if self.store_role != StoreRole::Producer {
                return Err(ControlledTermInternError::ReadOnlySnapshot);
            }
            let mut cost = sort_cost(sort, &mut admission, 0)?;
            let children: &[TermId] = match term {
                TermData::Const(Constant::Bool(_)) if sort == &Sort::Bool => &[],
                TermData::Const(Constant::Int(_)) if sort == &Sort::Int => &[],
                TermData::Const(Constant::Rational(value)) if sort == &Sort::Real => {
                    super::rational::admit(&value.0, &mut admission)?;
                    &[]
                }
                TermData::App(Symbol::Named(name), args)
                    if name.len() <= 256 && args.len() <= 256 =>
                {
                    admission.pay(name.len().saturating_add(args.len()), 0)?;
                    cost.work = cost
                        .work
                        .checked_add(name.len())
                        .and_then(|n| n.checked_add(args.len()))
                        .ok_or(ControlledTermInternError::ResourceLimit)?;
                    args
                }
                TermData::Not(inner) => std::slice::from_ref(inner),
                TermData::Ite(c, t, e) => {
                    for &child in [*c, *t, *e].iter() {
                        self.entry_stamp(child)
                            .ok_or(ControlledTermInternError::InvalidInput)?;
                        sort_cost(self.sort(child), &mut admission, 0)?;
                    }
                    if self.sort(*c) != &Sort::Bool
                        || self.sort(*t) != sort
                        || self.sort(*e) != sort
                    {
                        return Err(ControlledTermInternError::InvalidInput);
                    }
                    &[]
                }
                _ => return Err(ControlledTermInternError::UnsupportedFragment),
            };
            for &child in children {
                self.entry_stamp(child)
                    .ok_or(ControlledTermInternError::InvalidInput)?;
                sort_cost(self.sort(child), &mut admission, 0)?;
            }
            if let TermData::Not(child) = term {
                if sort != &Sort::Bool || self.sort(*child) != &Sort::Bool {
                    return Err(ControlledTermInternError::InvalidInput);
                }
            }
            self.intern_controlled_validated(term, sort, Some(&cost), &mut admission)
        })();
        let final_poll = admission.pay(0, 0);
        match (result, final_poll) {
            (Ok(term), Ok(())) => Ok(term),
            (Err(error), _) | (_, Err(error)) => Err(error),
        }
    }
}

fn sort_cost(sort: &Sort, admission: &mut Admission<'_>, depth: usize) -> Result<shape::SortCost> {
    if depth > 128 {
        return Err(ControlledTermInternError::ResourceLimit);
    }
    admission.pay(1, 0)?;
    let mut cost = shape::SortCost {
        work: 1,
        bytes: size_of::<Sort>(),
    };
    match sort {
        Sort::Bool | Sort::Int | Sort::Real => {}
        Sort::Array(array) => {
            for child in [&array.index_sort, &array.element_sort] {
                let child = sort_cost(child, admission, depth + 1)?;
                cost.work = cost
                    .work
                    .checked_add(child.work)
                    .ok_or(ControlledTermInternError::ResourceLimit)?;
                cost.bytes = cost
                    .bytes
                    .checked_add(child.bytes)
                    .ok_or(ControlledTermInternError::ResourceLimit)?;
            }
        }
        _ => return Err(ControlledTermInternError::UnsupportedFragment),
    }
    Ok(cost)
}
