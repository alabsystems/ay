// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Raw typed proof-instance DATA. No rewriting, source or theorem authority.

use super::*;
use crate::Symbol;
use std::mem::size_of;

#[cfg(test)]
mod tests;

impl TermStore {
    /// Construct a raw native proof-instance node under the caller's original
    /// owner. The separate ordinary fragment validator stays unchanged.
    ///
    /// Admits named Apps, Not/ITE and a nonempty bounded native quantifier;
    /// never Vars, literals, Lets, indexed symbols or datatype descriptors.
    /// Binder/trigger lists and every physical sort/name/edge are priced
    /// before comparison/hash/copy. This checks structural/live handles and
    /// basic Boolean shapes, not a UF interpretation or logical rule. The
    /// independent proof checker must rederive source substitution/duality.
    pub fn try_intern_native_proof_with_progress(
        &mut self,
        data: &TermData,
        sort: &Sort,
        progress: &mut dyn FnMut(usize, usize) -> bool,
    ) -> std::result::Result<TermId, ControlledTermInternError> {
        let mut admission = Admission {
            progress,
            refused: false,
        };
        admission.pay(0, 0)?;
        let result = (|| {
            let cost = admit(self, data, sort, &mut admission)?;
            self.intern_controlled_validated(data, sort, Some(&cost), &mut admission)
        })();
        let terminal = admission.pay(0, 0);
        match (result, terminal) {
            (Ok(id), Ok(())) => Ok(id),
            (Err(e), _) | (_, Err(e)) => Err(e),
        }
    }
    /// Copy one live admitted proof node and its actual arena sort. This is
    /// bounded data inspection, never a source/declaration adoption. Literal
    /// and Var leaves remain borrowed/unchanged in the substitution producer.
    pub fn try_copy_native_proof_node_with_progress(
        &self,
        id: TermId,
        progress: &mut dyn FnMut(usize, usize) -> bool,
    ) -> std::result::Result<(TermData, Sort), ControlledTermInternError> {
        let mut admission = Admission {
            progress,
            refused: false,
        };
        admission.pay(0, 0)?;
        let result = (|| {
            self.entry_stamp(id)
                .ok_or(ControlledTermInternError::InvalidInput)?;
            let data = self.get(id);
            let sort = self.sort(id);
            let cost = admit(self, data, sort, &mut admission)?;
            let payload = owned_payload(data)?.unwrap_or(0);
            admission.pay(
                cost.work
                    .checked_add(payload)
                    .ok_or(ControlledTermInternError::ResourceLimit)?,
                cost.bytes
                    .checked_add(payload)
                    .ok_or(ControlledTermInternError::ResourceLimit)?,
            )?;
            Ok((shape::copy(data)?, sort.clone()))
        })();
        let terminal = admission.pay(0, 0);
        match (result, terminal) {
            (Ok(node), Ok(())) => Ok(node),
            (Err(e), _) | (_, Err(e)) => Err(e),
        }
    }
}

fn admit(
    store: &TermStore,
    data: &TermData,
    sort: &Sort,
    admission: &mut Admission<'_>,
) -> Result<shape::SortCost> {
    if store.store_role != StoreRole::Producer {
        return Err(ControlledTermInternError::ReadOnlySnapshot);
    }
    let mut cost = shape::admit_owned_sort(sort, admission)?;
    match data {
        TermData::App(Symbol::Named(name), args) if name.len() <= 4096 && args.len() <= 64 => {
            admission.pay(
                name.len()
                    .checked_add(args.len())
                    .ok_or(ControlledTermInternError::ResourceLimit)?,
                0,
            )?;
            let mut child_work = 0usize;
            for &id in args {
                child_work = child_work
                    .checked_add(admit_child(store, id, admission)?.work)
                    .ok_or(ControlledTermInternError::ResourceLimit)?;
            }
            // Includes every borrowed recursive sort comparison performed by
            // the small reserved-Boolean signature guard below.
            admission.pay(
                child_work
                    .checked_add(cost.work)
                    .and_then(|n| n.checked_mul(4))
                    .ok_or(ControlledTermInternError::ResourceLimit)?,
                0,
            )?;
            if !boolean_signature(store, name, args, sort) {
                return Err(ControlledTermInternError::InvalidInput);
            }
            cost.work = cost
                .work
                .checked_add(name.len())
                .and_then(|n| n.checked_add(args.len()))
                .ok_or(ControlledTermInternError::ResourceLimit)?;
        }
        TermData::Not(id) => {
            admit_child(store, *id, admission)?;
            if sort != &Sort::Bool || store.sort(*id) != &Sort::Bool {
                return Err(ControlledTermInternError::InvalidInput);
            }
        }
        TermData::Ite(c, t, e) => {
            let mut work = cost.work;
            for id in [*c, *t, *e] {
                work = work
                    .checked_add(admit_child(store, id, admission)?.work)
                    .ok_or(ControlledTermInternError::ResourceLimit)?;
            }
            admission.pay(
                work.checked_mul(2)
                    .ok_or(ControlledTermInternError::ResourceLimit)?,
                0,
            )?;
            if store.sort(*c) != &Sort::Bool || store.sort(*t) != sort || store.sort(*e) != sort {
                return Err(ControlledTermInternError::InvalidInput);
            }
        }
        TermData::Forall(bindings, body, triggers) | TermData::Exists(bindings, body, triggers)
            if (1..=16).contains(&bindings.len()) && triggers.len() <= 64 =>
        {
            admit_child(store, *body, admission)?;
            if sort != &Sort::Bool || store.sort(*body) != &Sort::Bool {
                return Err(ControlledTermInternError::InvalidInput);
            }
            for group in triggers {
                if group.len() > 4096 {
                    return Err(ControlledTermInternError::UnsupportedFragment);
                }
                for &id in group {
                    admit_child(store, id, admission)?;
                }
            }
            for (position, (name, ty)) in bindings.iter().enumerate() {
                if name.len() > 4096 {
                    return Err(ControlledTermInternError::UnsupportedFragment);
                }
                admission.pay(name.len(), 0)?;
                for (prior, _) in &bindings[..position] {
                    admission.pay(
                        name.len()
                            .checked_add(prior.len())
                            .ok_or(ControlledTermInternError::ResourceLimit)?,
                        0,
                    )?;
                    if name == prior {
                        return Err(ControlledTermInternError::InvalidInput);
                    }
                }
                let field = shape::admit_owned_sort(ty, admission)?;
                cost.work = cost
                    .work
                    .checked_add(field.work)
                    .and_then(|n| n.checked_add(name.len()))
                    .ok_or(ControlledTermInternError::ResourceLimit)?;
                cost.bytes = cost
                    .bytes
                    .checked_add(field.bytes)
                    .and_then(|n| n.checked_add(name.len()))
                    .ok_or(ControlledTermInternError::ResourceLimit)?;
            }
            cost.work = cost
                .work
                .checked_add(bindings.len())
                .and_then(|n| n.checked_add(triggers.len()))
                .ok_or(ControlledTermInternError::ResourceLimit)?;
        }
        _ => return Err(ControlledTermInternError::UnsupportedFragment),
    }
    // Includes the admitted payload-volume census before common hashing,
    // collision checks, copy and scratch disposal.
    admission.pay(
        cost.work
            .checked_mul(2)
            .ok_or(ControlledTermInternError::ResourceLimit)?,
        cost.bytes,
    )?;
    Ok(cost)
}

fn admit_child(
    store: &TermStore,
    id: TermId,
    admission: &mut Admission<'_>,
) -> Result<shape::SortCost> {
    admission.pay(1, 0)?;
    store
        .entry_stamp(id)
        .ok_or(ControlledTermInternError::InvalidInput)?;
    shape::admit_owned_sort(store.sort(id), admission)
}

fn boolean_signature(store: &TermStore, name: &str, args: &[TermId], sort: &Sort) -> bool {
    match name {
        "and" | "or" => sort == &Sort::Bool && args.iter().all(|id| store.sort(*id) == &Sort::Bool),
        "=>" | "xor" => {
            sort == &Sort::Bool
                && args.len() == 2
                && args.iter().all(|id| store.sort(*id) == &Sort::Bool)
        }
        "=" | "distinct" => {
            sort == &Sort::Bool
                && args.len() >= 2
                && args[1..]
                    .iter()
                    .all(|id| store.sort(args[0]) == store.sort(*id))
        }
        // All other names are raw source applications. Their interpretation
        // remains the native context/checker's job, never this data factory's.
        _ => true,
    }
}

/// Called only AFTER native_proof validated/prepaid all borrowed metadata.
/// No public ordinary fragment accepts quantifiers through this helper.
pub(super) fn owned_payload(data: &TermData) -> Result<Option<usize>> {
    let bytes = match data {
        TermData::App(Symbol::Named(name), args) => {
            return Ok(Some(
                name.len()
                    .checked_add(
                        args.len()
                            .checked_mul(size_of::<TermId>())
                            .ok_or(ControlledTermInternError::ResourceLimit)?,
                    )
                    .ok_or(ControlledTermInternError::ResourceLimit)?,
            ))
        }
        TermData::Forall(bindings, _, triggers) | TermData::Exists(bindings, _, triggers) => {
            let mut bytes = bindings
                .len()
                .checked_mul(size_of::<(String, Sort)>())
                .ok_or(ControlledTermInternError::ResourceLimit)?;
            for (name, ty) in bindings {
                bytes = bytes
                    .checked_add(name.len())
                    .and_then(|n| n.checked_add(sort_storage(ty, 0)?))
                    .ok_or(ControlledTermInternError::ResourceLimit)?;
            }
            bytes = bytes
                .checked_add(
                    triggers
                        .len()
                        .checked_mul(size_of::<Vec<TermId>>())
                        .ok_or(ControlledTermInternError::ResourceLimit)?,
                )
                .ok_or(ControlledTermInternError::ResourceLimit)?;
            for group in triggers {
                bytes = bytes
                    .checked_add(
                        group
                            .len()
                            .checked_mul(size_of::<TermId>())
                            .ok_or(ControlledTermInternError::ResourceLimit)?,
                    )
                    .ok_or(ControlledTermInternError::ResourceLimit)?;
            }
            bytes
        }
        _ => return Ok(None),
    };
    Ok(Some(bytes))
}

fn sort_storage(sort: &Sort, depth: usize) -> Option<usize> {
    if depth > 128 {
        return None;
    }
    let extra = match sort {
        Sort::Uninterpreted(name) => name.len(),
        Sort::Array(a) => sort_storage(&a.index_sort, depth + 1)?
            .checked_add(sort_storage(&a.element_sort, depth + 1)?)?,
        Sort::Seq(element) => sort_storage(element, depth + 1)?,
        _ => 0,
    };
    size_of::<Sort>().checked_add(extra)
}
