// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Live declaration ownership for the typed native proof snapshot.
//! Sticky datatype definitions and current source bindings are distinct: old
//! retained terms keep their original member identity after scope rollback.

use super::{codec, Executor, TermEntryStamp};
use ay_core::{Sort, TermData};
use ay_frontend::{DeclarationId, DeclarationKind, SymbolInfo};
use ay_proof::DatatypeMemberSignature;

#[derive(Clone, Debug)]
struct MemberBinding {
    declaration: DeclarationId,
    kind: DeclarationKind,
    nullary_entry: Option<TermEntryStamp>,
}

#[derive(Clone, Debug)]
pub(super) struct NativeDatatypeContext {
    declarations: Vec<(String, Vec<String>)>,
    selectors: Vec<(String, Vec<String>)>,
    signatures: Vec<DatatypeMemberSignature>,
    members: Vec<MemberBinding>,
    live_bindings: Vec<(String, usize)>,
}

impl NativeDatatypeContext {
    pub(super) fn capture(executor: &Executor, control: &mut codec::Control<'_>) -> Option<Self> {
        let declarations = executor
            .datatype_decls_for_strict_proof_with_progress(&mut |w, b| {
                control.charge(w, b).is_some()
            })
            .ok()?;
        let selectors = executor
            .ctor_selector_decls_for_strict_proof_with_progress(&mut |w, b| {
                control.charge(w, b).is_some()
            })
            .ok()?;
        let signatures = executor
            .datatype_member_signatures_for_strict_proof_with_progress(&mut |w, b| {
                control.charge(w, b).is_some()
            })
            .ok()??;
        if declarations.len() > super::MAX_SOURCE_DECLARATIONS
            || signatures.len() > super::MAX_SOURCE_DECLARATIONS
        {
            return None;
        }
        control.charge(
            signatures.len(),
            signatures
                .len()
                .checked_mul(std::mem::size_of::<MemberBinding>())?,
        )?;
        let mut members = Vec::new();
        members.try_reserve_exact(signatures.len()).ok()?;
        for signature in &signatures {
            control.charge(signature.identity.len(), 0)?;
            let info = executor
                .ctx
                .exact_datatype_member_info(&signature.identity)?;
            let kind = info.declaration_kind();
            if !matches!(
                kind,
                DeclarationKind::DatatypeConstructor
                    | DeclarationKind::DatatypeSelector
                    | DeclarationKind::DatatypeTester
            ) || info.arg_sorts != signature.argument_sorts
                || info.sort != signature.result_sort
                || info.term != signature.nullary_term
            {
                return None;
            }
            let nullary_entry = match signature.nullary_term {
                Some(term) => {
                    let entry = executor.ctx.terms.entry_stamp(term)?;
                    if kind != DeclarationKind::DatatypeConstructor
                        || !signature.argument_sorts.is_empty()
                        || executor.ctx.terms.sort(term) != &signature.result_sort
                        || !matches!(executor.ctx.terms.get(term), TermData::Var(name, _) if name == &signature.identity)
                    {
                        return None;
                    }
                    Some(entry)
                }
                None => None,
            };
            members.push(MemberBinding {
                declaration: info.declaration_id().clone(),
                kind,
                nullary_entry,
            });
        }
        let mut captured = Self {
            declarations,
            selectors,
            signatures,
            members,
            live_bindings: Vec::new(),
        };
        for signature in &captured.signatures {
            captured.admits_sort(&signature.result_sort, control)?;
            for sort in &signature.argument_sorts {
                captured.admits_sort(sort, control)?;
            }
        }
        let binding_bound = if captured.members.is_empty() {
            0
        } else {
            executor
                .ctx
                .symbols_iter()
                .size_hint()
                .1?
                .min(super::MAX_SOURCE_DECLARATIONS)
        };
        control.charge(
            binding_bound,
            binding_bound.checked_mul(std::mem::size_of::<(String, usize)>())?,
        )?;
        captured
            .live_bindings
            .try_reserve_exact(binding_bound)
            .ok()?;
        for (surface, info) in executor.ctx.symbols_iter() {
            control.charge(captured.members.len().checked_add(1)?, 0)?;
            let Some(index) = captured
                .members
                .iter()
                .position(|member| &member.declaration == info.declaration_id())
            else {
                continue;
            };
            if !captured.contains_binding(executor, surface, info) {
                return None;
            }
            if captured.live_bindings.len() >= binding_bound {
                return None;
            }
            control.charge(surface.len(), surface.len())?;
            captured.live_bindings.push((surface.clone(), index));
        }
        control.charge(captured.live_bindings.len(), 0)?;
        let longest = captured
            .live_bindings
            .iter()
            .map(|(name, _)| name.len())
            .max()
            .unwrap_or(0);
        control.charge(
            captured
                .live_bindings
                .len()
                .checked_mul(captured.live_bindings.len())?
                .checked_mul(longest.checked_add(1)?)?,
            0,
        )?;
        captured
            .live_bindings
            .sort_unstable_by(|a, b| a.0.cmp(&b.0));
        Some(captured)
    }

    pub(super) fn declarations(&self) -> &[(String, Vec<String>)] {
        &self.declarations
    }

    pub(super) fn selectors(&self) -> &[(String, Vec<String>)] {
        &self.selectors
    }

    pub(super) fn signatures(&self) -> &[DatatypeMemberSignature] {
        &self.signatures
    }

    pub(super) fn live_bindings(&self) -> &[(String, usize)] {
        &self.live_bindings
    }

    /// An ordinary source binding may be skipped only when its actual opaque
    /// declaration identity is one of the captured native datatype members.
    pub(super) fn contains_binding(
        &self,
        executor: &Executor,
        surface: &str,
        info: &SymbolInfo,
    ) -> bool {
        let identity = executor.ctx.symbol_identity_name(surface, info);
        self.signatures
            .iter()
            .zip(&self.members)
            .any(|(signature, binding)| {
                &binding.declaration == info.declaration_id()
                    && signature.identity == identity
                    && binding.kind == info.declaration_kind()
                    && signature.argument_sorts == info.arg_sorts
                    && signature.result_sort == info.sort
                    && signature.nullary_term == info.term
            })
    }

    /// This first native source slice admits actual registered datatype
    /// carriers. Unknown nominal names remain unsupported; an opaque sort
    /// requires the independently owned native declaration event capability.
    pub(super) fn admits_sort(&self, sort: &Sort, control: &mut codec::Control<'_>) -> Option<()> {
        codec::validate_sort(sort, 32, false, control)?;
        self.admits_sort_inner(sort, control)
    }

    fn admits_sort_inner(&self, sort: &Sort, control: &mut codec::Control<'_>) -> Option<()> {
        control.charge(1, 0)?;
        match sort {
            Sort::Uninterpreted(name) => {
                control.charge(
                    self.declarations
                        .len()
                        .checked_mul(name.len().checked_add(1)?)?,
                    0,
                )?;
                self.declarations
                    .iter()
                    .any(|(carrier, _)| carrier == name)
                    .then_some(())
            }
            Sort::Array(array) => {
                self.admits_sort_inner(&array.index_sort, control)?;
                self.admits_sort_inner(&array.element_sort, control)
            }
            Sort::Seq(element) => self.admits_sort_inner(element, control),
            Sort::Bool
            | Sort::Int
            | Sort::Real
            | Sort::BitVec(_)
            | Sort::String
            | Sort::RegLan
            | Sort::FloatingPoint(..)
            | Sort::Char => Some(()),
            _ => None,
        }
    }

    pub(super) fn is_current(&self, executor: &Executor) -> bool {
        // The enclosing source context/metadata generations must match before
        // this bounded identity check. Definitions are sticky, so current
        // source-name visibility is deliberately not substituted for identity.
        self.signatures
            .iter()
            .zip(&self.members)
            .all(|(signature, binding)| {
                executor
                    .ctx
                    .exact_datatype_member_info(&signature.identity)
                    .is_some_and(|info| {
                        info.declaration_id() == &binding.declaration
                            && info.declaration_kind() == binding.kind
                            && info.arg_sorts == signature.argument_sorts
                            && info.sort == signature.result_sort
                            && info.term == signature.nullary_term
                            && signature
                                .nullary_term
                                .map(|term| executor.ctx.terms.entry_stamp(term))
                                == binding.nullary_entry.map(Some)
                    })
            })
    }
}
