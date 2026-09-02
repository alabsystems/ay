// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Exact typed reconstruction of array-valued datatype fields.

mod authority;
mod certificate;
mod certificate_members;
mod completion_capability;
mod constructor_sources;
mod extensionality_roots;
mod hard_equalities;
mod normalization;
mod observed_fields;
mod parser;
mod projection;
mod query_roots;

pub(super) use authority::{
    ArrayFieldClasses, AuthenticatedDatatypeArrayClass, AuthenticatedDatatypeArrayExtensionality,
    AuthenticatedDatatypeArrayMembers, AuthorizedDatatypeArrayCell,
    DatatypeArrayConstructionAuthorization, ExactDatatypeArrayClassAuthority,
    ExactDatatypeArrayFieldCompletion,
};
use hard_equalities::AuthoredArrayDefinition;
use normalization::{
    normalize_array_value, typed_array_value, typed_datatype_array_value, ArrayAccumulator,
    NormalizedArrayValue,
};
pub(super) use normalization::{
    normalize_datatype_array_value, NormalizedDatatypeArrayValue, SemanticNormalizationBudget,
};
#[cfg(test)]
use normalization::{same_array_value, same_datatype_array_value, same_value};
#[cfg(test)]
pub(super) use parser::sexpr_items;
pub(super) use parser::{
    parse_bounded_typed_array_text, TypedArrayParseBudget, MAX_TYPED_ARRAY_DEPTH,
};

use ay_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};
use ay_core::term::{Symbol, TermData};
use ay_core::{ArraySort, Sort, TermId};
use ay_model_check::ModelValue;

use super::datatype_cell_authority::exact_datatype_carrier_token;
use super::dt_construct::eval_to_mv;
use super::rendered_dt_guard::RenderedDatatypeGuard;
use super::rendered_dt_limits::SchemaSourceBudget;
use super::Model;
use crate::executor::Executor;

pub(super) const MAX_EXACT_ARRAY_FIELD_TERMS: usize = 4 * 1024;

/// Outcome of the narrow class-level reconstruction protocol.
pub(super) enum ExactDatatypeArrayFields {
    NotApplicable,
    Complete(ExactDatatypeArrayFieldCompletion),
    Rejected,
}

struct ExactClass {
    cell_sort: Sort,
    carrier: String,
    members: HashSet<TermId>,
    fields: Vec<(usize, String, Sort)>,
}

struct ConstructorArrayFieldSources {
    exact: Vec<TermId>,
    unresolved: bool,
}

impl Executor {
    /// Build one total value for every array field of an exact, same-sort,
    /// same-EUF-carrier single-constructor class. Any partial or contradictory
    /// field poisons the whole attempt.
    pub(super) fn exact_datatype_array_fields(
        &self,
        model: &Model,
        members: &HashSet<TermId>,
        ctor: &str,
        candidate_args: &[ModelValue],
        work: &mut usize,
    ) -> ExactDatatypeArrayFields {
        let class = match self.exact_array_field_class(model, members, ctor) {
            Ok(Some(class)) => class,
            Ok(None) => return ExactDatatypeArrayFields::NotApplicable,
            Err(()) => return ExactDatatypeArrayFields::Rejected,
        };
        let Some(required_terms) = self.datatype_array_field_required_terms() else {
            return ExactDatatypeArrayFields::Rejected;
        };
        let guard = RenderedDatatypeGuard::new(self);
        if !guard.is_bounded() {
            return ExactDatatypeArrayFields::Rejected;
        }
        let mut source_budget = SchemaSourceBudget::new();
        let Some(constructor_source_members) = self.datatype_array_constructor_source_members(
            &required_terms,
            &guard,
            work,
            &mut source_budget,
        ) else {
            return ExactDatatypeArrayFields::Rejected;
        };
        let mut field_evidence = Vec::with_capacity(class.fields.len());
        for (index, selector, sort) in &class.fields {
            let Some(apps) =
                self.selector_apps(model, &class, selector, sort, &required_terms, work)
            else {
                return ExactDatatypeArrayFields::Rejected;
            };
            let Some(sources) = self.constructor_array_field_sources(
                model,
                &class,
                ctor,
                *index,
                sort,
                &constructor_source_members,
                work,
            ) else {
                return ExactDatatypeArrayFields::Rejected;
            };
            // Preserve the legacy fail-closed model path for constructor
            // arguments such as a free array variable or a store over one.
            // Only a structurally exact finite array may mint W6 authority;
            // the final assertion gate remains authoritative for unresolved
            // sources.
            if sources.unresolved {
                return ExactDatatypeArrayFields::NotApplicable;
            }
            field_evidence.push((*index, sort, apps, sources.exact));
        }
        if !self.canonical_select_owner() {
            return ExactDatatypeArrayFields::Rejected;
        }
        if !charge_work(work, field_evidence.len()) {
            return ExactDatatypeArrayFields::Rejected;
        }
        let mut completed = HashMap::default();
        let mut unobserved_fields = HashSet::default();
        let mut parse_budget = TypedArrayParseBudget::new();
        let mut semantic_budget = SemanticNormalizationBudget::new();
        for (index, sort, apps, sources) in field_evidence {
            if apps.is_empty() {
                // This provenance bit records selector-observation absence.
                // An exact constructor argument may still authoritatively fix
                // the field and is revalidated separately by the certificate.
                unobserved_fields.insert(index);
            }
            let value = if apps.is_empty() && sources.is_empty() {
                self.validated_unobserved_array_candidate(
                    candidate_args.get(index),
                    sort,
                    &mut parse_budget,
                    &mut semantic_budget,
                )
            } else {
                self.reconstruct_array_field(
                    model,
                    sort,
                    apps,
                    sources,
                    &required_terms,
                    work,
                    &mut parse_budget,
                )
            };
            let Some(value) = value else {
                return ExactDatatypeArrayFields::Rejected;
            };
            completed.insert(index, value);
        }
        let Some(member_stamps) = class
            .members
            .iter()
            .map(|&member| {
                self.ctx
                    .terms
                    .entry_stamp(member)
                    .map(|stamp| (member, stamp))
            })
            .collect::<Option<HashMap<_, _>>>()
        else {
            return ExactDatatypeArrayFields::Rejected;
        };
        ExactDatatypeArrayFields::Complete(ExactDatatypeArrayFieldCompletion {
            fields: completed,
            authority: ExactDatatypeArrayClassAuthority {
                cell_sort: class.cell_sort,
                carrier: class.carrier,
                members: member_stamps,
                unobserved_fields,
            },
        })
    }

    fn exact_array_field_class(
        &self,
        model: &Model,
        members: &HashSet<TermId>,
        ctor: &str,
    ) -> Result<Option<ExactClass>, ()> {
        if members.is_empty() || members.len() > MAX_EXACT_ARRAY_FIELD_TERMS {
            return Ok(None);
        }
        if model.euf_model.is_none() {
            return Ok(None);
        }
        // `members` is the complete bounded class obligation. The EUF model is
        // an append-only solve artifact and may contain unrelated generated
        // rows; only the direct lookups below participate in this certificate.
        let first = *members.iter().next().ok_or(())?;
        self.ctx.terms.entry_stamp(first).ok_or(())?;
        let first_sort = self.ctx.terms.sort(first);
        let mut source_budget = SchemaSourceBudget::new();
        if !source_budget.charge_sort(first_sort) {
            return Err(());
        }
        let cell_sort = first_sort.clone();
        if members.iter().any(|&term| {
            self.ctx.terms.entry_stamp(term).is_none() || self.ctx.terms.sort(term) != &cell_sort
        }) {
            return Err(());
        }
        let guard = RenderedDatatypeGuard::new(self);
        let Some(name) = guard.datatype_name(&cell_sort) else {
            return Ok(None);
        };
        let constructors = self.ctx.datatype_constructors(name).ok_or(())?;
        if constructors.len() != 1 || constructors[0] != ctor {
            return Ok(None);
        }
        let fields = self.array_fields(ctor)?;
        if fields.is_empty() {
            return Ok(None);
        }
        let carrier = self.exact_class_carrier(model, members, &cell_sort, &guard)?;
        Ok(Some(ExactClass {
            cell_sort,
            carrier,
            members: members.clone(),
            fields,
        }))
    }

    fn array_fields(&self, ctor: &str) -> Result<Vec<(usize, String, Sort)>, ()> {
        let fields = self.ctx.constructor_selector_info(ctor).ok_or(())?;
        if fields.len() > MAX_EXACT_ARRAY_FIELD_TERMS {
            return Err(());
        }
        Ok(fields
            .iter()
            .enumerate()
            .filter_map(|(index, (selector, sort))| {
                matches!(sort, Sort::Array(_)).then_some((index, selector.clone(), sort.clone()))
            })
            .collect())
    }

    fn exact_class_carrier(
        &self,
        model: &Model,
        members: &HashSet<TermId>,
        cell_sort: &Sort,
        guard: &RenderedDatatypeGuard,
    ) -> Result<String, ()> {
        let euf = model.euf_model.as_ref().ok_or(())?;
        let constructor_tokens: HashSet<String> = self
            .ctx
            .datatype_iter()
            .flat_map(|(_, ctors)| ctors)
            .flat_map(|ctor| [ctor.clone(), self.dt_surface(ctor).to_string()])
            .collect();
        let mut carrier = None;
        let mut source_budget = SchemaSourceBudget::new();
        for &term in members {
            let candidate = euf.term_values.get(&term).ok_or(())?;
            if !source_budget.charge_name(candidate.len())
                || !exact_datatype_carrier_token(guard, &constructor_tokens, cell_sort, candidate)
            {
                return Err(());
            }
            if carrier.as_ref().is_some_and(|old| old != candidate) {
                return Err(());
            }
            carrier = Some(candidate.clone());
        }
        carrier.ok_or(())
    }

    fn exact_datatype_selector(&self, name: &str) -> bool {
        self.ctx
            .exact_datatype_member_info(name)
            .is_some_and(|info| {
                info.declaration_kind() == ay_frontend::DeclarationKind::DatatypeSelector
            })
    }

    fn canonical_select_owner(&self) -> bool {
        self.ctx
            .symbol_info_by_identity("select")
            .is_none_or(|info| {
                self.ctx.effective_declaration_kind(info.declaration_id())
                    == Some(ay_frontend::DeclarationKind::Theory)
            })
    }
}

fn charge_work(work: &mut usize, amount: usize) -> bool {
    let Some(next) = work.checked_add(amount) else {
        return false;
    };
    if next > MAX_EXACT_ARRAY_FIELD_TERMS {
        return false;
    }
    *work = next;
    true
}

#[cfg(test)]
mod tests;
