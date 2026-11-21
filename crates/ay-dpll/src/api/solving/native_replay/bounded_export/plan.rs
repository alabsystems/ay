// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Borrowed v1 records after raw source admission. No term/event/JSON clone.

use ay_core::{DatatypeField, DatatypeSort, Sort, TermData, TermId};
use ay_frontend::{DeclarationKind, SymbolInfo};

use super::super::{
    authenticated_native_constant_core_name_ref, authenticated_native_function_core_name_ref,
    native_replay_symbol_kind, NativeReplayEventKind,
};
use super::meter::{Meter, Result};
use crate::api::{
    NativeReplayExportError as Error, NativeReplayMetadata, NativeReplaySymbolKind, Solver,
};

#[derive(Clone, Copy)]
pub(super) enum Name<'a> {
    Direct(&'a str),
    Tester(&'a str),
}

impl Name<'_> {
    pub(super) fn equals(self, value: &str) -> bool {
        match self {
            Self::Direct(name) => name == value,
            Self::Tester(name) => value.strip_prefix("is-") == Some(name),
        }
    }
}

#[derive(Clone, Copy)]
pub(super) enum ApiSort<'a> {
    Core(&'a Sort),
    Datatype(&'a DatatypeSort),
    Bool,
}

#[derive(Clone, Copy)]
pub(super) enum Domain<'a> {
    Empty,
    Sorts(&'a [Sort]),
    Fields(&'a [DatatypeField]),
    Datatype(&'a DatatypeSort),
}

pub(super) struct Declaration<'a> {
    pub name: &'a str,
    pub core: &'a str,
    pub term: TermId,
    pub sort: &'a Sort,
}
pub(super) struct SortDeclaration<'a> {
    pub name: &'a str,
    pub core: &'a str,
}
pub(super) struct Function<'a> {
    pub name: &'a str,
    pub core: &'a str,
    pub domain: &'a [Sort],
    pub range: &'a Sort,
}
pub(super) struct Identity<'a> {
    pub surface: Name<'a>,
    pub core: &'a str,
    pub domain: Domain<'a>,
    pub range: ApiSort<'a>,
    pub info: &'a SymbolInfo,
    pub kind: NativeReplaySymbolKind,
    pub datatype: Option<(&'a str, &'a str)>,
}
pub(super) struct Assertion<'a> {
    pub term: TermId,
    pub name: Option<&'a str>,
    pub scope_depth: usize,
}

pub(super) struct Plan<'a> {
    pub solver: &'a Solver,
    pub metadata: &'a NativeReplayMetadata,
    pub logic: Option<&'a str>,
    pub created_unix_ms: u128,
    pub terms: Vec<TermId>,
    pub declarations: Vec<Declaration<'a>>,
    pub functions: Vec<Function<'a>>,
    pub sort_declarations: Vec<SortDeclaration<'a>>,
    pub identities: Vec<Identity<'a>>,
    pub datatype_carriers: Vec<&'a str>,
    pub assertions: Vec<Assertion<'a>>,
}

fn unavailable<T>(meter: &mut Meter<'_>, shape: &'static str) -> Result<T> {
    meter.fail(Error::UnsupportedSource { shape })
}

fn current_identity<'a>(
    solver: &'a Solver,
    symbols: &[(&'a String, &'a SymbolInfo)],
    surface: Name<'a>,
    core: &str,
) -> Option<&'a SymbolInfo> {
    let context = solver.executor.context();
    let mut matching = symbols.iter().filter(|(name, info)| {
        surface.equals(name) && context.symbol_identity_name(name, info) == core
    });
    let (_, info) = matching.next()?;
    if matching.next().is_some()
        || context.effective_declaration_kind(info.declaration_id())
            != Some(info.declaration_kind())
    {
        return None;
    }
    Some(*info)
}

pub(super) fn build<'a>(
    solver: &'a Solver,
    metadata: &'a NativeReplayMetadata,
    terms: Vec<TermId>,
    meter: &mut Meter<'_>,
) -> Result<Plan<'a>> {
    let context = solver.executor.context();
    let mut symbols = Vec::new();
    for entry in context.symbols_iter() {
        meter.push(&mut symbols, entry)?;
    }
    let mut plan = Plan {
        solver,
        metadata,
        logic: solver
            .executor
            .logic()
            .filter(|logic| !crate::logic_detection::declared_logic_routes_as_all(logic)),
        created_unix_ms: super::super::created_unix_ms(),
        terms,
        declarations: Vec::new(),
        functions: Vec::new(),
        sort_declarations: Vec::new(),
        identities: Vec::new(),
        datatype_carriers: Vec::new(),
        assertions: Vec::new(),
    };
    let mut reachable = Vec::new();
    for &term in &plan.terms {
        meter.push(&mut reachable, term)?;
    }
    reachable.sort_unstable();
    meter.charge(solver.var_names.capacity(), 0)?;
    for (&term, name) in &solver.var_names {
        meter.poll()?;
        if reachable.binary_search(&term).is_err() {
            continue;
        }
        let Some(sort) = solver.var_sorts.get(&term) else {
            return unavailable(meter, "native constant sort metadata");
        };
        let Some(core) = authenticated_native_constant_core_name_ref(solver, name, term) else {
            return unavailable(meter, "exact native constant identity");
        };
        let Some(info) = current_identity(solver, &symbols, Name::Direct(name), core) else {
            return unavailable(meter, "unique native constant identity");
        };
        meter.push(
            &mut plan.declarations,
            Declaration {
                name,
                core,
                term,
                sort,
            },
        )?;
        meter.push(
            &mut plan.identities,
            Identity {
                surface: Name::Direct(name),
                core,
                domain: Domain::Empty,
                range: ApiSort::Core(sort),
                info,
                kind: NativeReplaySymbolKind::Uninterpreted,
                datatype: None,
            },
        )?;
    }
    plan.declarations
        .sort_unstable_by_key(|declaration| declaration.term);

    let mut needed_functions = Vec::new();
    for &term in &plan.terms {
        meter.poll()?;
        if let TermData::App(ay_core::Symbol::Named(name), _) = solver.terms().get(term) {
            meter.push(&mut needed_functions, name.as_str())?;
        }
        if let Some(name) = solver.terms().get_as_array_func(term) {
            meter.push(&mut needed_functions, name)?;
        }
        if let Some((name, _)) = solver.terms().get_array_map(term) {
            meter.push(&mut needed_functions, name)?;
        }
    }
    for event in &solver.native_replay_events {
        meter.poll()?;
        let NativeReplayEventKind::DeclareFun {
            name,
            domain,
            range,
        } = &event.kind
        else {
            continue;
        };
        let core_key = solver
            .native_fun_signatures
            .get(name)
            .map_or(name.as_str(), |registration| {
                registration.core_name.as_str()
            });
        if !needed_functions.contains(&core_key) {
            continue;
        }
        if plan
            .functions
            .iter()
            .any(|old| old.name == name && old.domain == domain.as_slice() && old.range == range)
        {
            continue;
        }
        let Some(core) = authenticated_native_function_core_name_ref(solver, name, domain, range)
        else {
            return unavailable(meter, "exact native function identity");
        };
        let Some(info) = current_identity(solver, &symbols, Name::Direct(name), core) else {
            return unavailable(meter, "unique native function identity");
        };
        let Some(kind) = native_replay_symbol_kind(info.declaration_kind()) else {
            return unavailable(meter, "native function declaration kind");
        };
        meter.push(
            &mut plan.functions,
            Function {
                name,
                core,
                domain,
                range,
            },
        )?;
        meter.push(
            &mut plan.identities,
            Identity {
                surface: Name::Direct(name),
                core,
                domain: Domain::Sorts(domain),
                range: ApiSort::Core(range),
                info,
                kind,
                datatype: None,
            },
        )?;
    }

    // Native opaque declarations are global to assertion scopes. Retain
    // their original event order and exact allocated nominal identities;
    // source names alone never authenticate an engine sort.
    for event in &solver.native_replay_events {
        meter.poll()?;
        let NativeReplayEventKind::DeclareSort { name, core_name } = &event.kind else {
            continue;
        };
        super::meter::sort_lookup(context, name, meter)?;
        if !matches!(context.sort_definition(name), Some(Sort::Uninterpreted(core)) if core == core_name)
            || context.is_live_datatype_carrier(core_name)
            || context.sort_surface_name(core_name) != name.as_str()
        {
            return unavailable(meter, "exact native opaque sort identity");
        }
        meter.push(
            &mut plan.sort_declarations,
            SortDeclaration {
                name,
                core: core_name,
            },
        )?;
    }

    let mut datatypes = Vec::<&DatatypeSort>::new();
    for event in &solver.native_replay_events {
        for datatype in event.kind.datatypes() {
            meter.poll()?;
            if !datatypes.iter().any(|old| *old == datatype) {
                meter.push(&mut datatypes, datatype)?;
            }
        }
    }
    for datatype in datatypes {
        meter.poll()?;
        super::meter::sort_lookup(context, &datatype.name, meter)?;
        let Some(Sort::Uninterpreted(recorded_carrier)) = context.sort_definition(&datatype.name)
        else {
            return unavailable(meter, "native datatype sort definition");
        };
        meter.push(&mut plan.datatype_carriers, recorded_carrier.as_str())?;
        // Empty declarations still belong to the full event stream. They have
        // no member identities or signature-lowering scratch to authenticate.
        if datatype.constructors.is_empty() {
            continue;
        }
        // Signature lowering scratch is admitted before this bounded metadata
        // comparison. The v1 records themselves borrow their original sorts.
        let carrier = solver.lower_live_sort(&Sort::Datatype(datatype.clone()));
        let Sort::Uninterpreted(carrier_name) = &carrier else {
            return unavailable(meter, "native datatype carrier");
        };
        if !context.is_live_datatype_carrier(carrier_name) {
            return unavailable(meter, "live native datatype carrier");
        }
        // Borrow the equivalent live carrier spelling; no record refers to
        // temporary signature-lowering storage.
        let carrier_core = context
            .native_input_symbol_storage_iter()
            .find_map(|(_, info)| match &info.sort {
                Sort::Uninterpreted(name) if name == carrier_name => Some(name.as_str()),
                _ => None,
            });
        let Some(carrier_core) = carrier_core else {
            return unavailable(meter, "native datatype carrier identity");
        };
        for constructor in &datatype.constructors {
            meter.poll()?;
            let mut domain = Vec::new();
            for field in &constructor.fields {
                meter.push(&mut domain, solver.lower_live_sort(&field.sort))?;
            }
            let Some(info) =
                context.symbol_info_with_signature(&constructor.name, &domain, &carrier)
            else {
                return unavailable(meter, "native constructor signature");
            };
            let core = context.symbol_identity_name(&constructor.name, info);
            if info.declaration_kind() != DeclarationKind::DatatypeConstructor
                || !context
                    .constructor_metadata(core)
                    .is_some_and(|(owner, _)| owner == carrier_core)
                || !context
                    .exact_datatype_member_info(core)
                    .is_some_and(|exact| exact.declaration_id() == info.declaration_id())
            {
                return unavailable(meter, "exact native constructor provenance");
            }
            meter.push(
                &mut plan.identities,
                Identity {
                    surface: Name::Direct(&constructor.name),
                    core,
                    domain: Domain::Fields(&constructor.fields),
                    range: ApiSort::Datatype(datatype),
                    info,
                    kind: NativeReplaySymbolKind::DatatypeConstructor,
                    datatype: Some((&datatype.name, carrier_core)),
                },
            )?;
            let Some(selectors) = context.constructor_selectors(core) else {
                return unavailable(meter, "native selector identities");
            };
            if selectors.len() != constructor.fields.len() {
                return unavailable(meter, "native selector identity arity");
            }
            for (field, selector_core) in constructor.fields.iter().zip(selectors) {
                meter.poll()?;
                let Some(selector) = context.exact_datatype_member_info(selector_core) else {
                    return unavailable(meter, "exact native selector identity");
                };
                if selector.declaration_kind() != DeclarationKind::DatatypeSelector
                    || context
                        .dt_surface_name(selector_core)
                        .unwrap_or(selector_core)
                        != field.name
                    || selector.arg_sorts.as_slice() != std::slice::from_ref(&carrier)
                    || selector.sort != solver.lower_live_sort(&field.sort)
                {
                    return unavailable(meter, "exact native selector provenance");
                }
                meter.push(
                    &mut plan.identities,
                    Identity {
                        surface: Name::Direct(&field.name),
                        core: selector_core,
                        domain: Domain::Datatype(datatype),
                        range: ApiSort::Core(&field.sort),
                        info: selector,
                        kind: NativeReplaySymbolKind::DatatypeSelector,
                        datatype: Some((&datatype.name, carrier_core)),
                    },
                )?;
            }
            // Hidden datatype members remain exact even when their public
            // spelling was shadowed. Borrow the raw identity key after census.
            let tester = context
                .native_input_symbol_storage_iter()
                .find_map(|(key, info)| {
                    (key.strip_prefix("is-") == Some(core)
                        && info.declaration_kind() == DeclarationKind::DatatypeTester
                        && info.arg_sorts.as_slice() == std::slice::from_ref(&carrier)
                        && info.sort == Sort::Bool
                        && context
                            .exact_datatype_member_info(key)
                            .is_some_and(|exact| exact.declaration_id() == info.declaration_id())
                        && Name::Tester(&constructor.name)
                            .equals(context.dt_surface_name(key).unwrap_or(key)))
                    .then_some((key.as_str(), info))
                });
            let Some((tester_core, tester)) = tester else {
                return unavailable(meter, "exact native tester provenance");
            };
            meter.push(
                &mut plan.identities,
                Identity {
                    surface: Name::Tester(&constructor.name),
                    core: tester_core,
                    domain: Domain::Datatype(datatype),
                    range: ApiSort::Bool,
                    info: tester,
                    kind: NativeReplaySymbolKind::DatatypeTester,
                    datatype: Some((&datatype.name, carrier_core)),
                },
            )?;
        }
    }
    plan.identities
        .sort_unstable_by(|left, right| left.core.cmp(right.core));

    // Reconstruct occurrence metadata through the complete push/pop history
    // without copying names. Truncation follows the same event semantics as v1.
    let mut active = Vec::new();
    let mut scopes = Vec::new();
    for event in &solver.native_replay_events {
        meter.poll()?;
        match &event.kind {
            NativeReplayEventKind::Assert { term, name } => meter.push(
                &mut active,
                (*term, name.as_deref(), event.scope_depth as usize, false),
            )?,
            NativeReplayEventKind::Push => meter.push(&mut scopes, active.len())?,
            NativeReplayEventKind::Pop => {
                if let Some(start) = scopes.pop() {
                    active.truncate(start);
                }
            }
            NativeReplayEventKind::Reset | NativeReplayEventKind::ResetAssertions => {
                scopes.clear();
                active.clear();
            }
            _ => {}
        }
    }
    let mut boundaries = context.native_input_assertion_boundaries().peekable();
    let mut depth = 0usize;
    for (index, &term) in context.assertions.iter().enumerate() {
        while boundaries.peek().is_some_and(|boundary| index >= *boundary) {
            boundaries.next();
            if boundaries.peek().is_none() {
                break;
            }
            depth = depth.saturating_add(1);
            meter.poll()?;
        }
        meter.poll()?;
        let event = active
            .iter_mut()
            .find(|(candidate, _, _, used)| *candidate == term && !*used);
        let (name, scope_depth) = if let Some((_, name, depth, used)) = event {
            *used = true;
            (*name, *depth)
        } else {
            let occurrence = plan
                .assertions
                .iter()
                .filter(|old| old.term == term)
                .count();
            let name = solver
                .native_replay_events
                .iter()
                .filter_map(|event| match &event.kind {
                    NativeReplayEventKind::Assert {
                        term: candidate,
                        name,
                    } if *candidate == term => name.as_deref(),
                    _ => None,
                })
                .nth(occurrence);
            // The legacy field is the minimum active depth for this TermId,
            // even when the occurrence metadata was not retained.
            let mut current = 0usize;
            let mut limits = context.native_input_assertion_boundaries().peekable();
            let mut minimum = depth;
            for (position, candidate) in context.assertions.iter().enumerate() {
                while limits.peek().is_some_and(|limit| position >= *limit) {
                    limits.next();
                    if limits.peek().is_none() {
                        break;
                    }
                    current = current.saturating_add(1);
                }
                if *candidate == term {
                    minimum = minimum.min(current);
                }
            }
            (name, minimum)
        };
        meter.push(
            &mut plan.assertions,
            Assertion {
                term,
                name,
                scope_depth,
            },
        )?;
    }
    meter.poll()?;
    Ok(plan)
}
