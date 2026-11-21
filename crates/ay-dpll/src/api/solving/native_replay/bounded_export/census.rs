// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Borrowed source admission before header scratch or JSON output allocation.

use std::mem::size_of;

use ay_core::{
    Constant, DatatypeConstructor, DatatypeField, DatatypeSort, Sort, Symbol, TermData, TermId,
};
use ay_frontend::PublicSort;

use super::super::{HashMap, NativeReplayEventKind};
use super::meter::{Meter, Result};
use crate::api::{NativeReplayExportError as Error, NativeReplayMetadata, Solver};

#[derive(Clone, Copy, Default)]
struct Shape {
    bytes: usize,
    nodes: usize,
}

impl Shape {
    fn add(&mut self, other: Self) {
        self.bytes = self.bytes.saturating_add(other.bytes);
        self.nodes = self.nodes.saturating_add(other.nodes);
    }
}

enum Raw<'a> {
    Sort(&'a Sort),
    Public(&'a PublicSort),
    Datatype(&'a DatatypeSort),
    Constructor(&'a DatatypeConstructor),
    Field(&'a DatatypeField),
}

fn text(value: &str, meter: &mut Meter<'_>) -> Result<Shape> {
    meter.charge(value.len().saturating_add(1), 0)?;
    Ok(Shape {
        bytes: value.len(),
        nodes: 1,
    })
}

fn payload(root: Raw<'_>, meter: &mut Meter<'_>) -> Result<Shape> {
    let mut pending = Vec::new();
    meter.push(&mut pending, (root, 1usize))?;
    let mut shape = Shape::default();
    while let Some((raw, depth)) = pending.pop() {
        meter.depth(depth)?;
        // Native v1's recursive sort codecs/readers have a finite nesting
        // envelope independently of the caller's iterative term-DAG limit.
        if depth > 128 {
            return meter.fail(Error::Limit {
                resource: crate::api::NativeReplayExportResource::Depth,
                limit: 128,
                requested: depth,
            });
        }
        shape.nodes = shape.nodes.saturating_add(1);
        match raw {
            Raw::Sort(sort) => {
                shape.bytes = shape.bytes.saturating_add(size_of::<Sort>());
                match sort {
                    Sort::Bool
                    | Sort::Int
                    | Sort::Real
                    | Sort::String
                    | Sort::RegLan
                    | Sort::FloatingPoint(_, _)
                    | Sort::BitVec(_)
                    | Sort::Char => {}
                    Sort::Uninterpreted(name)
                    | Sort::TypeVar(name)
                    | Sort::FiniteDomain(name, _) => shape.add(text(name, meter)?),
                    Sort::Array(array) => {
                        meter.push(
                            &mut pending,
                            (Raw::Sort(&array.index_sort), depth.saturating_add(1)),
                        )?;
                        meter.push(
                            &mut pending,
                            (Raw::Sort(&array.element_sort), depth.saturating_add(1)),
                        )?;
                    }
                    Sort::Seq(element) => {
                        meter.push(&mut pending, (Raw::Sort(element), depth.saturating_add(1)))?
                    }
                    Sort::Datatype(datatype) => meter.push(
                        &mut pending,
                        (Raw::Datatype(datatype), depth.saturating_add(1)),
                    )?,
                    _ => {
                        return meter.fail(Error::UnsupportedSource {
                            shape: "sort outside native v1",
                        })
                    }
                }
            }
            Raw::Public(sort) => {
                shape.bytes = shape.bytes.saturating_add(size_of::<PublicSort>());
                match sort {
                    PublicSort::Core(sort) => {
                        meter.push(&mut pending, (Raw::Sort(sort), depth.saturating_add(1)))?
                    }
                    PublicSort::Array(index, element) => {
                        meter.push(&mut pending, (Raw::Public(index), depth.saturating_add(1)))?;
                        meter.push(
                            &mut pending,
                            (Raw::Public(element), depth.saturating_add(1)),
                        )?;
                    }
                    PublicSort::Seq(element)
                    | PublicSort::FiniteSet(element)
                    | PublicSort::AmbiguousSet(element) => {
                        meter.push(
                            &mut pending,
                            (Raw::Public(element), depth.saturating_add(1)),
                        )?;
                    }
                    PublicSort::Unknown => {}
                    _ => {
                        return meter.fail(Error::UnsupportedSource {
                            shape: "public sort outside native v1",
                        })
                    }
                }
            }
            Raw::Datatype(datatype) => {
                shape.add(text(&datatype.name, meter)?);
                meter.charge(datatype.constructors.len(), 0)?;
                for constructor in &datatype.constructors {
                    meter.push(
                        &mut pending,
                        (Raw::Constructor(constructor), depth.saturating_add(1)),
                    )?;
                }
            }
            Raw::Constructor(constructor) => {
                shape.bytes = shape.bytes.saturating_add(size_of::<DatatypeConstructor>());
                shape.add(text(&constructor.name, meter)?);
                meter.charge(constructor.fields.len(), 0)?;
                for field in &constructor.fields {
                    meter.push(&mut pending, (Raw::Field(field), depth.saturating_add(1)))?;
                }
            }
            Raw::Field(field) => {
                shape.bytes = shape.bytes.saturating_add(size_of::<DatatypeField>());
                shape.add(text(&field.name, meter)?);
                meter.push(
                    &mut pending,
                    (Raw::Sort(&field.sort), depth.saturating_add(1)),
                )?;
            }
        }
    }
    Ok(shape)
}

fn bigint(value: &num_bigint::BigInt, meter: &mut Meter<'_>) -> Result<Shape> {
    let bits = usize::try_from(value.bits()).unwrap_or(usize::MAX);
    // Decimal conversion uses repeated multi-limb division. Charging a square
    // of the bit count conservatively covers it before Display/to_string can
    // allocate or perform that conversion. This is work, not a width policy.
    meter.charge(
        bits.saturating_mul(bits)
            .saturating_mul(2)
            .saturating_add(1),
        bits.saturating_mul(16).saturating_add(512),
    )?;
    Ok(Shape {
        bytes: bits.saturating_add(7) / 8 + 64,
        nodes: 1,
    })
}

fn term_payload(data: &TermData, meter: &mut Meter<'_>) -> Result<Shape> {
    let mut shape = Shape {
        bytes: size_of::<TermData>(),
        nodes: 1,
    };
    match data {
        TermData::Const(value) => match value {
            Constant::Bool(_) => {}
            Constant::Int(value) | Constant::BitVec { value, .. } => {
                shape.add(bigint(value, meter)?)
            }
            Constant::Rational(value) => {
                shape.add(bigint(value.0.numer(), meter)?);
                shape.add(bigint(value.0.denom(), meter)?);
            }
            Constant::String(value) => shape.add(text(value, meter)?),
            _ => {
                return meter.fail(Error::UnsupportedSource {
                    shape: "constant outside native v1",
                })
            }
        },
        TermData::Var(name, _) => shape.add(text(name, meter)?),
        TermData::App(symbol, args) => {
            meter.charge(args.len(), 0)?;
            shape.bytes = shape
                .bytes
                .saturating_add(args.len().saturating_mul(size_of::<TermId>()));
            match symbol {
                Symbol::Named(name) => shape.add(text(name, meter)?),
                Symbol::Indexed(name, indices) => {
                    shape.add(text(name, meter)?);
                    meter.charge(indices.len(), 0)?;
                    shape.bytes = shape
                        .bytes
                        .saturating_add(indices.len().saturating_mul(size_of::<u32>()));
                }
                _ => {
                    return meter.fail(Error::UnsupportedSource {
                        shape: "symbol outside native v1",
                    })
                }
            }
        }
        TermData::Let(bindings, _) => {
            meter.charge(bindings.len(), 0)?;
            for (name, _) in bindings {
                shape.add(text(name, meter)?);
            }
            shape.bytes = shape
                .bytes
                .saturating_add(bindings.len().saturating_mul(size_of::<(String, TermId)>()));
        }
        TermData::Not(_) | TermData::Ite(_, _, _) => {}
        TermData::Forall(vars, _, triggers) | TermData::Exists(vars, _, triggers) => {
            meter.charge(vars.len().saturating_add(triggers.len()), 0)?;
            shape.bytes = shape
                .bytes
                .saturating_add(vars.len().saturating_mul(size_of::<(String, Sort)>()));
            for (name, sort) in vars {
                shape.add(text(name, meter)?);
                shape.add(payload(Raw::Sort(sort), meter)?);
            }
            for trigger in triggers {
                meter.charge(trigger.len(), 0)?;
                shape.bytes = shape
                    .bytes
                    .saturating_add(trigger.len().saturating_mul(size_of::<TermId>()))
                    .saturating_add(size_of::<Vec<TermId>>());
            }
        }
        _ => {
            return meter.fail(Error::UnsupportedSource {
                shape: "term outside native v1",
            })
        }
    }
    Ok(shape)
}

fn children(data: &TermData, mut visit: impl FnMut(TermId) -> Result<()>) -> Result<()> {
    match data {
        TermData::Const(_) | TermData::Var(_, _) => {}
        TermData::App(_, args) => {
            for &arg in args {
                visit(arg)?;
            }
        }
        TermData::Let(bindings, body) => {
            for (_, value) in bindings {
                visit(*value)?;
            }
            visit(*body)?;
        }
        TermData::Not(inner) => visit(*inner)?,
        TermData::Ite(condition, yes, no) => {
            visit(*condition)?;
            visit(*yes)?;
            visit(*no)?;
        }
        TermData::Forall(_, body, triggers) | TermData::Exists(_, body, triggers) => {
            visit(*body)?;
            for trigger in triggers {
                for &term in trigger {
                    visit(term)?;
                }
            }
        }
        _ => {
            return Err(Error::UnsupportedSource {
                shape: "term dependency outside native v1",
            })
        }
    }
    Ok(())
}

fn reserve_nodes(nodes: &mut HashMap<TermId, Option<usize>>, meter: &mut Meter<'_>) -> Result<()> {
    if nodes.len() < nodes.capacity() {
        return Ok(());
    }
    let capacity = nodes.len().saturating_add(1).saturating_mul(2).max(8);
    // Prepay hashbrown buckets and control bytes before reserve. The logical
    // Four requested-entry allowances cover load-factor expansion followed
    // by power-of-two bucket rounding (two alone can underpay, e.g.30->64).
    meter.charge(
        nodes
            .capacity()
            .saturating_mul(2)
            .saturating_add(capacity.saturating_mul(4)),
        capacity
            .saturating_mul(4)
            .saturating_mul(size_of::<(TermId, Option<usize>)>() + 1)
            .saturating_add(64),
    )?;
    if nodes
        .try_reserve(capacity.saturating_sub(nodes.len()))
        .is_err()
    {
        return meter.fail(Error::Allocation);
    }
    Ok(())
}

/// Prepay collision/probe worst cases before using our private state table.
/// Term IDs have fixed-size hashing and equality payloads.
fn probe_nodes(nodes: &HashMap<TermId, Option<usize>>, meter: &mut Meter<'_>) -> Result<()> {
    meter.charge(nodes.capacity().saturating_mul(2).saturating_add(8), 0)
}

/// An input admission bound. No pointer/hash here is proof authority.
pub(super) struct Admission {
    pub(super) ordered_terms: Vec<TermId>,
    header_work: usize,
    header_storage: usize,
}

impl Admission {
    pub(super) fn charge_headers(&self, meter: &mut Meter<'_>) -> Result<()> {
        meter.charge(self.header_work, self.header_storage)
    }
}

pub(super) fn admit(
    solver: &Solver,
    metadata: &NativeReplayMetadata,
    meter: &mut Meter<'_>,
) -> Result<Admission> {
    for value in [
        &metadata.consumer,
        &metadata.consumer_revision,
        &metadata.fixture_path,
        &metadata.function_path,
        &metadata.source_span,
        &metadata.obligation_kind,
        &metadata.notes,
    ]
    .into_iter()
    .flatten()
    {
        text(value, meter)?;
    }
    if let Some(logic) = solver.executor.logic() {
        text(logic, meter)?;
    }
    let context = solver.executor.context();
    let registry_capacity = context.native_input_symbol_storage_capacity();
    meter.charge(registry_capacity.saturating_mul(2), 0)?;
    let mut registry = Shape::default();
    let mut max_signature = Shape::default();
    for (name, info) in context.native_input_symbol_storage_iter() {
        let mut item = text(name, meter)?;
        if let Some(name) = &info.internal_name {
            item.add(text(name, meter)?);
        }
        item.add(payload(Raw::Sort(&info.sort), meter)?);
        item.add(payload(Raw::Public(&info.public_sort), meter)?);
        meter.charge(
            info.arg_sorts
                .len()
                .saturating_add(info.public_arg_sorts.len()),
            0,
        )?;
        for sort in &info.arg_sorts {
            item.add(payload(Raw::Sort(sort), meter)?);
        }
        for sort in &info.public_arg_sorts {
            item.add(payload(Raw::Public(sort), meter)?);
        }
        registry.add(item);
        max_signature.bytes = max_signature.bytes.max(item.bytes);
    }
    let mut sort_definitions = Shape::default();
    let mut max_sort_definition = Shape::default();
    let sort_capacity = context.native_input_sort_storage_capacity();
    meter.charge(sort_capacity.saturating_mul(2), 0)?;
    for (name, sort) in context.native_input_sort_storage_iter() {
        let mut item = text(name, meter)?;
        item.add(payload(Raw::Sort(sort), meter)?);
        sort_definitions.add(item);
        max_sort_definition.bytes = max_sort_definition.bytes.max(item.bytes);
    }
    meter.charge(
        solver
            .var_names
            .capacity()
            .saturating_add(solver.var_sorts.capacity())
            .saturating_add(solver.native_fun_signatures.capacity())
            .saturating_mul(2),
        0,
    )?;
    for (&term, name) in &solver.var_names {
        if solver.terms().entry_stamp(term).is_none() {
            return meter.fail(Error::InvalidTerm { term: term.0 });
        }
        text(name, meter)?;
        term_payload(solver.terms().get(term), meter)?;
        meter.charge(
            solver
                .var_sorts
                .capacity()
                .saturating_mul(2)
                .saturating_add(8),
            0,
        )?;
        if let Some(sort) = solver.var_sorts.get(&term) {
            payload(Raw::Sort(sort), meter)?;
        }
    }
    let mut function_payload = Shape::default();
    for (name, registration) in &solver.native_fun_signatures {
        function_payload.add(text(name, meter)?);
        function_payload.add(text(&registration.core_name, meter)?);
        for sort in &registration.domain {
            function_payload.add(payload(Raw::Sort(sort), meter)?);
        }
        function_payload.add(payload(Raw::Sort(&registration.range), meter)?);
    }
    let mut events = Shape::default();
    let mut datatype_payload = Shape::default();
    let mut datatype_members = 0usize;
    let mut datatype_events = 0usize;
    let mut function_events = 0usize;
    let mut sort_events = 0usize;
    for event in &solver.native_replay_events {
        meter.charge(1, 0)?;
        events.bytes = events
            .bytes
            .saturating_add(size_of::<super::super::NativeReplayEvent>());
        events.nodes = events.nodes.saturating_add(1);
        match &event.kind {
            NativeReplayEventKind::SetLogic { logic } => events.add(text(logic, meter)?),
            NativeReplayEventKind::DeclareSort { name, core_name } => {
                sort_events = sort_events.saturating_add(1);
                events.add(text(name, meter)?);
                events.add(text(core_name, meter)?);
            }
            NativeReplayEventKind::DeclareConst { name, sort, .. } => {
                events.add(text(name, meter)?);
                events.add(payload(Raw::Sort(sort), meter)?);
            }
            NativeReplayEventKind::DeclareFun {
                name,
                domain,
                range,
            } => {
                function_events = function_events.saturating_add(1);
                events.add(text(name, meter)?);
                for sort in domain {
                    events.add(payload(Raw::Sort(sort), meter)?);
                }
                events.add(payload(Raw::Sort(range), meter)?);
            }
            NativeReplayEventKind::DeclareDatatype { .. }
            | NativeReplayEventKind::DeclareDatatypes { .. } => {}
            NativeReplayEventKind::Assert { name, .. } => {
                if let Some(name) = name {
                    events.add(text(name, meter)?);
                }
            }
            NativeReplayEventKind::CheckSatAssuming { assumptions } => {
                meter.charge(assumptions.len(), 0)?;
                events.bytes = events
                    .bytes
                    .saturating_add(assumptions.len().saturating_mul(size_of::<TermId>()));
            }
            NativeReplayEventKind::Push
            | NativeReplayEventKind::Pop
            | NativeReplayEventKind::Reset
            | NativeReplayEventKind::ResetAssertions
            | NativeReplayEventKind::CheckSat => {}
        }
        meter.charge(event.kind.datatypes().len(), 0)?;
        for datatype in event.kind.datatypes() {
            datatype_events = datatype_events.saturating_add(1);
            let mut shape = payload(Raw::Datatype(datatype), meter)?;
            // Batch payloads own a Vec of full declaration headers too.
            shape.bytes = shape.bytes.saturating_add(size_of::<DatatypeSort>());
            events.add(shape);
            datatype_payload.add(shape);
            datatype_members =
                datatype_members.saturating_add(datatype.constructors.len().saturating_mul(2));
            for constructor in &datatype.constructors {
                datatype_members = datatype_members.saturating_add(constructor.fields.len());
            }
        }
    }
    let mut nodes: HashMap<TermId, Option<usize>> = HashMap::default();
    let mut pending = Vec::new();
    let mut ordered_terms = Vec::new();
    let mut term_shape = Shape::default();
    let mut edges = 0usize;
    let mut constructor_variables = 0usize;
    let roots = context.assertions.iter().copied().chain(
        super::super::final_check_sat_assumptions(&solver.native_replay_events)
            .into_iter()
            .flatten()
            .copied(),
    );
    for root in roots {
        meter.push(&mut pending, (root, false, 1usize))?;
        while let Some((term, expanded, depth)) = pending.pop() {
            meter.depth(depth)?;
            if solver.terms().entry_stamp(term).is_none() {
                return meter.fail(Error::InvalidTerm { term: term.0 });
            }
            if expanded {
                let mut height = 1usize;
                children(solver.terms().get(term), |child| {
                    probe_nodes(&nodes, meter)?;
                    if let Some(Some(child_height)) = nodes.get(&child) {
                        height = height.max(child_height.saturating_add(1));
                    }
                    Ok(())
                })?;
                probe_nodes(&nodes, meter)?;
                nodes.insert(term, Some(height));
                meter.push(&mut ordered_terms, term)?;
                meter.depth(depth.saturating_add(height).saturating_sub(1))?;
                continue;
            }
            probe_nodes(&nodes, meter)?;
            if let Some(state) = nodes.get(&term) {
                if let Some(height) = state {
                    meter.depth(depth.saturating_add(*height).saturating_sub(1))?;
                    continue;
                }
                return meter.fail(Error::UnsupportedSource {
                    shape: "cyclic native term graph",
                });
            }
            reserve_nodes(&mut nodes, meter)?;
            probe_nodes(&nodes, meter)?;
            nodes.insert(term, None);
            term_shape.add(payload(Raw::Sort(solver.terms().sort(term)), meter)?);
            term_shape.add(term_payload(solver.terms().get(term), meter)?);
            if let TermData::Var(name, _) = solver.terms().get(term) {
                super::meter::constructor_lookup(context, name, meter)?;
                if context.constructor_metadata(name).is_some() {
                    constructor_variables = constructor_variables.saturating_add(1);
                }
            }
            meter.push(&mut pending, (term, true, depth))?;
            children(solver.terms().get(term), |child| {
                edges = edges.saturating_add(1);
                meter.push(&mut pending, (child, false, depth.saturating_add(1)))
            })?;
        }
    }
    let assertion_count = context.assertions.len();
    meter.charge(solver.var_names.capacity().saturating_mul(2), 0)?;
    let mut active_variables = 0usize;
    for term in solver.var_names.keys() {
        probe_nodes(&nodes, meter)?;
        if nodes.contains_key(term) {
            active_variables = active_variables.saturating_add(1);
        }
    }
    // Exact constructors are reused after admission. These bounds cover their
    // repeated registry scans, signature equality/lowering, deduplication and
    // datatype identity copies as well as the DAG/active-event workspaces.
    let registry_scan = registry_capacity
        .saturating_add(sort_capacity)
        .saturating_add(context.native_input_constructor_storage_capacity())
        .saturating_mul(2)
        .saturating_add(registry.bytes)
        .saturating_add(registry.nodes)
        .saturating_add(sort_definitions.bytes)
        .saturating_add(sort_definitions.nodes);
    let scans = active_variables
        .saturating_mul(4)
        .saturating_add(solver.native_fun_signatures.len().saturating_mul(4))
        .saturating_add(datatype_members.saturating_mul(4))
        .saturating_add(sort_events.saturating_mul(4))
        .saturating_add(constructor_variables.saturating_mul(4))
        .saturating_add(1);
    let lowered_sort_copies = function_payload.nodes.saturating_mul(4).saturating_add(
        datatype_payload
            .nodes
            .saturating_mul(datatype_members.saturating_add(4)),
    );
    let lowered_sort_payload = max_sort_definition
        .bytes
        .saturating_mul(lowered_sort_copies);
    let header_work = assertion_count
        .saturating_mul(assertion_count)
        .saturating_mul(8)
        .saturating_add(
            context
                .native_input_assertion_boundary_count()
                .saturating_mul(assertion_count.saturating_add(1)),
        )
        .saturating_add(registry_scan.saturating_mul(scans))
        .saturating_add(lowered_sort_payload)
        .saturating_add(
            events
                .bytes
                .saturating_add(events.nodes)
                .saturating_mul(assertion_count.saturating_add(1)),
        )
        .saturating_add(term_shape.bytes)
        .saturating_add(edges.saturating_mul(16))
        .saturating_add(term_shape.bytes.saturating_mul(function_events))
        .saturating_add(
            datatype_payload.bytes.saturating_mul(
                datatype_members
                    .saturating_add(datatype_events)
                    .saturating_add(4),
            ),
        )
        .saturating_add(
            function_payload
                .bytes
                .saturating_mul(solver.native_fun_signatures.len().saturating_add(4)),
        );
    // Header authentication reuses bounded signature-lowering workspaces.
    // Terms, events, metadata and final declaration records remain borrowed.
    let header_storage = lowered_sort_payload
        .saturating_add(function_payload.bytes.saturating_mul(4))
        .saturating_add(
            datatype_payload
                .bytes
                .saturating_mul(datatype_members.saturating_add(4)),
        )
        .saturating_add(
            max_signature
                .bytes
                .saturating_mul(solver.native_fun_signatures.len()),
        );
    Ok(Admission {
        ordered_terms,
        header_work,
        header_storage,
    })
}
