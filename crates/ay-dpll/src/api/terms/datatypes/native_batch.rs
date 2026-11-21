// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Native mutual declarations retain one atomic source/event boundary.

use std::mem::size_of;
use std::sync::{atomic::Ordering, Arc};

use ay_core::{DatatypeSort, Sort};
use ay_frontend::command::{ConstructorDec, DatatypeDec, SelectorDec, SortDec};

use super::super::declaration_budget::Meter;
use crate::api::types::SortExt;
use crate::api::{
    NativeDatatypeBatchBudget as Budget, NativeDatatypeBatchError as Error,
    NativeDatatypeBatchLimits, NativeDatatypeBatchRefusal as Refusal, NativeReplayEvent,
    NativeReplayEventKind, Solver, SolverError,
};

fn invalid(message: &'static str) -> Error {
    Refusal::UnsupportedSource { shape: message }.into()
}

fn member_name(name: &str, meter: &mut Meter<'_>) -> Result<(), Error> {
    meter.text(name)?;
    // The fixed frontend vocabulary includes Core operators that ordinary
    // function declarations may overload for array-map targets. A native
    // datatype member cannot claim one of those theory identities.
    meter.pay(4096, 0, 0)?;
    if name.is_empty()
        || ay_frontend::is_reserved_symbol(name)
        || ay_frontend::is_builtin_operator_name(name)
    {
        return Err(invalid("reserved or empty native datatype member name"));
    }
    Ok(())
}

/// Retained declaration payload, distinct from work already paid to validate
/// borrowed input. Only this footprint participates in frontend copy pricing.
#[derive(Default)]
struct SourceFootprint {
    work: usize,
    storage: usize,
    members: usize,
}

impl SourceFootprint {
    fn payload(&mut self, work: usize, storage: usize) {
        self.work = self.work.saturating_add(work);
        self.storage = self.storage.saturating_add(storage);
    }

    fn text(&mut self, text: &str) {
        self.payload(text.len().saturating_add(1), text.len());
    }
}

fn source_sorts<'a>(
    solver: &Solver,
    group: &'a [DatatypeSort],
    meter: &mut Meter<'_>,
) -> Result<SourceFootprint, Error> {
    let mut source = SourceFootprint::default();
    source.payload(
        group.len(),
        group.len().saturating_mul(size_of::<DatatypeSort>()),
    );
    let mut pending = Vec::<(&'a Sort, usize)>::new();
    meter.pay(
        group.len(),
        group.len().saturating_mul(size_of::<DatatypeSort>()),
        0,
    )?;
    for (index, datatype) in group.iter().enumerate() {
        meter.text(&datatype.name)?;
        source.text(&datatype.name);
        source.payload(
            datatype.constructors.len(),
            datatype
                .constructors
                .len()
                .saturating_mul(size_of::<ConstructorDec>()),
        );
        for previous in &group[..index] {
            meter.pay(
                previous.name.len().saturating_add(datatype.name.len()),
                0,
                0,
            )?;
            if previous.name == datatype.name {
                return Err(invalid("datatype group repeats a sort name"));
            }
        }
        if datatype.constructors.is_empty() {
            return Err(invalid("datatype group contains an empty declaration"));
        }
        meter.pay(
            datatype.constructors.len(),
            datatype
                .constructors
                .len()
                .saturating_mul(size_of::<ConstructorDec>()),
            0,
        )?;
        for (ctor_index, constructor) in datatype.constructors.iter().enumerate() {
            member_name(&constructor.name, meter)?;
            source.text(&constructor.name);
            source.payload(
                constructor.fields.len(),
                constructor
                    .fields
                    .len()
                    .saturating_mul(size_of::<SelectorDec>()),
            );
            for previous in &datatype.constructors[..ctor_index] {
                meter.pay(
                    previous.name.len().saturating_add(constructor.name.len()),
                    0,
                    0,
                )?;
                if previous.name == constructor.name {
                    return Err(invalid("datatype repeats a constructor name"));
                }
            }
            source.members = source
                .members
                .saturating_add(constructor.fields.len().saturating_add(2));
            meter.pay(
                constructor.fields.len(),
                constructor
                    .fields
                    .len()
                    .saturating_mul(size_of::<SelectorDec>()),
                0,
            )?;
            for (field_index, field) in constructor.fields.iter().enumerate() {
                member_name(&field.name, meter)?;
                source.text(&field.name);
                for previous in &constructor.fields[..field_index] {
                    meter.pay(previous.name.len().saturating_add(field.name.len()), 0, 0)?;
                    if previous.name == field.name {
                        return Err(invalid("constructor repeats a selector name"));
                    }
                }
                meter.push(&mut pending, (&field.sort, 1))?;
            }
        }
    }
    while let Some((sort, depth)) = pending.pop() {
        meter.pay(1, size_of::<Sort>(), depth)?;
        source.payload(1, size_of::<Sort>());
        match sort {
            Sort::Bool | Sort::Int | Sort::Real | Sort::String | Sort::RegLan | Sort::Char => {}
            Sort::BitVec(width) if width.width > 0 => {}
            Sort::FloatingPoint(exponent, significand) if *exponent >= 2 && *significand >= 2 => {}
            Sort::Uninterpreted(name) => {
                meter.text(name)?;
                source.text(name);
                let mut found = false;
                for datatype in group {
                    meter.pay(name.len().saturating_add(datatype.name.len()), 0, 0)?;
                    found |= datatype.name == *name;
                }
                if !found {
                    let context = solver.executor.context();
                    meter.pay(
                        context
                            .native_input_sort_storage_capacity()
                            .saturating_mul(2)
                            .saturating_add(8)
                            .saturating_mul(name.len().saturating_add(1)),
                        0,
                        0,
                    )?;
                    if context.sort_definition(name).is_none() {
                        return Err(invalid(
                            "field references an undeclared sort outside its group",
                        ));
                    }
                }
            }
            Sort::Array(array) => {
                meter.push(&mut pending, (&array.index_sort, depth + 1))?;
                meter.push(&mut pending, (&array.element_sort, depth + 1))?;
            }
            Sort::Seq(element) => meter.push(&mut pending, (element, depth + 1))?,
            // A named reference avoids smuggling a second nested definition or
            // a different same-spelling declaration into a field signature.
            Sort::Datatype(_) => {
                return meter.fail(Refusal::UnsupportedSource {
                    shape: "embedded datatype definition; use a declared named field sort",
                })
            }
            _ => {
                return meter.fail(Refusal::UnsupportedSource {
                    shape: "field sort outside monomorphic native datatype group",
                })
            }
        }
    }
    Ok(source)
}

impl Solver {
    /// Declare one atomic group of monomorphic, possibly mutually recursive,
    /// datatypes. Forward fields use `Sort::Uninterpreted(group_name)`.
    /// Existing named fields must already be declared. Embedded definitions and
    /// schematic source contexts are refused before mutation.
    ///
    /// The convenience envelope is 64Mi work units, 64MiB cumulative storage,
    /// and depth128. Use the caller-owned method to share an explicit envelope.
    pub fn try_declare_datatypes(&mut self, datatypes: &[DatatypeSort]) -> Result<(), SolverError> {
        let mut budget = Budget::new(NativeDatatypeBatchLimits::new(
            64 * 1024 * 1024,
            64 * 1024 * 1024,
            128,
        ));
        let interrupt = self.interrupt.clone();
        self.try_declare_datatypes_with_progress(datatypes, &mut budget, &mut |_, _| {
            !interrupt.load(Ordering::Relaxed)
        })
        .map_err(|error| match error {
            Error::Declaration(error) => error,
            Error::Refused(refusal) => SolverError::InvalidArgument {
                operation: "declare_datatypes",
                message: refusal.to_string(),
            },
        })
    }

    /// Admit the borrowed full group and live monomorphic source metadata
    /// before cloning commands/events or changing any solver state. Resource
    /// refusal/cancellation is sticky in `budget`; no callback runs after the
    /// final pre-commit poll. The real frontend performs group-wide atomic
    /// name/sort validation. A successful commit invalidates prior solve data
    /// and records exactly one ordered group event, global to assertion scopes.
    pub fn try_declare_datatypes_with_progress(
        &mut self,
        datatypes: &[DatatypeSort],
        budget: &mut Budget,
        progress: &mut dyn FnMut(usize, usize) -> bool,
    ) -> Result<(), Error> {
        let mut meter = Meter {
            budget,
            progress,
            interrupt: Arc::clone(&self.interrupt),
            deadline: self.executor.current_solve_deadline(),
        };
        meter.pay(0, 0, 0)?;
        if self.interrupt.load(Ordering::Relaxed) {
            return meter.fail(Refusal::Cancelled);
        }
        if datatypes.is_empty() {
            return Err(invalid("datatype group must not be empty"));
        }
        let source = source_sorts(self, datatypes, &mut meter)?;
        if !self
            .executor
            .context()
            .admit_native_monomorphic_datatype_group(
                source.work,
                source.storage,
                source.members,
                &mut |work, storage, depth| meter.pay(work, storage, depth).is_ok(),
            )
        {
            return meter.fail(Refusal::UnsupportedSource {
                shape: "unadmitted live source metadata or schematic declaration context",
            });
        }
        meter.pay(
            self.native_replay_events.len().saturating_add(1),
            self.native_replay_events
                .len()
                .saturating_add(1)
                .saturating_mul(2)
                .saturating_mul(size_of::<NativeReplayEvent>()),
            0,
        )?;
        if self.native_replay_events.try_reserve(1).is_err() {
            return meter.fail(Refusal::Allocation);
        }
        // All recursive copies and command work have been admitted through
        // the same cumulative owner before materialization starts.
        let sort_decs = datatypes
            .iter()
            .map(|datatype| SortDec {
                name: datatype.name.clone(),
                arity: 0,
            })
            .collect();
        let datatype_decs = datatypes
            .iter()
            .map(|datatype| DatatypeDec {
                constructors: datatype
                    .constructors
                    .iter()
                    .map(|constructor| ConstructorDec {
                        name: constructor.name.clone(),
                        selectors: constructor
                            .fields
                            .iter()
                            .map(|field| SelectorDec {
                                name: field.name.clone(),
                                sort: field.sort.to_command_sort(),
                            })
                            .collect(),
                    })
                    .collect(),
                type_params: Vec::new(),
            })
            .collect();
        let event = NativeReplayEventKind::DeclareDatatypes {
            datatypes: datatypes.to_vec(),
        };
        meter.pay(0, 0, 0)?;
        if self.interrupt.load(Ordering::Relaxed) {
            return meter.fail(Refusal::Cancelled);
        }
        self.executor
            .execute_native_global_declaration(&ay_frontend::Command::DeclareDatatypes(
                sort_decs,
                datatype_decs,
            ))
            .map_err(SolverError::from)?;
        self.record_native_replay_event(event);
        Ok(())
    }
}
