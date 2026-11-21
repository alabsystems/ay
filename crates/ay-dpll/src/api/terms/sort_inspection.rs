// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Borrowed sort custody: current source ownership and actual arena data are distinct.

use super::declaration_budget::Meter;
use crate::api::{
    NativeDeclarationBudget as Budget, NativeDeclarationError as Error,
    NativeDeclarationRefusal as Refusal, Solver, Sort, Term, MAX_API_BITVECTOR_WIDTH,
};
use std::{mem::size_of, sync::Arc};

pub(super) fn admit_shape(sort: &Sort, meter: &mut Meter<'_>, depth: usize) -> Result<(), Error> {
    meter.pay(1, size_of::<Sort>(), depth)?;
    match sort {
        Sort::Bool | Sort::Int | Sort::Real | Sort::String | Sort::RegLan | Sort::Char => Ok(()),
        Sort::BitVec(width) if width.width > 0 && width.width <= MAX_API_BITVECTOR_WIDTH => Ok(()),
        Sort::FloatingPoint(exponent, significand) if *exponent >= 2 && *significand >= 2 => Ok(()),
        Sort::Uninterpreted(name) => meter.text(name),
        Sort::Array(array) => {
            admit_shape(&array.index_sort, meter, depth + 1)?;
            admit_shape(&array.element_sort, meter, depth + 1)
        }
        Sort::Seq(element) => admit_shape(element, meter, depth + 1),
        Sort::Datatype(datatype) => {
            meter.text(&datatype.name)?;
            meter.pay(
                datatype.constructors.len(),
                datatype
                    .constructors
                    .len()
                    .saturating_mul(size_of::<ay_core::DatatypeConstructor>()),
                depth,
            )?;
            for constructor in &datatype.constructors {
                meter.text(&constructor.name)?;
                meter.pay(
                    constructor.fields.len(),
                    constructor
                        .fields
                        .len()
                        .saturating_mul(size_of::<ay_core::DatatypeField>()),
                    depth,
                )?;
                for field in &constructor.fields {
                    meter.text(&field.name)?;
                    admit_shape(&field.sort, meter, depth + 1)?;
                }
            }
            Ok(())
        }
        _ => meter.fail(Refusal::UnsupportedSource {
            shape: "empty sequence has an unsupported or ill-formed element sort",
        }),
    }
}

pub(super) fn admit_lowering(
    solver: &Solver,
    sort: &Sort,
    meter: &mut Meter<'_>,
    depth: usize,
) -> Result<(), Error> {
    meter.pay(1, 0, depth)?;
    match sort {
        Sort::Uninterpreted(name) => {
            meter.pay(
                solver
                    .executor
                    .context()
                    .native_input_sort_storage_capacity()
                    .saturating_add(8)
                    .saturating_mul(name.len().saturating_add(1)),
                0,
                depth,
            )?;
            // Preserve ordinary native uninterpreted-sort construction. When
            // a live nominal declaration exists, price its exact retained
            // representation before lower_live_sort copies it.
            if let Some(live) = solver.executor.context().sort_definition(name) {
                admit_shape(live, meter, depth + 1)?;
            }
            Ok(())
        }
        Sort::Datatype(datatype) => {
            meter.pay(
                solver
                    .executor
                    .context()
                    .native_input_sort_storage_capacity()
                    .saturating_add(8)
                    .saturating_mul(datatype.name.len().saturating_add(1)),
                0,
                depth,
            )?;
            let Some(live) = solver.executor.context().sort_definition(&datatype.name) else {
                return meter.fail(Refusal::UnsupportedSource {
                    shape: "empty sequence datatype element has no live declaration",
                });
            };
            let ay_core::Sort::Uninterpreted(carrier) = live else {
                return meter.fail(Refusal::UnsupportedSource {
                    shape: "empty sequence datatype name has a non-nominal live definition",
                });
            };
            // Price the actual private carrier membership lookup before hashing
            // it, rather than using only the shorter public surface spelling.
            meter.pay(
                solver
                    .executor
                    .context()
                    .native_input_sort_storage_capacity()
                    .saturating_add(8)
                    .saturating_mul(carrier.len().saturating_add(1)),
                0,
                depth,
            )?;
            if !solver.executor.context().is_live_datatype_carrier(carrier) {
                return meter.fail(Refusal::UnsupportedSource {
                    shape: "empty sequence datatype name is not a live datatype carrier",
                });
            }
            admit_shape(live, meter, depth + 1)
        }
        Sort::Array(array) => {
            admit_lowering(solver, &array.index_sort, meter, depth + 1)?;
            admit_lowering(solver, &array.element_sort, meter, depth + 1)
        }
        Sort::Seq(element) => admit_lowering(solver, element, meter, depth + 1),
        _ => Ok(()),
    }
}

#[derive(Clone, Copy)]
enum NominalKind {
    Any,
    Datatype,
}

fn current_nominal<'a>(
    solver: &'a Solver,
    name: &str,
    kind: NominalKind,
    meter: &mut Meter<'_>,
    depth: usize,
) -> Result<&'a Sort, Error> {
    let context = solver.executor.context();
    let capacity = context
        .native_input_sort_storage_capacity()
        .saturating_add(8);
    meter.pay(
        capacity.saturating_mul(name.len().saturating_add(1)),
        0,
        depth,
    )?;
    let mut resolved = context.sort_definition(name);
    if resolved.is_none() {
        // An engine identity is accepted only if an actual CURRENT source
        // binding retains that exact identity. No prefix or sticky old registry.
        meter.pay(
            capacity.saturating_mul(name.len().saturating_add(2)),
            0,
            depth,
        )?;
        for (_, live) in context.native_input_sort_storage_iter() {
            meter.pay(1, 0, depth)?;
            if matches!(live, Sort::Uninterpreted(core) if core == name) {
                resolved = Some(live);
                break;
            }
        }
    }
    let Some(live @ Sort::Uninterpreted(core)) = resolved else {
        return meter.fail(Refusal::UnsupportedSource {
            shape: "sort has no current nominal source binding",
        });
    };
    meter.pay(
        capacity
            .saturating_mul(core.len().saturating_add(1))
            .saturating_mul(2),
        0,
        depth,
    )?;
    let known_datatype = context.datatype_constructors(core).is_some();
    let live_datatype = context.is_live_datatype_carrier(core);
    if (known_datatype && !live_datatype)
        || (matches!(kind, NominalKind::Datatype) && !live_datatype)
    {
        return meter.fail(Refusal::UnsupportedSource {
            shape: "datatype carrier is not currently source-visible",
        });
    }
    admit_shape(live, meter, depth)?;
    Ok(live)
}

fn text(name: &str, meter: &mut Meter<'_>, depth: usize) -> Result<String, Error> {
    meter.pay(name.len().saturating_add(1), name.len(), depth)?;
    let mut result = String::new();
    if result.try_reserve_exact(name.len()).is_err() {
        return meter.fail(Refusal::Allocation);
    }
    result.push_str(name);
    Ok(result)
}

/// Copy actual metadata without contextual reinterpretation. Every variable
/// capacity is reserved fallibly; fixed Box allocations are prepaid, as in the
/// existing bounded producers (allocator aborts are not converted to errors).
pub(super) fn copy_actual(sort: &Sort, meter: &mut Meter<'_>, depth: usize) -> Result<Sort, Error> {
    meter.pay(1, size_of::<Sort>(), depth)?;
    Ok(match sort {
        Sort::Uninterpreted(name) => Sort::Uninterpreted(text(name, meter, depth)?),
        Sort::Array(array) => {
            meter.pay(1, size_of::<ay_core::ArraySort>(), depth)?;
            Sort::array(
                copy_actual(&array.index_sort, meter, depth + 1)?,
                copy_actual(&array.element_sort, meter, depth + 1)?,
            )
        }
        Sort::Seq(element) => Sort::seq(copy_actual(element, meter, depth + 1)?),
        Sort::Datatype(datatype) => {
            let name = text(&datatype.name, meter, depth)?;
            meter.pay(
                datatype.constructors.len(),
                datatype
                    .constructors
                    .len()
                    .saturating_mul(size_of::<ay_core::DatatypeConstructor>()),
                depth,
            )?;
            let mut constructors = Vec::new();
            if constructors
                .try_reserve_exact(datatype.constructors.len())
                .is_err()
            {
                return meter.fail(Refusal::Allocation);
            }
            for constructor in &datatype.constructors {
                let name = text(&constructor.name, meter, depth)?;
                meter.pay(
                    constructor.fields.len(),
                    constructor
                        .fields
                        .len()
                        .saturating_mul(size_of::<ay_core::DatatypeField>()),
                    depth,
                )?;
                let mut fields = Vec::new();
                if fields.try_reserve_exact(constructor.fields.len()).is_err() {
                    return meter.fail(Refusal::Allocation);
                }
                for field in &constructor.fields {
                    fields.push(ay_core::DatatypeField::new(
                        text(&field.name, meter, depth)?,
                        copy_actual(&field.sort, meter, depth + 1)?,
                    ));
                }
                constructors.push(ay_core::DatatypeConstructor::new(name, fields));
            }
            Sort::Datatype(ay_core::DatatypeSort::new(name, constructors))
        }
        Sort::Bool
        | Sort::Int
        | Sort::Real
        | Sort::String
        | Sort::RegLan
        | Sort::Char
        | Sort::BitVec(_)
        | Sort::FloatingPoint(..) => sort.clone(),
        _ => {
            return meter.fail(Refusal::UnsupportedSource {
                shape: "actual sort kind is unsupported by bounded inspection",
            })
        }
    })
}

fn copy_current(
    sort: &Sort,
    solver: &Solver,
    meter: &mut Meter<'_>,
    depth: usize,
) -> Result<Sort, Error> {
    meter.pay(1, size_of::<Sort>(), depth)?;
    match sort {
        Sort::Uninterpreted(name) => copy_actual(
            current_nominal(solver, name, NominalKind::Any, meter, depth)?,
            meter,
            depth,
        ),
        Sort::Datatype(datatype) => copy_actual(
            current_nominal(solver, &datatype.name, NominalKind::Datatype, meter, depth)?,
            meter,
            depth,
        ),
        Sort::Array(array) => {
            meter.pay(1, size_of::<ay_core::ArraySort>(), depth)?;
            Ok(Sort::array(
                copy_current(&array.index_sort, solver, meter, depth + 1)?,
                copy_current(&array.element_sort, solver, meter, depth + 1)?,
            ))
        }
        Sort::Seq(element) => Ok(Sort::seq(copy_current(element, solver, meter, depth + 1)?)),
        _ => Ok(sort.as_term_sort()),
    }
}

impl Solver {
    /// Resolve a requested sort only through current nominal source bindings,
    /// including nested carriers. Unknown, popped or reset names refuse; the
    /// returned owned data grants no source, term, model or proof authority.
    pub fn try_live_sort_with_progress(
        &self,
        sort: &Sort,
        budget: &mut Budget,
        progress: &mut dyn FnMut(usize, usize) -> bool,
    ) -> Result<Sort, Error> {
        let mut meter = Meter {
            budget,
            progress,
            interrupt: Arc::clone(&self.interrupt),
            deadline: self.executor.current_solve_deadline(),
        };
        meter.pay(0, 0, 0)?;
        admit_shape(sort, &mut meter, 1)?;
        let result = copy_current(sort, self, &mut meter, 1)?;
        meter.pay(0, 0, 0)?;
        Ok(result)
    }

    /// Authenticate this exact handle and copy its ACTUAL arena sort through
    /// the existing cumulative owner. Public name/sort caches are not consulted
    /// and old retained carriers are never rebound to a current surface name.
    pub fn try_engine_term_sort_with_progress(
        &self,
        term: Term,
        budget: &mut Budget,
        progress: &mut dyn FnMut(usize, usize) -> bool,
    ) -> Result<Sort, Error> {
        let mut meter = Meter {
            budget,
            progress,
            interrupt: Arc::clone(&self.interrupt),
            deadline: self.executor.current_solve_deadline(),
        };
        meter.pay(1, 0, 0)?;
        let id = self.resolve_term("engine_term_sort", term)?;
        let actual = self.terms().sort(id);
        admit_shape(actual, &mut meter, 1)?;
        let result = copy_actual(actual, &mut meter, 1)?;
        meter.pay(0, 0, 0)?;
        Ok(result)
    }
}
