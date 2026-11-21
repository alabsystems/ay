// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Bounded native nominal-sort declarations. No source-text elaboration or
//! implicit declaration is used to confer ownership on a preexisting carrier.

use super::declaration_budget::Meter;
use crate::api::{
    NativeDeclarationBudget as Budget, NativeDeclarationError as Error,
    NativeDeclarationLimits as Limits, NativeDeclarationRefusal as Refusal, NativeReplayEvent,
    NativeReplayEventKind, Solver, SolverError,
};
use ay_core::{Sort, TermData, TermId};
use std::mem::size_of;
use std::sync::{atomic::Ordering, Arc};

// These spellings dispatch before ordinary named sorts in the frontend. An
// opaque declaration must round-trip as the actual declared carrier everywhere.
fn reserved_sort_name(name: &str) -> bool {
    name.is_empty()
        || ay_frontend::is_reserved_symbol(name)
        || matches!(
            name,
            "Bool"
                | "Int"
                | "Real"
                | "String"
                | "RegLan"
                | "Char"
                | "Array"
                | "Seq"
                | "Set"
                | "FiniteSet"
                | "BitVec"
                | "FloatingPoint"
                | "RoundingMode"
                | "Float16"
                | "Float32"
                | "Float64"
                | "Float128"
        )
}

fn invalid(shape: &'static str) -> Error {
    Refusal::UnsupportedSource { shape }.into()
}

fn unused_sort(root: &Sort, name: &str, meter: &mut Meter<'_>) -> Result<(), Error> {
    let mut pending = Vec::new();
    meter.push(&mut pending, (root, 1usize))?;
    while let Some((sort, depth)) = pending.pop() {
        meter.pay(1, 0, depth)?;
        match sort {
            Sort::Uninterpreted(old) | Sort::TypeVar(old) | Sort::FiniteDomain(old, _) => {
                meter.pay(old.len().saturating_add(name.len()), 0, depth)?;
                if old == name {
                    return Err(invalid(
                        "opaque sort name already used by an unowned native sort",
                    ));
                }
            }
            Sort::Array(array) => {
                meter.push(&mut pending, (&array.index_sort, depth + 1))?;
                meter.push(&mut pending, (&array.element_sort, depth + 1))?;
            }
            Sort::Seq(element) => meter.push(&mut pending, (element, depth + 1))?,
            Sort::Datatype(datatype) => {
                meter.pay(datatype.name.len().saturating_add(name.len()), 0, depth)?;
                if datatype.name == name {
                    return Err(invalid(
                        "opaque sort name already used by a datatype source sort",
                    ));
                }
                meter.pay(datatype.constructors.len(), 0, depth)?;
                for constructor in &datatype.constructors {
                    meter.pay(constructor.fields.len(), 0, depth)?;
                    for field in &constructor.fields {
                        meter.push(&mut pending, (&field.sort, depth + 1))?;
                    }
                }
            }
            Sort::Bool
            | Sort::Int
            | Sort::Real
            | Sort::String
            | Sort::RegLan
            | Sort::Char
            | Sort::BitVec(_)
            | Sort::FloatingPoint(..) => {}
            _ => {
                return Err(invalid(
                    "unadmitted existing sort during opaque declaration",
                ))
            }
        }
    }
    Ok(())
}

fn unowned_name_is_unused(solver: &Solver, name: &str, meter: &mut Meter<'_>) -> Result<(), Error> {
    // Native constants/fresh variables/UF signatures may historically have
    // used an undeclared U(name). Do not turn those old terms into a new
    // nominal declaration merely because its first allocator spelling matches.
    // All retained terms are checked, including ones outside active roots.
    let terms = solver.terms();
    meter.pay(terms.len(), 0, 0)?;
    for index in 0..terms.len() {
        let id = u32::try_from(index)
            .map(TermId)
            .map_err(|_| invalid("native term identity outside representable input"))?;
        unused_sort(terms.sort(id), name, meter)?;
        if let TermData::Forall(variables, _, _) | TermData::Exists(variables, _, _) = terms.get(id)
        {
            // An unused quantified binding need not have a separate Var node.
            meter.pay(variables.len(), 0, 0)?;
            for (_, sort) in variables {
                unused_sort(sort, name, meter)?;
            }
        }
    }
    // Public API metadata may retain a source carrier that was refined or
    // lowered in the engine. It cannot be silently rebound either.
    meter.pay(solver.var_sorts.capacity(), 0, 0)?;
    for sort in solver.var_sorts.values() {
        unused_sort(sort, name, meter)?;
    }
    meter.pay(solver.native_fun_signatures.capacity(), 0, 0)?;
    for declaration in solver.native_fun_signatures.values() {
        meter.pay(declaration.domain.len(), 0, 0)?;
        for sort in &declaration.domain {
            unused_sort(sort, name, meter)?;
        }
        unused_sort(&declaration.range, name, meter)?;
    }
    let context = solver.executor.context();
    meter.pay(context.native_input_symbol_storage_capacity(), 0, 0)?;
    for (_, info) in context.native_input_symbol_storage_iter() {
        unused_sort(&info.sort, name, meter)?;
        meter.pay(info.arg_sorts.len(), 0, 0)?;
        for sort in &info.arg_sorts {
            unused_sort(sort, name, meter)?;
        }
    }
    meter.pay(context.native_input_sort_storage_capacity(), 0, 0)?;
    for (_, sort) in context.native_input_sort_storage_iter() {
        unused_sort(sort, name, meter)?;
    }
    Ok(())
}

impl Solver {
    /// Declare one zero-arity opaque sort, global to assertion scopes.
    ///
    /// The returned public sort resolves through this solver's actual nominal
    /// declaration. Existing unowned same-name sorts are refused; this never
    /// reinterprets preexisting terms. The finite default envelope is the same
    /// 64Mi work/64MiB storage/depth128 used by native datatype declarations.
    pub fn try_declare_opaque_sort(&mut self, name: &str) -> Result<Sort, SolverError> {
        let mut budget = Budget::new(Limits::new(64 * 1024 * 1024, 64 * 1024 * 1024, 128));
        self.try_declare_opaque_sort_with_progress(name, &mut budget, &mut |_, _| true)
            .map_err(|error| match error {
                Error::Declaration(error) => error,
                Error::Refused(refusal) => SolverError::InvalidArgument {
                    operation: "declare_opaque_sort",
                    message: refusal.to_string(),
                },
            })
    }

    /// Declare a sort under one cumulative caller-owned native declaration
    /// budget. Refusals precede declaration mutation and preserve prior solve
    /// data; success records one ordered event and invalidates that data.
    pub fn try_declare_opaque_sort_with_progress(
        &mut self,
        name: &str,
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
        meter.text(name)?;
        if reserved_sort_name(name) {
            return Err(invalid("reserved or empty opaque sort name"));
        }
        // Refuse redeclaration before scanning or allocating another incarnation
        // of a live global declaration. The frontend also checks its namespace.
        meter.pay(
            self.executor
                .context()
                .native_input_sort_storage_capacity()
                .saturating_mul(2)
                .saturating_add(8)
                .saturating_mul(name.len().saturating_add(1)),
            0,
            0,
        )?;
        if self.executor.context().sort_definition(name).is_some() {
            return Err(invalid("opaque sort name is already declared"));
        }
        unowned_name_is_unused(self, name, &mut meter)?;
        if !self
            .executor
            .context()
            .admit_native_monomorphic_datatype_group(
                name.len().saturating_add(1),
                name.len().saturating_add(256),
                1,
                &mut |w, b, d| meter.pay(w, b, d).is_ok(),
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
                .saturating_mul(size_of::<NativeReplayEvent>())
                .saturating_add(name.len().saturating_mul(4)),
            0,
        )?;
        if self.native_replay_events.try_reserve(1).is_err() {
            return meter.fail(Refusal::Allocation);
        }
        let command = ay_frontend::Command::DeclareSort(name.to_owned(), 0);
        let event_name = name.to_owned();
        let result = Sort::Uninterpreted(name.to_owned());
        meter.pay(0, 0, 0)?;
        if self.interrupt.load(Ordering::Relaxed) {
            return meter.fail(Refusal::Cancelled);
        }
        self.executor
            .execute_native_global_declaration(&command)
            .map_err(SolverError::from)?;
        // The frontend's successful zero-arity DeclareSort always inserts this
        // exact nominal carrier. It is read back, never guessed from `name`.
        let Some(Sort::Uninterpreted(core_name)) = self.executor.context().sort_definition(name)
        else {
            return Err(invalid(
                "native frontend did not retain its opaque sort identity",
            ));
        };
        let core_name = core_name.clone();
        self.record_native_replay_event(NativeReplayEventKind::DeclareSort {
            name: event_name,
            core_name,
        });
        Ok(result)
    }
}
