// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Borrowed, nonadopting function declaration with one cumulative owner.

use super::{declaration_budget::Meter, sort_inspection::copy_actual};
use crate::api::types::FrontendFuncDeclIdentity;
use crate::api::{
    FuncDecl, NativeDeclarationBudget as Budget, NativeDeclarationError as Error,
    NativeDeclarationRefusal as Refusal, NativeFunctionRegistration, NativeReplayEvent,
    NativeReplayEventKind, Solver, Sort,
};
use ay_core::kani_compat::{hash_table_cost as table, DetHashMap as HashMap};
use std::{mem::size_of, sync::Arc};

fn text(value: &str, meter: &mut Meter<'_>) -> Result<String, Error> {
    meter.text(value)?;
    let mut out = String::new();
    if out.try_reserve_exact(value.len()).is_err() {
        return meter.fail(Refusal::Allocation);
    }
    out.push_str(value);
    Ok(out)
}

fn copy_sorts(values: &[Sort], meter: &mut Meter<'_>) -> Result<Vec<Sort>, Error> {
    meter.pay(
        values.len(),
        values
            .len()
            .checked_mul(size_of::<Sort>())
            .unwrap_or(usize::MAX),
        0,
    )?;
    let mut out = Vec::new();
    if out.try_reserve_exact(values.len()).is_err() {
        return meter.fail(Refusal::Allocation);
    }
    for value in values {
        out.push(copy_actual(value, meter, 1)?);
    }
    Ok(out)
}

fn probe<V>(map: &HashMap<String, V>, name: &str, meter: &mut Meter<'_>) -> Result<(), Error> {
    let Some(work) =
        table::string_lookup::<(String, V)>(map.allocation_size(), map.len(), name.len())
    else {
        return meter.fail(Refusal::Allocation);
    };
    meter.pay(work, 0, 0)
}

fn reserve<V>(map: &mut HashMap<String, V>, meter: &mut Meter<'_>) -> Result<(), Error> {
    let Some(cost) =
        table::reserve_one::<(String, V)>(map.allocation_size(), map.len(), map.capacity())
    else {
        return meter.fail(Refusal::Allocation);
    };
    meter.pay(cost.work, cost.storage_bytes, 0)?;
    if cost.rehashes {
        let Some(work) = table::iteration::<(String, V)>(map.allocation_size(), map.len()) else {
            return meter.fail(Refusal::Allocation);
        };
        meter.pay(work, 0, 0)?;
        for key in map.keys() {
            let Some(work) = table::string_hash_payload(key.len()) else {
                return meter.fail(Refusal::Allocation);
            };
            meter.pay(work, 0, 0)?;
        }
    }
    if map.try_reserve(1).is_err() {
        return meter.fail(Refusal::Allocation);
    }
    Ok(())
}

fn frontend_result<T>(
    result: Result<T, ay_frontend::NativeOwnedConstantError>,
    precise: Option<Error>,
    meter: &mut Meter<'_>,
) -> Result<T, Error> {
    if let Some(error) = precise {
        return Err(error);
    }
    match result {
        Ok(value) => Ok(value),
        Err(ay_frontend::NativeOwnedConstantError::ResourceLimit) => {
            meter.fail(Refusal::Allocation)
        }
        Err(ay_frontend::NativeOwnedConstantError::Occupied) => {
            meter.fail(Refusal::UnsupportedSource {
                shape: "new function name is occupied by retained native/source data",
            })
        }
        Err(ay_frontend::NativeOwnedConstantError::InvalidName) => {
            meter.fail(Refusal::UnsupportedSource {
                shape: "new function name is empty or reserved",
            })
        }
        _ => meter.fail(Refusal::UnsupportedSource {
            shape: "new function signature has an unsupported or unowned current carrier",
        }),
    }
}

impl Solver {
    /// Declare a genuinely NEW native function, never adopt a matching old
    /// name/signature. Every raw/current signature copy, namespace lookup,
    /// table reservation, event/model/handle payload and final stop fence uses
    /// the SAME cumulative declaration budget and progress callback.
    ///
    /// The returned handle is tied to the actual frontend declaration/context
    /// identity. Declaring a function supplies no equation, law, membership or
    /// source-proof grant. Refusals publish no binding/event/handle; capacity,
    /// or an inert zero-arity Var from a late refusal, may remain consumed.
    #[must_use = "this returns a Result that must be checked"]
    pub fn try_declare_new_fun_with_progress(
        &mut self,
        name: &str,
        domain: &[Sort],
        range: &Sort,
        budget: &mut Budget,
        progress: &mut dyn FnMut(usize, usize) -> bool,
    ) -> Result<FuncDecl, Error> {
        let interrupt = Arc::clone(&self.interrupt);
        let deadline = self.executor.current_solve_deadline();
        {
            let mut meter = Meter {
                budget,
                progress,
                interrupt: Arc::clone(&interrupt),
                deadline,
            };
            meter.pay(name.len().saturating_add(1), 0, 0)?;
            probe(&self.native_fun_signatures, name, &mut meter)?;
            probe(&self.var_terms_by_name, name, &mut meter)?;
            probe(&self.defined_funs, name, &mut meter)?;
            if self.native_fun_signatures.contains_key(name)
                || self.var_terms_by_name.contains_key(name)
                || self.defined_funs.contains_key(name)
            {
                return meter.fail(Refusal::UnsupportedSource {
                    shape: "new function name is occupied by an API declaration",
                });
            }
        }
        // Prepay actual source-table geometry before the live-sort adapter's
        // first owned nominal copy, including a private carrier wider than its
        // requested public spelling. No new owner is created by either layer.
        for sort in domain.iter().chain(std::iter::once(range)) {
            let mut meter = Meter {
                budget,
                progress,
                interrupt: Arc::clone(&interrupt),
                deadline,
            };
            let mut precise = None;
            let result = self
                .executor
                .context()
                .admit_native_function_sort_context_with_progress(sort, &mut |w, b, d| match meter
                    .pay(w, b, d)
                {
                    Ok(()) => true,
                    Err(error) => {
                        precise.get_or_insert(error);
                        false
                    }
                });
            frontend_result(result, precise, &mut meter)?;
        }
        let mut live_domain = Vec::new();
        {
            let mut meter = Meter {
                budget,
                progress,
                interrupt: Arc::clone(&interrupt),
                deadline,
            };
            meter.pay(
                domain.len(),
                domain
                    .len()
                    .checked_mul(size_of::<Sort>())
                    .unwrap_or(usize::MAX),
                0,
            )?;
            if live_domain.try_reserve_exact(domain.len()).is_err() {
                return meter.fail(Refusal::Allocation);
            }
        }
        for sort in domain {
            live_domain.push(self.try_live_sort_with_progress(sort, budget, progress)?);
        }
        let live_range = self.try_live_sort_with_progress(range, budget, progress)?;
        let mut meter = Meter {
            budget,
            progress,
            interrupt,
            deadline,
        };
        reserve(&mut self.native_fun_signatures, &mut meter)?;
        if self.native_replay_events.len() == self.native_replay_events.capacity() {
            let capacity = self
                .native_replay_events
                .capacity()
                .checked_mul(2)
                .unwrap_or(usize::MAX)
                .max(4);
            meter.pay(
                self.native_replay_events.len(),
                capacity
                    .checked_mul(size_of::<NativeReplayEvent>())
                    .unwrap_or(usize::MAX),
                0,
            )?;
            if self
                .native_replay_events
                .try_reserve_exact(capacity.saturating_sub(self.native_replay_events.len()))
                .is_err()
            {
                return meter.fail(Refusal::Allocation);
            }
        }
        let key = text(name, &mut meter)?;
        let registration_core = text(name, &mut meter)?;
        let handle_name = text(name, &mut meter)?;
        let handle_core = text(name, &mut meter)?;
        let event_name = text(name, &mut meter)?;
        let registration_domain = copy_sorts(domain, &mut meter)?;
        let registration_range = copy_actual(range, &mut meter, 1)?;
        let handle_domain = copy_sorts(domain, &mut meter)?;
        let handle_range = copy_actual(range, &mut meter, 1)?;
        let event_domain = copy_sorts(&live_domain, &mut meter)?;
        let event_range = copy_actual(&live_range, &mut meter, 1)?;
        probe(&self.native_fun_signatures, name, &mut meter)?;
        let mut precise = None;
        let result = self
            .executor
            .context_mut_internal()
            .try_register_native_owned_function_with_progress(
                name,
                &live_domain,
                &live_range,
                &mut |w, b, d| match meter.pay(w, b, d) {
                    Ok(()) => true,
                    Err(error) => {
                        precise.get_or_insert(error);
                        false
                    }
                },
            );
        let declaration = frontend_result(result, precise, &mut meter)?;
        // From the frontend's terminal fence onward, only prepaid inserts and
        // moves remain. Arc identity clones create no replacement declaration.
        let identity = FrontendFuncDeclIdentity::new(
            self.executor.context().source_context_stamp(),
            declaration,
            ay_frontend::DeclarationKind::Uninterpreted,
        );
        self.native_fun_signatures.insert(
            key,
            NativeFunctionRegistration {
                domain: registration_domain,
                range: registration_range,
                core_name: registration_core,
                identity: identity.clone(),
            },
        );
        let index = self.native_replay_events.len();
        self.native_replay_events.push(NativeReplayEvent::new(
            index,
            NativeReplayEventKind::DeclareFun {
                name: event_name,
                domain: event_domain,
                range: event_range,
            },
            self.scope_level,
        ));
        self.executor.invalidate_for_native_api_mutation();
        Ok(FuncDecl::with_frontend_identity(
            handle_name,
            handle_core,
            handle_domain,
            handle_range,
            identity,
        ))
    }
}
