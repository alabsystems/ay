// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Bounded data freshness and separately registered native source constants.

use super::{declaration_budget::Meter, sort_inspection::copy_actual};
use crate::api::{
    NativeDeclarationBudget as Budget, NativeDeclarationError as Error,
    NativeDeclarationRefusal as Refusal, NativeReplayEvent, NativeReplayEventKind, Solver, Sort,
    Term,
};
use ay_core::kani_compat::hash_table_cost as table;
use ay_core::kani_compat::DetHashMap as HashMap;
use std::{hash::Hash, mem::size_of, sync::Arc};

fn text(value: &str, meter: &mut Meter<'_>) -> Result<String, Error> {
    meter.text(value)?;
    let mut result = String::new();
    if result.try_reserve_exact(value.len()).is_err() {
        return meter.fail(Refusal::Allocation);
    }
    result.push_str(value);
    Ok(result)
}

fn probe<V>(map: &HashMap<String, V>, name: &str, meter: &mut Meter<'_>) -> Result<(), Error> {
    let Some(work) =
        table::string_lookup::<(String, V)>(map.allocation_size(), map.len(), name.len())
    else {
        return meter.fail(Refusal::Allocation);
    };
    meter.pay(work, 0, 0)
}

// Called only for TermId keys, or after the caller prepays retained String
// payloads. Value Sort/String data move as headers; no deep copy is requested.
fn reserve<K: Eq + Hash, V>(map: &mut HashMap<K, V>, meter: &mut Meter<'_>) -> Result<(), Error> {
    let Some(cost) = table::reserve_one::<(K, V)>(map.allocation_size(), map.len(), map.capacity())
    else {
        return meter.fail(Refusal::Allocation);
    };
    meter.pay(cost.work, cost.storage_bytes, 0)?;
    if map.try_reserve(1).is_err() {
        return meter.fail(Refusal::Allocation);
    }
    Ok(())
}

fn core_refusal<T>(
    result: std::result::Result<T, ay_core::term::ControlledTermInternError>,
    precise: Option<Error>,
    meter: &mut Meter<'_>,
) -> Result<T, Error> {
    if let Some(error) = precise {
        return Err(error);
    }
    match result {
        Ok(value) => Ok(value),
        Err(ay_core::term::ControlledTermInternError::ResourceLimit) => {
            meter.fail(Refusal::Allocation)
        }
        Err(_) => meter.fail(Refusal::UnsupportedSource {
            shape: "controlled fresh Var refused its producer arena, sort or name",
        }),
    }
}

impl Solver {
    /// Construct a fresh logical binder DATA variable under the caller's SAME
    /// cumulative declaration budget. The sort resolves only current owned
    /// nominal carriers. No frontend declaration, model key or replay event is
    /// registered; this grants no logical/source authority to the caller.
    /// A late refusal can leave an inert entry/consumed serial but no handle.
    pub fn try_fresh_var_with_progress(
        &mut self,
        prefix: &str,
        sort: &Sort,
        budget: &mut Budget,
        progress: &mut dyn FnMut(usize, usize) -> bool,
    ) -> Result<Term, Error> {
        let live = self.try_live_sort_with_progress(sort, budget, progress)?;
        let mut meter = Meter {
            budget,
            progress,
            interrupt: Arc::clone(&self.interrupt),
            deadline: self.executor.current_solve_deadline(),
        };
        meter.pay(0, 0, 0)?;
        let id = loop {
            let mut precise = None;
            let result = self.terms_mut().try_fresh_var_with_progress(
                prefix,
                &live,
                &mut |w, b| match meter.pay(w, b, 0) {
                    Ok(()) => true,
                    Err(error) => {
                        precise = Some(error);
                        false
                    }
                },
            );
            let id = core_refusal(result, precise, &mut meter)?;
            let ay_core::TermData::Var(name, _) = self.terms().get(id) else {
                return meter.fail(Refusal::UnsupportedSource {
                    shape: "fresh factory did not return a Var",
                });
            };
            let mut source_precise = None;
            let available =
                self.executor
                    .context()
                    .native_fresh_data_name_is_available_with_progress(name, &mut |w, b, d| {
                        match meter.pay(w, b, d) {
                            Ok(()) => true,
                            Err(error) => {
                                source_precise = Some(error);
                                false
                            }
                        }
                    });
            if let Some(error) = source_precise {
                return Err(error);
            }
            match available {
                Ok(true) => break id,
                // The source metadata has a declaration not materialized as
                // a core App. Burn this inert candidate and continue the SAME
                // serial/resource owner; never publish it as a logical binder.
                Ok(false) => continue,
                Err(_) => return meter.fail(Refusal::Allocation),
            }
        };
        drop(live);
        meter.pay(0, 0, 0)?;
        Ok(self.wrap_term(id))
    }

    /// Declare a genuinely fresh native constant under one caller-owned
    /// work/storage/depth/deadline/interrupt owner. `display` is ignored: it
    /// supplies neither authority nor the model/replay identity and may use
    /// reserved or shadowed spelling. `identity` must be unused in every
    /// retained declaration/arena namespace; an existing binding is not adopted.
    ///
    /// Real frontend allocation+registration binds its actual engine Var,
    /// current live carrier and declaration identity atomically. Model maps and
    /// one ordered DeclareConst event use that SAME identity. Data freshness
    /// and source registration stay separate from the binder-only API above.
    /// All new physical copies/reserves/probes are admitted before source
    /// commit; the existing result-cache invalidation remains unchanged.
    pub fn try_declare_const_with_fresh_identity_with_progress(
        &mut self,
        _display: &str,
        identity: &str,
        sort: &Sort,
        budget: &mut Budget,
        progress: &mut dyn FnMut(usize, usize) -> bool,
    ) -> Result<Term, Error> {
        let live = self.try_live_sort_with_progress(sort, budget, progress)?;
        let mut meter = Meter {
            budget,
            progress,
            interrupt: Arc::clone(&self.interrupt),
            deadline: self.executor.current_solve_deadline(),
        };
        meter.pay(identity.len().saturating_add(1), 0, 0)?;
        probe(&self.var_terms_by_name, identity, &mut meter)?;
        probe(&self.native_fun_signatures, identity, &mut meter)?;
        if self.var_terms_by_name.contains_key(identity)
            || self.native_fun_signatures.contains_key(identity)
        {
            return meter.fail(Refusal::UnsupportedSource {
                shape: "fresh constant identity is already owned by an API declaration",
            });
        }
        reserve(&mut self.var_names, &mut meter)?;
        reserve(&mut self.var_sorts, &mut meter)?;
        // Existing string keys are rehashed if this particular table grows.
        if self.var_terms_by_name.capacity() == self.var_terms_by_name.len() {
            let Some(work) = table::iteration::<(String, ay_core::TermId)>(
                self.var_terms_by_name.allocation_size(),
                self.var_terms_by_name.len(),
            ) else {
                return meter.fail(Refusal::Allocation);
            };
            meter.pay(work, 0, 0)?;
            for key in self.var_terms_by_name.keys() {
                let Some(work) = table::string_hash_payload(key.len()) else {
                    return meter.fail(Refusal::Allocation);
                };
                meter.pay(work, 0, 0)?;
            }
        }
        reserve(&mut self.var_terms_by_name, &mut meter)?;
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
        let model_key = text(identity, &mut meter)?;
        let reverse_key = text(identity, &mut meter)?;
        let event_key = text(identity, &mut meter)?;
        let source_sort = copy_actual(sort, &mut meter, 1)?;
        let event_sort = copy_actual(&live, &mut meter, 1)?;
        // Fixed-key insertions have bounded scalar equality/hashing; the only
        // variable-length incoming key is charged against all possible probes.
        for work in [
            table::fixed_lookup::<(ay_core::TermId, String)>(
                self.var_names.allocation_size(),
                self.var_names.len(),
            ),
            table::fixed_lookup::<(ay_core::TermId, Sort)>(
                self.var_sorts.allocation_size(),
                self.var_sorts.len(),
            ),
        ] {
            let Some(work) = work else {
                return meter.fail(Refusal::Allocation);
            };
            meter.pay(work, 0, 0)?;
        }
        probe(&self.var_terms_by_name, identity, &mut meter)?;
        let mut precise = None;
        let result = self
            .executor
            .context_mut_internal()
            .try_register_native_owned_constant_with_progress(identity, &live, &mut |w, b, d| {
                match meter.pay(w, b, d) {
                    Ok(()) => true,
                    Err(error) => {
                        precise = Some(error);
                        false
                    }
                }
            });
        let id =
            match (result, precise) {
                (_, Some(error)) => return Err(error),
                (Ok(id), None) => id,
                (Err(error), None) => return meter.fail(match error {
                    ay_frontend::NativeOwnedConstantError::ResourceLimit => Refusal::Allocation,
                    ay_frontend::NativeOwnedConstantError::Occupied => Refusal::UnsupportedSource {
                        shape: "fresh constant identity is occupied by retained native/source data",
                    },
                    ay_frontend::NativeOwnedConstantError::InvalidName => {
                        Refusal::UnsupportedSource {
                            shape: "fresh constant identity is empty or reserved",
                        }
                    }
                    _ => Refusal::UnsupportedSource {
                        shape: "fresh constant sort is unsupported or has no current source owner",
                    },
                }),
            };
        // No fallible allocation/callback after the frontend's final fence:
        // complete model/replay custody together before publishing the handle.
        self.var_names.insert(id, model_key);
        self.var_terms_by_name.insert(reverse_key, id);
        self.var_sorts.insert(id, source_sort);
        let index = self.native_replay_events.len();
        self.native_replay_events.push(NativeReplayEvent::new(
            index,
            NativeReplayEventKind::DeclareConst {
                name: event_key,
                term: id,
                sort: event_sort,
            },
            self.scope_level,
        ));
        self.executor.invalidate_for_native_api_mutation();
        Ok(self.wrap_term(id))
    }
}
