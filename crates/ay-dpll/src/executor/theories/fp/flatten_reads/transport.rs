// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Attempt-local transport of candidate Boolean UF values, not SAT authority.
//! The exact read substitution supplies the application images. Array
//! reconstruction and the unchanged authored-root/model gates still decide
//! whether those candidate values form a valid interpretation.

use ay_core::kani_compat::DetHashMap as HashMap;
use ay_core::term::{Symbol, TermData, TermEntryStamp};
use ay_core::{Sort, TermId};
use ay_frontend::{CheckedProjectionBinding, ProjectionBindingRequest};

use crate::executor::{model::eval_memo_clear, Executor};

// Same identity-size envelope as the frontend's bounded declaration checker.
const MAX_IDENTITY_BYTES: usize = 256;

fn flat_argument_sort(sort: &Sort) -> bool {
    matches!(sort, Sort::Bool | Sort::BitVec(_) | Sort::FloatingPoint(..))
        || matches!(sort, Sort::Uninterpreted(name) if name == "RoundingMode")
}

#[derive(Debug)]
struct Pair {
    original: TermId,
    image: TermId,
    original_stamp: TermEntryStamp,
    image_stamp: TermEntryStamp,
}

/// Private provenance, created only from this flattening pass's rewrite memo.
/// Nothing is retained on the executor after the attempt.
#[derive(Debug)]
pub(in crate::executor::theories::fp) struct BoolUfTransport {
    bindings: HashMap<Symbol, CheckedProjectionBinding>,
    pairs: Vec<Pair>,
}

impl BoolUfTransport {
    pub(super) fn capture(
        executor: &mut Executor,
        rewrites: &HashMap<TermId, TermId>,
    ) -> Option<Self> {
        let mut result = Self {
            bindings: HashMap::default(),
            pairs: Vec::new(),
        };
        for (&original, &image) in rewrites {
            if executor.should_abort_theory_loop() {
                return None;
            }
            let terms = &executor.ctx.terms;
            let original_stamp = terms.entry_stamp(original)?;
            let image_stamp = terms.entry_stamp(image)?;
            if original == image || terms.sort(original) != &Sort::Bool {
                continue;
            }
            let TermData::App(Symbol::Named(name), args) = terms.get(original) else {
                continue;
            };
            if args.is_empty()
                || Executor::is_known_theory_symbol(name)
                || crate::features::is_builtin_symbol_name(name)
            {
                continue;
            }
            if name.len() > MAX_IDENTITY_BYTES {
                return None;
            }
            let TermData::App(image_symbol, image_args) = terms.get(image) else {
                return None;
            };
            let symbol = Symbol::named(name.as_str());
            if image_symbol != &symbol
                || terms.sort(image) != &Sort::Bool
                || args.len() != image_args.len()
            {
                return None;
            }
            // Re-read by index after each stop poll, avoiding an unbounded
            // argument clone. Every image must be the actual recursive memo
            // result, including unchanged argument identities.
            let arity = args.len();
            let mut parameter_sorts = Vec::new();
            for index in 0..arity {
                if executor.should_abort_theory_loop() {
                    return None;
                }
                let terms = &executor.ctx.terms;
                let TermData::App(_, args) = terms.get(original) else {
                    return None;
                };
                let TermData::App(_, image_args) = terms.get(image) else {
                    return None;
                };
                let (arg, image_arg) = (args[index], image_args[index]);
                terms.entry_stamp(arg)?;
                terms.entry_stamp(image_arg)?;
                // The FP lane represents flat arguments. Check shape before
                // comparing or cloning a potentially recursive user sort.
                if !flat_argument_sort(terms.sort(arg))
                    || !flat_argument_sort(terms.sort(image_arg))
                    || rewrites.get(&arg) != Some(&image_arg)
                    || terms.sort(arg) != terms.sort(image_arg)
                {
                    return None;
                }
                parameter_sorts.push(terms.sort(arg).clone());
            }
            if let Some(binding) = result.bindings.get(&symbol) {
                if binding.parameter_sorts() != parameter_sorts {
                    return None;
                }
            } else {
                // Reuse the existing bounded, positively checked declaration
                // boundary: a same-spelled builtin, alias or definition is not
                // an ordinary UF. This supplies no occurrence/model theorem.
                if result.bindings.is_empty() {
                    executor
                        .ctx
                        .bounded_projection_declaration_inventory_size()?;
                }
                let binding = executor
                    .ctx
                    .check_projection_declaration(&ProjectionBindingRequest {
                        symbol: symbol.clone(),
                        parameter_sorts,
                        result_sort: Sort::Bool,
                    })
                    .ok()?;
                result.bindings.insert(symbol, binding);
            }
            result.pairs.push(Pair {
                original,
                image,
                original_stamp,
                image_stamp,
            });
        }
        Some(result)
    }

    /// Validate the complete batch before changing any model state. Indices
    /// already belong to Model's zero-based namespace; do not re-offset them.
    pub(in crate::executor::theories::fp) fn install(&self, executor: &mut Executor) -> bool {
        for binding in self.bindings.values() {
            if executor.should_abort_theory_loop()
                || !executor.ctx.projection_binding_still_current(binding)
            {
                return false;
            }
        }
        let mut aliases = Vec::new();
        for pair in &self.pairs {
            if executor.should_abort_theory_loop() {
                return false;
            }
            let terms = &executor.ctx.terms;
            if terms.entry_stamp(pair.original) != Some(pair.original_stamp)
                || terms.entry_stamp(pair.image) != Some(pair.image_stamp)
            {
                return false;
            }
            let Some(model) = executor.last_model.as_ref() else {
                return false;
            };
            let Some(&image_index) = model.term_to_var.get(&pair.image) else {
                return false;
            };
            let Some(&value) = model.sat_model.get(image_index as usize) else {
                return false;
            };
            if let Some(&original_index) = model.term_to_var.get(&pair.original) {
                if model.sat_model.get(original_index as usize) != Some(&value) {
                    return false;
                }
            } else {
                aliases.push((pair.original, image_index));
            }
        }
        if executor.should_abort_theory_loop() {
            return false;
        }
        let Some(model) = executor.last_model.as_mut() else {
            return false;
        };
        // Array reconstruction also changed the candidate, even for a batch
        // with no UF aliases. No earlier validation/seal may survive it.
        model.revoke_all_quantified_model_seals();
        model.term_to_var.extend(aliases);
        executor.last_model_validated = false;
        eval_memo_clear();
        true
    }
}

#[cfg(test)]
mod tests;
