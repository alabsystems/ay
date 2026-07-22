// Copyright 2026 Andrew Yates
// Author: Andrew Yates

//! Lazy array Skolemization refinement for blocking cubes.
//!
//! Array-heavy counterexample-to-induction (CTI) models often need only a small
//! subset of concrete array indices to make a blocking cube inductive. Instead of
//! eagerly materializing every `select(arr, idx) = value` fact from the model, this
//! module maintains a per-predicate set of tracked indices and refines it lazily.
//!
//! The refinement loop starts from the currently-active indices for the predicate,
//! then adds at most one new model-derived index per array variable per iteration.
//! Each iteration rebuilds a point-style cube whose array component is restricted to
//! the active indices and retries the standard inductiveness check.

use super::super::*;
use crate::expr::{eval_array_select, evaluate_expr};

const MAX_ARRAY_SKOLEM_REFINEMENT_ITERS: usize = 5;

/// Per-predicate tracked array indices currently active for lazy Skolemization.
#[derive(Debug, Clone, Default)]
pub(in crate::pdr::solver) struct TrackedIndices {
    /// Maps each canonical array variable to the concrete index expressions that
    /// are currently tracked for that predicate.
    pub(in crate::pdr::solver) indices: Vec<(ChcVar, Vec<ChcExpr>)>,
}

impl TrackedIndices {
    fn tracked_for(&self, array_var: &ChcVar) -> &[ChcExpr] {
        self.indices
            .iter()
            .find(|(candidate, _)| candidate == array_var)
            .map(|(_, tracked)| tracked.as_slice())
            .unwrap_or(&[])
    }

    fn insert_indices(&mut self, array_var: &ChcVar, new_indices: &[ChcExpr]) -> usize {
        let tracked = if let Some(position) = self
            .indices
            .iter()
            .position(|(candidate, _)| candidate == array_var)
        {
            &mut self.indices[position].1
        } else {
            self.indices.push((array_var.clone(), Vec::new()));
            match self.indices.last_mut() {
                Some((_, tracked)) => tracked,
                None => return 0,
            }
        };

        let mut inserted = 0;
        for index_expr in new_indices {
            if !tracked.contains(index_expr) {
                tracked.push(index_expr.clone());
                inserted += 1;
            }
        }
        inserted
    }

    fn has_any(&self) -> bool {
        self.indices.iter().any(|(_, tracked)| !tracked.is_empty())
    }
}

/// Persistent lazy-Skolemization state, keyed by predicate.
#[derive(Debug, Clone, Default)]
pub(in crate::pdr::solver) struct ArraySkolemState {
    /// Active tracked indices for each predicate.
    pub(in crate::pdr::solver) active_indices: FxHashMap<PredicateId, TrackedIndices>,
}

/// Per-attempt refinement loop state.
#[derive(Debug, Clone)]
pub(in crate::pdr::solver) struct ArraySkolemRefinement {
    tracked: TrackedIndices,
    pending: Vec<(ChcVar, Vec<ChcExpr>)>,
}

impl ArraySkolemRefinement {
    fn new(active: TrackedIndices, extracted: TrackedIndices) -> Self {
        let pending = extracted
            .indices
            .into_iter()
            .filter_map(|(array_var, extracted_indices)| {
                let mut unseen = Vec::new();
                for index_expr in extracted_indices {
                    if !active.tracked_for(&array_var).contains(&index_expr) {
                        unseen.push(index_expr);
                    }
                }
                if unseen.is_empty() {
                    None
                } else {
                    Some((array_var, unseen))
                }
            })
            .collect();

        Self {
            tracked: active,
            pending,
        }
    }

    fn tracked(&self) -> &TrackedIndices {
        &self.tracked
    }

    fn into_tracked(self) -> TrackedIndices {
        self.tracked
    }

    fn activate_next_batch(&mut self) -> bool {
        let mut made_progress = false;

        for (array_var, pending_indices) in &mut self.pending {
            let next_index = if pending_indices.is_empty() {
                None
            } else {
                Some(pending_indices.remove(0))
            };

            if let Some(index_expr) = next_index {
                self.tracked
                    .insert_indices(array_var, std::slice::from_ref(&index_expr));
                made_progress = true;
            }
        }

        self.pending.retain(|(_, pending)| !pending.is_empty());
        made_progress
    }
}

impl PdrSolver {
    /// Refine a scalar-only point cube by lazily adding array indices from the CTI model.
    pub(in crate::pdr::solver) fn try_refine_with_array_indices(
        &mut self,
        pob: &ProofObligation,
    ) -> Option<ChcExpr> {
        if !self.uses_arrays {
            return None;
        }

        let model = pob.smt_model.as_ref()?;
        let extracted = self.collect_array_indices_for_predicate(pob.predicate, model);
        if extracted.indices.is_empty() {
            return None;
        }

        let active = self
            .array_skolem_state
            .active_indices
            .get(&pob.predicate)
            .cloned()
            .unwrap_or_default();
        let mut refinement = ArraySkolemRefinement::new(active, extracted);
        let mut attempted = false;

        for iteration in 0..MAX_ARRAY_SKOLEM_REFINEMENT_ITERS {
            if !attempted && !refinement.tracked().has_any() && !refinement.activate_next_batch() {
                break;
            }
            if attempted && !refinement.activate_next_batch() {
                break;
            }
            attempted = true;

            let Some(candidate) =
                self.build_skolemized_cube(pob.predicate, refinement.tracked(), model)
            else {
                break;
            };

            if self.config.verbose {
                safe_eprintln!(
                    "PDR: Array lazy-Skolem refinement iter {} for pred {} level {} -> {}",
                    iteration + 1,
                    pob.predicate.index(),
                    pob.level,
                    candidate
                );
            }

            if self.is_safety_path_point_blocking_acceptable(&candidate, pob.predicate, pob.level) {
                let tracked = refinement.into_tracked();
                self.array_skolem_state
                    .active_indices
                    .insert(pob.predicate, tracked);
                return Some(candidate);
            }
        }

        let tracked = refinement.into_tracked();
        if tracked.has_any() {
            self.array_skolem_state
                .active_indices
                .insert(pob.predicate, tracked);
        }
        None
    }

    /// Extract concrete model indices from an `ArrayMap`.
    pub(in crate::pdr::solver) fn extract_array_indices_from_model(
        &self,
        array_var: &ChcVar,
        model_value: &SmtValue,
    ) -> Vec<ChcExpr> {
        let ChcSort::Array(index_sort, _) = &array_var.sort else {
            return Vec::new();
        };

        let SmtValue::ArrayMap { entries, .. } = model_value else {
            return Vec::new();
        };

        let mut indices = Vec::new();
        for (index_value, _) in entries {
            let Some(index_expr) = Self::smt_value_to_expr_for_sort(index_value, index_sort) else {
                continue;
            };
            if !indices.contains(&index_expr) {
                indices.push(index_expr);
            }
        }
        indices
    }

    /// Build a point-style cube whose array component is restricted to `active_indices`.
    pub(in crate::pdr::solver) fn build_skolemized_cube(
        &self,
        predicate: PredicateId,
        active_indices: &TrackedIndices,
        model: &FxHashMap<String, SmtValue>,
    ) -> Option<ChcExpr> {
        let canonical_vars = self.canonical_vars(predicate)?;
        let mut conjuncts = Vec::new();
        let mut has_array_selects = false;

        for canonical_var in canonical_vars {
            match &canonical_var.sort {
                ChcSort::Array(_, element_sort) => {
                    let Some(array_value) = model.get(&canonical_var.name) else {
                        continue;
                    };

                    for index_expr in active_indices.tracked_for(canonical_var) {
                        let Some(index_value) = evaluate_expr(index_expr, model) else {
                            continue;
                        };
                        let Some(element_value) = eval_array_select(array_value, &index_value)
                        else {
                            continue;
                        };
                        let Some(element_expr) =
                            Self::smt_value_to_expr_for_sort(&element_value, element_sort)
                        else {
                            continue;
                        };

                        conjuncts.push(ChcExpr::eq(
                            ChcExpr::select(
                                ChcExpr::var(canonical_var.clone()),
                                index_expr.clone(),
                            ),
                            element_expr,
                        ));
                        has_array_selects = true;
                    }
                }
                ChcSort::Bool => match model.get(&canonical_var.name) {
                    Some(SmtValue::Bool(true)) => {
                        conjuncts.push(ChcExpr::var(canonical_var.clone()))
                    }
                    Some(SmtValue::Bool(false)) => {
                        conjuncts.push(ChcExpr::not(ChcExpr::var(canonical_var.clone())));
                    }
                    _ => {}
                },
                other_sort => {
                    let Some(value) = model.get(&canonical_var.name) else {
                        continue;
                    };
                    let Some(value_expr) = Self::smt_value_to_expr_for_sort(value, other_sort)
                    else {
                        continue;
                    };
                    conjuncts.push(ChcExpr::eq(ChcExpr::var(canonical_var.clone()), value_expr));
                }
            }
        }

        if !has_array_selects || conjuncts.is_empty() {
            return None;
        }

        Some(ChcExpr::and_all(conjuncts))
    }

    fn collect_array_indices_for_predicate(
        &self,
        predicate: PredicateId,
        model: &FxHashMap<String, SmtValue>,
    ) -> TrackedIndices {
        let mut tracked = TrackedIndices::default();
        let Some(canonical_vars) = self.canonical_vars(predicate) else {
            return tracked;
        };

        for canonical_var in canonical_vars {
            if !matches!(&canonical_var.sort, ChcSort::Array(_, _)) {
                continue;
            }

            let Some(model_value) = model.get(&canonical_var.name) else {
                continue;
            };
            let indices = self.extract_array_indices_from_model(canonical_var, model_value);
            if !indices.is_empty() {
                tracked.indices.push((canonical_var.clone(), indices));
            }
        }

        tracked
    }

    fn smt_value_to_expr_for_sort(value: &SmtValue, sort: &ChcSort) -> Option<ChcExpr> {
        match (value, sort) {
            (SmtValue::Bool(flag), ChcSort::Bool) => Some(ChcExpr::Bool(*flag)),
            (SmtValue::Int(number), ChcSort::Int) => Some(ChcExpr::Int(*number)),
            (SmtValue::Real(rational), ChcSort::Real) => {
                use num_traits::ToPrimitive;
                let numer = rational.numer().to_i64()?;
                let denom = rational.denom().to_i64()?;
                Some(ChcExpr::Real(numer, denom))
            }
            (SmtValue::BitVec(bits, width), ChcSort::BitVec(_)) => {
                Some(ChcExpr::BitVec(*bits, *width))
            }
            // Datatype values are not expected in array element positions for
            // Skolemization (arrays typically contain scalars). Skip gracefully.
            _ => None,
        }
    }
}
