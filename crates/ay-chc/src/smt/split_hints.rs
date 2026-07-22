// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Phase-hint helpers for DPLL(T) split atoms.
//!
//! When the LIA solver requests a branch-and-bound or disequality split,
//! these methods set SAT variable phase hints so the solver explores the
//! direction closest to the seed model first.

use super::context::SmtContext;
use super::types::SmtValue;
use ay_core::TermId;
use num_rational::BigRational;
use num_traits::ToPrimitive;

impl SmtContext {
    pub(super) fn seed_int_value_for_term(&self, term: TermId) -> Option<i128> {
        let seed = self.phase_seed_model.as_ref()?;
        let qualified_name = match self.terms.get(term) {
            ay_core::term::TermData::Var(name, _) => name,
            _ => return None,
        };
        // #6100: term names are now sort-qualified; seed model uses original
        // names. Try original name first (via reverse map), fall back to
        // qualified name for backward compatibility.
        let original = self.original_var_name(qualified_name);
        match seed.get(original).or_else(|| seed.get(qualified_name)) {
            Some(SmtValue::Int(v)) => Some(*v),
            _ => None,
        }
    }

    pub(crate) fn apply_integer_split_phase_hint(
        &self,
        sat: &mut ay_sat::Solver,
        le_sat_var: ay_sat::Variable,
        ge_sat_var: ay_sat::Variable,
        split: &ay_core::SplitRequest,
    ) {
        let prefer_ceil = self
            .seed_int_value_for_term(split.variable)
            .and_then(|seed| {
                // #6179: Use checked conversion — skip hint if floor/ceil exceed i128.
                let floor = split.floor.to_i128()?;
                let ceil = split.ceil.to_i128()?;
                if seed <= floor {
                    Some(false)
                } else if seed >= ceil {
                    Some(true)
                } else {
                    None
                }
            })
            .unwrap_or_else(|| {
                let floor = BigRational::from_integer(split.floor.clone());
                let ceil = BigRational::from_integer(split.ceil.clone());
                let dist_floor = &split.value - &floor;
                let dist_ceil = &ceil - &split.value;
                dist_ceil < dist_floor
            });

        if prefer_ceil {
            sat.set_var_phase(ge_sat_var, true);
            sat.set_var_phase(le_sat_var, false);
        } else {
            sat.set_var_phase(le_sat_var, true);
            sat.set_var_phase(ge_sat_var, false);
        }
    }

    pub(crate) fn apply_disequality_split_phase_hint(
        &self,
        sat: &mut ay_sat::Solver,
        lt_sat_var: ay_sat::Variable,
        gt_sat_var: ay_sat::Variable,
        split: &ay_core::DisequalitySplitRequest,
    ) {
        let Some(seed) = self.seed_int_value_for_term(split.variable) else {
            return;
        };
        if !split.excluded_value.is_integer() {
            return;
        }

        // #6179: Use checked conversion — skip hint if excluded value exceeds i128.
        let Some(excluded) = split.excluded_value.numer().to_i128() else {
            return;
        };
        if seed < excluded {
            sat.set_var_phase(lt_sat_var, true);
            sat.set_var_phase(gt_sat_var, false);
        } else if seed > excluded {
            sat.set_var_phase(gt_sat_var, true);
            sat.set_var_phase(lt_sat_var, false);
        }
    }
}
