// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Fail-closed work budget for the opaque-datatype completion widening.

mod field_scans;
mod render_cost;

#[cfg(not(test))]
use field_scans::MAX_DT_FIELD_SCAN_COMPARISONS;
#[cfg(test)]
pub(super) use field_scans::{
    MAX_DT_FIELD_SCAN_COMPARISONS, MAX_DT_FIELD_SCAN_FIELDS, MAX_DT_FIELD_SCAN_ROWS,
};

use ay_model_check::ModelValue;

use super::EvalValue;
use render_cost::{canonical_render_bytes, model_value_work};

/// Opaque applications were previously an immediate construction bailout.
/// Keep their new post-solve completion lane deliberately small.
pub(super) const MAX_OPAQUE_DT_TERMS: usize = 64;
pub(super) const MAX_OPAQUE_DT_APP_ARGS: usize = 64;
const MAX_OPAQUE_DT_WORK: usize = 32 * 1024 * 1024;
const MAX_ROUNDTRIP_SCHEMA_NODES: usize = 1024;
const MAX_BOUNDED_NODE_WORK: usize = 272;
const MAX_CANDIDATE_WORK: usize = MAX_ROUNDTRIP_SCHEMA_NODES * MAX_BOUNDED_NODE_WORK;
pub(super) const MAX_OPAQUE_DT_COLLECTION_ROOTS: usize = 1024;
const MAX_OPAQUE_DT_COLLECTION_ITEMS: usize = 1024;
const MAX_OPAQUE_DT_COLLECTION_RAW_ARGS: usize = 4096;
const MAX_OPAQUE_DT_COLLECTION_TERMS: usize = 16 * 1024;
const MAX_OPAQUE_DT_COLLECTION_WORK: usize = 32 * 1024 * 1024;
const MAX_OPAQUE_DT_PAIR_WORK: usize = 1_000_000;
const MAX_CONGRUENCE_ROUNDS: usize = 64;

/// Exact preflight result for one query containing opaque datatype apps.
#[derive(Clone, Copy)]
pub(super) struct OpaqueDtCollectionScope {
    opaque_terms: usize,
}

impl OpaqueDtCollectionScope {
    pub(super) fn new(opaque_terms: usize) -> Option<Self> {
        (opaque_terms > 0 && opaque_terms <= MAX_OPAQUE_DT_TERMS).then_some(Self { opaque_terms })
    }

    pub(super) fn opaque_terms(self) -> usize {
        self.opaque_terms
    }
}

/// Allocation/work envelope checked before opaque-aware collection starts.
/// Counts raw application arity, not unique datatype terms, so a repeated term
/// in one large `distinct` cannot hide its argument clone or quadratic pairs.
pub(super) struct OpaqueDtCollectionBudget {
    query_terms: usize,
    dt_terms: usize,
    items: usize,
    raw_args: usize,
    work: usize,
    pair_work: usize,
    valid: bool,
}

impl OpaqueDtCollectionBudget {
    pub(super) fn new() -> Self {
        Self {
            query_terms: 0,
            dt_terms: 0,
            items: 0,
            raw_args: 0,
            work: 0,
            pair_work: 0,
            valid: true,
        }
    }

    pub(super) fn visit_term(&mut self) -> bool {
        self.query_terms = self.query_terms.saturating_add(1);
        self.valid &= self.query_terms <= MAX_OPAQUE_DT_COLLECTION_TERMS;
        self.charge_work(1)
    }

    pub(super) fn record_roots(&mut self, count: usize) -> bool {
        self.valid &= count <= MAX_OPAQUE_DT_COLLECTION_ROOTS;
        self.charge_raw_args(count) && self.charge_work(count)
    }

    pub(super) fn visit_app(&mut self, arity: usize) -> bool {
        self.valid &= arity <= MAX_OPAQUE_DT_COLLECTION_ITEMS;
        self.visit_children(arity) && self.charge_work(1)
    }

    pub(super) fn visit_children(&mut self, count: usize) -> bool {
        self.charge_raw_args(count) && self.charge_work(count)
    }

    pub(super) fn record_dt_term(&mut self) -> bool {
        self.dt_terms = self.dt_terms.saturating_add(1);
        self.valid &= self.dt_terms <= MAX_OPAQUE_DT_COLLECTION_ITEMS;
        self.valid
    }

    pub(super) fn record_signature_check(&mut self, descriptor_work: usize) -> bool {
        self.charge_work(descriptor_work)
    }

    pub(super) fn record_constructor(&mut self, arity: usize, name_bytes: usize) -> bool {
        let Some(raw_args) = arity.checked_mul(2) else {
            return self.invalidate();
        };
        let Some(name_work) = name_bytes
            .checked_mul(2)
            .and_then(|work| work.checked_add(256))
        else {
            return self.invalidate();
        };
        self.charge_raw_args(raw_args) && self.charge_work(raw_args.saturating_add(name_work))
    }

    pub(super) fn record_selector(&mut self, name_bytes: usize, copies: usize) -> bool {
        let Some(name_work) = name_bytes.checked_mul(copies) else {
            return self.invalidate();
        };
        self.charge_item() && self.charge_work(name_work.saturating_add(1))
    }

    pub(super) fn record_tester(&mut self, name_bytes: usize) -> bool {
        self.charge_item() && self.charge_work(name_bytes.saturating_add(1))
    }

    pub(super) fn record_equality(&mut self) -> bool {
        self.charge_item() && self.charge_work(1)
    }

    pub(super) fn record_distinct(&mut self, arity: usize) -> bool {
        if arity > MAX_OPAQUE_DT_COLLECTION_ITEMS {
            return self.invalidate();
        }
        let Some(raw_args) = arity.checked_mul(2) else {
            return self.invalidate();
        };
        let Some(pairs) = pair_count(arity) else {
            return self.invalidate();
        };
        self.charge_item()
            && self.charge_raw_args(raw_args)
            && self.charge_pair_work(pairs)
            && self.charge_work(raw_args.saturating_add(pairs))
    }

    pub(super) fn finish(
        &mut self,
        opaque_terms: usize,
        datatype_selectors: usize,
        constructors: usize,
        congruence_weight: usize,
    ) -> Option<OpaqueDtCollectionScope> {
        let selector_pairs = pair_count(datatype_selectors)?;
        let constructor_pairs = pair_count(constructors)?;
        let congruence = selector_pairs
            .checked_add(constructor_pairs)?
            .checked_mul(MAX_CONGRUENCE_ROUNDS)?
            .checked_mul(congruence_weight.max(1))?;
        let selector_scans = self
            .dt_terms
            .checked_mul(datatype_selectors)?
            .checked_mul(congruence_weight.max(1))?
            .checked_mul(16)?;
        if !self.charge_pair_work(congruence)
            || !self.charge_work(congruence.saturating_add(selector_scans))
            || !self.valid
        {
            return None;
        }
        OpaqueDtCollectionScope::new(opaque_terms)
    }

    fn charge_item(&mut self) -> bool {
        self.items = self.items.saturating_add(1);
        self.valid &= self.items <= MAX_OPAQUE_DT_COLLECTION_ITEMS;
        self.valid
    }

    fn charge_raw_args(&mut self, amount: usize) -> bool {
        self.raw_args = self.raw_args.saturating_add(amount);
        self.valid &= self.raw_args <= MAX_OPAQUE_DT_COLLECTION_RAW_ARGS;
        self.valid
    }

    fn charge_work(&mut self, amount: usize) -> bool {
        self.work = self.work.saturating_add(amount);
        self.valid &= self.work <= MAX_OPAQUE_DT_COLLECTION_WORK;
        self.valid
    }

    fn charge_pair_work(&mut self, amount: usize) -> bool {
        self.pair_work = self.pair_work.saturating_add(amount);
        self.valid &= self.pair_work <= MAX_OPAQUE_DT_PAIR_WORK;
        self.valid
    }

    fn invalidate(&mut self) -> bool {
        self.valid = false;
        false
    }
}

fn pair_count(arity: usize) -> Option<usize> {
    if arity < 2 {
        return Some(0);
    }
    arity.checked_sub(1)?.checked_mul(arity)?.checked_div(2)
}

pub(super) struct OpaqueDtConstructionBudget {
    active: bool,
    remaining: usize,
    /// Field-by-selector scans also run in native datatype construction, where
    /// the opaque work budget is intentionally inactive. Keep their aggregate
    /// comparison envelope unconditional so a large schema/query product
    /// cannot escape accounting on that lane.
    field_scan_remaining: usize,
    exhausted: bool,
}

impl OpaqueDtConstructionBudget {
    pub(super) fn new(opaque_terms: usize) -> Option<Self> {
        if opaque_terms > MAX_OPAQUE_DT_TERMS {
            return None;
        }
        Some(Self {
            active: opaque_terms != 0,
            remaining: MAX_OPAQUE_DT_WORK,
            field_scan_remaining: MAX_DT_FIELD_SCAN_COMPARISONS,
            exhausted: false,
        })
    }

    /// Reserve a conservative whole-schema allowance before constructing one
    /// class. Recursive class construction reserves again at each class.
    pub(super) fn charge_class(&mut self) -> bool {
        self.charge(MAX_CANDIDATE_WORK)
    }

    /// Reserve work *before* building candidate `k`. A directly-recursive
    /// candidate grows linearly in `k`, while cloning its accumulated prefix at
    /// each level is quadratic. Multiplying that square by the independently
    /// enforced schema-node bound covers both allocations and clone work.
    pub(super) fn charge_candidate(&mut self, k: usize) -> bool {
        let Some(span) = k.checked_add(1) else {
            return self.fail();
        };
        let Some(work) = span
            .checked_mul(span)
            .and_then(|square| square.checked_mul(MAX_CANDIDATE_WORK))
        else {
            return self.fail();
        };
        self.charge(work)
    }

    /// Charge the exact number of value nodes before a memo/dt_ground clone or
    /// a canonical rendering. This prevents output assembly from escaping the
    /// same budget after candidate construction has completed.
    pub(super) fn charge_value(&mut self, value: &ModelValue) -> bool {
        if !self.active {
            return true;
        }
        let Some(work) = model_value_work(value, self.remaining) else {
            return self.fail();
        };
        self.charge(work)
    }

    /// Precharge a checked upper bound on the canonical output length before
    /// rendering it.
    pub(super) fn charge_render(&mut self, value: &ModelValue) -> bool {
        if !self.active {
            return true;
        }
        let Some(bytes) = canonical_render_bytes(value, self.remaining) else {
            return self.fail();
        };
        self.charge(bytes)
    }

    /// Charge retained byte payloads whose allocation is separate from the
    /// value tree itself (for example a canonical-string clone).
    pub(super) fn charge_bytes(&mut self, bytes: usize) -> bool {
        self.charge(bytes)
    }

    /// Charge a scalar pin before cloning it into the completed model. The
    /// active opaque fragment admits Bool, bounded canonical BV, numeric
    /// (Int/Real via `Rational`), element-token, and string payloads — the
    /// same scalar fields ordinary (non-opaque) total-DT construction has
    /// always produced (#dt-opaque-app-model). Every admitted payload is
    /// charged by its actual size against the shared work budget, so an
    /// oversized pin still fails closed; structured payloads (Seq/FP/
    /// algebraic) remain outside the lane.
    pub(super) fn charge_scalar_pin(&mut self, value: &EvalValue) -> bool {
        if !self.active {
            return true;
        }
        let work = match value {
            EvalValue::Bool(_) => Some(1),
            EvalValue::BitVec { value, width }
                if *width <= 256
                    && value.sign() != num_bigint::Sign::Minus
                    && value.bits() <= u64::from(*width) =>
            {
                usize::try_from(*width)
                    .ok()
                    .map(|bits| bits.div_ceil(8) + 1)
            }
            EvalValue::Rational(value) => usize::try_from(value.numer().bits())
                .ok()
                .zip(usize::try_from(value.denom().bits()).ok())
                .and_then(|(numer, denom)| {
                    numer
                        .div_ceil(8)
                        .checked_add(denom.div_ceil(8))?
                        .checked_add(1)
                }),
            EvalValue::Element(token) => token.len().checked_add(1),
            EvalValue::String(text) => text.len().checked_add(1),
            _ => None,
        };
        let Some(work) = work else {
            return self.fail();
        };
        self.charge(work)
    }

    /// Precharge one retained constructor-name clone.
    pub(super) fn charge_name_clone(&mut self, name: &str) -> bool {
        self.charge(name.len().saturating_add(1))
    }

    /// Precharge constructor/exclusion name comparisons before filtering a
    /// class's remaining constructor choices.
    pub(super) fn charge_constructor_filter(
        &mut self,
        constructors: usize,
        exclusions: usize,
    ) -> bool {
        let Some(work) = constructors
            .checked_mul(exclusions.max(1))
            .and_then(|comparisons| comparisons.checked_mul(257))
        else {
            return self.fail();
        };
        self.charge(work)
    }

    pub(super) fn exhausted(&self) -> bool {
        self.exhausted
    }

    fn charge(&mut self, work: usize) -> bool {
        if !self.active {
            return true;
        }
        let Some(remaining) = self.remaining.checked_sub(work) else {
            return self.fail();
        };
        self.remaining = remaining;
        true
    }

    fn fail(&mut self) -> bool {
        self.exhausted = true;
        false
    }

    #[cfg(test)]
    pub(super) fn with_limit(limit: usize) -> Self {
        Self {
            active: true,
            remaining: limit,
            field_scan_remaining: MAX_DT_FIELD_SCAN_COMPARISONS,
            exhausted: false,
        }
    }
}
