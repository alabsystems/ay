// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Exact scoped Seq membership in native datatype acyclicity explanations.

use super::DtSolver;
use ay_core::{
    proof_validation::{
        owned_subvalue_cycle_with_progress, OwnedSubvalueBudget, OwnedSubvalueConstructor,
        OwnedSubvalueCycle, OwnedSubvalueEdgeKind, OwnedSubvalueRefusal,
    },
    resource, Symbol, TermData, TermId, TheoryLit, TheorySolver,
};
use std::mem::size_of;

fn progress(work: usize, _storage: usize) -> bool {
    let cost = u64::try_from(work).unwrap_or(u64::MAX);
    resource::current_guard().is_none_or(|guard| guard.tick(cost).is_ok())
        && !resource::check_stop_requested()
}
fn pay(
    owner: &mut OwnedSubvalueBudget,
    work: usize,
    bytes: usize,
) -> Result<(), OwnedSubvalueRefusal> {
    owner.charge_with_progress(work, bytes, &mut progress)
}

impl DtSolver<'_> {
    pub(super) fn record_seq_owned_guard(&mut self, term: TermId, value: bool) {
        let TermData::App(Symbol::Named(name), args) = self.terms.get(term) else {
            return;
        };
        if args.len() != 2 || !matches!(name.as_str(), "<" | "<=" | ">" | ">=") {
            return;
        }
        if self.seq_owned_refused {
            return;
        }
        if pay(&mut self.seq_owned_budget, 1, 0).is_err() {
            self.seq_owned_refused = true;
            return;
        }
        if self.seq_owned_guards.len() == self.seq_owned_guards.capacity() {
            let capacity = self.seq_owned_guards.capacity().saturating_mul(2).max(4);
            if pay(
                &mut self.seq_owned_budget,
                self.seq_owned_guards.len(),
                capacity.saturating_mul(size_of::<TheoryLit>()),
            )
            .is_err()
                || self
                    .seq_owned_guards
                    .try_reserve_exact(capacity - self.seq_owned_guards.len())
                    .is_err()
            {
                self.seq_owned_refused = true;
                return;
            }
        }
        self.seq_owned_guards.push(TheoryLit::new(term, value));
    }

    fn seq_owned_witness(
        &self,
        owner: &mut OwnedSubvalueBudget,
    ) -> Result<Option<OwnedSubvalueCycle>, OwnedSubvalueRefusal> {
        let count = self.terms.len();
        pay(owner, count, count.saturating_mul(size_of::<TermId>()))?;
        if count > 4096 {
            return Err(OwnedSubvalueRefusal::Limit);
        }
        let mut universe = Vec::new();
        universe
            .try_reserve_exact(count)
            .map_err(|_| OwnedSubvalueRefusal::Allocation)?;
        universe.extend((0..count).map(|index| TermId(index as u32)));
        pay(
            owner,
            self.ctor_to_dt.capacity(),
            self.ctor_to_dt
                .len()
                .saturating_mul(size_of::<OwnedSubvalueConstructor<'_>>()),
        )?;
        let mut constructors = Vec::new();
        constructors
            .try_reserve_exact(self.ctor_to_dt.len())
            .map_err(|_| OwnedSubvalueRefusal::Allocation)?;
        constructors.extend(
            self.ctor_to_dt
                .iter()
                .map(|(identity, carrier)| OwnedSubvalueConstructor { identity, carrier }),
        );
        // The guard scan is bounded before each callback consultation. No model
        // value is read; only exact still-live asserted guard literals qualify.
        let callback_quote = self
            .parent
            .capacity()
            .saturating_mul(self.parent.len().saturating_add(1))
            .saturating_add(self.seq_owned_guards.len())
            .saturating_add(1);
        pay(owner, count.saturating_mul(callback_quote), 0)?;
        owned_subvalue_cycle_with_progress(
            self.terms,
            &constructors,
            &universe,
            &mut |term| {
                (
                    u64::from(self.find(term).0),
                    self.seq_owned_guards
                        .iter()
                        .rev()
                        .find(|literal| literal.term == term)
                        .map(|literal| literal.value),
                )
            },
            owner,
            &mut progress,
        )
    }

    pub(super) fn check_seq_owned_cycle(
        &mut self,
    ) -> Result<Option<Vec<TheoryLit>>, OwnedSubvalueRefusal> {
        // Do not charge or alter unrelated datatype-only checks. The native
        // constructor arguments, not source spelling, identify this feature.
        if !self.seq_owned_possible {
            return Ok(None);
        }
        if self.seq_owned_refused {
            return Err(OwnedSubvalueRefusal::Limit);
        }
        // Keep one cumulative owner even through independent reconstruction;
        // neither scope rollback nor a new witness attempt replenishes it.
        let mut owner =
            std::mem::replace(&mut self.seq_owned_budget, OwnedSubvalueBudget::new(0, 0));
        let result = self.check_seq_owned_cycle_inner(&mut owner);
        self.seq_owned_budget = owner;
        result
    }
    fn check_seq_owned_cycle_inner(
        &mut self,
        owner: &mut OwnedSubvalueBudget,
    ) -> Result<Option<Vec<TheoryLit>>, OwnedSubvalueRefusal> {
        let Some(witness) = self.seq_owned_witness(owner)? else {
            return Ok(None);
        };
        let mut literals = Vec::new();
        let count = self
            .asserted_eq_lits
            .len()
            .saturating_add(witness.edges.len().saturating_mul(2));
        pay(owner, count, count.saturating_mul(size_of::<TheoryLit>()))?;
        literals
            .try_reserve_exact(count)
            .map_err(|_| OwnedSubvalueRefusal::Allocation)?;
        // Retain the complete actual equality inventory. Native independent
        // reconstruction, not a guessed path pedigree, proves it suffices.
        literals.extend(
            self.asserted_eq_lits
                .iter()
                .map(|&term| TheoryLit::new(term, true)),
        );
        for edge in &witness.edges {
            if let OwnedSubvalueEdgeKind::SequenceNth { lower, upper } = edge.kind {
                literals.extend(lower);
                literals.push(upper);
            }
        }
        pay(owner, literals.len().saturating_mul(literals.len()), 0)?;
        literals.sort_unstable();
        literals.dedup();
        if literals.is_empty() {
            return Err(OwnedSubvalueRefusal::InvalidSource);
        }
        if !self.recheck_seq_owned_literals(&literals, owner)? {
            return Err(OwnedSubvalueRefusal::InvalidSource);
        }
        Ok(Some(literals))
    }
    fn recheck_seq_owned_literals(
        &self,
        literals: &[TheoryLit],
        owner: &mut OwnedSubvalueBudget,
    ) -> Result<bool, OwnedSubvalueRefusal> {
        let count = self.terms.len();
        let mut bytes = 0usize;
        let mut names = 0usize;
        pay(
            owner,
            self.datatype_defs
                .capacity()
                .saturating_add(self.ctor_selectors.capacity()),
            0,
        )?;
        for (name, constructors) in &self.datatype_defs {
            pay(owner, name.len().saturating_add(constructors.len()), 0)?;
            names = names
                .saturating_add(name.len())
                .saturating_add(constructors.len());
            for ctor in constructors {
                pay(owner, ctor.len().saturating_add(1), 0)?;
                names = names.saturating_add(ctor.len());
            }
        }
        for (name, selectors) in &self.ctor_selectors {
            pay(owner, name.len().saturating_add(selectors.len()), 0)?;
            names = names
                .saturating_add(name.len())
                .saturating_add(selectors.len());
            for selector in selectors {
                pay(owner, selector.len().saturating_add(1), 0)?;
                names = names.saturating_add(selector.len());
            }
        }
        bytes = bytes
            .saturating_add(names.saturating_mul(16))
            .saturating_add(count.saturating_mul(count).saturating_mul(256));
        pay(
            owner,
            names.saturating_add(count.saturating_mul(count)),
            bytes,
        )?;
        // The legacy constructor registrar is recursive. Admit its exact
        // constructor-only depth before invoking it in this new recheck path.
        pay(owner, count, count.saturating_mul(size_of::<usize>()))?;
        let mut heights = Vec::<usize>::new();
        heights
            .try_reserve_exact(count)
            .map_err(|_| OwnedSubvalueRefusal::Allocation)?;
        for raw in 0..count {
            let term = TermId(raw as u32);
            let height = match self.terms.get(term) {
                TermData::App(Symbol::Named(name), args) => {
                    pay(
                        owner,
                        self.ctor_to_dt
                            .capacity()
                            .saturating_add(1)
                            .saturating_mul(name.len().saturating_add(1)),
                        0,
                    )?;
                    if self.ctor_to_dt.contains_key(name.as_str()) {
                        pay(owner, args.len(), 0)?;
                        let mut height = 1usize;
                        for argument in args {
                            if argument.0 as usize >= raw {
                                return Err(OwnedSubvalueRefusal::InvalidSource);
                            }
                            height = height.max(heights[argument.0 as usize].saturating_add(1));
                        }
                        height
                    } else {
                        0
                    }
                }
                _ => 0,
            };
            if height > 128 {
                return Err(OwnedSubvalueRefusal::Limit);
            }
            heights.push(height);
        }
        let mut fresh = DtSolver::new(self.terms);
        for (name, constructors) in &self.datatype_defs {
            fresh.register_datatype(name, constructors);
        }
        for (constructor, selectors) in &self.ctor_selectors {
            fresh.register_ctor_selectors(constructor, selectors);
        }
        for literal in literals {
            fresh.assert_literal(literal.term, literal.value);
        }
        // Rebuild the native equality consequences independently. Productive
        // rounds merge classes, so at most one round per source term is needed.
        for _ in 0..count.saturating_add(1) {
            pay(
                owner,
                count
                    .saturating_mul(count)
                    .saturating_mul(names.saturating_add(1)),
                0,
            )?;
            let before = fresh.union_trail.len();
            fresh.apply_selector_projection();
            fresh.apply_constructor_congruence();
            // Injectivity may imply a field equality used by the cycle. Its
            // own contradiction also establishes the exact source set UNSAT.
            if fresh.check_injectivity_conflicts().is_some() {
                return Ok(true);
            }
            if fresh.union_trail.len() == before {
                break;
            }
        }
        Ok(fresh.seq_owned_witness(owner)?.is_some())
    }
}

#[cfg(test)]
mod tests;
