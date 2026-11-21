// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use ay_core::kani_compat::DetHashMap as Map;

use super::inventory::Inventory;
use super::{charge, entries, same_sort, Atom, Checked, Pay, Probe, Refusal};

pub(super) struct Closure<'p> {
    probe: &'p Probe,
    parents: Vec<usize>,
    values: Vec<Option<Atom>>,
    hard: Vec<Option<Atom>>,
}
impl Closure<'_> {
    pub(super) fn changes_value(
        &self,
        inventory: &Inventory<'_>,
        pay: &mut Pay<'_>,
    ) -> Checked<bool> {
        for (index, node) in inventory.nodes.iter().enumerate() {
            self.probe.check("changed-value", Some(node.term), None);
            if node.alias.is_some() {
                // A present soft raw Bool is only a prior proposal. Its source
                // definition follows current UF leaves even without a merge.
                let current = self.evaluate(inventory, node.term, pay)?;
                if let Some(old) = &node.value {
                    if !current.same(old, pay)? {
                        return Ok(true);
                    }
                } else {
                    return Ok(true);
                }
            } else if node.leaf {
                let old = node.value.as_ref().ok_or(Refusal::Unsupported)?;
                if !self.value(index, pay)?.same(old, pay)? {
                    return Ok(true);
                }
            }
        }
        Ok(false)
    }

    pub(super) fn representative(&self, mut index: usize, pay: &mut Pay<'_>) -> Checked<usize> {
        for _ in 0..=self.parents.len() {
            pay(1, 0)?;
            let parent = *self.parents.get(index).ok_or(Refusal::Unsupported)?;
            if parent == index {
                return Ok(index);
            }
            index = parent;
        }
        Err(Refusal::Unsupported)
    }
    pub(super) fn value(&self, index: usize, pay: &mut Pay<'_>) -> Checked<&Atom> {
        self.values[self.representative(index, pay)?]
            .as_ref()
            .ok_or(Refusal::Unsupported)
    }
    pub(super) fn is_hard(&self, index: usize, pay: &mut Pay<'_>) -> Checked<bool> {
        Ok(self.hard[self.representative(index, pay)?].is_some())
    }
    pub(super) fn evaluate(
        &self,
        inventory: &Inventory<'_>,
        term: ay_core::TermId,
        pay: &mut Pay<'_>,
    ) -> Checked<Atom> {
        let mut leaf = |term, pay: &mut Pay<'_>| -> Checked<Option<super::evaluate::Resolution>> {
            self.probe.check("leaf-value", Some(term), None);
            pay(1, 0)?;
            let Some(&index) = inventory.by_term.get(&term) else {
                return Ok(None);
            };
            if let Some(target) = inventory.nodes[index].alias {
                return Ok(Some(super::evaluate::Resolution::Alias(target)));
            }
            if !inventory.nodes[index].leaf {
                return Ok(None);
            }
            Ok(Some(super::evaluate::Resolution::Value(
                self.value(index, pay)?.copy(pay)?,
            )))
        };
        super::evaluate::resolved_value_observed(inventory.ctx, term, &mut leaf, pay, self.probe)
    }
    fn validate_disequalities(&self, inventory: &Inventory<'_>, pay: &mut Pay<'_>) -> Checked<()> {
        for &(left, right) in &inventory.disequalities {
            self.probe
                .check("known-disequality", Some(left), Some(right));
            let left_value = self.evaluate(inventory, left, pay)?;
            let right_value = self.evaluate(inventory, right, pay)?;
            // Value equality matters even when graph representatives differ.
            // Same spelling in different nominal sorts is never compared.
            if same_sort(
                inventory.ctx.terms.sort(left),
                inventory.ctx.terms.sort(right),
                pay,
            )? && left_value.same(&right_value, pay)?
            {
                self.probe
                    .check("known-disequality-conflict", Some(left), Some(right));
                return Err(Refusal::Conflict);
            }
        }
        Ok(())
    }
    fn validate_semantics(&self, inventory: &Inventory<'_>, pay: &mut Pay<'_>) -> Checked<()> {
        // Derived terms can constrain a live class, but do not acquire a free
        // model variable or authority from a speculative raw compound value.
        let mut first_of_class: Map<ay_core::TermId, usize> = Map::default();
        for (left, a) in inventory.nodes.iter().enumerate() {
            if let Some(pin) = &a.hard {
                self.probe.check("semantic-hard-pin", Some(a.term), None);
                if !self.evaluate(inventory, a.term, pay)?.same(pin, pay)? {
                    self.probe
                        .check("semantic-hard-pin-conflict", Some(a.term), None);
                    return Err(Refusal::Conflict);
                }
            }
            // Compare with the first node of the same live class only
            // (AY-SMT-3): sort and value equality are both `==`, so every
            // node agreeing with that first one is exactly every pair
            // agreeing, as the former all-pairs scan checked.
            pay(1, 0)?;
            let Some(class) = a.live_class else {
                continue;
            };
            let Some(&first) = first_of_class.get(&class) else {
                entries(pay, 1)?;
                first_of_class.insert(class, left);
                continue;
            };
            let b = &inventory.nodes[first];
            self.probe
                .check("semantic-class", Some(a.term), Some(b.term));
            if !same_sort(a.sort, b.sort, pay)?
                || !self
                    .evaluate(inventory, a.term, pay)?
                    .same(&self.evaluate(inventory, b.term, pay)?, pay)?
            {
                self.probe
                    .check("semantic-class-conflict", Some(a.term), Some(b.term));
                return Err(Refusal::Conflict);
            }
        }
        for &(left, right) in inventory.equalities.iter().chain(&inventory.semantic_peers) {
            self.probe
                .check("semantic-equality", Some(left), Some(right));
            if !self
                .evaluate(inventory, left, pay)?
                .same(&self.evaluate(inventory, right, pay)?, pay)?
            {
                self.probe
                    .check("semantic-equality-conflict", Some(left), Some(right));
                return Err(Refusal::Conflict);
            }
        }
        self.validate_disequalities(inventory, pay)
    }
    fn merge(
        &mut self,
        inventory: &Inventory<'_>,
        left: usize,
        right: usize,
        pay: &mut Pay<'_>,
    ) -> Checked<bool> {
        let left = self.representative(left, pay)?;
        let right = self.representative(right, pay)?;
        if left == right {
            return Ok(false);
        }
        if !same_sort(inventory.nodes[left].sort, inventory.nodes[right].sort, pay)? {
            return Err(Refusal::Conflict);
        }
        self.probe.check(
            "merge-hard-values",
            Some(inventory.nodes[left].term),
            Some(inventory.nodes[right].term),
        );
        if let (Some(left), Some(right)) = (&self.hard[left], &self.hard[right]) {
            if !left.same(right, pay)? {
                return Err(Refusal::Conflict);
            }
        }
        let (keep, retire) = if left < right {
            (left, right)
        } else {
            (right, left)
        };
        // A genuine hard pin wins; otherwise use the current value of the
        // deterministic least occurrence, not sampled-row absence/provenance.
        let pin = self.hard[keep].as_ref().or(self.hard[retire].as_ref());
        let value = pin
            .or(self.values[keep].as_ref())
            .ok_or(Refusal::Unsupported)?
            .copy(pay)?;
        let pin = pin.map(|value| value.copy(pay)).transpose()?;
        self.parents[retire] = keep;
        self.values[keep] = Some(value);
        self.hard[keep] = pin;
        // The mutation is to scratch only; a failed check discards ALL work.
        self.validate_disequalities(inventory, pay)?;
        Ok(true)
    }
}

pub(super) fn close<'p>(
    inventory: &Inventory<'_>,
    pay: &mut Pay<'_>,
    probe: &'p Probe,
) -> Checked<Closure<'p>> {
    entries(
        pay,
        inventory
            .nodes
            .len()
            .checked_mul(3)
            .ok_or(Refusal::Unsupported)?,
    )?;
    let mut closure = Closure {
        probe,
        parents: Vec::new(),
        values: Vec::new(),
        hard: Vec::new(),
    };
    for (index, node) in inventory.nodes.iter().enumerate() {
        closure.parents.push(index);
        closure.values.push(
            node.value
                .as_ref()
                .map(|value| value.copy(pay))
                .transpose()?,
        );
        closure.hard.push(
            node.hard
                .as_ref()
                .map(|value| value.copy(pay))
                .transpose()?,
        );
    }
    // Preserve complete live equality components before using model-only
    // congruence. Missing graph nodes were explicit None, never singleton proof.
    //
    // Each leaf merges with the FIRST (least-index) leaf of its live class
    // (AY-SMT-3). The former all-pairs scan made exactly these merges in this
    // order: for each leaf, its first same-class partner is that least leaf
    // and every later partner was already in the same component, a no-op.
    // It paid for N^2/2 pairs, and on SMT-COMP incremental QF_AUFLIA
    // 2721719d (985 inventory nodes) that pair scan took about 1 s of every
    // check-sat that reached UF model recovery.
    let mut first_leaf_of_class: Map<ay_core::TermId, usize> = Map::default();
    for (left, a) in inventory.nodes.iter().enumerate() {
        pay(1, 0)?;
        let (true, Some(class)) = (a.leaf, a.live_class) else {
            continue;
        };
        match first_leaf_of_class.get(&class) {
            Some(&right) => {
                closure.merge(inventory, left, right, pay)?;
            }
            None => {
                entries(pay, 1)?;
                first_leaf_of_class.insert(class, left);
            }
        }
    }
    for &(left, right) in &inventory.equalities {
        pay(2, 0)?;
        if let (Some(&left), Some(&right)) =
            (inventory.by_term.get(&left), inventory.by_term.get(&right))
        {
            if inventory.nodes[left].leaf && inventory.nodes[right].leaf {
                closure.merge(inventory, left, right, pay)?;
            }
        }
    }
    closure.validate_disequalities(inventory, pay)?;
    // Every productive step retires a distinct component. At most N-1 such
    // steps can occur; no cyclic RF/UF syntax can refill this finite work.
    for _ in 0..=inventory.nodes.len() {
        let mut changed = false;
        for (left, a) in inventory.apps.iter().enumerate() {
            for b in &inventory.apps[..left] {
                charge(pay, &[1, a.symbol.name().len(), b.symbol.name().len()], &[])?;
                // Full Symbol equality, not name-only overloading/index erasure.
                if a.symbol != b.symbol || a.arguments.len() != b.arguments.len() {
                    continue;
                }
                let mut same = true;
                for (&x, &y) in a.arguments.iter().zip(&b.arguments) {
                    probe.check("point-argument", Some(x), Some(y));
                    if !same_sort(
                        inventory.ctx.terms.sort(x),
                        inventory.ctx.terms.sort(y),
                        pay,
                    )? || !closure
                        .evaluate(inventory, x, pay)?
                        .same(&closure.evaluate(inventory, y, pay)?, pay)?
                    {
                        same = false;
                        break;
                    }
                }
                if same {
                    changed |= closure.merge(inventory, a.output, b.output, pay)?;
                }
            }
        }
        if !changed {
            closure.validate_semantics(inventory, pay)?;
            return Ok(closure);
        }
    }
    Err(Refusal::Unsupported)
}
