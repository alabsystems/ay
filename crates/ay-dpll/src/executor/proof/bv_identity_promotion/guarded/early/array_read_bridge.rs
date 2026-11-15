// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Derive demanded read values with existing array axioms before BV replay.
//! The original assertion is the only Assume. Rewritten roots are derived by
//! congruence/equivalence, never installed as additional input assertions.

use ay_core::{
    kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet},
    AletheRule, Proof, ProofId, Sort, Symbol, TermData, TermId, TheoryLemmaKind,
};

use super::Executor;
use std::rc::Rc;

mod read_hints;
mod residual_reads;
mod substitution;

use read_hints::ReadHints;

// The existing bounded ground producer's source/visit/step allowances. This
// producer uses ArrayRowChain; sparse BV's independent MAX_STORES=64 is unchanged.
const MAX_TERMS: usize = 2_048;
const MAX_VISITS: usize = 2_048 * 16;
const MAX_STEPS: usize = 16_384;
const MAX_SOURCE_DEPTH: usize = 96;
// One jointly checked lemma contains the address normalizations, exact index
// equalities and negation of the planned root. It fits the executor's existing
// aggregate reservation for ONE expensive BV lemma, not merely its structural
// eight-lemma ceiling. Boolean projections are ordinary checked derivations.
const SIDE_GROUP_SIZE: usize = 512;

impl Executor {
    pub(super) fn early_array_read_memory_candidate(&mut self, root: TermId) -> Option<Proof> {
        self.ctx.terms.entry_stamp(root)?;
        if self.ctx.terms.sort(root) != &Sort::Bool {
            return None;
        }
        let stop = self.make_proof_assembly_should_stop();
        let mut visits = 0;
        let read_hints = ReadHints::preflight(&self.ctx, root, &mut visits, &stop)?;
        let mut proof = Proof::new();
        let assumed = proof.add_assume(root, None);
        let mut builder = ReadBridge {
            executor: self,
            proof,
            memo: HashMap::default(),
            arithmetic: HashMap::default(),
            source_seen: HashSet::default(),
            rewrite_seen: HashSet::default(),
            side_seen: HashSet::default(),
            side_literals: Vec::new(),
            side_unique: HashSet::default(),
            read_hints,
            plan_memo: HashMap::default(),
            address_norms: HashMap::default(),
            visits,
            stop: &stop,
        };
        builder
            .collect(root, 0)
            .or_else(|| builder.declined("source/side preflight"))?;
        let planned = *builder.plan_memo.get(&root)?;
        if planned == root {
            return None;
        }
        let binding = builder.source_address_binding(planned)?;
        let bound_target = if let Some(binding) = binding.as_ref() {
            builder.substitution_image(planned, binding, None)?.0
        } else {
            planned
        };
        let (target, residual_reads) = builder.plan_residual_read_image(bound_target)?;
        let negative = builder.executor.ctx.terms.mk_not_raw(target);
        if !builder
            .executor
            .early_ground_memory_terms_print_faithfully(&[target, negative])
        {
            return builder.declined("derived root print contract");
        }
        if builder.side_literals.len() >= SIDE_GROUP_SIZE {
            return None;
        }
        builder.side_unique.insert(negative);
        builder.side_literals.push(negative);
        builder
            .prove_side_conditions()
            .or_else(|| builder.declined("side proof construction"))?;
        let (normalized, equality) = builder
            .rewrite(root, 0)
            .or_else(|| builder.declined("read rewrite"))?;
        if normalized != planned {
            return None;
        }
        let equality = equality?;
        let eq = builder.equal(root, normalized);
        let not_eq = builder.executor.ctx.terms.mk_not_raw(eq);
        let not_root = builder.executor.ctx.terms.mk_not_raw(root);
        let implication = builder.proof.add_rule_step(
            AletheRule::EquivPos2,
            vec![not_eq, not_root, normalized],
            vec![],
            vec![],
        );
        let implication =
            builder
                .proof
                .add_resolution(vec![not_root, normalized], eq, implication, equality);
        let mut derived =
            builder
                .proof
                .add_resolution(vec![normalized], root, implication, assumed);
        if let Some(binding) = binding.as_ref() {
            derived = builder.derive_substitution(normalized, bound_target, derived, binding)?;
        }
        if !residual_reads.is_empty() {
            derived = builder.derive_residual_read_image(
                bound_target,
                target,
                derived,
                &residual_reads,
            )?;
        }
        let lemma = builder.arithmetic_unit(negative)?;
        builder.proof.add_resolution(vec![], target, derived, lemma);
        builder.poll()?;
        Some(builder.proof)
    }
}

struct ReadBridge<'a> {
    executor: &'a mut Executor,
    proof: Proof,
    memo: HashMap<TermId, (TermId, Option<ProofId>)>,
    arithmetic: HashMap<TermId, ProofId>,
    source_seen: HashSet<TermId>,
    rewrite_seen: HashSet<TermId>,
    side_seen: HashSet<TermId>,
    side_literals: Vec<TermId>,
    side_unique: HashSet<TermId>,
    // Read-only preflight hints are bound to exact original terms/epoch.
    // All actual relations are independently derived by the kernel below.
    read_hints: ReadHints,
    plan_memo: HashMap<TermId, TermId>,
    address_norms: HashMap<TermId, AddressNormalization>,
    visits: usize,
    stop: &'a dyn Fn() -> bool,
}

impl ReadBridge<'_> {
    fn declined<T>(&self, phase: &str) -> Option<T> {
        crate::executor::unsat_cert::probe_cert_reject(|| {
            format!(
            "array-read bridge: {phase} declined visits={} source={} rewritten={} sides={} steps={}",
            self.visits, self.source_seen.len(), self.memo.len(), self.side_unique.len(), self.proof.steps.len(),
        )
        });
        #[cfg(test)]
        eprintln!("ARRAY_READ_BRIDGE_DECLINED phase={phase} visits={} source={} rewritten={} sides={} steps={}",
            self.visits, self.source_seen.len(), self.memo.len(), self.side_unique.len(), self.proof.steps.len());
        None
    }
    fn poll(&mut self) -> Option<()> {
        self.visits = self.visits.checked_add(1)?;
        (self.visits <= MAX_VISITS && self.proof.steps.len() <= MAX_STEPS && !(self.stop)())
            .then_some(())
    }

    fn equal(&mut self, left: TermId, right: TermId) -> TermId {
        self.executor
            .ctx
            .terms
            .mk_app(Symbol::named("="), [left, right], Sort::Bool)
    }

    fn children(&self, term: TermId) -> Option<Vec<TermId>> {
        ReadHints::children(&self.executor.ctx.terms, term)
    }

    fn collect(&mut self, term: TermId, depth: usize) -> Option<()> {
        self.poll()?;
        if depth > MAX_SOURCE_DEPTH {
            return None;
        }
        self.executor.ctx.terms.entry_stamp(term)?;
        if self.source_seen.contains(&term) {
            return Some(());
        }
        // Reserve before descent: pending parents count, not only completed
        // memo entries. Unwinding cannot silently exceed the source cap.
        if self.source_seen.len() >= MAX_TERMS {
            return None;
        }
        self.source_seen.insert(term);
        let children = self.children(term)?;
        let mut next = Vec::with_capacity(children.len());
        for &child in &children {
            self.collect(child, depth + 1)?;
            next.push(*self.plan_memo.get(&child)?);
        }
        let rebuilt = self.rebuild(term, &children, &next)?;
        let result = if let Some(plan) = self.read_plan(rebuilt) {
            for guard in plan.guards {
                let TermData::App(_, pair) = self.executor.ctx.terms.get(guard) else {
                    return None;
                };
                let [left, right] = pair.as_slice() else {
                    return None;
                };
                let (left, right) = (*left, *right);
                let reading = self.executor.ctx.terms.bv_offset_equality(left, right)?;
                if reading.minuend != reading.subtrahend {
                    return None;
                }
                self.normalize_address(left, reading.minuend)?;
                self.normalize_address(right, reading.minuend)?;
            }
            if plan.key != plan.at {
                let index = self.equal(plan.key, plan.at);
                self.collect_side(index)?;
            }
            plan.value
        } else {
            rebuilt
        };
        self.plan_memo.insert(term, result);
        Some(())
    }

    fn normalize_address(&mut self, address: TermId, base: TermId) -> Option<()> {
        if let Some(normal) = self.address_norms.get(&address) {
            return (normal.base == base).then_some(());
        }
        self.poll()?;
        let Sort::BitVec(width) = self.executor.ctx.terms.sort(address) else {
            return None;
        };
        let width = width.width;
        if self.executor.ctx.terms.sort(base) != &Sort::bitvec(width) {
            return None;
        }
        let value = if address == base {
            0u32.into()
        } else {
            let reading = self.executor.ctx.terms.bv_offset_equality(address, base)?;
            if reading.minuend != reading.subtrahend {
                return None;
            }
            -reading.constant
        };
        let constant = self.executor.ctx.terms.mk_bitvec(value, width);
        let difference = self.executor.ctx.terms.mk_app(
            Symbol::named("bvsub"),
            [address, base],
            Sort::bitvec(width),
        );
        let literal = self.equal(difference, constant);
        self.collect_side(literal)?;
        self.address_norms.insert(
            address,
            AddressNormalization {
                base,
                difference,
                constant,
                literal,
                unit: None,
            },
        );
        Some(())
    }

    fn collect_side(&mut self, literal: TermId) -> Option<()> {
        if self.side_unique.contains(&literal) {
            return Some(());
        }
        if self.side_literals.len() >= SIDE_GROUP_SIZE {
            return None;
        }
        let mut pending = vec![(literal, 0usize)];
        while let Some((term, depth)) = pending.pop() {
            if depth > MAX_SOURCE_DEPTH {
                return None;
            }
            if self.side_seen.contains(&term) {
                continue;
            }
            self.poll()?;
            self.executor.ctx.terms.entry_stamp(term)?;
            if !matches!(
                self.executor.ctx.terms.sort(term),
                Sort::Bool | Sort::BitVec(_)
            ) {
                return None;
            }
            let children = self.children(term)?;
            // No array read, array memory, binder or assumed intermediate
            // state may be smuggled into an allegedly array-free side lemma.
            if matches!(self.executor.ctx.terms.get(term), TermData::App(Symbol::Named(op), _) if op == "select" || op == "store")
            {
                return None;
            }
            self.side_seen.insert(term);
            pending.extend(children.into_iter().map(|child| (child, depth + 1)));
        }
        self.side_unique.insert(literal);
        self.side_literals.push(literal);
        Some(())
    }

    fn balanced_group(&mut self, literals: &[TermId]) -> Option<TermId> {
        self.poll()?;
        if let [literal] = literals {
            return Some(*literal);
        }
        if literals.is_empty() {
            return None;
        }
        let chunk = literals.len().div_ceil(4);
        let mut children = Vec::with_capacity(4);
        for part in literals.chunks(chunk) {
            children.push(self.balanced_group(part)?);
        }
        Some(
            self.executor
                .ctx
                .terms
                .mk_app(Symbol::named("and"), &children, Sort::Bool),
        )
    }

    fn group_units(&mut self, group: TermId, unit: ProofId) -> Option<()> {
        self.poll()?;
        if self.side_unique.contains(&group) {
            self.arithmetic.insert(group, unit);
            return Some(());
        }
        let TermData::App(Symbol::Named(op), children) = self.executor.ctx.terms.get(group) else {
            return None;
        };
        if op != "and" || !(2..=4).contains(&children.len()) {
            return None;
        }
        let children = children.clone();
        let negative = self.executor.ctx.terms.mk_not_raw(group);
        for (position, child) in children.into_iter().enumerate() {
            let projection = self.proof.add_rule_step(
                AletheRule::AndPos(position as u32),
                vec![negative, child],
                vec![],
                vec![group],
            );
            let child_unit = self
                .proof
                .add_resolution(vec![child], group, projection, unit);
            self.group_units(child, child_unit)?;
        }
        Some(())
    }

    fn prove_side_conditions(&mut self) -> Option<()> {
        let mut literals = std::mem::take(&mut self.side_literals);
        let negative = literals.pop()?;
        // Only small address facts need a projection tree. Keep the complete
        // planned root at depth1 instead of copying its lowered expression
        // along every parent of that tree.
        let root = if literals.is_empty() {
            negative
        } else {
            let facts = self.balanced_group(&literals)?;
            self.executor
                .ctx
                .terms
                .mk_app(Symbol::named("and"), [negative, facts], Sort::Bool)
        };
        if !self
            .executor
            .early_ground_memory_terms_print_faithfully(&[root])
        {
            return None;
        }
        let unit =
            self.proof
                .add_theory_lemma_with_kind("bv", vec![root], TheoryLemmaKind::BvBitBlast);
        self.group_units(root, unit)?;
        // Reuse the exact projected normalization unit for every guard that
        // reaches this address; avoid two repeated map probes per index pair.
        for normal in self.address_norms.values_mut() {
            normal.unit = Some(*self.arithmetic.get(&normal.literal)?);
        }
        Some(())
    }

    fn arithmetic_unit(&mut self, literal: TermId) -> Option<ProofId> {
        self.poll()?;
        self.arithmetic.get(&literal).copied()
    }

    fn guard_unit(&mut self, guard: TermId) -> Option<ProofId> {
        self.poll()?;
        let negative = self.executor.ctx.terms.mk_not_raw(guard);
        if let Some(&unit) = self.arithmetic.get(&negative) {
            return Some(unit);
        }
        let TermData::App(_, args) = self.executor.ctx.terms.get(guard) else {
            return None;
        };
        let [left, right] = args.as_slice() else {
            return None;
        };
        let left = *self.address_norms.get(left)?;
        let right = *self.address_norms.get(right)?;
        if left.base != right.base || left.constant == right.constant {
            return None;
        }
        let left_unit = left.unit?;
        let right_unit = right.unit?;
        let difference = self.equal(left.difference, right.difference);
        let congruence = self.proof.add_theory_lemma_with_kind(
            "euf",
            vec![negative, difference],
            TheoryLemmaKind::EufCongruent,
        );
        let constants = self.equal(left.constant, right.constant);
        let not_left = self.executor.ctx.terms.mk_not_raw(left.literal);
        let not_difference = self.executor.ctx.terms.mk_not_raw(difference);
        let not_right = self.executor.ctx.terms.mk_not_raw(right.literal);
        let transitive = self.proof.add_theory_lemma_with_kind(
            "euf",
            vec![not_left, not_difference, not_right, constants],
            TheoryLemmaKind::EufTransitive,
        );
        let distinct = self.executor.ctx.terms.mk_not_raw(constants);
        // Existing zero-variable Boolean evaluation. The printer already
        // derives exact closed BV disequalities with checked standard rules.
        let evaluated = self.proof.add_theory_lemma_with_kind(
            "bool",
            vec![distinct],
            TheoryLemmaKind::BoolTautology,
        );
        let unit = self.proof.add_rule_step(
            AletheRule::Resolution,
            vec![negative],
            vec![transitive, left_unit, right_unit, evaluated, congruence],
            vec![],
        );
        self.arithmetic.insert(negative, unit);
        Some(unit)
    }

    fn rebuild(&mut self, term: TermId, children: &[TermId], next: &[TermId]) -> Option<TermId> {
        if children == next {
            return Some(term);
        }
        Some(match self.executor.ctx.terms.get(term).clone() {
            TermData::App(head, _) => self.executor.ctx.terms.mk_app(
                head,
                next,
                self.executor.ctx.terms.sort(term).clone(),
            ),
            TermData::Not(_) if self.executor.ctx.terms.sort(next[0]) == &Sort::Bool => {
                self.executor.ctx.terms.mk_not_raw(next[0])
            }
            TermData::Ite(..)
                if self.executor.ctx.terms.sort(next[0]) == &Sort::Bool
                    && self.executor.ctx.terms.sort(next[1])
                        == self.executor.ctx.terms.sort(next[2]) =>
            {
                self.executor
                    .ctx
                    .terms
                    .mk_ite_raw(next[0], next[1], next[2])
            }
            _ => return None,
        })
    }

    fn rewrite(&mut self, term: TermId, depth: usize) -> Option<(TermId, Option<ProofId>)> {
        self.poll()?;
        if depth > MAX_SOURCE_DEPTH {
            return None;
        }
        self.executor.ctx.terms.entry_stamp(term)?;
        if let Some(&result) = self.memo.get(&term) {
            return Some(result);
        }
        if !self.source_seen.contains(&term)
            || self.rewrite_seen.len() >= MAX_TERMS
            || !self.rewrite_seen.insert(term)
        {
            return None;
        }
        let children = self.children(term)?;
        let mut next = Vec::with_capacity(children.len());
        let mut premises = Vec::new();
        for &child in &children {
            let (rewritten, equality) = self.rewrite(child, depth + 1)?;
            next.push(rewritten);
            premises.extend(equality);
        }
        let rebuilt = self.rebuild(term, &children, &next)?;
        let congruence = if rebuilt == term {
            None
        } else {
            let equality = self.equal(term, rebuilt);
            Some(
                self.proof
                    .add_rule_step(AletheRule::Cong, vec![equality], premises, vec![]),
            )
        };
        let (result, read) = self.read(rebuilt).unwrap_or((rebuilt, None));
        let equality = match (congruence, read) {
            (Some(first), Some(second)) => {
                let equality = self.equal(term, result);
                Some(self.proof.add_rule_step(
                    AletheRule::Trans,
                    vec![equality],
                    vec![first, second],
                    vec![],
                ))
            }
            (first, second) => first.or(second),
        };
        self.memo.insert(term, (result, equality));
        Some((result, equality))
    }

    fn read_plan(&mut self, term: TermId) -> Option<ReadPlan> {
        let hint = self
            .read_hints
            .read(&self.executor.ctx, term, &mut self.visits, self.stop)?;
        let guards = hint
            .skipped_keys
            .iter()
            .map(|&key| self.equal(hint.at, key))
            .collect();
        Some(ReadPlan {
            array: hint.array,
            key: hint.key,
            at: hint.at,
            value: hint.value,
            position: hint.position,
            element_sort: hint.element_sort,
            guards,
        })
    }

    fn read(&mut self, term: TermId) -> Option<(TermId, Option<ProofId>)> {
        let ReadPlan {
            array,
            key,
            at,
            value,
            position,
            element_sort,
            guards,
        } = self.read_plan(term)?;
        let mut units = Vec::with_capacity(guards.len());
        for &guard in &guards {
            units.push(self.guard_unit(guard)?);
        }
        let selected = if key == at {
            term
        } else {
            self.executor
                .ctx
                .terms
                .mk_app(Symbol::named("select"), [array, at], element_sort)
        };
        let conclusion = self.equal(selected, value);
        let mut clause = guards;
        clause.push(conclusion);
        let kind = if position == 0 {
            TheoryLemmaKind::ArraySelectStore { index_eq: true }
        } else {
            TheoryLemmaKind::ArrayRowChain
        };
        let lemma = self
            .proof
            .add_theory_lemma_with_kind("arrays", clause, kind);
        let chain = if units.is_empty() {
            lemma
        } else {
            // All guards are independently refuted units. N-ary resolution
            // avoids materializing quadratic intermediate guard clauses.
            let mut premises = vec![lemma];
            premises.extend(units);
            self.proof
                .add_rule_step(AletheRule::Resolution, vec![conclusion], premises, vec![])
        };
        let unit = if selected == term {
            chain
        } else {
            let index = self.equal(key, at);
            let index_unit = self.arithmetic_unit(index)?;
            let moved = self.equal(term, selected);
            let moved =
                self.proof
                    .add_rule_step(AletheRule::Cong, vec![moved], vec![index_unit], vec![]);
            let final_eq = self.equal(term, value);
            self.proof.add_rule_step(
                AletheRule::Trans,
                vec![final_eq],
                vec![moved, chain],
                vec![],
            )
        };
        Some((value, Some(unit)))
    }
}

struct ReadPlan {
    array: TermId,
    key: TermId,
    at: TermId,
    value: TermId,
    position: usize,
    element_sort: Sort,
    guards: Vec<TermId>,
}

#[derive(Clone, Copy)]
struct AddressNormalization {
    base: TermId,
    difference: TermId,
    constant: TermId,
    literal: TermId,
    unit: Option<ProofId>,
}

#[cfg(test)]
mod tests;

#[cfg(test)]
mod read_hints_tests;
