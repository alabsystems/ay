// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Conditional read preservation outside a modular interval. Proposals use
//! actual earlier array/index equalities; existing array, BV and Boolean
//! rules must validate the entire emitted derivation.

use ay_core::kani_compat::{DetHashMap, DetHashSet};
use num_traits::ToPrimitive;

use super::emit::ClosureEmitter;
use super::slice::MAX_MEMBERS_PER_SITE;
use super::*;

// A producer domain, not a larger checker/search allowance. The actual E1
// materialization has sixteen byte stores. All planning also shares the
// existing goal allowance and all emission shares the ordinary step bound.
const MAX_RANGE_STORES: usize = 64;

#[derive(Clone)]
struct Key {
    original: TermId,
    image: TermId,
    base: TermId,
}

struct Link {
    array: TermId,
    store: TermId,
    base: TermId,
    keys: Vec<Key>,
}

pub(super) struct ReadRangePlan {
    goal: TermId,
    inside: TermId,
    equality: TermId,
    observe: TermId,
    range_base: TermId,
    first: TermId,
    last: TermId,
    links: Vec<Link>,
}

struct Clause {
    step: ProofId,
    literals: Vec<TermId>,
}

fn spend(work: &mut usize) -> Option<()> {
    *work = work.checked_sub(1)?;
    Some(())
}

fn literal(terms: &TermStore, term: TermId, width: u32) -> Option<u128> {
    let TermData::Const(Constant::BitVec {
        value,
        width: actual,
    }) = terms.get(term)
    else {
        return None;
    };
    let value = value.to_u128()?;
    (*actual == width && value <= (u128::MAX >> (128 - width))).then_some(value)
}

/// Only a variable or a single literal offset. Existing closure offset
/// normalization supplies any more elaborate spelling together with its
/// earlier equality. This matcher creates no arithmetic fact.
fn address(terms: &TermStore, term: TermId, width: u32) -> Option<(TermId, u128)> {
    if terms.entry_stamp(term).is_none() || terms.sort(term).bitvec_width() != Some(width) {
        return None;
    }
    if matches!(terms.get(term), TermData::Var(..)) {
        return Some((term, 0));
    }
    let TermData::App(Symbol::Named(head), args) = terms.get(term) else {
        return None;
    };
    let &[left, right] = args.as_slice() else {
        return None;
    };
    let (base, value) = if matches!(terms.get(left), TermData::Var(..)) {
        let value = literal(terms, right, width)?;
        match head.as_str() {
            "bvadd" => (left, value),
            "bvsub" => (left, value.wrapping_neg() & (u128::MAX >> (128 - width))),
            _ => return None,
        }
    } else if head == "bvadd" && matches!(terms.get(right), TermData::Var(..)) {
        (right, literal(terms, left, width)?)
    } else {
        return None;
    };
    (terms.sort(base).bitvec_width() == Some(width)).then_some((base, value))
}

impl Executor {
    pub(super) fn ground_read_range_plan(
        &self,
        closure: &GroundClosure,
        goal: TermId,
        work: &mut usize,
    ) -> Option<Option<ReadRangePlan>> {
        spend(work)?;
        let TermData::App(Symbol::Named(head), args) = self.ctx.terms.get(goal) else {
            return Some(None);
        };
        let &[inside, equality] = args.as_slice() else {
            return Some(None);
        };
        if head != "or" {
            return Some(None);
        }
        let TermData::App(Symbol::Named(head), args) = self.ctx.terms.get(inside) else {
            return Some(None);
        };
        let &[difference, bound] = args.as_slice() else {
            return Some(None);
        };
        if head != "bvult" {
            return Some(None);
        }
        let TermData::App(Symbol::Named(head), args) = self.ctx.terms.get(difference) else {
            return Some(None);
        };
        let &[observe, range_base] = args.as_slice() else {
            return Some(None);
        };
        if head != "bvsub" {
            return Some(None);
        }
        let Some(width) = self
            .ctx
            .terms
            .sort(observe)
            .bitvec_width()
            .filter(|w| (1..=128).contains(w))
        else {
            return Some(None);
        };
        if self.ctx.terms.sort(range_base) != self.ctx.terms.sort(observe)
            || !matches!(self.ctx.terms.get(observe), TermData::Var(..))
            || !matches!(self.ctx.terms.get(range_base), TermData::Var(..))
        {
            return Some(None);
        }
        let Some(length) = literal(&self.ctx.terms, bound, width).filter(|n| *n != 0) else {
            return Some(None);
        };
        let Some((first, last)) = decode_eq_local(&self.ctx.terms, equality) else {
            return Some(None);
        };
        let (Some((mut array, first_key)), Some((last_array, last_key))) = (
            select_parts_local(&self.ctx.terms, first),
            select_parts_local(&self.ctx.terms, last),
        ) else {
            return Some(None);
        };
        if first_key != observe
            || last_key != observe
            || self.ctx.terms.sort(first) != self.ctx.terms.sort(last)
            || self.ctx.terms.sort(array) != self.ctx.terms.sort(last_array)
        {
            return Some(None);
        }
        let Some(last_class) = closure.class(last_array) else {
            return Some(None);
        };
        let stop = self.make_proof_assembly_should_stop();
        let mut members: DetHashMap<usize, Vec<TermId>> = DetHashMap::default();
        for &node in closure.nodes() {
            if stop() {
                return None;
            }
            spend(work)?;
            let class = closure.class(node)?;
            let entries = members.entry(class).or_default();
            if entries.len() < MAX_MEMBERS_PER_SITE {
                entries.try_reserve(1).ok()?;
                entries.push(node);
            }
        }
        let mut visited = DetHashSet::default();
        let mut links = Vec::new();
        let mut count = 0usize;
        loop {
            if stop() {
                return None;
            }
            spend(work)?;
            let Some(class) = closure.class(array) else {
                return Some(None);
            };
            if class == last_class {
                break;
            }
            if !visited.insert(class) {
                return Some(None);
            }
            let Some(store) = members.get(&class).and_then(|nodes| {
                nodes
                    .iter()
                    .copied()
                    .find(|&node| store_parts_local(&self.ctx.terms, node).is_some())
            }) else {
                return Some(None);
            };
            let mut cursor = store;
            let mut keys = Vec::new();
            while let Some((base, index, value)) = store_parts_local(&self.ctx.terms, cursor) {
                if stop() {
                    return None;
                }
                spend(work)?;
                count = count.checked_add(1)?;
                if count > MAX_RANGE_STORES
                    || self.ctx.terms.sort(cursor) != self.ctx.terms.sort(array)
                    || self.ctx.terms.sort(base) != self.ctx.terms.sort(array)
                    || self.ctx.terms.sort(index).bitvec_width() != Some(width)
                    || self.ctx.terms.sort(value) != self.ctx.terms.sort(first)
                {
                    return Some(None);
                }
                let Some(indices) = closure.class(index).and_then(|c| members.get(&c)) else {
                    return Some(None);
                };
                let mut chosen = None;
                for &image in indices {
                    if stop() {
                        return None;
                    }
                    spend(work)?;
                    if let Some((base, offset)) = address(&self.ctx.terms, image, width) {
                        if offset < length && closure.same_class(base, range_base) {
                            chosen = Some(Key {
                                original: index,
                                image,
                                base,
                            });
                            break;
                        }
                    }
                }
                let Some(key) = chosen else {
                    return Some(None);
                };
                keys.try_reserve(1).ok()?;
                keys.push(key);
                cursor = base;
            }
            if keys.is_empty() {
                return Some(None);
            }
            links.try_reserve(1).ok()?;
            links.push(Link {
                array,
                store,
                base: cursor,
                keys,
            });
            array = cursor;
        }
        if links.is_empty() {
            return Some(None);
        }
        Some(Some(ReadRangePlan {
            goal,
            inside,
            equality,
            observe,
            range_base,
            first,
            last,
            links,
        }))
    }

    fn range_eq(&mut self, a: TermId, b: TermId) -> TermId {
        self.ctx
            .terms
            .mk_app(Symbol::named("="), [a, b], Sort::Bool)
    }

    /// Only explicit positive/negative pivot pairs are accepted. The clauses
    /// here use atomic equalities and one positive range predicate; duplicate
    /// literals are sets, as in the existing resolution owner.
    fn resolve_range_clauses(
        &mut self,
        emitter: &mut ClosureEmitter<'_>,
        left: Clause,
        right: Clause,
        pivot: TermId,
    ) -> Option<Clause> {
        emitter.admit_steps(1)?;
        let negative = self.ctx.terms.mk_not_raw(pivot);
        if !left.literals.contains(&pivot)
            || !right.literals.contains(&negative)
            || left.literals.contains(&negative)
            || right.literals.contains(&pivot)
        {
            return None;
        }
        let mut seen = DetHashSet::default();
        let mut literals = Vec::new();
        for term in left
            .literals
            .into_iter()
            .filter(|&t| t != pivot)
            .chain(right.literals.into_iter().filter(|&t| t != negative))
        {
            if seen.insert(term) {
                literals.try_reserve(1).ok()?;
                literals.push(term);
            }
        }
        emitter.admit_steps(1)?;
        let step = emitter
            .proof
            .add_resolution(literals.clone(), pivot, left.step, right.step);
        Some(Clause { step, literals })
    }

    fn range_select_alias(
        &mut self,
        emitter: &mut ClosureEmitter<'_>,
        from: TermId,
        to: TermId,
        observe: TermId,
        limit: usize,
    ) -> Option<DerivedUnit> {
        if self.make_proof_assembly_should_stop()() {
            return None;
        }
        emitter.admit_steps(1)?;
        let sort = match self.ctx.terms.sort(from) {
            Sort::Array(shape) => shape.element_sort.clone(),
            _ => return None,
        };
        let alias = if from == to {
            None
        } else {
            Some(self.emit_closure_path_unit(emitter, from, to, limit)?)
        };
        // Explaining the source alias can consume the final available step.
        // Admit the select congruence before interning its proof-only terms.
        emitter.admit_steps(1)?;
        let left = self
            .ctx
            .terms
            .mk_app(Symbol::named("select"), [from, observe], sort.clone());
        let right = self
            .ctx
            .terms
            .mk_app(Symbol::named("select"), [to, observe], sort);
        let literal = self.range_eq(left, right);
        let step = if let Some(alias) = alias {
            emitter.proof.add_rule_step(
                AletheRule::Cong,
                vec![literal],
                vec![alias.step],
                Vec::new(),
            )
        } else {
            emitter.proof.add_theory_lemma_with_kind(
                "euf",
                vec![literal],
                TheoryLemmaKind::EufReflexive,
            )
        };
        Some(DerivedUnit { literal, step })
    }

    pub(super) fn emit_ground_read_range(
        &mut self,
        emitter: &mut ClosureEmitter<'_>,
        plan: ReadRangePlan,
    ) -> Option<DerivedUnit> {
        let limit = emitter.closure.edges().len();
        let stop = self.make_proof_assembly_should_stop();
        if stop() {
            return None;
        }
        emitter.admit_steps(1)?;
        let mut aliases = Vec::new();
        let mut path = Vec::new();
        let mut rows = Vec::new();
        let mut keys = Vec::new();
        let mut seen = DetHashSet::default();
        for link in &plan.links {
            if stop() {
                return None;
            }
            if link.array != link.store {
                let alias =
                    self.range_select_alias(emitter, link.array, link.store, plan.observe, limit)?;
                path.push(alias.literal);
                aliases.push(alias);
            }
            emitter.admit_steps(1)?;
            let sort = self.ctx.terms.sort(plan.first).clone();
            let read = self.ctx.terms.mk_app(
                Symbol::named("select"),
                [link.store, plan.observe],
                sort.clone(),
            );
            let base_read =
                self.ctx
                    .terms
                    .mk_app(Symbol::named("select"), [link.base, plan.observe], sort);
            let equality = self.range_eq(read, base_read);
            let mut literals = Vec::new();
            for key in &link.keys {
                let guard = self.range_eq(plan.observe, key.original);
                if !literals.contains(&guard) {
                    literals.push(guard);
                }
                if seen.insert(guard) {
                    keys.push((guard, key.clone()));
                }
            }
            literals.push(equality);
            emitter.admit_steps(1)?;
            let step = emitter.proof.add_theory_lemma_with_kind(
                "array",
                literals.clone(),
                TheoryLemmaKind::ArrayRowChain,
            );
            rows.push((equality, Clause { step, literals }));
            path.push(equality);
        }
        let (target_array, _) = select_parts_local(&self.ctx.terms, plan.last)?;
        let final_base = plan.links.last()?.base;
        if final_base != target_array {
            let end =
                self.range_select_alias(emitter, final_base, target_array, plan.observe, limit)?;
            path.push(end.literal);
            aliases.push(end);
        }
        let mut combined = if rows.len() == 1 && rows[0].0 == plan.equality {
            rows.pop()?.1
        } else {
            emitter.admit_steps(1)?;
            let mut transitive: Vec<_> = path
                .into_iter()
                .map(|p| self.ctx.terms.mk_not_raw(p))
                .collect();
            transitive.push(plan.equality);
            emitter.admit_steps(1)?;
            let step = emitter.proof.add_theory_lemma_with_kind(
                "euf",
                transitive.clone(),
                TheoryLemmaKind::EufTransitive,
            );
            let mut tail: Vec<_> = rows
                .iter()
                .map(|(e, _)| self.ctx.terms.mk_not_raw(*e))
                .collect();
            tail.push(plan.equality);
            let step = self.resolve_closure_units(emitter, step, transitive, &aliases, &tail)?;
            let mut combined = Clause {
                step,
                literals: tail,
            };
            for (pivot, row) in rows {
                combined = self.resolve_range_clauses(emitter, row, combined, pivot)?;
            }
            combined
        };

        // One jointly checked BV conjunction, rather than a renewed expensive
        // lemma allowance per store. Source alias premises remain conditional
        // inside this theorem and are resolved using actual earlier edges.
        let mut formulas = Vec::new();
        let mut cases = Vec::new();
        for (guard, key) in keys {
            if stop() {
                return None;
            }
            let mut premises = Vec::new();
            if key.original != key.image {
                premises.push(self.emit_closure_path_unit(
                    emitter,
                    key.original,
                    key.image,
                    limit,
                )?);
            }
            if key.base != plan.range_base {
                premises.push(self.emit_closure_path_unit(
                    emitter,
                    key.base,
                    plan.range_base,
                    limit,
                )?);
            }
            emitter.admit_steps(1)?;
            let mut literals: Vec<_> = premises
                .iter()
                .map(|p| self.ctx.terms.mk_not_raw(p.literal))
                .collect();
            literals.push(self.ctx.terms.mk_not_raw(guard));
            literals.push(plan.inside);
            let formula = self
                .ctx
                .terms
                .mk_app(Symbol::named("or"), literals.clone(), Sort::Bool);
            formulas.push(formula);
            cases.push((guard, formula, literals, premises));
        }
        emitter.admit_steps(1)?;
        // A singleton conjunction is normalized away on the wire. Prove
        // its sole implication directly, avoiding an unrenderable and_pos.
        let group = match formulas.as_slice() {
            [] => return None,
            [formula] => *formula,
            _ => self
                .ctx
                .terms
                .mk_app(Symbol::named("and"), formulas, Sort::Bool),
        };
        emitter.admit_steps(1)?;
        let checked = emitter.proof.add_theory_lemma_with_kind(
            "bv",
            vec![group],
            TheoryLemmaKind::BvBitBlast,
        );
        for (position, (guard, formula, literals, premises)) in cases.into_iter().enumerate() {
            if stop() {
                return None;
            }
            let projected = if group == formula {
                Clause {
                    step: checked,
                    literals: vec![group],
                }
            } else {
                emitter.admit_steps(1)?;
                let negative_group = self.ctx.terms.mk_not_raw(group);
                let introduced = emitter.proof.add_rule_step(
                    AletheRule::AndPos(u32::try_from(position).ok()?),
                    vec![negative_group, formula],
                    Vec::new(),
                    Vec::new(),
                );
                self.resolve_range_clauses(
                    emitter,
                    Clause {
                        step: checked,
                        literals: vec![group],
                    },
                    Clause {
                        step: introduced,
                        literals: vec![negative_group, formula],
                    },
                    group,
                )?
            };
            let mut clause = vec![self.ctx.terms.mk_not_raw(formula)];
            clause.extend(literals.iter().copied());
            emitter.admit_steps(1)?;
            let introduced = emitter.proof.add_rule_step(
                AletheRule::OrPos(0),
                clause.clone(),
                Vec::new(),
                Vec::new(),
            );
            let flat = self.resolve_range_clauses(
                emitter,
                projected,
                Clause {
                    step: introduced,
                    literals: clause,
                },
                formula,
            )?;
            let expected = [self.ctx.terms.mk_not_raw(guard), plan.inside];
            let step = self.resolve_closure_units(
                emitter,
                flat.step,
                flat.literals,
                &premises,
                &expected,
            )?;
            combined = self.resolve_range_clauses(
                emitter,
                combined,
                Clause {
                    step,
                    literals: expected.to_vec(),
                },
                guard,
            )?;
        }
        if combined.literals.len() != 2
            || !combined.literals.contains(&plan.inside)
            || !combined.literals.contains(&plan.equality)
        {
            return None;
        }
        let step = self.emit_coverage_or_unit(
            emitter,
            combined.step,
            &[plan.inside, plan.equality],
            plan.goal,
        )?;
        Some(DerivedUnit {
            literal: plan.goal,
            step,
        })
    }
}
