// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Derive an address substitution from an actual conjunct, never an assumed
//! provider fact. Planning changes no assertion; every transport uses ordinary
//! AndPos, congruence, equivalence and resolution over the original premise.

use super::*;

#[derive(Clone, Copy)]
pub(super) enum ImagePurpose {
    Plan,
    Derive,
}

pub(super) struct SourceBinding {
    from: TermId,
    to: TermId,
    premise: TermId,
    path: Vec<u32>,
    forward: bool,
}

impl ReadBridge<'_> {
    pub(super) fn source_address_binding(&mut self, root: TermId) -> Option<Option<SourceBinding>> {
        let mut references: HashMap<TermId, usize> = HashMap::default();
        let values: Vec<_> = self.plan_memo.values().copied().collect();
        for value in values {
            self.poll()?;
            for child in self.children(value)? {
                *references.entry(child).or_default() += 1;
            }
        }
        let mut best: Option<(usize, SourceBinding)> = None;
        let mut pending = vec![(root, Vec::new())];
        while let Some((term, path)) = pending.pop() {
            self.poll()?;
            let TermData::App(Symbol::Named(head), args) = self.executor.ctx.terms.get(term) else {
                continue;
            };
            if head == "and" {
                if path.len() >= MAX_SOURCE_DEPTH {
                    return None;
                }
                for (position, &child) in args.iter().enumerate().rev() {
                    let mut next = path.clone();
                    next.push(u32::try_from(position).ok()?);
                    pending.push((child, next));
                }
                continue;
            }
            if head != "=" || args.len() != 2 {
                continue;
            }
            for (from, to, forward) in [(args[0], args[1], true), (args[1], args[0], false)] {
                if !matches!(self.executor.ctx.terms.get(from), TermData::Var(..))
                    || self.executor.ctx.terms.sort(from) != self.executor.ctx.terms.sort(to)
                    || !matches!(self.executor.ctx.terms.sort(from), Sort::BitVec(width) if (1..=128).contains(&width.width))
                {
                    continue;
                }
                // Bounded search hint only: a declared word plus/minus a
                // literal. All actual substitution authority is the selected
                // equality conjunct, independently derived below.
                let TermData::App(Symbol::Named(op), parts) = self.executor.ctx.terms.get(to)
                else {
                    continue;
                };
                let [left, right] = parts.as_slice() else {
                    continue;
                };
                let simple = matches!(op.as_str(), "bvadd" | "bvsub")
                    && ((matches!(self.executor.ctx.terms.get(*left), TermData::Var(..))
                        && matches!(
                            self.executor.ctx.terms.get(*right),
                            TermData::Const(ay_core::Constant::BitVec { .. })
                        ))
                        || (op == "bvadd"
                            && matches!(self.executor.ctx.terms.get(*right), TermData::Var(..))
                            && matches!(
                                self.executor.ctx.terms.get(*left),
                                TermData::Const(ay_core::Constant::BitVec { .. })
                            )));
                let count = references.get(&from).copied().unwrap_or(0);
                if !simple || count <= 1 {
                    continue;
                }
                if best.as_ref().is_none_or(|(rank, binding)| {
                    count > *rank || (count == *rank && from.index() < binding.from.index())
                }) {
                    best = Some((
                        count,
                        SourceBinding {
                            from,
                            to,
                            premise: term,
                            path: path.clone(),
                            forward,
                        },
                    ));
                }
            }
        }
        Some(best.map(|(_, binding)| binding))
    }

    pub(super) fn substitution_image(
        &mut self,
        root: TermId,
        binding: &SourceBinding,
        unit: Option<ProofId>,
    ) -> Option<(TermId, Option<ProofId>)> {
        let replacements = HashMap::from_iter([(binding.from, (binding.to, unit))]);
        let purpose = if unit.is_some() {
            ImagePurpose::Derive
        } else {
            ImagePurpose::Plan
        };
        self.replacement_image(root, &replacements, purpose)
    }

    pub(super) fn replacement_image(
        &mut self,
        root: TermId,
        replacements: &HashMap<TermId, (TermId, Option<ProofId>)>,
        purpose: ImagePurpose,
    ) -> Option<(TermId, Option<ProofId>)> {
        if replacements.len() > MAX_TERMS {
            return None;
        }
        self.substitute_term(
            root,
            replacements,
            purpose,
            &mut HashSet::default(),
            &mut HashMap::default(),
            0,
        )
    }

    fn substitute_term(
        &mut self,
        term: TermId,
        replacements: &HashMap<TermId, (TermId, Option<ProofId>)>,
        purpose: ImagePurpose,
        seen: &mut HashSet<TermId>,
        memo: &mut HashMap<TermId, (TermId, Option<ProofId>)>,
        depth: usize,
    ) -> Option<(TermId, Option<ProofId>)> {
        self.poll()?;
        if depth > MAX_SOURCE_DEPTH {
            return None;
        }
        self.executor.ctx.terms.entry_stamp(term)?;
        if let Some(&result) = memo.get(&term) {
            return Some(result);
        }
        if seen.len() >= MAX_TERMS || !seen.insert(term) {
            return None;
        }
        if let Some(&(image, unit)) = replacements.get(&term) {
            self.executor.ctx.terms.entry_stamp(image)?;
            if self.executor.ctx.terms.sort(term) != self.executor.ctx.terms.sort(image)
                || (matches!(purpose, ImagePurpose::Derive) && unit.is_none())
            {
                return None;
            }
            let result = (
                image,
                if matches!(purpose, ImagePurpose::Derive) {
                    unit
                } else {
                    None
                },
            );
            memo.insert(term, result);
            return Some(result);
        }
        let children = self.children(term)?;
        let mut next = Vec::with_capacity(children.len());
        let mut premises = Vec::new();
        for &child in &children {
            let (image, equality) =
                self.substitute_term(child, replacements, purpose, seen, memo, depth + 1)?;
            next.push(image);
            premises.extend(equality);
        }
        let image = self.rebuild(term, &children, &next)?;
        let equality = if image != term && matches!(purpose, ImagePurpose::Derive) {
            let equality = self.equal(term, image);
            Some(
                self.proof
                    .add_rule_step(AletheRule::Cong, vec![equality], premises, vec![]),
            )
        } else {
            None
        };
        let result = (image, equality);
        memo.insert(term, result);
        Some(result)
    }

    pub(super) fn derive_substitution(
        &mut self,
        root: TermId,
        target: TermId,
        unit: ProofId,
        binding: &SourceBinding,
    ) -> Option<ProofId> {
        self.poll()?;
        let helper_steps = binding
            .path
            .len()
            .checked_mul(2)?
            .checked_add(usize::from(!binding.forward))?;
        if self.proof.steps.len().checked_add(helper_steps)? > MAX_STEPS {
            return None;
        }
        let mut equality_unit = Executor::emit_and_pos_chain(
            &mut self.executor.ctx.terms,
            &mut self.proof,
            unit,
            root,
            &binding.path,
            binding.premise,
        )?;
        if !binding.forward {
            let equality = self.equal(binding.from, binding.to);
            equality_unit = self.proof.add_rule_step(
                AletheRule::Symm,
                vec![equality],
                vec![equality_unit],
                vec![],
            );
        }
        let (image, equality) = self.substitution_image(root, binding, Some(equality_unit))?;
        if image != target {
            return None;
        }
        self.transport_image_unit(root, target, unit, equality?)
    }

    pub(super) fn transport_image_unit(
        &mut self,
        root: TermId,
        target: TermId,
        unit: ProofId,
        equality_unit: ProofId,
    ) -> Option<ProofId> {
        let equality = self.equal(root, target);
        let negative_eq = self.executor.ctx.terms.mk_not_raw(equality);
        let negative_root = self.executor.ctx.terms.mk_not_raw(root);
        let implication = self.proof.add_rule_step(
            AletheRule::EquivPos2,
            vec![negative_eq, negative_root, target],
            vec![],
            vec![],
        );
        let implication = self.proof.add_resolution(
            vec![negative_root, target],
            equality,
            implication,
            equality_unit,
        );
        let result = self
            .proof
            .add_resolution(vec![target], root, implication, unit);
        self.poll()?;
        Some(result)
    }
}
