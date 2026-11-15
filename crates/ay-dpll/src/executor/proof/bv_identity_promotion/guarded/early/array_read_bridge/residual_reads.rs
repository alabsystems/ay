// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Align actual reads through checked address equality, without assuming array
//! values. An offset reading chooses candidates only; the same joint BV lemma
//! proves every key equality and ordinary congruence proves each replacement.

use super::substitution::ImagePurpose;
use super::*;

type ReadImages = HashMap<TermId, (TermId, TermId)>;

impl ReadBridge<'_> {
    pub(super) fn plan_residual_read_image(
        &mut self,
        root: TermId,
    ) -> Option<(TermId, ReadImages)> {
        let Some(base) = self
            .address_norms
            .values()
            .map(|n| n.base)
            .min_by_key(|t| t.index())
        else {
            return Some((root, HashMap::default()));
        };
        let mut seen = HashSet::default();
        let mut pending = vec![(root, 0usize)];
        let mut representatives: HashMap<(TermId, TermId, TermId), (TermId, TermId)> =
            HashMap::default();
        let mut images = HashMap::default();
        while let Some((term, depth)) = pending.pop() {
            self.poll()?;
            if depth > MAX_SOURCE_DEPTH {
                return None;
            }
            self.executor.ctx.terms.entry_stamp(term)?;
            if seen.contains(&term) {
                continue;
            }
            if seen.len() >= MAX_TERMS {
                return None;
            }
            seen.insert(term);
            let children = self.children(term)?;
            pending.extend(children.iter().rev().map(|&child| (child, depth + 1)));
            let TermData::App(Symbol::Named(head), args) = self.executor.ctx.terms.get(term) else {
                continue;
            };
            let [array, key] = args.as_slice() else {
                continue;
            };
            let (array, key) = (*array, *key);
            if head != "select" || !matches!(self.executor.ctx.terms.get(array), TermData::Var(..))
            {
                continue;
            }
            let Sort::Array(shape) = self.executor.ctx.terms.sort(array) else {
                return None;
            };
            if self.executor.ctx.terms.sort(key) != &shape.index_sort
                || self.executor.ctx.terms.sort(term) != &shape.element_sort
                || !matches!(&shape.element_sort, Sort::BitVec(width) if (1..=128).contains(&width.width))
            {
                return None;
            }
            // This is only an exact, bounded search key, not a derived
            // premise. The actual key equality below must still be proved by
            // the joint BV lemma; unused normalization tautologies would only
            // consume proof steps and strict-check byte reservations.
            let Sort::BitVec(width) = self.executor.ctx.terms.sort(key) else {
                continue;
            };
            let width = width.width;
            if !(1..=128).contains(&width)
                || self.executor.ctx.terms.sort(base) != self.executor.ctx.terms.sort(key)
            {
                continue;
            }
            let offset = if key == base {
                0u32.into()
            } else {
                let Some(reading) = self.executor.ctx.terms.bv_offset_equality(key, base) else {
                    continue;
                };
                if reading.minuend != reading.subtrahend {
                    continue;
                }
                -reading.constant
            };
            let constant = self.executor.ctx.terms.mk_bitvec(offset, width);
            let group = (array, base, constant);
            if let Some(&(representative, representative_key)) = representatives.get(&group) {
                if term != representative {
                    let equality = self.equal(key, representative_key);
                    self.collect_side(equality)?;
                    images.insert(term, (representative, equality));
                }
            } else {
                representatives.insert(group, (term, key));
            }
        }
        let replacements = images
            .iter()
            .map(|(&from, &(to, _))| (from, (to, None)))
            .collect();
        let image = self
            .replacement_image(root, &replacements, ImagePurpose::Plan)?
            .0;
        Some((image, images))
    }

    pub(super) fn derive_residual_read_image(
        &mut self,
        root: TermId,
        target: TermId,
        unit: ProofId,
        images: &ReadImages,
    ) -> Option<ProofId> {
        let mut replacements = HashMap::default();
        for (&from, &(to, index_equality)) in images {
            self.poll()?;
            let index_unit = self.arithmetic_unit(index_equality)?;
            let equality = self.equal(from, to);
            let equality_unit = self.proof.add_rule_step(
                AletheRule::Cong,
                vec![equality],
                vec![index_unit],
                vec![],
            );
            replacements.insert(from, (to, Some(equality_unit)));
        }
        let (image, equality) =
            self.replacement_image(root, &replacements, ImagePurpose::Derive)?;
        if image != target {
            return None;
        }
        self.transport_image_unit(root, target, unit, equality?)
    }
}
