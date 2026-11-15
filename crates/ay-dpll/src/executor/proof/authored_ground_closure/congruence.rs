// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Revisit parents whose argument classes changed instead of spending one
//! outer saturation round per SSA alias. Every edge still has an earlier
//! argument-equality explanation, and the existing strict replay proves it.

use super::*;
use ay_core::kani_compat::{DetHashMap, DetHashSet};
use std::collections::VecDeque;
/// The function a congruence signature is keyed on.
#[derive(Clone, PartialEq, Eq, Hash)]
enum CongruenceHead {
    App(Symbol),
    Ite,
    Not,
}

impl Executor {
    /// The exact function identity and current argument classes, as before.
    fn ground_congruence_signature(
        &self,
        closure: &GroundClosure,
        term: TermId,
    ) -> Option<(CongruenceHead, Vec<usize>)> {
        let (head, args) = match self.ctx.terms.get(term) {
            TermData::App(symbol, args) if !args.is_empty() && symbol.name() != "distinct" => {
                (CongruenceHead::App(symbol.clone()), args.clone())
            }
            TermData::Ite(c, t, e) => (CongruenceHead::Ite, vec![*c, *t, *e]),
            TermData::Not(t) => (CongruenceHead::Not, vec![*t]),
            _ => return None,
        };
        Some((
            head,
            args.iter()
                .map(|&a| closure.class(a))
                .collect::<Option<Vec<_>>>()?,
        ))
    }
    /// Requeue only parents of the class removed by a justified merge.
    /// Stale signatures remain safe: argument classes only merge, and their
    /// old representative can never become a current representative again.
    /// The caller shares a bounded signature-work allowance across rounds.
    pub(super) fn close_ground_congruence(
        &self,
        closure: &mut GroundClosure,
        budget: &mut SharedGroundWork,
    ) -> Option<()> {
        let mut uses: DetHashMap<usize, Vec<TermId>> = DetHashMap::default();
        let mut queue = VecDeque::new();
        let mut queued = DetHashSet::default();
        for &term in closure.nodes() {
            if let Some((_, classes)) = self.ground_congruence_signature(closure, term) {
                for class in classes {
                    uses.entry(class).or_default().push(term);
                }
                queue.push_back(term);
                queued.insert(term);
            }
        }
        let stop = self.make_proof_assembly_should_stop();
        let mut signatures: DetHashMap<(CongruenceHead, Vec<usize>), TermId> =
            DetHashMap::default();
        while let Some(term) = queue.pop_front() {
            budget.spend(1)?;
            if budget.remaining() % 256 == 0 && stop() {
                return None;
            }
            queued.remove(&term);
            let Some(signature) = self.ground_congruence_signature(closure, term) else {
                continue;
            };
            let Some(&other) = signatures.get(&signature) else {
                signatures.insert(signature, term);
                continue;
            };
            if self.ctx.terms.sort(other) != self.ctx.terms.sort(term) {
                continue;
            }
            let left = closure.class(other)?;
            let right = closure.class(term)?;
            if left == right {
                continue;
            }
            if closure.edges().len() >= MAX_EDGES {
                return None;
            }
            closure.merge(other, term, EdgeReason::Congruent);
            if let Some(parents) = uses.remove(&left) {
                for &parent in &parents {
                    if queued.insert(parent) {
                        queue.push_back(parent);
                    }
                }
                uses.entry(right).or_default().extend(parents);
            }
        }
        Some(())
    }
}
