// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! A rule-level refutation of an authored negated reflexive equality conjunct.

use super::*;
use ay_core::{term::TermData, AletheRule, Symbol, TermId};

impl Executor {
    pub(super) fn early_reflexive_memory_candidate(&mut self, root: TermId) -> Option<Proof> {
        let mut pending = vec![(root, Vec::new())];
        let mut scanned = 0usize;
        while let Some((term, path)) = pending.pop() {
            scanned = scanned.checked_add(1)?;
            if scanned > 8_192 {
                return None;
            }
            match self.ctx.terms.get(term) {
                TermData::App(Symbol::Named(head), args) if head == "and" => {
                    for (index, &child) in args.iter().enumerate().rev() {
                        let mut child_path = path.clone();
                        child_path.push(u32::try_from(index).ok()?);
                        pending.push((child, child_path));
                    }
                }
                TermData::Not(equality) => {
                    let equality = *equality;
                    if !matches!(self.ctx.terms.get(equality),
                        TermData::App(Symbol::Named(head), args)
                            if head == "=" && args.len() == 2 && args[0] == args[1])
                    {
                        continue;
                    }
                    let mut candidate = Proof::new();
                    let premise = candidate.add_assume(root, None);
                    let negative = Self::emit_and_pos_chain(
                        &mut self.ctx.terms,
                        &mut candidate,
                        premise,
                        root,
                        &path,
                        term,
                    )?;
                    let positive = candidate.add_rule_step(
                        AletheRule::EqReflexive,
                        vec![equality],
                        Vec::new(),
                        Vec::new(),
                    );
                    candidate.add_resolution(Vec::new(), equality, negative, positive);
                    return Some(candidate);
                }
                _ => (),
            }
        }
        None
    }
}
