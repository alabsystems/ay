// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Recognition of the complete live preprocessor-collapse proof shape.

use super::*;

pub(super) struct FalseCollapseShape {
    pub(super) assume: Option<TermId>,
    pub(super) assume_count: usize,
    pub(super) false_step: Option<(TermId, TermId)>,
    pub(super) trust_false: bool,
    pub(super) lia_lemma: bool,
}

impl Executor {
    /// Recognize only the complete, uniquely-closing collapse proof.
    ///
    /// Theory-lemma and ordinary-step encodings of the `(not false)` wiring are
    /// equivalent here. Any extra live rule, repeated closing resolution, or
    /// malformed false step declines the repair without changing the proof.
    pub(super) fn recognize_false_collapse_shape(
        &self,
        proof: &Proof,
    ) -> Option<FalseCollapseShape> {
        let live = taut_surface::live_steps(proof)?;
        let mut shape = FalseCollapseShape {
            assume: None,
            assume_count: 0,
            false_step: None,
            trust_false: false,
            lia_lemma: false,
        };
        let mut closing = false;
        for (index, step) in proof.steps.iter().enumerate() {
            if !live[index] {
                continue;
            }
            match step {
                ProofStep::Assume(term) => {
                    shape.assume_count += 1;
                    if shape.assume.is_none() {
                        shape.assume = Some(*term);
                    }
                }
                ProofStep::TheoryLemma {
                    kind: TheoryLemmaKind::LiaGeneric,
                    ..
                } if !shape.lia_lemma => shape.lia_lemma = true,
                ProofStep::Step {
                    rule: AletheRule::False,
                    clause,
                    premises,
                    args,
                } if shape.false_step.is_none() && clause.len() == 1 && premises.is_empty() => {
                    if args.len() == 1 {
                        shape.false_step = Some((clause[0], args[0]));
                    } else if !matches!(
                        self.ctx.terms.get(atom_of(&self.ctx.terms, clause[0])),
                        TermData::Const(ay_core::term::Constant::Bool(false))
                    ) {
                        return None;
                    }
                }
                ProofStep::Step {
                    rule: AletheRule::Trust,
                    clause,
                    premises,
                    ..
                } if !shape.trust_false
                    && clause.len() == 1
                    && premises.is_empty()
                    && matches!(
                        self.ctx.terms.get(clause[0]),
                        TermData::Const(ay_core::term::Constant::Bool(false))
                    ) =>
                {
                    shape.trust_false = true
                }
                // A theory-lemma `(cl (not false))` is wiring, not authority.
                ProofStep::TheoryLemma { clause, kind, .. }
                    if kind.is_trust()
                        && clause.len() == 1
                        && matches!(
                            self.ctx.terms.get(atom_of(&self.ctx.terms, clause[0])),
                            TermData::Const(ay_core::term::Constant::Bool(false))
                        )
                        && clause[0] != atom_of(&self.ctx.terms, clause[0]) => {}
                ProofStep::TheoryLemma { clause, kind, .. }
                    if !shape.trust_false
                        && kind.is_trust()
                        && clause.len() == 1
                        && matches!(
                            self.ctx.terms.get(clause[0]),
                            TermData::Const(ay_core::term::Constant::Bool(false))
                        ) =>
                {
                    shape.trust_false = true
                }
                ProofStep::Resolution { clause, .. }
                | ProofStep::Step {
                    rule: AletheRule::Resolution | AletheRule::ThResolution,
                    clause,
                    ..
                } => {
                    if clause.is_empty() {
                        if closing {
                            return None;
                        }
                        closing = true;
                    }
                }
                _ => return None,
            }
        }
        closing.then_some(shape)
    }
}
