// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Proposal-only use of the separately checked bounded BV intrinsics.
//! Full candidate replay retains its one aggregate checker envelope.

use super::emit::ClosureEmitter;
use super::*;

#[derive(Clone, Copy)]
enum FrameOp {
    AddRight,
    AddLeft,
    SubRight,
}

#[derive(Clone, Copy)]
struct Frame {
    source: TermId,
    constant: TermId,
    op: FrameOp,
}

struct Spine {
    frames: [Frame; 16],
    length: usize,
    width: u32,
}

// Structural substitution only: an actual earlier equality supplies the
// changed base. No offset is calculated or inferred by this context builder.
fn spine(terms: &TermStore, mut term: TermId, base: TermId) -> Option<Spine> {
    terms.entry_stamp(base)?;
    terms.entry_stamp(term)?;
    let width = terms.sort(base).bitvec_width()?;
    if !(1..=128).contains(&width) || !matches!(terms.get(base), TermData::Var(..)) {
        return None;
    }
    let mut result = Spine {
        frames: [Frame {
            source: base,
            constant: base,
            op: FrameOp::AddRight,
        }; 16],
        length: 0,
        width,
    };
    while term != base {
        if result.length == 16 {
            return None;
        }
        terms.entry_stamp(term)?;
        if terms.sort(term).bitvec_width() != Some(width) {
            return None;
        }
        let TermData::App(Symbol::Named(name), args) = terms.get(term) else {
            return None;
        };
        let &[left, right] = args.as_slice() else {
            return None;
        };
        if name != "bvadd" && name != "bvsub" {
            return None;
        }
        let literal = |child| {
            terms.entry_stamp(child)?;
            if terms.sort(child).bitvec_width() != Some(width) {
                return None;
            }
            Some(match terms.get(child) {
                TermData::Const(Constant::BitVec {
                    value,
                    width: actual,
                }) if *actual == width
                    && value.sign() != num_bigint::Sign::Minus
                    && value.bits() <= u64::from(width) =>
                {
                    true
                }
                TermData::Const(_) => return None,
                _ => false,
            })
        };
        let (child, constant, op) = match (literal(left)?, literal(right)?, name.as_str()) {
            (false, true, "bvadd") => (left, right, FrameOp::AddRight),
            (true, false, "bvadd") => (right, left, FrameOp::AddLeft),
            (false, true, "bvsub") => (left, right, FrameOp::SubRight),
            _ => return None,
        };
        result.frames[result.length] = Frame {
            source: term,
            constant,
            op,
        };
        result.length += 1;
        term = child;
    }
    Some(result)
}

impl Executor {
    /// None is cancellation/assembly exhaustion; Some(None) retains the old
    /// fallback. A successful proposal is independently checked in the whole
    /// source-scoped candidate, never in a new per-step strict-check budget.
    pub(super) fn emit_ground_offset_intrinsic(
        &mut self,
        emitter: &mut ClosureEmitter<'_>,
        equality: TermId,
        truth: bool,
    ) -> Option<Option<DerivedUnit>> {
        if self.alethe_dialect() != ay_proof::AletheDialect::Clean {
            return Some(None);
        }
        let stop = self.make_proof_assembly_should_stop();
        if stop() {
            return None;
        }
        emitter.admit_steps(1)?;
        let value = if truth {
            self.ctx.terms.true_term()
        } else {
            self.ctx.terms.false_term()
        };
        let claim = self
            .ctx
            .terms
            .mk_app(Symbol::named("="), [equality, value], Sort::Bool);
        if !ay_proof::recognize_bv_offset_spines_with_progress(
            &self.ctx.terms,
            &[claim],
            &mut |_, _| !stop(),
        ) {
            return (!stop()).then_some(None);
        }
        let slot = usize::from(truth);
        emitter.admit_steps(3 + usize::from(emitter.offset_constants[slot].is_none()))?;
        let result = if truth {
            equality
        } else {
            self.ctx.terms.mk_not_raw(equality)
        };
        let negative_claim = self.ctx.terms.mk_not_raw(claim);
        let complement = self.ctx.terms.mk_not_raw(value);
        let primitive =
            emitter
                .proof
                .add_rule_step(AletheRule::BvOffsetSpinesV1, vec![claim], vec![], vec![]);
        let tail = if truth { complement } else { value };
        let rule = if truth {
            AletheRule::EquivPos1
        } else {
            AletheRule::EquivPos2
        };
        let logical =
            emitter
                .proof
                .add_rule_step(rule, vec![negative_claim, result, tail], vec![], vec![]);
        let constant = if let Some(step) = emitter.offset_constants[slot] {
            step
        } else {
            let step = emitter.proof.add_rule_step(
                if truth {
                    AletheRule::True
                } else {
                    AletheRule::False
                },
                vec![if truth { value } else { complement }],
                vec![],
                vec![],
            );
            emitter.offset_constants[slot] = Some(step);
            step
        };
        // One ordinary n-ary resolution removes both tails. Share only the
        // unconditional Boolean constant, never an authored source premise.
        let step = emitter.proof.add_rule_step(
            AletheRule::Resolution,
            vec![result],
            vec![logical, primitive, constant],
            vec![],
        );
        (!stop()).then_some(Some(DerivedUnit {
            literal: result,
            step,
        }))
    }

    pub(super) fn emit_ground_offset_alias_skip(
        &mut self,
        emitter: &mut ClosureEmitter<'_>,
        pair: (TermId, TermId),
        skipped: TermId,
        point: TermId,
        bases: (TermId, TermId),
        limit: usize,
    ) -> Option<Option<ProofId>> {
        let stop = self.make_proof_assembly_should_stop();
        if stop() {
            return None;
        }
        let Some(context) = spine(&self.ctx.terms, skipped, bases.0) else {
            return Some(None);
        };
        self.ctx.terms.entry_stamp(bases.1)?;
        if self.ctx.terms.sort(bases.1).bitvec_width() != Some(context.width)
            || !matches!(self.ctx.terms.get(bases.1), TermData::Var(..))
        {
            return Some(None);
        }
        let local_steps = context
            .length
            .checked_add(7 + usize::from(emitter.offset_constants[0].is_none()))?;
        emitter.admit_steps(local_steps)?;
        // Establish custody before constructing any pure proof context.
        let alias = self.emit_closure_path_unit(emitter, bases.0, bases.1, limit)?;
        emitter.admit_steps(local_steps)?;
        let mut targets = [bases.1; 16];
        let mut target = bases.1;
        for index in (0..context.length).rev() {
            if stop() {
                return None;
            }
            let frame = context.frames[index];
            let (name, args) = match frame.op {
                FrameOp::AddRight => ("bvadd", [target, frame.constant]),
                FrameOp::AddLeft => ("bvadd", [frame.constant, target]),
                FrameOp::SubRight => ("bvsub", [target, frame.constant]),
            };
            target = self
                .ctx
                .terms
                .mk_app(Symbol::named(name), args, Sort::bitvec(context.width));
            targets[index] = target;
        }
        let transported_pair = if pair.0 == skipped {
            (target, point)
        } else {
            (point, target)
        };
        let pure_equality = self.ctx.terms.mk_app(
            Symbol::named("="),
            [transported_pair.0, transported_pair.1],
            Sort::Bool,
        );
        let Some(denied) = self.emit_ground_offset_intrinsic(emitter, pure_equality, false)? else {
            return Some(None);
        };
        let mut transport = alias;
        for index in (0..context.length).rev() {
            if stop() {
                return None;
            }
            emitter.admit_steps(1)?;
            let literal = self.ctx.terms.mk_app(
                Symbol::named("="),
                [context.frames[index].source, targets[index]],
                Sort::Bool,
            );
            let step = emitter.proof.add_rule_step(
                AletheRule::Cong,
                vec![literal],
                vec![transport.step],
                vec![],
            );
            transport = DerivedUnit { step, literal };
        }
        emitter.admit_steps(4)?;
        let equality = self
            .ctx
            .terms
            .mk_app(Symbol::named("="), [pair.0, pair.1], Sort::Bool);
        let congruence =
            self.ctx
                .terms
                .mk_app(Symbol::named("="), [equality, pure_equality], Sort::Bool);
        let congruence_step = emitter.proof.add_rule_step(
            AletheRule::Cong,
            vec![congruence],
            vec![transport.step],
            vec![],
        );
        let not_congruence = self.ctx.terms.mk_not_raw(congruence);
        let result = self.ctx.terms.mk_not_raw(equality);
        let bridge = emitter.proof.add_rule_step(
            AletheRule::EquivPos2,
            vec![not_congruence, result, pure_equality],
            vec![],
            vec![],
        );
        let bridge = emitter.proof.add_resolution(
            vec![result, pure_equality],
            congruence,
            congruence_step,
            bridge,
        );
        let step = emitter
            .proof
            .add_resolution(vec![result], pure_equality, bridge, denied.step);
        (!stop()).then_some(Some(step))
    }
}
