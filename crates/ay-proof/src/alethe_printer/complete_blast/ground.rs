// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! A GROUND shift amount re-spelled as its literal value, discharged by the
//! checker's own `evaluate`.
//!
//! ## Why this exists
//!
//! AY prints `bitblast_ashr` only when the operand is provably non-negative
//! or every bit of the amount that could make it reach the width is LITERALLY
//! `false` (`arithmetic_shift_is_admissible`; the pinned zero fill is false
//! anywhere else). A wasm or AArch64 lowering masks its shift
//! amount — `(bvashr x (bvand (_ bv24 32) (_ bv31 32)))` — so the amount is a
//! constant, but its blasted bits are `(and false true)` gates, never the
//! literal `false`. The shift then fell back to an opaque word, the lemma it
//! belonged to became satisfiable, and external-codegen's narrow i8/i16
//! renormalizations, `shr_s_i32`/`shr_s_i64` and their kin were printed as a
//! hole (measured 2026-09-28 on build 11431: 18 strict-gate obligations).
//!
//! ## What is printed
//!
//! ```text
//! (step e (cl (= (bvand (_ bv24 32) (_ bv31 32)) #b…11000)) :rule evaluate)
//! (step k (cl (= #b…11000 (@bbterm false false false true true false …))) :rule bitblast_const)
//! (step w (cl (= (bvand (_ bv24 32) (_ bv31 32)) (@bbterm false …))) :rule trans :premises (e k))
//! ```
//!
//! `evaluate` is re-derived by the consumer from the term alone, so nothing
//! here is assumed. The value printed is the one the already-blasted circuit
//! computes; a disagreement between the two would fail the `evaluate` step, so
//! the operator set is restricted to the ones whose circuits ARE the checker's
//! `bitblast_*` rules and whose evaluation the checker implements (Clean
//! `5390f432b8`, `third-party/carcara/carcara/src/ast/evaluate.rs`).

use super::circuit::GateKind;
use super::*;

/// Bound on the ground term walked before it is re-spelled: an amount is a
/// handful of nodes, and anything larger is left to the ordinary lowering.
const MAX_GROUND_NODES: usize = 256;

impl Blaster<'_, '_> {
    /// The operands of a shift, with an inadmissible `bvashr` amount replaced
    /// by its evaluated literal when it is ground. Every other shift, and every
    /// amount that is not ground, is returned unchanged.
    pub(super) fn with_ground_shift_amount(
        &mut self,
        op: ShiftOp,
        operands: Vec<usize>,
        args: &[TermId],
        width: u32,
    ) -> Vec<usize> {
        let (&[x, amount], &[_, amount_term]) = (operands.as_slice(), args) else {
            return operands;
        };
        if op != ShiftOp::AShr
            || self.arithmetic_shift_is_admissible(&self.words[x].bits, &self.words[amount].bits)
        {
            return operands;
        }
        match self.evaluated_word(amount_term, amount, width) {
            Some(literal) => vec![x, literal],
            None => operands,
        }
    }

    /// Bind `term` (already blasted as word `source`) to its literal value,
    /// or `None` when it is not a ground term over the evaluated operators.
    fn evaluated_word(&mut self, term: TermId, source: usize, width: u32) -> Option<usize> {
        if !self.is_evaluable_ground(term) {
            return None;
        }
        let values = constant_values(&self.circuit, &self.words[source].bits)?;
        if values.len() != width as usize {
            return None;
        }
        let literal: String = std::iter::once("#b".to_string())
            .chain(
                values
                    .iter()
                    .rev()
                    .map(|bit| if *bit { "1" } else { "0" }.to_string()),
            )
            .collect();
        let constant = self.new_word(literal.clone(), width, WordOp::Const(values))?;
        let body = self.printer.format_term(term);
        let reference = self.bind_word_reference(body, width)?;
        let evaluation = self.step_name(".ev");
        let step = self.step_name("");
        let constant_step = self.words[constant].step.clone();
        let bits = self.words[constant].bits.clone();
        let bbterm = self.bbterm(&bits);
        self.push_step(&format!(
            "(step {evaluation} (cl (= {reference} {literal})) :rule evaluate)"
        ))?;
        self.push_step(&format!(
            "(step {step} (cl (= {reference} {bbterm})) :rule trans :premises ({evaluation} {constant_step}))"
        ))?;
        self.words.push(Word {
            reference,
            width,
            bits,
            step,
        });
        Some(self.words.len() - 1)
    }

    /// Whether `term` is built from bit-vector literals by operators the
    /// checker's `evaluate` computes exactly as `bitblast_*` spells them.
    fn is_evaluable_ground(&self, term: TermId) -> bool {
        let mut stack = vec![term];
        let mut visited = 0_usize;
        while let Some(current) = stack.pop() {
            visited += 1;
            if visited > MAX_GROUND_NODES {
                return false;
            }
            match self.printer.terms.get(current) {
                TermData::Const(Constant::BitVec { .. }) => {}
                TermData::App(Symbol::Named(name), args)
                    if matches!(
                        name.as_ref(),
                        "bvand"
                            | "bvor"
                            | "bvxor"
                            | "bvnot"
                            | "bvadd"
                            | "bvsub"
                            | "bvneg"
                            | "bvmul"
                            | "concat"
                    ) =>
                {
                    stack.extend(args.iter().copied());
                }
                TermData::App(Symbol::Indexed(name, _), args)
                    if matches!(name.as_ref(), "extract" | "zero_extend" | "sign_extend") =>
                {
                    stack.extend(args.iter().copied());
                }
                _ => return false,
            }
        }
        true
    }
}

/// The value of every bit in `bits` when each is a function of constants
/// alone, or `None` when any depends on an atom. Gates are interned after
/// their operands, so one ascending pass over the reachable gates suffices.
pub(super) fn constant_values(circuit: &Circuit, bits: &[SRef]) -> Option<Vec<bool>> {
    let mut reachable: DetHashSet<u32> = DetHashSet::default();
    let mut stack: Vec<u32> = bits.iter().map(|bit| bit.gate).collect();
    while let Some(gate) = stack.pop() {
        if !reachable.insert(gate) {
            continue;
        }
        match circuit.kind(gate) {
            GateKind::Const(_) => {}
            GateKind::Atom(_) | GateKind::Theory(_) => return None,
            GateKind::And(args) | GateKind::Or(args) => {
                stack.extend(args.iter().map(|arg| arg.gate));
            }
            GateKind::Xor(a, b) | GateKind::Implies(a, b) | GateKind::Iff(a, b) => {
                stack.extend([a.gate, b.gate]);
            }
            GateKind::Ite(c, a, b) => stack.extend([c.gate, a.gate, b.gate]),
        }
    }
    let mut order: Vec<u32> = reachable.into_iter().collect();
    order.sort_unstable();
    let mut values: DetHashMap<u32, bool> = DetHashMap::default();
    for gate in order {
        let read = |r: &SRef| values.get(&r.gate).map(|value| *value != r.negative());
        let value = match circuit.kind(gate) {
            GateKind::Const(value) => *value,
            GateKind::And(args) => args
                .iter()
                .map(read)
                .collect::<Option<Vec<_>>>()?
                .iter()
                .all(|v| *v),
            GateKind::Or(args) => args
                .iter()
                .map(read)
                .collect::<Option<Vec<_>>>()?
                .iter()
                .any(|v| *v),
            GateKind::Xor(a, b) => read(a)? != read(b)?,
            GateKind::Implies(a, b) => !read(a)? || read(b)?,
            GateKind::Iff(a, b) => read(a)? == read(b)?,
            GateKind::Ite(c, a, b) => {
                if read(c)? {
                    read(a)?
                } else {
                    read(b)?
                }
            }
            GateKind::Atom(_) | GateKind::Theory(_) => return None,
        };
        values.insert(gate, value);
    }
    bits.iter()
        .map(|bit| values.get(&bit.gate).map(|value| *value != bit.negative()))
        .collect()
}
