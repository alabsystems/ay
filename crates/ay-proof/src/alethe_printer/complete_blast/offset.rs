// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! An equality between two OFFSET words, bridged to its shared difference.
//!
//! The complete bit-blast's twin of `bv_packed/circuit/offset.rs`. Blasted
//! as authored, `(= (bvadd c1 x) (bvadd c2 y))` is two adders and a
//! comparator per atom, and the transported refutation needs the solver's
//! raw-form conflict count: on external-codegen's coroutine-slot row the lane ran out
//! its counted work envelope (`134226710 proof-body bytes exceed 134217728`)
//! twice per lemma, whenever the circuit lane declined first. Here the atom
//! becomes its own theory gate `(= lhs rhs)`, tied by the bridge
//! (`offset_bridge.rs`: `poly_simp`, `poly_simp_rel`, then `equiv1`/`equiv2`
//! as two planned clauses) to the gate `(= d k)` that `theory_atom` blasts,
//! with `d` one `(bvsub x y)` word per pair of words; at `k = 0` the bridge
//! targets `(= x y)`. The authored operands are never built: the traversal
//! asks [`Blaster::offset_bridge`] for the equality's children, and
//! `build_bool` asks it again, so the two agree. Only a reading that pays is
//! bridged: one that cancels, or whose pair two of the roots' equalities read
//! (`ay_core::BvOffsetShares`, DR-33); `prepare_more` counts a root's
//! equalities before it builds any.

use super::*;
use crate::alethe_printer::offset_bridge::printed_factor;
use ay_core::BvOffsetEquality;

/// An offset equality this lane bridges, with the printed text it bridges.
pub(super) struct OffsetBridge {
    reading: BvOffsetEquality,
    factor: String,
    lhs: String,
    rhs: String,
}

impl OffsetBridge {
    /// The two words the bridged equality is built from.
    pub(super) fn words(&self) -> Vec<TermId> {
        vec![self.reading.minuend, self.reading.subtrahend]
    }
}

impl Blaster<'_, '_> {
    /// The bridge for `term` when it is a bit-vector `(= a b)` between two
    /// offset words whose printed sides read as one linear form.
    pub(super) fn offset_bridge(&self, term: TermId) -> Option<OffsetBridge> {
        let terms = self.printer.terms;
        let TermData::App(Symbol::Named(name), args) = terms.get(term) else {
            return None;
        };
        let [a, b] = args.as_slice() else {
            return None;
        };
        if name != "=" {
            return None;
        }
        let reading = terms.bv_offset_equality(*a, *b)?;
        if reading.width == 0 || reading.width > MAX_WIDTH || !self.offset_shares.uses(&reading) {
            return None;
        }
        if reading.minuend == reading.subtrahend {
            self.printer
                .full_offset_source_surfaces_agree(*a, *b, reading.width)?;
        }
        let lhs = self.printer.format_term(*a);
        let rhs = self.printer.format_term(*b);
        let minuend = self.printer.format_term(reading.minuend);
        let subtrahend = self.printer.format_term(reading.subtrahend);
        let (left, right) = if reading.constant.sign() == num_bigint::Sign::NoSign {
            (minuend, subtrahend)
        } else {
            (
                format!("(bvsub {minuend} {subtrahend})"),
                format!("(_ bv{} {})", reading.constant, reading.width),
            )
        };
        let factor = printed_factor(&lhs, &rhs, &left, &right, reading.width)?;
        Some(OffsetBridge {
            reading,
            factor,
            lhs,
            rhs,
        })
    }

    /// The Boolean gate of the bridged equality `(= lhs rhs)`.
    pub(super) fn offset_atom(&mut self, bridge: OffsetBridge) -> Option<SRef> {
        let OffsetBridge {
            reading,
            factor,
            lhs,
            rhs,
        } = bridge;
        let width = reading.width;
        // Atoms with one reading share one blasted `(= d k)` gate.
        let key = (
            reading.minuend,
            reading.subtrahend,
            reading.constant.to_string(),
        );
        let (target, left, right) = match self.offset_targets.get(&key) {
            Some(known) => known.clone(),
            None => {
                let (left, right) = self.offset_words(&reading)?;
                let target = self.theory_atom(left, right, AtomKind::Equality)?;
                let known = (target, self.word_ref(left), self.word_ref(right));
                self.offset_targets.insert(key, known.clone());
                known
            }
        };
        let source = self.circuit.theory(format!("(= {lhs} {rhs})"));
        let source_text = self.circuit.text(source);
        let target_text = self.circuit.text(target);
        let polynomial = self.step_name(".op");
        let relation = self.step_name(".or");
        let forward = self.step_name(".of");
        let backward = self.step_name(".ob");
        self.push_step(&format!(
            "(step {polynomial} (cl (= (bvmul (_ bv1 {width}) (bvsub {lhs} {rhs})) (bvmul {factor} (bvsub {left} {right})))) :rule poly_simp)"
        ))?;
        self.push_step(&format!(
            "(step {relation} (cl (= {source_text} {target_text})) :rule poly_simp_rel :premises ({polynomial}))"
        ))?;
        self.push_step(&format!(
            "(step {forward} (cl (not {source_text}) {target_text}) :rule equiv1 :premises ({relation}))"
        ))?;
        self.push_step(&format!(
            "(step {backward} (cl {source_text} (not {target_text})) :rule equiv2 :premises ({relation}))"
        ))?;
        self.plan(vec![source.not()?, target], ClauseEmit::Existing(forward))?;
        self.plan(vec![source, target.not()?], ClauseEmit::Existing(backward))?;
        Some(source)
    }

    /// The two words `(= d k)` compares: the words themselves at `k = 0`,
    /// else their difference (one per pair of words) and the literal `k`.
    fn offset_words(&mut self, reading: &BvOffsetEquality) -> Option<(usize, usize)> {
        let width = reading.width;
        let minuend = self.word_of_term(reading.minuend)?;
        let subtrahend = self.word_of_term(reading.subtrahend)?;
        if reading.constant.sign() == num_bigint::Sign::NoSign {
            return Some((minuend, subtrahend));
        }
        let pair = (reading.minuend, reading.subtrahend);
        let difference = match self.differences.get(&pair) {
            Some(&word) => word,
            None => {
                let word = self.build_subtraction(&[minuend, subtrahend], width)?;
                self.differences.insert(pair, word);
                word
            }
        };
        let bits = (0..u64::from(width))
            .map(|bit| reading.constant.bit(bit))
            .collect();
        let literal = format!("(_ bv{} {width})", reading.constant);
        let literal = self.new_word(literal, width, WordOp::Const(bits))?;
        Some((difference, literal))
    }
}
