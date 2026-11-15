// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! `bvudiv` / `bvurem` through a checker's long-division circuit, and which
//! checker's circuit a step may be spelled with.
//!
//! Clean's fixed divider (the default, e9b297e37) is SMT-LIB's quotient and
//! remainder for every operand pair. Pinned Carcara 9a352ee builds another
//! circuit for the same rules (`circuit::divide`) and refuses Clean's, so a
//! Clean-divider step is reported Clean-only
//! ([`CleanOnlySpelling::FixedDivider`]) unless the dividend is literally zero,
//! where both recursions stop at once and build the same terms.
//!
//! Pinned Carcara's divider is FALSE for most operand pairs, and pinned
//! Carcara accepts it all the same (it compares terms, not meanings). So
//! [`AletheDialect::PinnedCarcara`] prints it only where
//! [`pinned_divider_is_true`] shows that the printed bits ARE SMT-LIB's;
//! everywhere else it keeps Clean's divider and reports it, as it does for
//! `zero_extend`. That guard is the soundness precondition of the pinned
//! spelling, exactly as `arithmetic_shift_is_admissible` is for
//! `bitblast_ashr`: outside it a pinned-valid certificate would carry a false
//! step. Never relax it.

use super::super::dialect::{self, AletheDialect, CleanOnlySpelling};
use super::circuit::{Circuit, Divider, GateKind, SRef};
use super::ground::constant_values;
use super::{Blasted, Blaster};
use num_bigint::BigUint;
use num_traits::Zero;

impl Blaster<'_, '_> {
    /// `bvudiv` / `bvurem` through a checker's long-division circuit: the
    /// pinned one where [`pinned_divider_is_true`] admits it in the pinned
    /// dialect, Clean's everywhere else.
    pub(super) fn blast_division(
        &mut self,
        x: usize,
        y: usize,
        remainder: bool,
    ) -> Option<(Vec<SRef>, Blasted)> {
        let xs = self.words[x].bits.clone();
        let ys = self.words[y].bits.clone();
        let divider = if dialect::current() == AletheDialect::PinnedCarcara
            && pinned_divider_is_true(&self.circuit, &xs, &ys, remainder)
        {
            Divider::Pinned
        } else {
            Divider::Clean
        };
        let (quot, rem) = self.circuit.udiv_urem_spelled(&xs, &ys, divider)?;
        // Reported only once the circuit exists: a step that is not printed
        // spells nothing.
        if divider == Divider::Clean && !xs.iter().all(|bit| literally_false(&self.circuit, bit)) {
            dialect::note_clean_only(CleanOnlySpelling::FixedDivider);
        }
        let (bits, head, rule) = if remainder {
            (rem, "bvurem", "bitblast_urem")
        } else {
            (quot, "bvudiv", "bitblast_udiv")
        };
        Some((bits, self.blasted_application(head, &[x, y], rule)))
    }
}

/// Whether `bit` is spelled as the literal `false` (the checker's
/// `is_bool_false`).
fn literally_false(circuit: &Circuit, bit: &SRef) -> bool {
    bit.nots == 0 && matches!(circuit.kind(bit.gate), GateKind::Const(false))
}

/// Whether pinned Carcara's divider, spelled over `xs` / `ys`, concludes a
/// TRUE `bitblast_udiv` (`remainder == false`) or `bitblast_urem` step. It is
/// decided on the two domains where this can be shown, and refused elsewhere:
///
/// * every divisor bit is closed and `false`: both dividers' outer
///   `(ite (and (= y_i false) ..) ..)` then selects SMT-LIB's all-ones
///   quotient and the dividend as remainder, whatever the recursion below
///   computed;
/// * every operand bit is closed: the printed bits are then closed Boolean
///   terms, evaluated here and compared with SMT-LIB's quotient or remainder,
///   computed independently.
///
/// A symbolic operand with a non-zero divisor is refused: for every non-zero
/// divisor some dividend is divided wrongly.
pub(super) fn pinned_divider_is_true(
    circuit: &Circuit,
    xs: &[SRef],
    ys: &[SRef],
    remainder: bool,
) -> bool {
    let Some(divisor) = constant_values(circuit, ys) else {
        return false;
    };
    if divisor.iter().all(|bit| !bit) {
        return true;
    }
    let Some(dividend) = constant_values(circuit, xs) else {
        return false;
    };
    // The divider reads two things of an operand bit: its value, and whether
    // it is spelled as the literal `false` (the recursion's syntactic base
    // case). Stand-ins that keep both evaluate exactly like the printed
    // circuit, without growing the document's gate table.
    let mut scratch = Circuit::new(String::new());
    let stand_ins = |scratch: &mut Circuit, bits: &[SRef], values: &[bool]| {
        bits.iter()
            .zip(values)
            .map(
                |(bit, value)| match (literally_false(circuit, bit), value) {
                    (true, _) => Some(scratch.constant(false)),
                    (false, true) => Some(scratch.constant(true)),
                    (false, false) => scratch.constant(true).not(),
                },
            )
            .collect::<Option<Vec<_>>>()
    };
    let (Some(x), Some(y)) = (
        stand_ins(&mut scratch, xs, &dividend),
        stand_ins(&mut scratch, ys, &divisor),
    ) else {
        return false;
    };
    let Some((quot, rem)) = scratch.udiv_urem_spelled(&x, &y, Divider::Pinned) else {
        return false;
    };
    let printed = constant_values(&scratch, if remainder { &rem } else { &quot });
    let (want_quot, want_rem) = smt_lib_udiv_urem(&dividend, &divisor);
    printed == Some(if remainder { want_rem } else { want_quot })
}

/// SMT-LIB's `bvudiv` and `bvurem` over little-endian bits: an all-ones
/// quotient and the dividend as remainder for a zero divisor.
fn smt_lib_udiv_urem(dividend: &[bool], divisor: &[bool]) -> (Vec<bool>, Vec<bool>) {
    let value = |bits: &[bool]| {
        bits.iter()
            .rev()
            .fold(BigUint::zero(), |acc, bit| (acc << 1_u32) + u32::from(*bit))
    };
    let bits = |value: &BigUint| {
        (0..dividend.len() as u64)
            .map(|index| value.bit(index))
            .collect::<Vec<_>>()
    };
    let (x, y) = (value(dividend), value(divisor));
    if y.is_zero() {
        return (vec![true; dividend.len()], dividend.to_vec());
    }
    (bits(&(&x / &y)), bits(&(&x % &y)))
}

#[cfg(test)]
#[path = "division_tests.rs"]
mod tests;
