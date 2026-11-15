// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The consumer's `bitblast_udiv` and `bitblast_urem`: Clean's fixed long
//! division (`bitblast_udiv_urem_rec`: the adder returns the carry OUT of the
//! top bit, and a remainder at least the divisor becomes the difference, not
//! all ones), then the SMT-LIB division by zero (`bvudiv x 0` is all ones,
//! `bvurem x 0` is `x`). Transcribed from Clean 7330fa6c's
//! `carcara/src/checker/rules/bitvectors.rs`, operand for operand.

use super::bitblast::{bits, ripple_carry_adder};
use super::document::Document;
use super::{nary, refuse, same, shape, Checked, StepInput, Verdict};

/// `bitblast_udiv_urem_rec`: the quotient and remainder bits.
fn long_division(
    document: &mut Document,
    x: &[u32],
    y: &[u32],
    n: usize,
) -> Result<(Vec<u32>, Vec<u32>), Verdict> {
    let f = document.atom("false");
    let t = document.atom("true");
    if n == 0 || x.iter().all(|&bit| bit == f) {
        return Ok((vec![f; x.len()], vec![f; x.len()]));
    }
    // `shift_right`: rotate toward bit 0 and clear the top bit.
    let mut x1 = x.to_vec();
    x1.rotate_left(1);
    *x1.last_mut().expect("a nonempty word") = f;
    let (mut q1, mut r1) = long_division(document, &x1, y, n - 1)?;
    // `shift_left`: rotate away from bit 0 and clear bit 0.
    for word in [&mut q1, &mut r1] {
        word.rotate_right(1);
        word[0] = f;
    }
    let x0_true = document.app("=", &[x[0], t]);
    let one_if_odd = document.app("ite", &[x0_true, t, f]);
    let zeros = vec![f; x.len()];
    let (mut r1_shift_add, _) = ripple_carry_adder(document, &r1, &zeros, Some(one_if_odd))?;
    let not_y: Vec<u32> = y.iter().map(|&bit| document.app("not", &[bit])).collect();
    let (r_minus_y, co1) = ripple_carry_adder(document, &r1_shift_add, &not_y, Some(t))?;
    let sign = document.app("not", &[co1]);
    q1[0] = document.app("ite", &[sign, q1[0], t]);
    for (bit, difference) in r1_shift_add.iter_mut().zip(r_minus_y) {
        *bit = document.app("ite", &[sign, *bit, difference]);
    }
    let (_, co2) = ripple_carry_adder(document, x, &not_y, Some(t))?;
    let x_lt_y = document.app("not", &[co2]);
    let mut quotient = Vec::with_capacity(x.len());
    let mut remainder = Vec::with_capacity(x.len());
    for i in 0..x.len() {
        quotient.push(document.app("ite", &[x_lt_y, f, q1[i]]));
        remainder.push(document.app("ite", &[x_lt_y, x[i], r1_shift_add[i]]));
    }
    Ok((quotient, remainder))
}

/// `bitblast_udiv_urem`: the long division, then the zero divisor.
fn divide(document: &mut Document, x: u32, y: u32) -> Result<(Vec<u32>, Vec<u32>), Verdict> {
    let x = bits(document, x)?;
    let y = bits(document, y)?;
    if x.is_empty() {
        return refuse("a zero-width word: the consumer's checker panics");
    }
    let (quotient, remainder) = long_division(document, &x, &y, x.len())?;
    let f = document.atom("false");
    let t = document.atom("true");
    let zero_bits: Vec<u32> = y.iter().map(|&bit| document.app("=", &[bit, f])).collect();
    let y_is_zero = document.app("and", &zero_bits);
    let quotient = quotient
        .into_iter()
        .map(|bit| document.app("ite", &[y_is_zero, t, bit]))
        .collect();
    let remainder = remainder
        .into_iter()
        .zip(x)
        .map(|(bit, x)| document.app("ite", &[y_is_zero, x, bit]))
        .collect();
    Ok((quotient, remainder))
}

fn divider(document: &mut Document, input: &StepInput, head: &str) -> Checked {
    let sides = shape(document, input.unit()?, "=", 2)?;
    let [x, y] = <[u32; 2]>::try_from(nary(document, sides[0], head)?).map_or_else(
        |_| refuse(format!("({head} …) does not have 2 operands")),
        Ok,
    )?;
    let (quotient, remainder) = divide(document, x, y)?;
    let word = if head == "bvudiv" {
        quotient
    } else {
        remainder
    };
    let expected = document.app("@bbterm", &word);
    same(document, expected, sides[1])
}

pub(super) fn udiv(document: &mut Document, input: &StepInput) -> Checked {
    divider(document, input, "bvudiv")
}

pub(super) fn urem(document: &mut Document, input: &StepInput) -> Checked {
    divider(document, input, "bvurem")
}
