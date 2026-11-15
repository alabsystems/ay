// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The consumer's `bitblast_shl`, `bitblast_lshr` and `bitblast_ashr`
//! (`bitblast_shift_op`: a barrel shifter over the amount's low bits, every
//! bit then guarded by `(bvult amount width)`, an overshift filled with
//! `false`, or with the sign bit for `bvashr` as Clean fixed it), and the
//! `bitblast_ashr` domain guard Clean runs before any rule
//! (`carcara_verify/ashr.rs`, `safe_shift`).

use super::bitblast::{bits, take, unsigned_less, width};
use super::document::Document;
use super::{nary, refuse, same, shape, Checked, StepInput, Verdict};

/// `bitblast_shift_op`.
fn shifted(document: &mut Document, head: &str, x: u32, y: u32) -> Result<u32, Verdict> {
    let size = width(document, x)?;
    let size_term = document.constant(size, size);
    let y_ult_size = unsigned_less(document, y, size_term)?;
    let mut res = bits(document, x)?;
    let y = bits(document, y)?;
    let Some(&sign) = res.last() else {
        return refuse("a zero-width word: the consumer's checker panics");
    };
    take(&res, size)?;
    let f = document.atom("false");
    let k = size.ilog2() as usize + usize::from(!size.is_power_of_two());
    for (s, &ys) in y.iter().enumerate().take(k) {
        let previous = res.clone();
        let thresh = 1usize << s;
        for i in 0..size {
            res[i] = match head {
                "bvshl" if i < thresh => document.app("ite", &[ys, f, previous[i]]),
                "bvshl" => document.app("ite", &[ys, previous[i - thresh], previous[i]]),
                _ if i + thresh >= size => {
                    let fill = if head == "bvashr" { sign } else { f };
                    document.app("ite", &[ys, fill, previous[i]])
                }
                _ => {
                    let not_ys = document.app("not", &[ys]);
                    document.app("ite", &[not_ys, previous[i], previous[i + thresh]])
                }
            };
        }
    }
    let overshift_fill = if head == "bvashr" { sign } else { f };
    for bit in &mut res {
        *bit = document.app("ite", &[y_ult_size, *bit, overshift_fill]);
    }
    Ok(document.app("@bbterm", &res))
}

fn shift(document: &mut Document, input: &StepInput, head: &str) -> Checked {
    let sides = shape(document, input.unit()?, "=", 2)?;
    let [x, y] = <[u32; 2]>::try_from(nary(document, sides[0], head)?).map_or_else(
        |_| refuse(format!("({head} …) does not have 2 operands")),
        Ok,
    )?;
    let expected = shifted(document, head, x, y)?;
    same(document, expected, sides[1])
}

pub(super) fn shl(document: &mut Document, input: &StepInput) -> Checked {
    shift(document, input, "bvshl")
}

pub(super) fn lshr(document: &mut Document, input: &StepInput) -> Checked {
    shift(document, input, "bvlshr")
}

/// Clean refuses a `bitblast_ashr` step unless the shifted word is
/// non-negative or the amount provably below the width (`safe_shift`), then
/// checks it as the rule.
pub(super) fn ashr(document: &mut Document, input: &StepInput) -> Checked {
    safe_shift(document, input)?;
    shift(document, input, "bvashr")
}

fn safe_shift(document: &Document, input: &StepInput) -> Checked {
    let unsafe_shift = || refuse("arithmetic shift may overshift a negative operand (safe_shift)");
    let [literal] = input.conclusion[..] else {
        return unsafe_shift();
    };
    let Ok(sides) = shape(document, literal, "=", 2) else {
        return unsafe_shift();
    };
    let Ok(operands) = shape(document, sides[0], "bvashr", 2) else {
        return unsafe_shift();
    };
    let (word, amount) = (operands[0], operands[1]);
    let width = width(document, word)?;
    if width == 0 || super::bitblast::width(document, amount)? != width {
        return unsafe_shift();
    }
    if non_negative(document, word, width) || below_width(document, amount, width) {
        Ok(())
    } else {
        unsafe_shift()
    }
}

fn non_negative(document: &Document, word: u32, width: usize) -> bool {
    if let Some(bits) = document.constant_bits(word) {
        return bits.len() == width && bits.last() == Some(&false);
    }
    document.op(word, "@bbterm").is_some_and(|bits| {
        bits.len() == width
            && bits
                .last()
                .is_some_and(|&bit| document.is_atom(bit, "false"))
    })
}

fn below_width(document: &Document, amount: u32, width: usize) -> bool {
    if let Some(bits) = document.constant_bits(amount) {
        let value = bits
            .iter()
            .enumerate()
            .try_fold(0usize, |value, (i, &one)| match one {
                false => Some(value),
                true => u32::try_from(i)
                    .ok()
                    .and_then(|i| 1usize.checked_shl(i))
                    .map(|w| value | w),
            });
        return bits.len() == width && value.is_some_and(|value| value < width);
    }
    let Some(bits) = document.op(amount, "@bbterm") else {
        return false;
    };
    if bits.len() != width {
        return false;
    }
    let mut largest = 0usize;
    for (i, &bit) in bits.iter().enumerate() {
        if document.is_atom(bit, "false") {
            continue;
        }
        let Some(weight) = u32::try_from(i).ok().and_then(|i| 1usize.checked_shl(i)) else {
            return false;
        };
        largest |= weight;
        if largest >= width {
            return false;
        }
    }
    true
}
