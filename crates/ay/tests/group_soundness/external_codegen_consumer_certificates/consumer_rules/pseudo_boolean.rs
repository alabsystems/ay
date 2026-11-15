// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The consumer's pseudo-Boolean comparison rules (Clean's Carcara
//! `pb_blasting.rs`, `pbblast_bv{eq,ult,ugt,uge,ule,slt,sgt,sge,sle}`) and
//! the `pb_widths` guard Clean runs before them: each side's sum has one
//! summand per bit, `2^i * ((_ @int_of i) x)` (the coefficient may be
//! omitted on bit 0), or the bits of an `@pbbterm` directly; a signed
//! relation sums all but the sign bit and adds `2^(n-1)` times it apart; and
//! both words have one width.

use num_bigint::BigInt;
use num_traits::One;

use super::document::Document;
use super::{refuse, require, same, shape, undecided, Checked, StepInput, Verdict};

/// A numeric constant pattern: the integer or decimal constant `k`.
fn bound_is(document: &Document, id: u32, k: &str) -> bool {
    let Some(text) = document.atom_text(id) else {
        return false;
    };
    let (whole, fraction) = text.split_once('.').unwrap_or((text, ""));
    whole == k && fraction.bytes().all(|b| b == b'0') && !whole.is_empty()
}

/// `split_summation`.
fn summands(document: &Document, sum: u32) -> Vec<u32> {
    document.op(sum, "+").unwrap_or_else(|| vec![sum])
}

/// `as_integer_err`: an integer constant.
fn integer(document: &Document, id: u32) -> Result<BigInt, Verdict> {
    document
        .atom_text(id)
        .filter(|text| text.bytes().all(|b| b.is_ascii_digit()))
        .and_then(|text| text.parse().ok())
        .map_or_else(
            || refuse(format!("{} is not an integer constant", document.show(id))),
            Ok,
        )
}

/// `((_ @int_of idx) bv)`: `(idx, bv)`.
fn int_of(document: &Document, id: u32) -> Option<(u32, u32)> {
    let children = match document.node(id) {
        super::document::Node::List(children) if children.len() == 2 => children.clone(),
        _ => return None,
    };
    let (name, indices) = document.indexed_name(children[0])?;
    match (name.as_str(), &indices[..]) {
        ("@int_of", [index]) => Some((*index, children[1])),
        _ => None,
    }
}

fn width(document: &Document, word: u32) -> Result<usize, Verdict> {
    document.width(word).map_or_else(
        || {
            undecided(format!(
                "the width of {} is not inferred",
                document.show(word)
            ))
        },
        Ok,
    )
}

/// `check_pbblast_sum` and, for an `@pbbterm` word, `…_short_circuit`.
fn check_sum(document: &Document, word: u32, sum: &[u32], signed: bool) -> Checked {
    if let Some(bits) = document.op(word, "@pbbterm") {
        let count = bits.len().checked_sub(usize::from(signed));
        require(count == Some(sum.len()), || {
            "not one summand per bit".to_string()
        })?;
        for (i, &element) in sum.iter().enumerate() {
            let (c, bit) = match shape(document, element, "*", 2) {
                Ok(product) => (integer(document, product[0])?, product[1]),
                Err(_) if i == 0 => (BigInt::one(), element),
                Err(why) => return Err(why),
            };
            require(c == BigInt::one() << i, || {
                format!("coefficient {c} is not 2^{i}")
            })?;
            same(document, bit, bits[i])?;
        }
        return Ok(());
    }
    let count = width(document, word)?.checked_sub(usize::from(signed));
    require(count == Some(sum.len()), || {
        "not one summand per bit".to_string()
    })?;
    for (i, &element) in sum.iter().enumerate() {
        let product = shape(document, element, "*", 2)
            .ok()
            .and_then(|p| Some((p[0], int_of(document, p[1])?)));
        let (c, (index, bv)) = match product {
            Some((c, bit)) => (integer(document, c)?, bit),
            None if i == 0 => match int_of(document, element) {
                Some(bit) => (BigInt::one(), bit),
                None => return refuse("a summand matches neither pattern"),
            },
            None => return refuse("a summand without its coefficient"),
        };
        require(c == BigInt::one() << i, || {
            format!("coefficient {c} is not 2^{i}")
        })?;
        require(integer(document, index)? == BigInt::from(i), || {
            format!("index is not {i}")
        })?;
        same(document, bv, word)?;
    }
    Ok(())
}

/// `check_pbblast_constraint`.
fn check_constraint(
    document: &Document,
    left: (u32, u32),
    right: (u32, u32),
    signed: bool,
) -> Checked {
    let (left_word, left_sum) = (left.0, summands(document, left.1));
    let (right_word, right_sum) = (right.0, summands(document, right.1));
    if document.op(left_word, "@pbbterm").is_some() {
        require(document.op(right_word, "@pbbterm").is_some(), || {
            "one @pbbterm side".to_string()
        })?;
    }
    check_sum(document, left_word, &left_sum, signed)?;
    check_sum(document, right_word, &right_sum, signed)
}

/// `check_pbblast_signed_relation`.
fn check_sign(document: &Document, n: usize, sign: u32, word: u32) -> Checked {
    let product = shape(document, sign, "*", 2)?;
    let coefficient = integer(document, product[0])?;
    let expected = BigInt::one()
        << n.checked_sub(1)
            .map_or_else(|| refuse("a zero-width word"), Ok)?;
    require(coefficient == expected, || {
        format!("coefficient {coefficient} is not 2^(n-1)")
    })?;
    if let Some(bits) = document.op(word, "@pbbterm") {
        let Some(&last) = bits.last() else {
            return refuse("no sign bit");
        };
        return same(document, product[1], last);
    }
    let Some((index, bv)) = int_of(document, product[1]) else {
        return refuse("the sign term is not 2^(n-1) * ((_ @int_of n-1) x)");
    };
    require(integer(document, index)? == BigInt::from(n - 1), || {
        "the sign index is not n-1".to_string()
    })?;
    same(document, bv, word)
}

/// `(= (op x y) (rel body k))`: `x`, `y` and `body`, with `rel`/`k` checked.
fn relation(
    document: &Document,
    input: &StepInput,
    op: &str,
    rel: &str,
    k: &str,
) -> Result<(u32, u32, u32), Verdict> {
    let sides = shape(document, input.unit()?, "=", 2)?;
    let words = shape(document, sides[0], op, 2)?;
    let target = shape(document, sides[1], rel, 2)?;
    require(bound_is(document, target[1], k), || {
        format!("the bound is not {k}")
    })?;
    // `pb_widths`: both words have one positive width.
    let width = width(document, words[0])?;
    require(width > 0 && document.width(words[1]) == Some(width), || {
        "the words differ in width".to_string()
    })?;
    Ok((words[0], words[1], target[0]))
}

/// Which word each part of `(- a b)` is checked against, in the consumer's
/// order: `x a, y b`; `y a, x b` (`bvult`); `x b, y a` (`bvule`, which
/// matches `(- sum_y sum_x)` and passes `x, y, sum_x, sum_y`).
#[derive(Clone, Copy)]
enum Order {
    Straight,
    Swapped,
    Crossed,
}

fn unsigned(
    document: &mut Document,
    input: &StepInput,
    op: &str,
    rel: &str,
    k: &str,
    order: Order,
) -> Checked {
    let (x, y, difference) = relation(document, input, op, rel, k)?;
    let [a, b] = <[u32; 2]>::try_from(shape(document, difference, "-", 2)?).unwrap_or([0; 2]);
    let (left, right) = match order {
        Order::Straight => ((x, a), (y, b)),
        Order::Swapped => ((y, a), (x, b)),
        Order::Crossed => ((x, b), (y, a)),
    };
    check_constraint(document, left, right, false)
}

fn signed(document: &mut Document, input: &StepInput, op: &str, k: &str, y_first: bool) -> Checked {
    let (x, y, sum) = relation(document, input, op, ">=", k)?;
    let halves = shape(document, sum, "+", 2)?;
    let (lower, upper) = (
        shape(document, halves[0], "-", 2)?,
        shape(document, halves[1], "-", 2)?,
    );
    let n = width(document, x)?;
    let (first, second) = if y_first { (y, x) } else { (x, y) };
    check_sign(document, n, lower[1], first)?;
    check_sign(document, n, upper[0], second)?;
    check_constraint(document, (first, lower[0]), (second, upper[1]), true)
}

pub(super) fn bveq(document: &mut Document, input: &StepInput) -> Checked {
    unsigned(document, input, "=", "=", "0", Order::Straight)
}
pub(super) fn bvult(document: &mut Document, input: &StepInput) -> Checked {
    unsigned(document, input, "bvult", ">=", "1", Order::Swapped)
}
pub(super) fn bvugt(document: &mut Document, input: &StepInput) -> Checked {
    unsigned(document, input, "bvugt", ">=", "1", Order::Straight)
}
pub(super) fn bvuge(document: &mut Document, input: &StepInput) -> Checked {
    unsigned(document, input, "bvuge", ">=", "0", Order::Straight)
}
pub(super) fn bvule(document: &mut Document, input: &StepInput) -> Checked {
    unsigned(document, input, "bvule", ">=", "0", Order::Crossed)
}
pub(super) fn bvslt(document: &mut Document, input: &StepInput) -> Checked {
    signed(document, input, "bvslt", "1", true)
}
pub(super) fn bvsgt(document: &mut Document, input: &StepInput) -> Checked {
    signed(document, input, "bvsgt", "1", false)
}
pub(super) fn bvsge(document: &mut Document, input: &StepInput) -> Checked {
    signed(document, input, "bvsge", "0", false)
}
pub(super) fn bvsle(document: &mut Document, input: &StepInput) -> Checked {
    signed(document, input, "bvsle", "0", true)
}
