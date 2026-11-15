// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The consumer's `bitblast_*` rules (Clean's `carcara/src/checker/rules/
//! bitvectors.rs`): each builds the expected circuit from the source term and
//! compares it with the printed result, structurally. The circuits here are
//! transcribed from that file, operand for operand, and the `bitblast_ashr`
//! domain guard from `carcara_verify/ashr.rs`.

use super::document::Document;
use super::{nary, refuse, require, same, shape, undecided, Checked, StepInput, Verdict};

/// `get_term_bits`: the operands of an `@bbterm`, else `((_ @bit_of i) t)`.
pub(super) fn bits(document: &mut Document, term: u32) -> Result<Vec<u32>, Verdict> {
    if let Some(bits) = document.op(term, "@bbterm") {
        return Ok(bits);
    }
    let width = width(document, term)?;
    Ok((0..width).map(|i| document.bit_of(i, term)).collect())
}

/// `bitvector_size`, where the reader infers the sort.
pub(super) fn width(document: &Document, term: u32) -> Result<usize, Verdict> {
    document.width(term).map_or_else(
        || {
            undecided(format!(
                "the width of {} is not inferred",
                document.show(term)
            ))
        },
        Ok,
    )
}

/// The first `size` bits: the consumer indexes past a narrower word and panics.
pub(super) fn take(bits: &[u32], size: usize) -> Result<Vec<u32>, Verdict> {
    bits.get(..size).map_or_else(
        || refuse("a word is narrower than its sort: the consumer's checker panics"),
        |bits| Ok(bits.to_vec()),
    )
}

/// `(= (head operands…) result)`.
fn source(document: &Document, input: &StepInput, head: &str) -> Result<(Vec<u32>, u32), Verdict> {
    let sides = shape(document, input.unit()?, "=", 2)?;
    Ok((nary(document, sides[0], head)?, sides[1]))
}

fn operands<const N: usize>(
    document: &Document,
    input: &StepInput,
    head: &str,
) -> Result<([u32; N], u32), Verdict> {
    let (operands, result) = source(document, input, head)?;
    let operands: [u32; N] = operands.try_into().map_or_else(
        |_| refuse(format!("({head} …) does not have {N} operands")),
        Ok,
    )?;
    Ok((operands, result))
}

/// `ripple_carry_adder`: the sum and the carry OUT of the top bit (Clean's fix).
pub(super) fn ripple_carry_adder(
    document: &mut Document,
    x: &[u32],
    y: &[u32],
    carry: Option<u32>,
) -> Result<(Vec<u32>, u32), Verdict> {
    let size = x.len();
    let y = take(y, size)?;
    let mut carries = vec![carry.unwrap_or_else(|| document.atom("false"))];
    for i in 1..=size {
        let both = document.app("and", &[x[i - 1], y[i - 1]]);
        let differ = document.app("xor", &[x[i - 1], y[i - 1]]);
        let propagated = document.app("and", &[differ, carries[i - 1]]);
        carries.push(document.app("or", &[both, propagated]));
    }
    let sum = (0..size)
        .map(|i| {
            let differ = document.app("xor", &[x[i], y[i]]);
            document.app("xor", &[differ, carries[i]])
        })
        .collect();
    Ok((sum, carries[size]))
}

/// `bitblast_ult`.
pub(super) fn unsigned_less(document: &mut Document, x: u32, y: u32) -> Result<u32, Verdict> {
    let size = width(document, x)?;
    let x = take(&bits(document, x)?, size)?;
    let y = take(&bits(document, y)?, size)?;
    let (Some(&x0), Some(&y0)) = (x.first(), y.first()) else {
        return refuse("a zero-width word: the consumer's checker panics");
    };
    let not_x0 = document.app("not", &[x0]);
    let mut result = document.app("and", &[not_x0, y0]);
    for i in 1..size {
        let equal = document.app("=", &[x[i], y[i]]);
        let kept = document.app("and", &[equal, result]);
        let not_x = document.app("not", &[x[i]]);
        let less = document.app("and", &[not_x, y[i]]);
        result = document.app("or", &[kept, less]);
    }
    Ok(result)
}

pub(super) fn constant(document: &mut Document, input: &StepInput) -> Checked {
    let sides = shape(document, input.unit()?, "=", 2)?;
    let bits = nary(document, sides[1], "@bbterm")?;
    let Some(value) = document
        .constant_bits(sides[0])
        .filter(|v| v.len() == bits.len())
    else {
        return refuse("not a constant of the result's width being bit-blasted");
    };
    for (i, (&bit, &one)) in bits.iter().zip(&value).enumerate() {
        let (is_true, is_false) = (
            document.is_atom(bit, "true"),
            document.is_atom(bit, "false"),
        );
        require(is_true || is_false, || {
            format!("bit {i} is neither true nor false")
        })?;
        require(is_true == one, || format!("bit {i} is not the constant's"))?;
    }
    Ok(())
}

pub(super) fn variable(document: &mut Document, input: &StepInput) -> Checked {
    let sides = shape(document, input.unit()?, "=", 2)?;
    let word = bits(document, sides[0])?;
    let expected = document.app("@bbterm", &word);
    same(document, expected, sides[1])
}

/// `bitblast_and`/`_or`/`_xor`: folded left to right, `gate` bit by bit.
fn bitwise(document: &mut Document, input: &StepInput, head: &str, gate: &str) -> Checked {
    let (operands, result) = source(document, input, head)?;
    let Some((&first, rest)) = operands.split_first() else {
        return refuse(format!("({head}) has no operands"));
    };
    let size = width(document, first)?;
    let mut expected = first;
    for &next in rest {
        let x = take(&bits(document, expected)?, size)?;
        let y = take(&bits(document, next)?, size)?;
        let out: Vec<u32> = (0..size)
            .map(|i| document.app(gate, &[x[i], y[i]]))
            .collect();
        expected = document.app("@bbterm", &out);
    }
    same(document, expected, result)
}

pub(super) fn and(document: &mut Document, input: &StepInput) -> Checked {
    bitwise(document, input, "bvand", "and")
}

pub(super) fn or(document: &mut Document, input: &StepInput) -> Checked {
    bitwise(document, input, "bvor", "or")
}

pub(super) fn xor(document: &mut Document, input: &StepInput) -> Checked {
    bitwise(document, input, "bvxor", "xor")
}

/// A binary operator's operand bits, each cut to the first operand's width.
fn two_words(
    document: &mut Document,
    input: &StepInput,
    head: &str,
) -> Result<(Vec<u32>, Vec<u32>, u32), Verdict> {
    let ([x, y], result) = operands::<2>(document, input, head)?;
    let size = width(document, x)?;
    let x = take(&bits(document, x)?, size)?;
    let y = take(&bits(document, y)?, size)?;
    Ok((x, y, result))
}

pub(super) fn xnor(document: &mut Document, input: &StepInput) -> Checked {
    let (x, y, result) = two_words(document, input, "bvxnor")?;
    let out: Vec<u32> = x
        .iter()
        .zip(&y)
        .map(|(&a, &b)| document.app("=", &[a, b]))
        .collect();
    let expected = document.app("@bbterm", &out);
    same(document, expected, result)
}

pub(super) fn not(document: &mut Document, input: &StepInput) -> Checked {
    let ([x], result) = operands::<1>(document, input, "bvnot")?;
    let size = width(document, x)?;
    let x = take(&bits(document, x)?, size)?;
    let out: Vec<u32> = x.iter().map(|&bit| document.app("not", &[bit])).collect();
    let expected = document.app("@bbterm", &out);
    same(document, expected, result)
}

pub(super) fn neg(document: &mut Document, input: &StepInput) -> Checked {
    let ([x], result) = operands::<1>(document, input, "bvneg")?;
    let size = width(document, x)?;
    let x = take(&bits(document, x)?, size)?;
    let f = document.atom("false");
    let mut carries = vec![document.atom("true")];
    for i in 1..size {
        let not_x = document.app("not", &[x[i - 1]]);
        let both = document.app("and", &[not_x, f]);
        let differ = document.app("xor", &[not_x, f]);
        let propagated = document.app("and", &[differ, carries[i - 1]]);
        carries.push(document.app("or", &[both, propagated]));
    }
    let out: Vec<u32> = (0..size)
        .map(|i| {
            let not_x = document.app("not", &[x[i]]);
            let differ = document.app("xor", &[not_x, f]);
            document.app("xor", &[differ, carries[i]])
        })
        .collect();
    let expected = document.app("@bbterm", &out);
    same(document, expected, result)
}

/// `(and (= x0 y0) …)`, or the one equality of a one-bit word.
fn bitwise_equal(document: &mut Document, x: &[u32], y: &[u32]) -> Result<u32, Verdict> {
    let equalities: Vec<u32> = x
        .iter()
        .zip(y)
        .map(|(&a, &b)| document.app("=", &[a, b]))
        .collect();
    match equalities[..] {
        [] => refuse("a zero-width word: the consumer's checker panics"),
        [only] => Ok(only),
        _ => Ok(document.app("and", &equalities)),
    }
}

pub(super) fn equal(document: &mut Document, input: &StepInput) -> Checked {
    let sides = shape(document, input.unit()?, "=", 2)?;
    let words = shape(document, sides[0], "=", 2)?;
    let size = width(document, words[0])?;
    let x = take(&bits(document, words[0])?, size)?;
    let y = take(&bits(document, words[1])?, size)?;
    let expected = bitwise_equal(document, &x, &y)?;
    same(document, expected, sides[1])
}

pub(super) fn comp(document: &mut Document, input: &StepInput) -> Checked {
    let (x, y, result) = two_words(document, input, "bvcomp")?;
    let equal = bitwise_equal(document, &x, &y)?;
    let expected = document.app("@bbterm", &[equal]);
    same(document, expected, result)
}

pub(super) fn ult(document: &mut Document, input: &StepInput) -> Checked {
    let ([x, y], result) = operands::<2>(document, input, "bvult")?;
    let expected = unsigned_less(document, x, y)?;
    same(document, expected, result)
}

pub(super) fn slt(document: &mut Document, input: &StepInput) -> Checked {
    let (x, y, result) = two_words(document, input, "bvslt")?;
    let size = x.len();
    if size == 1 {
        let not_y = document.app("not", &[y[0]]);
        let expected = document.app("and", &[x[0], not_y]);
        return same(document, expected, result);
    }
    let not_x0 = document.app("not", &[x[0]]);
    let mut expected = document.app("and", &[not_x0, y[0]]);
    for i in 1..size - 1 {
        let equal = document.app("=", &[x[i], y[i]]);
        let kept = document.app("and", &[equal, expected]);
        let not_x = document.app("not", &[x[i]]);
        let less = document.app("and", &[not_x, y[i]]);
        expected = document.app("or", &[kept, less]);
    }
    let top = size - 1;
    let equal = document.app("=", &[x[top], y[top]]);
    let kept = document.app("and", &[equal, expected]);
    let not_y = document.app("not", &[y[top]]);
    let negative = document.app("and", &[x[top], not_y]);
    let expected = document.app("or", &[kept, negative]);
    same(document, expected, result)
}

pub(super) fn add(document: &mut Document, input: &StepInput) -> Checked {
    let (operands, result) = source(document, input, "bvadd")?;
    let Some((&first, rest)) = operands.split_first() else {
        return refuse("(bvadd) has no operands");
    };
    let mut sum = bits(document, first)?;
    for &next in rest {
        let next = bits(document, next)?;
        sum = ripple_carry_adder(document, &sum, &next, None)?.0;
    }
    let expected = document.app("@bbterm", &sum);
    same(document, expected, result)
}

/// `shift_add_multiplier`.
fn multiply(document: &mut Document, x: u32, y: u32) -> Result<u32, Verdict> {
    let size = width(document, x)?;
    let x = take(&bits(document, x)?, size)?;
    let y = take(&bits(document, y)?, size)?;
    let f = document.atom("false");
    let shift: Vec<Vec<u32>> = (0..size)
        .map(|j| {
            (0..size)
                .map(|i| {
                    if j <= i {
                        document.app("and", &[y[j], x[i - j]])
                    } else {
                        f
                    }
                })
                .collect()
        })
        .collect();
    let mut carry: Vec<Vec<u32>> = vec![vec![f; size]];
    let mut res: Vec<Vec<u32>> = vec![shift[0].clone()];
    for j in 1..size {
        carry.push(vec![f]);
        for i in 1..size {
            let next = if j < i {
                let (r, s) = (res[j - 1][i - 1], shift[j][i - 1]);
                let both = document.app("and", &[r, s]);
                let differ = document.app("xor", &[r, s]);
                let propagated = document.app("and", &[differ, carry[j][i - 1]]);
                document.app("or", &[both, propagated])
            } else {
                f
            };
            carry[j].push(next);
        }
        let row: Vec<u32> = (0..size)
            .map(|i| {
                if i == 0 {
                    shift[0][0]
                } else if j > i {
                    res[i][i]
                } else {
                    let differ = document.app("xor", &[res[j - 1][i], shift[j][i]]);
                    document.app("xor", &[differ, carry[j][i]])
                }
            })
            .collect();
        res.push(row);
    }
    let Some(last) = res.last() else {
        return refuse("a zero-width word: the consumer's checker panics");
    };
    let last = last.clone();
    Ok(document.app("@bbterm", &last))
}

pub(super) fn mult(document: &mut Document, input: &StepInput) -> Checked {
    let (operands, result) = source(document, input, "bvmul")?;
    let Some((&first, rest)) = operands.split_first() else {
        return refuse("(bvmul) has no operands");
    };
    let mut expected = first;
    for &next in rest {
        expected = multiply(document, expected, next)?;
    }
    same(document, expected, result)
}

pub(super) fn extract(document: &mut Document, input: &StepInput) -> Checked {
    let sides = shape(document, input.unit()?, "=", 2)?;
    let right = nary(document, sides[1], "@bbterm")?;
    let Some(([_, low], [word])) =
        document
            .indexed(sides[0], "extract")
            .and_then(|(indices, args)| {
                Some((
                    <[usize; 2]>::try_from(indices).ok()?,
                    <[u32; 1]>::try_from(args).ok()?,
                ))
            })
    else {
        return refuse("not ((_ extract i j) x)");
    };
    let source_bits = document.op(word, "@bbterm");
    for (offset, &bit) in right.iter().enumerate() {
        let index = low + offset;
        let expected = match &source_bits {
            Some(source_bits) => match source_bits.get(index) {
                Some(&expected) => expected,
                None => return refuse("an index past the word: the consumer's checker panics"),
            },
            None => document.bit_of(index, word),
        };
        same(document, expected, bit)?;
    }
    Ok(())
}

pub(super) fn concat(document: &mut Document, input: &StepInput) -> Checked {
    let (operands, result) = source(document, input, "concat")?;
    let right = nary(document, result, "@bbterm")?;
    let mut size = 0;
    let mut expected = Vec::new();
    for &operand in operands.iter().rev() {
        size += width(document, operand)?;
        expected.extend(bits(document, operand)?);
    }
    require(right.len() == size, || {
        format!("{} bits, not {size}", right.len())
    })?;
    require(expected == right, || {
        "the bits are not the operands' in order".to_string()
    })
}

pub(super) fn sign_extend(document: &mut Document, input: &StepInput) -> Checked {
    let sides = shape(document, input.unit()?, "=", 2)?;
    let Some(([extra], [word])) =
        document
            .indexed(sides[0], "sign_extend")
            .and_then(|(indices, args)| {
                Some((
                    <[usize; 1]>::try_from(indices).ok()?,
                    <[u32; 1]>::try_from(args).ok()?,
                ))
            })
    else {
        return refuse("not ((_ sign_extend i) x)");
    };
    if extra == 0 {
        return same(document, word, sides[1]);
    }
    let size = width(document, word)?;
    let mut out = bits(document, word)?;
    let Some(&sign) = out.get(size.wrapping_sub(1)) else {
        return refuse("a word is narrower than its sort: the consumer's checker panics");
    };
    out.extend(std::iter::repeat_n(sign, extra));
    let expected = document.app("@bbterm", &out);
    same(document, expected, sides[1])
}
