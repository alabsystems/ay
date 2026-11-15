// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The consumer's `evaluate` rule: `(= t v)` holds when Clean's Carcara
//! evaluator (`ast/evaluate.rs`), which folds every operator application
//! whose arguments are all values and rebuilds the rest, turns `t` into
//! exactly `v`. Boolean and bit-vector operators are transcribed; an
//! arithmetic or other operator applied to values is `Undetermined`.

use std::collections::HashMap;

use num_bigint::{BigInt, BigUint, Sign};
use num_traits::{One, ToPrimitive, Zero};

use super::document::Document;
use super::{same, shape, undecided, Checked, StepInput, Verdict};

/// `MAX_EVALUATED_BV_WIDTH`: wider words are left unevaluated.
const MAX_WIDTH: usize = 1 << 16;

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
enum Value {
    Bool(bool),
    Int(BigInt),
    Bv(BigUint, usize),
}

fn modulus(width: usize) -> BigUint {
    BigUint::one() << width
}

/// `Value::new_bitvec`: the value modulo 2^width, `None` over the bound.
fn bitvec(value: BigInt, width: usize) -> Option<Value> {
    if width > MAX_WIDTH {
        return None;
    }
    let m = BigInt::from(modulus(width));
    let reduced = ((value % &m) + &m) % &m;
    Some(Value::Bv(reduced.to_biguint()?, width))
}

impl Value {
    fn bool(&self) -> Option<bool> {
        match self {
            Value::Bool(b) => Some(*b),
            _ => None,
        }
    }

    fn unsigned(&self) -> Option<(BigInt, usize)> {
        match self {
            Value::Bv(v, w) => Some((BigInt::from(v.clone()), *w)),
            _ => None,
        }
    }

    /// `as_signed_bitvec`: two's complement, `None` at width 0.
    fn signed(&self) -> Option<(BigInt, usize)> {
        let (v, w) = self.unsigned()?;
        if w == 0 {
            return None;
        }
        let top = BigInt::one() << (w - 1);
        Some(if v >= top {
            (v - (BigInt::one() << w), w)
        } else {
            (v, w)
        })
    }

    fn index(&self) -> Option<usize> {
        match self {
            Value::Int(i) => i.to_usize(),
            _ => None,
        }
    }
}

/// `Value::from_term` on an evaluated term.
fn value(document: &Document, id: u32) -> Option<Value> {
    if let Some(bits) = document.constant_bits(id) {
        let mut v = BigUint::zero();
        for (i, one) in bits.iter().enumerate() {
            if *one {
                v.set_bit(i as u64, true);
            }
        }
        return Some(Value::Bv(v, bits.len()));
    }
    match document.atom_text(id)? {
        "true" => Some(Value::Bool(true)),
        "false" => Some(Value::Bool(false)),
        text if text.bytes().all(|b| b.is_ascii_digit()) => {
            text.parse::<BigInt>().ok().map(Value::Int)
        }
        text => text
            .strip_prefix("\u{0}int:")
            .and_then(|t| t.parse().ok())
            .map(Value::Int),
    }
}

/// `Value::into_term`. A negative integer is a constant no printed term equals.
fn term(document: &mut Document, value: Value) -> u32 {
    match value {
        Value::Bool(b) => document.atom(if b { "true" } else { "false" }),
        Value::Int(i) if i.sign() == Sign::Minus => document.atom(&format!("\u{0}int:{i}")),
        Value::Int(i) => document.atom(&i.to_string()),
        Value::Bv(v, w) => {
            let bits: String = (0..w)
                .rev()
                .map(|i| if v.bit(i as u64) { '1' } else { '0' })
                .collect();
            document.atom(&format!("#b{bits}"))
        }
    }
}

enum Folded {
    Value(Value),
    /// The consumer leaves the application unevaluated.
    Kept,
}

/// `eval_op` over values; `Err` where the operator is not transcribed here.
fn fold(head: &str, args: &[Value]) -> Result<Folded, ()> {
    let kept = |v: Option<Value>| Ok(v.map_or(Folded::Kept, Folded::Value));
    let bools = || args.iter().map(Value::bool).collect::<Option<Vec<bool>>>();
    match head {
        "not" => kept(bools().and_then(|b| Some(Value::Bool(!*b.first()?)))),
        "=>" => kept(bools().and_then(|b| {
            let (last, init) = b.split_last()?;
            Some(Value::Bool(init.iter().any(|x| !x) || *last))
        })),
        "and" => kept(bools().map(|b| Value::Bool(b.iter().all(|&x| x)))),
        "or" => kept(bools().map(|b| Value::Bool(b.iter().any(|&x| x)))),
        "xor" => kept(bools().map(|b| Value::Bool(b.iter().fold(false, |acc, &x| acc != x)))),
        "=" => kept(Some(Value::Bool(args.windows(2).all(|w| w[0] == w[1])))),
        "distinct" => {
            let set: std::collections::HashSet<&Value> = args.iter().collect();
            kept(Some(Value::Bool(set.len() == args.len())))
        }
        "ite" => kept(
            args.first()
                .and_then(Value::bool)
                .and_then(|c| args.get(if c { 1 } else { 2 }).cloned()),
        ),
        "select" | "store" => Ok(Folded::Kept),
        _ => fold_bitvector(head, args),
    }
}

/// `eval_op`'s bit-vector operators.
fn fold_bitvector(head: &str, args: &[Value]) -> Result<Folded, ()> {
    let kept = |v: Option<Value>| Ok(v.map_or(Folded::Kept, Folded::Value));
    let bools = || args.iter().map(Value::bool).collect::<Option<Vec<bool>>>();
    let first = || args.first().and_then(Value::unsigned);
    let second = || args.get(1).and_then(Value::unsigned);
    match head {
        "bvnot" => kept(first().and_then(|(v, w)| bitvec(-v - 1, w))),
        "bvneg" => kept(first().and_then(|(v, w)| bitvec(-v, w))),
        "bvand" | "bvor" | "bvxor" | "bvadd" | "bvmul" => kept((|| {
            let (mut acc, w) = first()?;
            for arg in &args[1..] {
                let (x, _) = arg.unsigned()?;
                acc = match head {
                    "bvand" => acc & x,
                    "bvor" => acc | x,
                    "bvxor" => acc ^ x,
                    "bvadd" => acc + x,
                    _ => acc * x,
                };
                acc %= BigInt::from(modulus(w));
            }
            bitvec(acc, w)
        })()),
        "bvsub" | "bvudiv" | "bvurem" | "bvnand" | "bvnor" | "bvxnor" | "bvshl" | "bvlshr" => {
            kept((|| {
                let ((a, w), (b, _)) = (first()?, second()?);
                let all = BigInt::from(modulus(w)) - 1;
                let shift = b.to_usize().filter(|&s| s < w);
                let v = match head {
                    "bvsub" => a - b,
                    "bvudiv" if b.is_zero() => all,
                    "bvudiv" => a / b,
                    "bvurem" if b.is_zero() => a,
                    "bvurem" => a % b,
                    "bvnand" => all - (a & b),
                    "bvnor" => all - (a | b),
                    "bvxnor" => all - (a ^ b),
                    "bvshl" => shift.map_or_else(BigInt::zero, |s| a << s),
                    _ => shift.map_or_else(BigInt::zero, |s| a >> s),
                };
                bitvec(v, w)
            })())
        }
        "bvsdiv" | "bvsrem" | "bvsmod" | "bvashr" => fold_signed(head, args),
        "bvult" | "bvule" | "bvugt" | "bvuge" => kept((|| {
            let ((a, _), (b, _)) = (first()?, second()?);
            Some(Value::Bool(compare(head, &a, &b)))
        })()),
        "bvslt" | "bvsle" | "bvsgt" | "bvsge" => kept((|| {
            let ((a, _), (b, _)) = (args.first()?.signed()?, args.get(1)?.signed()?);
            Some(Value::Bool(compare(head, &a, &b)))
        })()),
        "concat" => kept((|| {
            let (mut v, mut width) = (BigInt::zero(), 0usize);
            for arg in args {
                let (b, j) = arg.unsigned()?;
                v = (v << j) + b;
                width += j;
            }
            bitvec(v, width)
        })()),
        "bvcomp" => kept((|| {
            let ((a, _), (b, _)) = (first()?, second()?);
            bitvec(BigInt::from(u8::from(a == b)), 1)
        })()),
        "@bbterm" => kept((|| {
            if args.len() > MAX_WIDTH {
                return None;
            }
            let bits = bools()?;
            let mut v = BigUint::zero();
            for (i, one) in bits.iter().enumerate() {
                v.set_bit(i as u64, *one);
            }
            Some(Value::Bv(v, bits.len()))
        })()),
        _ => Err(()),
    }
}

fn compare(head: &str, a: &BigInt, b: &BigInt) -> bool {
    match &head[head.len() - 2..] {
        "lt" => a < b,
        "le" => a <= b,
        "gt" => a > b,
        _ => a >= b,
    }
}

/// `eval_param_op`.
fn fold_indexed(name: &str, indices: &[Value], args: &[Value]) -> Result<Folded, ()> {
    let kept = |v: Option<Value>| Ok(v.map_or(Folded::Kept, Folded::Value));
    let index = |k: usize| indices.get(k).and_then(Value::index);
    let word = || args.first().and_then(Value::unsigned);
    match name {
        "extract" => kept((|| {
            let (i, j, (v, w)) = (index(0)?, index(1)?, word()?);
            if j > i || i >= w {
                return None;
            }
            bitvec((v % (BigInt::one() << (i + 1))) >> j, i - j + 1)
        })()),
        "zero_extend" => kept((|| {
            let (i, (v, w)) = (index(0)?, word()?);
            bitvec(v, w.checked_add(i)?)
        })()),
        "sign_extend" => kept((|| {
            let (i, (v, w)) = (index(0)?, args.first()?.signed()?);
            bitvec(v, w.checked_add(i)?)
        })()),
        "rotate_left" | "rotate_right" => kept((|| {
            let (i, (v, w)) = (index(0)?, word()?);
            if w == 0 {
                return None;
            }
            let r = if name == "rotate_left" {
                (w - i % w) % w
            } else {
                i % w
            };
            let low = &v % (BigInt::one() << r);
            bitvec((low << (w - r)) + (v >> r), w)
        })()),
        "repeat" => kept((|| {
            let (i, (v, w)) = (index(0).filter(|&i| i > 0)?, word()?);
            if w.checked_mul(i)? > MAX_WIDTH {
                return None;
            }
            let mut result = BigInt::zero();
            for _ in 0..i {
                result = (result << w) + &v;
            }
            bitvec(result, w * i)
        })()),
        "@bit_of" => kept((|| {
            let (i, (v, w)) = (index(0)?, word()?);
            (i < w).then(|| Value::Bool(v.bit(i as u64)))
        })()),
        _ => Err(()),
    }
}

/// The consumer's evaluation of `id`, memoized.
fn evaluate(
    document: &mut Document,
    id: u32,
    cache: &mut HashMap<u32, u32>,
) -> Result<u32, Verdict> {
    if let Some(&done) = cache.get(&id) {
        return Ok(done);
    }
    let children = match document.node(id) {
        super::document::Node::Atom(_) => return Ok(id),
        super::document::Node::List(children) => children.clone(),
    };
    let head = children[0];
    if let Some(name) = document.atom_text(head).map(str::to_string) {
        if matches!(
            name.as_str(),
            "forall" | "exists" | "let" | "choice" | "lambda" | "!"
        ) {
            return Ok(id);
        }
        let args = children[1..]
            .iter()
            .map(|&c| evaluate(document, c, cache))
            .collect::<Result<Vec<_>, _>>()?;
        let values: Option<Vec<Value>> = args.iter().map(|&a| value(document, a)).collect();
        // A problem symbol's application is the user's function, however it
        // is spelled: never folded as the operator it is named like.
        let operator = document.head(id).is_some();
        let folded = match values {
            Some(values) => operator
                .then(|| fold(&name, &values))
                .unwrap_or(Err(()))
                .map_or_else(
                    |()| undecided(format!("evaluating ({name} …) is not mirrored")),
                    Ok,
                )?,
            None => Folded::Kept,
        };
        let result = match folded {
            Folded::Value(v) => term(document, v),
            Folded::Kept => document.app(&name, &args),
        };
        cache.insert(id, result);
        return Ok(result);
    }
    let Some((name, _)) = document.indexed_name(head) else {
        return undecided("an application whose head is not an operator");
    };
    let indices: Vec<Value> = document.args(head)[1..]
        .iter()
        .filter_map(|&i| value(document, i))
        .collect();
    let args = children[1..]
        .iter()
        .map(|&c| evaluate(document, c, cache))
        .collect::<Result<Vec<_>, _>>()?;
    let values: Option<Vec<Value>> = args.iter().map(|&a| value(document, a)).collect();
    let folded = match values {
        Some(values) => fold_indexed(&name, &indices, &values).map_or_else(
            |()| undecided(format!("evaluating (_ {name} …) is not mirrored")),
            Ok,
        )?,
        None => Folded::Kept,
    };
    let result = match folded {
        Folded::Value(v) => term(document, v),
        Folded::Kept => {
            let mut rebuilt = vec![head];
            rebuilt.extend(args);
            document.intern(super::document::Node::List(rebuilt))
        }
    };
    cache.insert(id, result);
    Ok(result)
}

pub(super) fn evaluate_rule(document: &mut Document, input: &StepInput) -> Checked {
    let sides = shape(document, input.unit()?, "=", 2)?;
    let evaluated = evaluate(document, sides[0], &mut HashMap::new())?;
    same(document, evaluated, sides[1])
}

/// `eval_op`'s signed division and arithmetic shift.
fn fold_signed(head: &str, args: &[Value]) -> Result<Folded, ()> {
    let kept = |v: Option<Value>| Ok(v.map_or(Folded::Kept, Folded::Value));
    let second = || args.get(1).and_then(Value::unsigned);
    match head {
        "bvsdiv" | "bvsrem" | "bvsmod" => kept((|| {
            let ((a, w), (b, _)) = (args.first()?.signed()?, args.get(1)?.signed()?);
            if b.is_zero() {
                return None;
            }
            let v = match head {
                "bvsdiv" => &a / &b,
                "bvsrem" => &a % &b,
                _ => {
                    let r = &a % &b;
                    if !r.is_zero() && (r.sign() == Sign::Minus) != (b.sign() == Sign::Minus) {
                        r + b
                    } else {
                        r
                    }
                }
            };
            bitvec(v, w)
        })()),
        "bvashr" => kept((|| {
            let ((a, w), (b, _)) = (args.first()?.signed()?, second()?);
            let shift = b.to_usize().filter(|&s| s < w).unwrap_or(w);
            // Floor division: an arithmetic shift of a negative value.
            let divisor = BigInt::one() << shift;
            let q = &a / &divisor;
            let q = if a.sign() == Sign::Minus && !(&a % &divisor).is_zero() {
                q - 1
            } else {
                q
            };
            bitvec(q, w)
        })()),
        _ => Err(()),
    }
}
