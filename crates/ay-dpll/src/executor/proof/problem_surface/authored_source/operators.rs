// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The builtin operators of pinned Carcara's problem parser, with the arity
//! and sort rules its `Parser::make_op` enforces and the result sorts its
//! `TermPool::compute_sort` assigns (`carcara/src/parser/mod.rs`,
//! `carcara/src/ast/pool/mod.rs` at 9a352ee).
//!
//! Carcara runs these checks while it PARSES the problem, with no Int/Real
//! subtyping (the gate never passes `--allow-int-real-subtyping`): `(= x 1)`
//! over a `Real` `x`, `(+ n 1.5)`, `(abs r)`, a unary `(str.++ s)` or a
//! ternary `bvsub` stops the parse, although AY's frontend coerces or accepts
//! each of them. A spelling that is not listed here is not a Carcara builtin,
//! and must be a symbol the problem declared.

use super::sorts::CarcaraSort as S;

type Outcome = Result<S, String>;

/// Pinned Carcara's result sort for the builtin `name` applied to arguments
/// of sorts `args`, or why it refuses the application; `None` when `name` is
/// not a builtin of pinned Carcara at all.
pub(super) fn builtin(name: &str, args: &[S]) -> Option<Outcome> {
    let check = Check { name, args };
    core(&check)
        .or_else(|| arithmetic(&check))
        .or_else(|| bitvector(&check))
        .or_else(|| string(&check))
        .or_else(|| regex(&check))
        .or_else(|| internal(&check))
}

/// Whether `name` is spelled like a builtin of pinned Carcara, which its
/// parser reads as that builtin before it looks the name up in the problem's
/// declarations.
pub(super) fn is_builtin(name: &str) -> bool {
    builtin(name, &[]).is_some()
}

struct Check<'a> {
    name: &'a str,
    args: &'a [S],
}

impl Check<'_> {
    fn exactly(&self, count: usize) -> Result<(), String> {
        self.arity(self.args.len() == count, &count.to_string())
    }

    fn at_least(&self, count: usize) -> Result<(), String> {
        self.arity(self.args.len() >= count, &format!("at least {count}"))
    }

    fn arity(&self, ok: bool, required: &str) -> Result<(), String> {
        if ok {
            return Ok(());
        }
        Err(format!(
            "`{}` is applied to {} argument(s); pinned Carcara 1.1.0 requires {required}",
            self.name,
            self.args.len()
        ))
    }

    fn refuse(&self, index: usize, required: &str) -> String {
        format!(
            "argument {} of `{}` has sort {}; pinned Carcara 1.1.0 requires {required} (it \
             coerces no Int/Real, Bool/Int or bit-vector width)",
            index + 1,
            self.name,
            self.args[index]
        )
    }

    fn arg_is(&self, index: usize, required: &S) -> Result<(), String> {
        if &self.args[index] == required {
            return Ok(());
        }
        Err(self.refuse(index, &required.to_string()))
    }

    fn all_are(&self, required: &S) -> Result<(), String> {
        (0..self.args.len()).try_for_each(|index| self.arg_is(index, required))
    }

    fn all_equal(&self) -> Result<(), String> {
        let first = &self.args[0];
        (1..self.args.len()).try_for_each(|index| self.arg_is(index, first))
    }

    fn numeric(&self, index: usize) -> Result<(), String> {
        if self.args[index].is_numeric() {
            return Ok(());
        }
        Err(self.refuse(index, "Int or Real"))
    }

    fn bitvec(&self, index: usize) -> Result<u64, String> {
        match self.args[index] {
            S::BitVec(width) => Ok(width),
            _ => Err(self.refuse(index, "a bit-vector sort")),
        }
    }

    /// Exactly `required.len()` arguments, of exactly those sorts.
    fn fixed(&self, required: &[S], result: S) -> Outcome {
        self.exactly(required.len())?;
        for (index, sort) in required.iter().enumerate() {
            self.arg_is(index, sort)?;
        }
        Ok(result)
    }

    fn first(&self) -> S {
        self.args[0].clone()
    }
}

fn core(c: &Check<'_>) -> Option<Outcome> {
    Some(match c.name {
        "true" | "false" => c.exactly(0).map(|()| S::Bool),
        "not" => c.fixed(&[S::Bool], S::Bool),
        "=>" => c
            .at_least(2)
            .and_then(|()| c.all_are(&S::Bool))
            .map(|()| S::Bool),
        "and" | "or" | "xor" => c
            .at_least(1)
            .and_then(|()| c.all_are(&S::Bool))
            .map(|()| S::Bool),
        "=" | "distinct" => c.at_least(2).and_then(|()| c.all_equal()).map(|()| S::Bool),
        "ite" => c
            .exactly(3)
            .and_then(|()| c.arg_is(0, &S::Bool))
            .and_then(|()| c.arg_is(2, &c.args[1]))
            .map(|()| c.args[1].clone()),
        _ => return None,
    })
}

fn arithmetic(c: &Check<'_>) -> Option<Outcome> {
    let same_numeric = |minimum| {
        c.at_least(minimum)
            .and_then(|()| c.numeric(0))
            .and_then(|()| c.all_equal())
            .map(|()| c.first())
    };
    Some(match c.name {
        "+" | "*" => same_numeric(2),
        "-" => same_numeric(1),
        "div" => c
            .at_least(2)
            .and_then(|()| c.arg_is(0, &S::Int))
            .and_then(|()| c.all_equal())
            .map(|()| S::Int),
        "/" => c
            .at_least(2)
            .and_then(|()| c.arg_is(0, &S::Real))
            .and_then(|()| c.all_equal())
            .map(|()| S::Real),
        "mod" => c.fixed(&[S::Int, S::Int], S::Int),
        "abs" | "int.pow2" | "int.log2" => c.fixed(&[S::Int], S::Int),
        "int.ispow2" => c.fixed(&[S::Int], S::Bool),
        "<" | ">" | "<=" | ">=" => c
            .at_least(2)
            .and_then(|()| (0..c.args.len()).try_for_each(|index| c.numeric(index)))
            .map(|()| S::Bool),
        "to_real" => c.exactly(1).and_then(|()| c.numeric(0)).map(|()| S::Real),
        "to_int" => c.fixed(&[S::Real], S::Int),
        "is_int" => c.fixed(&[S::Real], S::Bool),
        "select" => c.exactly(2).and_then(|()| match &c.args[0] {
            S::Array(index, element) => c.arg_is(1, index).map(|()| (**element).clone()),
            _ => Err(c.refuse(0, "an Array sort")),
        }),
        "store" => c.exactly(3).and_then(|()| match &c.args[0] {
            S::Array(index, element) => c
                .arg_is(1, index)
                .and_then(|()| c.arg_is(2, element))
                .map(|()| c.first()),
            _ => Err(c.refuse(0, "an Array sort")),
        }),
        _ => return None,
    })
}

fn bitvector(c: &Check<'_>) -> Option<Outcome> {
    Some(match c.name {
        "bvnot" | "bvneg" => c.exactly(1).and_then(|()| c.bitvec(0)).map(S::BitVec),
        "ubv_to_int" | "sbv_to_int" => c.exactly(1).and_then(|()| c.bitvec(0)).map(|_| S::Int),
        "concat" => c.at_least(2).and_then(|()| {
            (0..c.args.len())
                .map(|index| c.bitvec(index))
                .sum::<Result<u64, String>>()
                .map(S::BitVec)
        }),
        "bvadd" | "bvmul" | "bvand" | "bvor" | "bvxor" => c
            .at_least(2)
            .and_then(|()| c.bitvec(0))
            .and_then(|_| c.all_equal())
            .map(|()| c.first()),
        "bvult" | "bvule" | "bvugt" | "bvuge" | "bvslt" | "bvsle" | "bvsgt" | "bvsge" => {
            binary_bitvector(c).map(|_| S::Bool)
        }
        "bvcomp" => binary_bitvector(c).map(|_| S::BitVec(1)),
        "bvudiv" | "bvurem" | "bvshl" | "bvlshr" | "bvnand" | "bvnor" | "bvxnor" | "bvsub"
        | "bvsdiv" | "bvsrem" | "bvsmod" | "bvashr" => binary_bitvector(c),
        _ => return None,
    })
}

fn binary_bitvector(c: &Check<'_>) -> Outcome {
    c.exactly(2)?;
    c.bitvec(0)?;
    c.all_equal()?;
    Ok(c.first())
}

fn string(c: &Check<'_>) -> Option<Outcome> {
    let (s, i, r) = (S::Str, S::Int, S::RegLan);
    Some(match c.name {
        "str.++" => c.at_least(2).and_then(|()| c.all_are(&s)).map(|()| S::Str),
        "str.len" | "str.to_code" | "str.to_int" => c.fixed(&[s], S::Int),
        "str.is_digit" => c.fixed(&[s], S::Bool),
        "str.<" | "str.<=" | "str.prefixof" | "str.suffixof" | "str.contains" => {
            c.fixed(&[s.clone(), s], S::Bool)
        }
        "re.range" => c.fixed(&[s.clone(), s], S::RegLan),
        "str.at" => c.fixed(&[s, i], S::Str),
        "str.substr" => c.fixed(&[s, i.clone(), i], S::Str),
        "str.indexof" => c.fixed(&[s.clone(), s, i], S::Int),
        "str.replace" | "str.replace_all" => c.fixed(&[s.clone(), s.clone(), s], S::Str),
        "str.from_code" | "str.from_int" => c.fixed(&[i], S::Str),
        "str.to_re" => c.fixed(&[s], S::RegLan),
        "str.in_re" => c.fixed(&[s, r], S::Bool),
        "str.replace_re" | "str.replace_re_all" => c.fixed(&[s.clone(), r, s], S::Str),
        _ => return None,
    })
}

fn regex(c: &Check<'_>) -> Option<Outcome> {
    Some(match c.name {
        "re.none" | "re.all" | "re.allchar" => c.exactly(0).map(|()| S::RegLan),
        "re.++" | "re.union" | "re.inter" | "re.diff" => c
            .at_least(2)
            .and_then(|()| c.all_are(&S::RegLan))
            .map(|()| S::RegLan),
        "re.*" | "re.comp" | "re.+" | "re.opt" => c.fixed(&[S::RegLan], S::RegLan),
        _ => return None,
    })
}

/// Spellings pinned Carcara's parser reads as operators of its own proof
/// language. None is an SMT-LIB function, so no problem uses one soundly.
fn internal(c: &Check<'_>) -> Option<Outcome> {
    matches!(
        c.name,
        "@pbbterm" | "@bbterm" | "@bv" | "@bvsize" | "rare-list" | "cl" | "@d"
    )
    .then(|| {
        Err(format!(
            "`{}` is an operator of pinned Carcara's own proof language, so its parser does \
             not read it as the problem's symbol",
            c.name
        ))
    })
}
