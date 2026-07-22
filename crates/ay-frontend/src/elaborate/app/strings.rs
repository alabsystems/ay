// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use ay_core::{Constant, Sort, Symbol, TermData, TermId};
use num_bigint::BigInt;

use super::{Context, ElaborateError, Result};

impl Context {
    /// Char operators (`char.to_int`, `char.<=`, `char.is_digit`) desugar to Int
    /// arithmetic on a Unicode code point: a char literal `(_ char n)` lowers to
    /// the Int `n` (see `elaborate/term.rs`), and the native `Sort::Char` also
    /// lowers to a bounded Int. So a well-formed char-op argument is `Int`- or
    /// `Char`-sorted. ANY other sort means the argument is not a code point —
    /// e.g. a variable over an auto-uninterpreted `Char` sort name: the SMT-LIB
    /// frontend does not resolve `Char`, so `(declare-const c Char)` yields
    /// `Uninterpreted("Char")` (which z3 rejects outright as an unknown sort).
    /// Desugaring `char.to_int` as the identity over such a term leaked an
    /// uninterpreted-sorted value into an Int context and produced a WRONG
    /// `unsat` (#char-nonint-arg: `char.to_int(c)=65` → unsat because `c`
    /// collapsed). Reject it here so the CLI's dropped-command path fails closed
    /// to `unknown`, never a wrong verdict. Cannot reject a valid char literal
    /// (those are `Int`) or an FFI `Char`-sorted term.
    fn expect_char_code_arg(&self, arg: TermId) -> Result<()> {
        match self.terms.sort(arg) {
            Sort::Int | Sort::Char => Ok(()),
            // Label the expected sort `Int` (the code point): the auto-declared
            // `Uninterpreted("Char")` sort renders as "Char" too, so naming the
            // expected side `Char` would print the baffling "Sorts Char and Char
            // are incompatible". Valid CLI char-op args are always `Int`.
            other => Err(ElaborateError::SortMismatch {
                expected: Sort::Int.to_string(),
                actual: other.to_string(),
            }),
        }
    }

    pub(super) fn try_elaborate_string_or_regex_app(
        &mut self,
        name: &str,
        arg_ids: &mut [TermId],
    ) -> Result<Option<TermId>> {
        match name {
            "str.++" => {
                self.expect_min_arity("str.++", arg_ids, 2)?;
                self.expect_all_args_sort(arg_ids, &Sort::String)?;
                let all_const: Option<String> =
                    arg_ids.iter().try_fold(String::new(), |mut acc, &id| {
                        if let TermData::Const(Constant::String(s)) = self.terms.get(id) {
                            acc.push_str(s);
                            Some(acc)
                        } else {
                            None
                        }
                    });
                if let Some(result) = all_const {
                    return Ok(Some(self.terms.mk_string(result)));
                }
                Ok(Some(self.terms.mk_app(
                    Symbol::named("str.++"),
                    &arg_ids,
                    Sort::String,
                )))
            }
            "str.len" => {
                self.expect_exact_arity("str.len", arg_ids, 1)?;
                self.expect_arg_sort(arg_ids[0], &Sort::String)?;
                if let TermData::Const(Constant::String(s)) = self.terms.get(arg_ids[0]) {
                    return Ok(Some(self.terms.mk_int(BigInt::from(s.chars().count()))));
                }
                Ok(Some(self.terms.mk_app(
                    Symbol::named("str.len"),
                    &arg_ids,
                    Sort::Int,
                )))
            }
            "str.at" => {
                self.expect_exact_arity("str.at", arg_ids, 2)?;
                self.expect_arg_sort(arg_ids[0], &Sort::String)?;
                self.expect_arg_sort(arg_ids[1], &Sort::Int)?;
                // SMT-LIB defines `(str.at s i)` == `(str.substr s i 1)` exactly
                // (singleton character at position i, or "" when out of bounds).
                // Lowering to str.substr routes it through the more complete
                // substr theory — the opaque `str.at` atom was `unknown` on
                // symbolic strings while `str.substr` (its strict generalization)
                // decides them. Ground/out-of-bounds cases are unchanged. (z3 parity)
                let one = self.terms.mk_int(BigInt::from(1));
                let substr_args = [arg_ids[0], arg_ids[1], one];
                Ok(Some(self.terms.mk_app(
                    Symbol::named("str.substr"),
                    substr_args,
                    Sort::String,
                )))
            }
            "str.substr" => {
                self.expect_exact_arity("str.substr", arg_ids, 3)?;
                self.expect_arg_sort(arg_ids[0], &Sort::String)?;
                self.expect_arg_sort(arg_ids[1], &Sort::Int)?;
                self.expect_arg_sort(arg_ids[2], &Sort::Int)?;
                Ok(Some(self.terms.mk_app(
                    Symbol::named("str.substr"),
                    &arg_ids,
                    Sort::String,
                )))
            }
            "str.contains" | "str.prefixof" | "str.suffixof" => {
                self.expect_exact_arity(name, arg_ids, 2)?;
                self.expect_all_args_sort(arg_ids, &Sort::String)?;
                // Empty-argument tautologies (sound, definitional): the empty
                // string is a substring / prefix / suffix of EVERY string.
                // Without this fold AY leaves `(str.contains H "")` (and the
                // prefixof/suffixof analogues) as an opaque atom it cannot always
                // decide over a concat/variable haystack (returns `unknown`); in
                // a disjunction whose other disjunct is refutable it then wrongly
                // concludes `unsat` — a false proof (found by z3 differential
                // fuzzing). contains(H, N) is true when needle N is ""; prefixof
                // (P,H) / suffixof(S,H) are true when P / S is "".
                let empty_candidate = if name == "str.contains" {
                    arg_ids[1]
                } else {
                    arg_ids[0]
                };
                if matches!(
                    self.terms.get(empty_candidate),
                    TermData::Const(Constant::String(s)) if s.is_empty()
                ) {
                    return Ok(Some(self.terms.true_term()));
                }
                Ok(Some(self.terms.mk_app(
                    Symbol::named(name),
                    &arg_ids,
                    Sort::Bool,
                )))
            }
            "str.indexof" => {
                self.expect_exact_arity("str.indexof", arg_ids, 3)?;
                self.expect_arg_sort(arg_ids[0], &Sort::String)?;
                self.expect_arg_sort(arg_ids[1], &Sort::String)?;
                self.expect_arg_sort(arg_ids[2], &Sort::Int)?;
                Ok(Some(self.terms.mk_app(
                    Symbol::named("str.indexof"),
                    &arg_ids,
                    Sort::Int,
                )))
            }
            "str.replace" => {
                self.expect_exact_arity("str.replace", arg_ids, 3)?;
                self.expect_all_args_sort(arg_ids, &Sort::String)?;
                Ok(Some(self.terms.mk_app(
                    Symbol::named("str.replace"),
                    &arg_ids,
                    Sort::String,
                )))
            }
            "str.replace_all" => {
                self.expect_exact_arity("str.replace_all", arg_ids, 3)?;
                self.expect_all_args_sort(arg_ids, &Sort::String)?;
                if let (
                    TermData::Const(Constant::String(s)),
                    TermData::Const(Constant::String(t)),
                    TermData::Const(Constant::String(u)),
                ) = (
                    self.terms.get(arg_ids[0]),
                    self.terms.get(arg_ids[1]),
                    self.terms.get(arg_ids[2]),
                ) {
                    let result = if t.is_empty() {
                        s.clone()
                    } else {
                        s.replace(t, u)
                    };
                    return Ok(Some(self.terms.mk_string(result)));
                }
                Ok(Some(self.terms.mk_app(
                    Symbol::named("str.replace_all"),
                    &arg_ids,
                    Sort::String,
                )))
            }
            "str.replace_re" | "str.replace_re_all" => {
                self.expect_exact_arity(name, arg_ids, 3)?;
                self.expect_arg_sort(arg_ids[0], &Sort::String)?;
                self.expect_arg_sort(arg_ids[1], &Sort::RegLan)?;
                self.expect_arg_sort(arg_ids[2], &Sort::String)?;
                Ok(Some(self.terms.mk_app(
                    Symbol::named(name),
                    &arg_ids,
                    Sort::String,
                )))
            }
            "str.to_int" | "str.to.int" => {
                self.expect_exact_arity(name, arg_ids, 1)?;
                self.expect_arg_sort(arg_ids[0], &Sort::String)?;
                Ok(Some(self.terms.mk_app(
                    Symbol::named("str.to_int"),
                    &arg_ids,
                    Sort::Int,
                )))
            }
            "str.from_int" | "int.to.str" => {
                self.expect_exact_arity(name, arg_ids, 1)?;
                self.expect_arg_sort(arg_ids[0], &Sort::Int)?;
                Ok(Some(self.terms.mk_app(
                    Symbol::named("str.from_int"),
                    &arg_ids,
                    Sort::String,
                )))
            }
            "str.to_code" => {
                self.expect_exact_arity("str.to_code", arg_ids, 1)?;
                self.expect_arg_sort(arg_ids[0], &Sort::String)?;
                Ok(Some(self.terms.mk_app(
                    Symbol::named("str.to_code"),
                    &arg_ids,
                    Sort::Int,
                )))
            }
            "str.from_code" => {
                self.expect_exact_arity("str.from_code", arg_ids, 1)?;
                self.expect_arg_sort(arg_ids[0], &Sort::Int)?;
                Ok(Some(self.terms.mk_app(
                    Symbol::named("str.from_code"),
                    &arg_ids,
                    Sort::String,
                )))
            }
            "str.to_lower" | "str.to_upper" => {
                self.expect_exact_arity(name, arg_ids, 1)?;
                self.expect_arg_sort(arg_ids[0], &Sort::String)?;
                Ok(Some(self.terms.mk_app(
                    Symbol::named(name),
                    &arg_ids,
                    Sort::String,
                )))
            }
            "str.<" | "str.<=" => {
                self.expect_exact_arity(name, arg_ids, 2)?;
                self.expect_all_args_sort(arg_ids, &Sort::String)?;
                Ok(Some(self.terms.mk_app(
                    Symbol::named(name),
                    &arg_ids,
                    Sort::Bool,
                )))
            }
            "str.is_digit" => {
                self.expect_exact_arity("str.is_digit", arg_ids, 1)?;
                self.expect_arg_sort(arg_ids[0], &Sort::String)?;
                Ok(Some(self.terms.mk_app(
                    Symbol::named("str.is_digit"),
                    &arg_ids,
                    Sort::Bool,
                )))
            }
            // Char theory. A Char is a Unicode code point, which AY represents as
            // that bounded Int (char literals `(_ Char n)` elaborate to the Int
            // `n`, see `elaborate/term.rs`), so every char operator desugars to
            // Int arithmetic on the code point — sound because a Char IS its code
            // point. `char.to_int` is then the identity.
            "char.to_int" => {
                self.expect_exact_arity("char.to_int", arg_ids, 1)?;
                self.expect_char_code_arg(arg_ids[0])?;
                Ok(Some(arg_ids[0]))
            }
            // NB: z3 exposes `char.<=` but NOT `char.<`, so AY rejects `char.<`
            // too (it is not in RESERVED_OP_NAMES) rather than being more
            // permissive than z3.
            "char.<=" => {
                self.expect_exact_arity("char.<=", arg_ids, 2)?;
                self.expect_char_code_arg(arg_ids[0])?;
                self.expect_char_code_arg(arg_ids[1])?;
                Ok(Some(self.terms.mk_le(arg_ids[0], arg_ids[1])))
            }
            "char.is_digit" => {
                self.expect_exact_arity("char.is_digit", arg_ids, 1)?;
                self.expect_char_code_arg(arg_ids[0])?;
                // ASCII digit range [48 ('0'), 57 ('9')].
                let lo = self.terms.mk_int(BigInt::from(48));
                let hi = self.terms.mk_int(BigInt::from(57));
                let ge_lo = self.terms.mk_le(lo, arg_ids[0]);
                let le_hi = self.terms.mk_le(arg_ids[0], hi);
                Ok(Some(self.terms.mk_and(vec![ge_lo, le_hi])))
            }
            "str.to_re" | "str.to.re" => {
                self.expect_exact_arity(name, arg_ids, 1)?;
                self.expect_arg_sort(arg_ids[0], &Sort::String)?;
                Ok(Some(self.terms.mk_app(
                    Symbol::named("str.to_re"),
                    &arg_ids,
                    Sort::RegLan,
                )))
            }
            "str.in_re" | "str.in.re" => {
                self.expect_exact_arity(name, arg_ids, 2)?;
                self.expect_arg_sort(arg_ids[0], &Sort::String)?;
                self.expect_arg_sort(arg_ids[1], &Sort::RegLan)?;
                // #8779 rewrite (Z3 seq_rewriter.cpp:4340-4343 lift_str_from_to_re):
                //   (str.in_re x (str.to_re s))  -->  (= x s)
                //
                // ay's regex ground-membership solver evaluates str.in_re atoms
                // correctly on models, but the literal `s` never enters the
                // string equality graph — so search cannot drive `x` toward `s`.
                // When search picks a branch forcing `x = ""` via concat/length
                // constraints, the regex atom is violated in the final model,
                // and only the soundness gate (#478af14c4) catches it, producing
                // `unknown` instead of `unsat`. Rewriting to a string equality
                // makes the constraint visible to the equality graph and to
                // Tseitin/BVE preprocessing, letting ay answer `unsat`.
                let inner = arg_ids[1];
                if let TermData::App(sym, inner_args) = self.terms.get(inner) {
                    if sym.name() == "str.to_re" && inner_args.len() == 1 {
                        let s = inner_args[0];
                        return Ok(Some(self.terms.mk_eq(arg_ids[0], s)));
                    }
                }
                Ok(Some(self.terms.mk_app(
                    Symbol::named("str.in_re"),
                    &arg_ids,
                    Sort::Bool,
                )))
            }
            "re.++" | "re.union" | "re.inter" => {
                // z3 parity: these n-ary regex ops accept a single argument as
                // the definitional n-ary identity ((re.++ r) = r, (re.union r) = r,
                // (re.inter r) = r). 0-arg stays an error (z3 errors too). Returning
                // the operand verbatim cannot introduce a semantic delta.
                self.expect_min_arity(name, arg_ids, 1)?;
                self.expect_all_args_sort(arg_ids, &Sort::RegLan)?;
                if arg_ids.len() == 1 {
                    return Ok(Some(arg_ids[0]));
                }
                Ok(Some(self.terms.mk_app(
                    Symbol::named(name),
                    &arg_ids,
                    Sort::RegLan,
                )))
            }
            "re.*" | "re.+" | "re.opt" | "re.comp" => {
                self.expect_exact_arity(name, arg_ids, 1)?;
                self.expect_arg_sort(arg_ids[0], &Sort::RegLan)?;
                Ok(Some(self.terms.mk_app(
                    Symbol::named(name),
                    &arg_ids,
                    Sort::RegLan,
                )))
            }
            "re.range" => {
                self.expect_exact_arity("re.range", arg_ids, 2)?;
                self.expect_all_args_sort(arg_ids, &Sort::String)?;
                Ok(Some(self.terms.mk_app(
                    Symbol::named("re.range"),
                    &arg_ids,
                    Sort::RegLan,
                )))
            }
            "re.diff" => {
                self.expect_exact_arity("re.diff", arg_ids, 2)?;
                self.expect_all_args_sort(arg_ids, &Sort::RegLan)?;
                Ok(Some(self.terms.mk_app(
                    Symbol::named("re.diff"),
                    &arg_ids,
                    Sort::RegLan,
                )))
            }
            "re.none" | "re.all" | "re.allchar" => {
                self.expect_exact_arity(name, arg_ids, 0)?;
                Ok(Some(self.terms.mk_app(
                    Symbol::named(name),
                    vec![],
                    Sort::RegLan,
                )))
            }
            _ => Ok(None),
        }
    }
}
