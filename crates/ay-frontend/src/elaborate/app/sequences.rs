// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use ay_core::{Sort, Symbol, TermId};
use num_bigint::BigInt;

use super::{Context, ElaborateError, Result};

/// The `str.*` twin of a `seq.*` operator, for the case where the operand is a
/// `String`. Each pair is the SAME operator on the same values, so routing to the
/// twin is a re-spelling, not a re-interpretation. `None` = AY has no twin.
///
/// Only operators whose SEQUENCE operand is argument 0 belong here; that is what
/// [`Context::seq_app_over_string`] inspects.
fn string_twin_of_seq_op(name: &str) -> Option<&'static str> {
    Some(match name {
        "seq.len" => "str.len",
        "seq.++" => "str.++",
        "seq.at" => "str.at",
        "seq.contains" => "str.contains",
        "seq.indexof" => "str.indexof",
        "seq.extract" => "str.substr",
        "seq.replace" => "str.replace",
        "seq.in.re" => "str.in_re",
        "seq.to.re" => "str.to_re",
        _ => return None,
    })
}

/// `seq.*` operators that take their sequence as argument 0. A `String` there
/// means the app is a string operation written with its sequence spelling.
const SEQ_OPS_WITH_SEQUENCE_ARG0: &[&str] = &[
    "seq.len",
    "seq.++",
    "seq.at",
    "seq.nth",
    "seq.contains",
    "seq.indexof",
    "seq.extract",
    "seq.replace",
    "seq.last_indexof",
    "seq.in.re",
    "seq.to.re",
];

impl Context {
    /// True when `name` is a sequence operator applied to a `String` operand.
    fn seq_app_over_string(&self, name: &str, arg_ids: &[TermId]) -> bool {
        SEQ_OPS_WITH_SEQUENCE_ARG0.contains(&name)
            && arg_ids
                .first()
                .is_some_and(|a| matches!(self.terms.sort(*a), Sort::String))
    }

    pub(super) fn try_elaborate_sequence_app(
        &mut self,
        name: &str,
        arg_ids: &mut [TermId],
    ) -> Result<Option<TermId>> {
        // SMT-LIB defines `String` as `(Seq Char)`, so every sequence operator is
        // also a string operator and z3 decides both spellings. AY models
        // `Sort::String` separately from `Sort::Seq`, so a `seq.*` app over a
        // String used to build a named app that NEITHER theory interprets — it
        // survived as an uninterpreted function and produced WRONG verdicts:
        // `(not (= (seq.len "abab") 4))` answered `sat` (z3: unsat), silently and
        // with exit 0. Route to the `str.*` twin where one exists; where it does
        // not, fail closed with an honest error rather than answer from a stub.
        if self.seq_app_over_string(name, arg_ids) {
            return match string_twin_of_seq_op(name) {
                Some(str_name) => self.try_elaborate_string_or_regex_app(str_name, arg_ids),
                None => Err(ElaborateError::Unsupported(format!(
                    "{name} over a String operand is not supported: AY has no string \
                     implementation of this sequence operator, and answering from an \
                     uninterpreted stub would risk a wrong verdict"
                ))),
            };
        }
        match name {
            "seq.unit" => {
                self.expect_exact_arity("seq.unit", arg_ids, 1)?;
                let elem_sort = self.terms.sort(arg_ids[0]).clone();
                Ok(Some(self.terms.mk_app(
                    Symbol::named("seq.unit"),
                    &arg_ids,
                    Sort::seq(elem_sort),
                )))
            }
            "seq.++" => {
                self.expect_min_arity("seq.++", arg_ids, 2)?;
                let seq_sort = self.terms.sort(arg_ids[0]).clone();
                Ok(Some(self.terms.mk_app(
                    Symbol::named("seq.++"),
                    &arg_ids,
                    seq_sort,
                )))
            }
            "seq.len" => {
                self.expect_exact_arity("seq.len", arg_ids, 1)?;
                Ok(Some(self.terms.mk_app(
                    Symbol::named("seq.len"),
                    &arg_ids,
                    Sort::Int,
                )))
            }
            "seq.nth" => {
                self.expect_exact_arity("seq.nth", arg_ids, 2)?;
                let seq_sort = self.terms.sort(arg_ids[0]).clone();
                let elem_sort = seq_sort.seq_element().cloned().unwrap_or(Sort::Int);
                Ok(Some(self.terms.mk_app(
                    Symbol::named("seq.nth"),
                    &arg_ids,
                    elem_sort,
                )))
            }
            "seq.at" => {
                self.expect_exact_arity("seq.at", arg_ids, 2)?;
                let seq_sort = self.terms.sort(arg_ids[0]).clone();
                let one = self.terms.mk_int(BigInt::from(1));
                Ok(Some(self.terms.mk_app(
                    Symbol::named("seq.extract"),
                    vec![arg_ids[0], arg_ids[1], one],
                    seq_sort,
                )))
            }
            "seq.extract" => {
                self.expect_exact_arity("seq.extract", arg_ids, 3)?;
                let seq_sort = self.terms.sort(arg_ids[0]).clone();
                Ok(Some(self.terms.mk_app(
                    Symbol::named("seq.extract"),
                    &arg_ids,
                    seq_sort,
                )))
            }
            "seq.contains" | "seq.prefixof" | "seq.suffixof" => {
                self.expect_exact_arity(name, arg_ids, 2)?;
                Ok(Some(self.terms.mk_app(
                    Symbol::named(name),
                    &arg_ids,
                    Sort::Bool,
                )))
            }
            "seq.indexof" => {
                self.expect_exact_arity("seq.indexof", arg_ids, 3)?;
                Ok(Some(self.terms.mk_app(
                    Symbol::named("seq.indexof"),
                    &arg_ids,
                    Sort::Int,
                )))
            }
            "seq.last_indexof" => {
                self.expect_exact_arity("seq.last_indexof", arg_ids, 2)?;
                Ok(Some(self.terms.mk_app(
                    Symbol::named("seq.last_indexof"),
                    &arg_ids,
                    Sort::Int,
                )))
            }
            "seq.replace" | "seq.replace_all" => {
                self.expect_exact_arity(name, arg_ids, 3)?;
                let seq_sort = self.terms.sort(arg_ids[0]).clone();
                Ok(Some(self.terms.mk_app(
                    Symbol::named(name),
                    &arg_ids,
                    seq_sort,
                )))
            }
            "seq.to.re" | "seq.to_re" => {
                self.expect_exact_arity(name, arg_ids, 1)?;
                let arg_sort = self.terms.sort(arg_ids[0]).clone();
                if !arg_sort.is_seq() {
                    return Err(ElaborateError::SortMismatch {
                        expected: "Seq".into(),
                        actual: arg_sort.to_string(),
                    });
                }
                Ok(Some(self.terms.mk_app(
                    Symbol::named("seq.to_re"),
                    &arg_ids,
                    Sort::RegLan,
                )))
            }
            "seq.in.re" | "seq.in_re" => {
                self.expect_exact_arity(name, arg_ids, 2)?;
                let arg0_sort = self.terms.sort(arg_ids[0]).clone();
                if !arg0_sort.is_seq() {
                    return Err(ElaborateError::SortMismatch {
                        expected: "Seq".into(),
                        actual: arg0_sort.to_string(),
                    });
                }
                self.expect_arg_sort(arg_ids[1], &Sort::RegLan)?;
                Ok(Some(self.terms.mk_app(
                    Symbol::named("seq.in_re"),
                    &arg_ids,
                    Sort::Bool,
                )))
            }
            "seq.map" => {
                self.expect_exact_arity("seq.map", arg_ids, 2)?;
                let (domain, result_elem) = match self.terms.sort(arg_ids[0]).clone() {
                    Sort::Array(function) => (function.index_sort, function.element_sort),
                    actual => {
                        return Err(ElaborateError::SortMismatch {
                            expected: "Array function: seq.map first operand".to_string(),
                            actual: actual.to_string(),
                        });
                    }
                };
                self.expect_arg_sort(arg_ids[1], &Sort::seq(domain))?;
                Ok(Some(self.terms.mk_app(
                    Symbol::named("seq.map"),
                    &arg_ids,
                    Sort::seq(result_elem),
                )))
            }
            "seq.mapi" => {
                self.expect_exact_arity("seq.mapi", arg_ids, 3)?;
                // The indexed map's function-as-array is CURRIED, index first:
                // `f : (Array Int (Array E R))` (libz3-cross-checked, matching
                // `Z3_mk_seq_mapi` in ay-ffi). The result element sort is the
                // INNER layer's range `R`, so peel two layers, not one.
                let outer = match self.terms.sort(arg_ids[0]).clone() {
                    Sort::Array(function) => function,
                    actual => {
                        return Err(ElaborateError::SortMismatch {
                            expected: "two-argument Array function: seq.mapi first operand"
                                .to_string(),
                            actual: actual.to_string(),
                        });
                    }
                };
                if outer.index_sort != Sort::Int {
                    return Err(ElaborateError::SortMismatch {
                        expected: "Int index domain: seq.mapi function".to_string(),
                        actual: outer.index_sort.to_string(),
                    });
                }
                let inner = match outer.element_sort {
                    Sort::Array(function) => function,
                    actual => {
                        return Err(ElaborateError::SortMismatch {
                            expected: "two-argument Array function: seq.mapi first operand"
                                .to_string(),
                            actual: actual.to_string(),
                        });
                    }
                };
                self.expect_arg_sort(arg_ids[1], &Sort::Int)?;
                self.expect_arg_sort(arg_ids[2], &Sort::seq(inner.index_sort.clone()))?;
                Ok(Some(self.terms.mk_app(
                    Symbol::named("seq.mapi"),
                    &arg_ids,
                    Sort::seq(inner.element_sort),
                )))
            }
            // `seq.fold_left` is z3's SMT-LIB spelling of `seq.foldl` (both
            // accepted by z3 4.15.4, identical semantics); normalize to the
            // internal `seq.foldl` symbol so the ho_unfold decision path fires.
            "seq.foldl" | "seq.fold_left" => {
                self.expect_exact_arity("seq.foldl", arg_ids, 3)?;
                Ok(Some(self.terms.mk_app(
                    Symbol::named("seq.foldl"),
                    &arg_ids,
                    self.terms.sort(arg_ids[1]).clone(),
                )))
            }
            "seq.foldli" | "seq.fold_lefti" => {
                self.expect_exact_arity("seq.foldli", arg_ids, 4)?;
                Ok(Some(self.terms.mk_app(
                    Symbol::named("seq.foldli"),
                    &arg_ids,
                    self.terms.sort(arg_ids[2]).clone(),
                )))
            }
            "seq.empty" => {
                self.expect_exact_arity("seq.empty", arg_ids, 0)?;
                Err(ElaborateError::Unsupported(
                    "bare seq.empty requires sort annotation: use (as seq.empty (Seq T))".into(),
                ))
            }
            _ => Ok(None),
        }
    }
}
