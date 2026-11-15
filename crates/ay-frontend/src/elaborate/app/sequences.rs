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
        "seq.replace_all" => "str.replace_all",
        "seq.prefixof" => "str.prefixof",
        "seq.suffixof" => "str.suffixof",
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
    "seq.replace_all",
    "seq.prefixof",
    "seq.suffixof",
    "seq.last_indexof",
    "seq.in.re",
    "seq.to.re",
];

/// Where a sequence operator takes its operands: the positions that hold a
/// sequence of the first operand's sort, and those that hold an Int.
fn sequence_operand_positions(name: &str) -> Option<(&'static [usize], &'static [usize])> {
    Some(match name {
        "seq.++" => (&[], &[]),
        "seq.len" => (&[0], &[]),
        "seq.nth" | "seq.at" => (&[0], &[1]),
        "seq.extract" => (&[0], &[1, 2]),
        "seq.contains" | "seq.prefixof" | "seq.suffixof" | "seq.last_indexof" => (&[0, 1], &[]),
        "seq.indexof" => (&[0, 1], &[2]),
        "seq.replace" | "seq.replace_all" => (&[0, 1, 2], &[]),
        _ => return None,
    })
}

impl Context {
    /// Check the operands of a sequence operator as z3 does: its sequence
    /// operands share one `(Seq T)` sort (every operand, for `seq.++`) and
    /// its index and length operands are Int. Called after the arity check.
    fn expect_sequence_operand_sorts(&self, name: &str, arg_ids: &[TermId]) -> Result<()> {
        let Some((sequences, ints)) = sequence_operand_positions(name) else {
            return Ok(());
        };
        let Some(&first) = arg_ids.first() else {
            return Ok(());
        };
        let sequence = self.terms.sort(first);
        if !sequence.is_seq() {
            return Err(ElaborateError::SortMismatch {
                expected: "Seq".to_string(),
                actual: sequence.to_string(),
            });
        }
        let sequence_positions: Vec<usize> = if name == "seq.++" {
            (0..arg_ids.len()).collect()
        } else {
            sequences.to_vec()
        };
        for position in sequence_positions {
            if let Some(&arg) = arg_ids.get(position) {
                self.expect_arg_sort(arg, sequence)?;
            }
        }
        for &position in ints {
            if let Some(&arg) = arg_ids.get(position) {
                self.expect_arg_sort(arg, &Sort::Int)?;
            }
        }
        Ok(())
    }

    /// Check a fold's function, initial value and sequence as z3 does. The
    /// function is curried as nested arrays: `leading` (the index for
    /// `seq.foldli`), then the accumulator, then the element, giving the
    /// accumulator's sort.
    fn expect_fold_operand_sorts(
        &self,
        leading: &[Sort],
        function: TermId,
        init: TermId,
        sequence: TermId,
    ) -> Result<()> {
        let accumulator = self.terms.sort(init).clone();
        let Some(element) = self.terms.sort(sequence).seq_element().cloned() else {
            return Err(ElaborateError::SortMismatch {
                expected: "Seq".to_string(),
                actual: self.terms.sort(sequence).to_string(),
            });
        };
        let expected = leading.iter().rev().fold(
            Sort::array(
                accumulator.clone(),
                Sort::array(element, accumulator.clone()),
            ),
            |inner, index| Sort::array(index.clone(), inner),
        );
        self.expect_arg_sort(function, &expected)
    }

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
        if matches!(name, "seq.power" | "str.power") {
            self.expect_exact_arity(name, arg_ids, 2)?;
            let sort = self.terms.sort(arg_ids[0]).clone();
            if !matches!(sort, Sort::String | Sort::Seq(_))
                || (name == "str.power" && sort != Sort::String)
            {
                return Err(ElaborateError::SortMismatch {
                    expected: "String or Seq".to_string(),
                    actual: sort.to_string(),
                });
            }
            self.expect_arg_sort(arg_ids[1], &Sort::Int)?;
            return Ok(Some(if self.preserve_sequence_power {
                self.terms
                    .mk_app_structural(Symbol::named("seq.power"), arg_ids, sort)
            } else {
                self.terms.mk_app(Symbol::named("seq.power"), arg_ids, sort)
            }));
        }
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
                self.expect_sequence_operand_sorts(name, arg_ids)?;
                let seq_sort = self.terms.sort(arg_ids[0]).clone();
                Ok(Some(self.terms.mk_app(
                    Symbol::named("seq.++"),
                    &arg_ids,
                    seq_sort,
                )))
            }
            "seq.len" => {
                self.expect_exact_arity("seq.len", arg_ids, 1)?;
                self.expect_sequence_operand_sorts(name, arg_ids)?;
                Ok(Some(self.terms.mk_app(
                    Symbol::named("seq.len"),
                    &arg_ids,
                    Sort::Int,
                )))
            }
            "seq.nth" => {
                self.expect_exact_arity("seq.nth", arg_ids, 2)?;
                self.expect_sequence_operand_sorts(name, arg_ids)?;
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
                self.expect_sequence_operand_sorts(name, arg_ids)?;
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
                self.expect_sequence_operand_sorts(name, arg_ids)?;
                let seq_sort = self.terms.sort(arg_ids[0]).clone();
                Ok(Some(self.terms.mk_app(
                    Symbol::named("seq.extract"),
                    &arg_ids,
                    seq_sort,
                )))
            }
            "seq.contains" | "seq.prefixof" | "seq.suffixof" => {
                self.expect_exact_arity(name, arg_ids, 2)?;
                self.expect_sequence_operand_sorts(name, arg_ids)?;
                Ok(Some(self.terms.mk_app(
                    Symbol::named(name),
                    &arg_ids,
                    Sort::Bool,
                )))
            }
            "seq.indexof" => {
                self.expect_exact_arity("seq.indexof", arg_ids, 3)?;
                self.expect_sequence_operand_sorts(name, arg_ids)?;
                Ok(Some(self.terms.mk_app(
                    Symbol::named("seq.indexof"),
                    &arg_ids,
                    Sort::Int,
                )))
            }
            "seq.last_indexof" => {
                self.expect_exact_arity("seq.last_indexof", arg_ids, 2)?;
                self.expect_sequence_operand_sorts(name, arg_ids)?;
                Ok(Some(self.terms.mk_app(
                    Symbol::named("seq.last_indexof"),
                    &arg_ids,
                    Sort::Int,
                )))
            }
            "seq.replace" | "seq.replace_all" => {
                self.expect_exact_arity(name, arg_ids, 3)?;
                self.expect_sequence_operand_sorts(name, arg_ids)?;
                let seq_sort = self.terms.sort(arg_ids[0]).clone();
                Ok(Some(self.terms.mk_app(
                    Symbol::named(name),
                    &arg_ids,
                    seq_sort,
                )))
            }
            // `RegLan` is the sort of regular expressions over strings, so
            // it cannot type one over a `(Seq T)`: z3 gives that the sort
            // `(RegEx (Seq T))` and rejects it beside a string regex, which
            // `RegLan` would accept. String operands were routed to the
            // `str.*` twins above.
            "seq.to.re" | "seq.to_re" | "seq.in.re" | "seq.in_re" => {
                let membership = matches!(name, "seq.in.re" | "seq.in_re");
                self.expect_exact_arity(name, arg_ids, if membership { 2 } else { 1 })?;
                let arg_sort = self.terms.sort(arg_ids[0]).clone();
                if !arg_sort.is_seq() {
                    return Err(ElaborateError::SortMismatch {
                        expected: "Seq".into(),
                        actual: arg_sort.to_string(),
                    });
                }
                if membership {
                    self.expect_arg_sort(arg_ids[1], &Sort::RegLan)?;
                }
                Err(ElaborateError::Unsupported(format!(
                    "{name} over a {arg_sort} operand is not supported: regular \
                     expressions are supported over String only"
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
                self.expect_fold_operand_sorts(&[], arg_ids[0], arg_ids[1], arg_ids[2])?;
                Ok(Some(self.terms.mk_app(
                    Symbol::named("seq.foldl"),
                    &arg_ids,
                    self.terms.sort(arg_ids[1]).clone(),
                )))
            }
            "seq.foldli" | "seq.fold_lefti" => {
                self.expect_exact_arity("seq.foldli", arg_ids, 4)?;
                self.expect_arg_sort(arg_ids[1], &Sort::Int)?;
                self.expect_fold_operand_sorts(&[Sort::Int], arg_ids[0], arg_ids[2], arg_ids[3])?;
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
