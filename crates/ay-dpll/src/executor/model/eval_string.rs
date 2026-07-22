// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! String evaluation helpers for model evaluation.
//!
//! Extracted from `mod.rs` to reduce file size (Wave C2 of #2998 module splits).

use ay_core::TermId;
use ay_strings::eval as str_eval;
use num_bigint::BigInt;
use num_rational::BigRational;

use super::{EvalValue, Executor, Model};

impl Executor {
    /// Evaluate a string application term.
    ///
    /// Handles all `str.*` operations including string arithmetic,
    /// comparison, regex matching, and conversion operations.
    pub(super) fn evaluate_str_app(&self, model: &Model, name: &str, args: &[TermId]) -> EvalValue {
        match name {
            "str.len" if args.len() == 1 => match self.evaluate_term(model, args[0]) {
                EvalValue::String(s) => {
                    EvalValue::Rational(BigRational::from(BigInt::from(s.chars().count())))
                }
                _ => EvalValue::Unknown,
            },
            "str.++" => {
                let mut result = String::new();
                for &arg in args {
                    match self.evaluate_term(model, arg) {
                        EvalValue::String(s) => result.push_str(&s),
                        _ => return EvalValue::Unknown,
                    }
                }
                EvalValue::String(result)
            }
            "str.substr" if args.len() == 3 => {
                let sv = self.evaluate_term(model, args[0]);
                let iv = self.evaluate_term(model, args[1]);
                let nv = self.evaluate_term(model, args[2]);
                match (sv, iv, nv) {
                    (
                        EvalValue::String(s),
                        EvalValue::Rational(i_rat),
                        EvalValue::Rational(n_rat),
                    ) => match str_eval::eval_str_substr(
                        &s,
                        &i_rat.to_integer(),
                        &n_rat.to_integer(),
                    ) {
                        Some(r) => EvalValue::String(r),
                        None => EvalValue::String(String::new()),
                    },
                    _ => EvalValue::Unknown,
                }
            }
            "str.at" if args.len() == 2 => {
                let sv = self.evaluate_term(model, args[0]);
                // SMT-LIB: `(str.at "" i)` is the empty string for ANY index
                // (every index is out of bounds on the empty string). Decide
                // this even when the index operand is Unknown (e.g. a
                // String-keyed array select), since the result is genuinely ""
                // regardless (#str-at-empty).
                if let EvalValue::String(ref s) = sv {
                    if s.is_empty() {
                        return EvalValue::String(String::new());
                    }
                }
                match (sv, self.evaluate_term(model, args[1])) {
                    (EvalValue::String(s), EvalValue::Rational(i_rat)) => {
                        match str_eval::eval_str_at(&s, &i_rat.to_integer()) {
                            Some(r) => EvalValue::String(r),
                            None => EvalValue::String(String::new()),
                        }
                    }
                    _ => EvalValue::Unknown,
                }
            }
            "str.contains" if args.len() == 2 => {
                match (
                    self.evaluate_term(model, args[0]),
                    self.evaluate_term(model, args[1]),
                ) {
                    (EvalValue::String(s), EvalValue::String(t)) => {
                        EvalValue::Bool(s.contains(&*t))
                    }
                    _ => EvalValue::Unknown,
                }
            }
            "str.prefixof" if args.len() == 2 => {
                match (
                    self.evaluate_term(model, args[0]),
                    self.evaluate_term(model, args[1]),
                ) {
                    (EvalValue::String(s), EvalValue::String(t)) => {
                        EvalValue::Bool(t.starts_with(&*s))
                    }
                    _ => EvalValue::Unknown,
                }
            }
            "str.suffixof" if args.len() == 2 => {
                match (
                    self.evaluate_term(model, args[0]),
                    self.evaluate_term(model, args[1]),
                ) {
                    (EvalValue::String(s), EvalValue::String(t)) => {
                        EvalValue::Bool(t.ends_with(&*s))
                    }
                    _ => EvalValue::Unknown,
                }
            }
            "str.<" if args.len() == 2 => {
                match (
                    self.evaluate_term(model, args[0]),
                    self.evaluate_term(model, args[1]),
                ) {
                    (EvalValue::String(a), EvalValue::String(b)) => EvalValue::Bool(a < b),
                    _ => EvalValue::Unknown,
                }
            }
            "str.<=" if args.len() == 2 => {
                match (
                    self.evaluate_term(model, args[0]),
                    self.evaluate_term(model, args[1]),
                ) {
                    (EvalValue::String(a), EvalValue::String(b)) => EvalValue::Bool(a <= b),
                    _ => EvalValue::Unknown,
                }
            }
            "str.replace" if args.len() == 3 => {
                match (
                    self.evaluate_term(model, args[0]),
                    self.evaluate_term(model, args[1]),
                    self.evaluate_term(model, args[2]),
                ) {
                    (EvalValue::String(s), EvalValue::String(t), EvalValue::String(u)) => {
                        EvalValue::String(str_eval::eval_str_replace(&s, &t, &u))
                    }
                    _ => EvalValue::Unknown,
                }
            }
            "str.replace_all" if args.len() == 3 => {
                match (
                    self.evaluate_term(model, args[0]),
                    self.evaluate_term(model, args[1]),
                    self.evaluate_term(model, args[2]),
                ) {
                    (EvalValue::String(s), EvalValue::String(t), EvalValue::String(u)) => {
                        EvalValue::String(str_eval::eval_str_replace_all(&s, &t, &u))
                    }
                    _ => EvalValue::Unknown,
                }
            }
            "str.indexof" if args.len() == 3 => {
                match (
                    self.evaluate_term(model, args[0]),
                    self.evaluate_term(model, args[1]),
                    self.evaluate_term(model, args[2]),
                ) {
                    (EvalValue::String(s), EvalValue::String(t), EvalValue::Rational(i_rat)) => {
                        match str_eval::eval_str_indexof(&s, &t, &i_rat.to_integer()) {
                            Some(n) => EvalValue::Rational(BigRational::from(n)),
                            None => EvalValue::Rational(BigRational::from(BigInt::from(-1))),
                        }
                    }
                    _ => EvalValue::Unknown,
                }
            }
            "str.to_int" if args.len() == 1 => match self.evaluate_term(model, args[0]) {
                EvalValue::String(s) => {
                    EvalValue::Rational(BigRational::from(str_eval::eval_str_to_int(&s)))
                }
                _ => EvalValue::Unknown,
            },
            "str.from_int" if args.len() == 1 => match self.evaluate_term(model, args[0]) {
                EvalValue::Rational(r) => {
                    EvalValue::String(str_eval::eval_str_from_int(&r.to_integer()))
                }
                _ => EvalValue::Unknown,
            },
            "str.to_code" if args.len() == 1 => match self.evaluate_term(model, args[0]) {
                EvalValue::String(s) => {
                    EvalValue::Rational(BigRational::from(str_eval::eval_str_to_code(&s)))
                }
                _ => EvalValue::Unknown,
            },
            "str.from_code" if args.len() == 1 => match self.evaluate_term(model, args[0]) {
                EvalValue::Rational(r) => {
                    EvalValue::String(str_eval::eval_str_from_code(&r.to_integer()))
                }
                _ => EvalValue::Unknown,
            },
            "str.is_digit" if args.len() == 1 => match self.evaluate_term(model, args[0]) {
                EvalValue::String(s) => EvalValue::Bool(str_eval::eval_str_is_digit(&s)),
                _ => EvalValue::Unknown,
            },
            "str.to_lower" if args.len() == 1 => match self.evaluate_term(model, args[0]) {
                EvalValue::String(s) => EvalValue::String(str_eval::eval_str_to_lower(&s)),
                _ => EvalValue::Unknown,
            },
            "str.to_upper" if args.len() == 1 => match self.evaluate_term(model, args[0]) {
                EvalValue::String(s) => EvalValue::String(str_eval::eval_str_to_upper(&s)),
                _ => EvalValue::Unknown,
            },
            // === Regex string operations (ground evaluation, #6006) ===
            "str.in_re" | "str.in.re" if args.len() == 2 => {
                match self.evaluate_term(model, args[0]) {
                    EvalValue::String(s) => {
                        match ay_strings::ground_eval_in_re(&self.ctx.terms, &s, args[1]) {
                            Some(b) => EvalValue::Bool(b),
                            None => EvalValue::Unknown,
                        }
                    }
                    _ => EvalValue::Unknown,
                }
            }
            "str.replace_re" if args.len() == 3 => {
                match (
                    self.evaluate_term(model, args[0]),
                    self.evaluate_term(model, args[2]),
                ) {
                    (EvalValue::String(s), EvalValue::String(t)) => {
                        match ay_strings::ground_eval_replace_re(&self.ctx.terms, &s, args[1], &t) {
                            Some(result) => EvalValue::String(result),
                            None => EvalValue::Unknown,
                        }
                    }
                    _ => EvalValue::Unknown,
                }
            }
            "str.replace_re_all" if args.len() == 3 => {
                match (
                    self.evaluate_term(model, args[0]),
                    self.evaluate_term(model, args[2]),
                ) {
                    (EvalValue::String(s), EvalValue::String(t)) => {
                        match ay_strings::ground_eval_replace_re_all(
                            &self.ctx.terms,
                            &s,
                            args[1],
                            &t,
                        ) {
                            Some(result) => EvalValue::String(result),
                            None => EvalValue::Unknown,
                        }
                    }
                    _ => EvalValue::Unknown,
                }
            }
            _ => EvalValue::Unknown,
        }
    }
}
