// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The read-only sort check for skipped subterms: it vouches that a subterm
//! in a small fragment elaborates, and holds no label, without elaborating
//! it.

use ay_core::kani_compat::DetHashMap as HashMap;
use ay_core::{Sort, TermId};

use crate::command::{ParsedConstant, ParsedSort, Term as ParsedTerm};
use crate::sexp::{PARSE_STACK_RED_ZONE, PARSE_STACK_SIZE};

use super::super::{Context, PublicSort};

/// `sort` when the read-only check compares it exactly.
fn checked_sort(sort: Sort) -> Option<Sort> {
    is_checked_sort(&sort).then_some(sort)
}

fn is_checked_sort(sort: &Sort) -> bool {
    match sort {
        Sort::Bool | Sort::Int | Sort::Real | Sort::BitVec(_) | Sort::Uninterpreted(_) => true,
        Sort::Array(array) => {
            is_checked_sort(&array.index_sort) && is_checked_sort(&array.element_sort)
        }
        _ => false,
    }
}

/// The sort of a bit-vector literal with `digits` digits of `bits` bits each.
fn bitvector_literal_sort(digits: &str, bits: u32) -> Option<Sort> {
    let width = u32::try_from(digits.len()).ok()?.checked_mul(bits)?;
    Context::checked_bitvector_sort(width).ok()
}

/// A negative integer written as one symbol, such as `-1`, which the
/// elaborator reads as a numeral.
fn is_negative_numeral(name: &str) -> bool {
    name.strip_prefix('-')
        .is_some_and(|digits| !digits.is_empty() && digits.bytes().all(|b| b.is_ascii_digit()))
}

/// The sort of a quantified variable, for the sorts the read-only check
/// resolves without declarations.
fn binder_sort(sort: &ParsedSort) -> Option<Sort> {
    match sort {
        ParsedSort::Simple(name) => match name.as_str() {
            "Bool" => Some(Sort::Bool),
            "Int" => Some(Sort::Int),
            "Real" => Some(Sort::Real),
            _ => None,
        },
        _ => None,
    }
}

/// The result sort of a core Boolean, arithmetic, bit-vector or array
/// operator applied to arguments of `sorts`, when the elaborator accepts that
/// application without a coercion. Mixed Int and Real arguments are left to
/// the elaborator.
fn builtin_application_sort(name: &str, sorts: &[Sort]) -> Option<Sort> {
    let count = sorts.len();
    let first = sorts.first()?;
    let all_first = sorts.iter().all(|sort| sort == first);
    let numeric = all_first && matches!(first, Sort::Int | Sort::Real);
    let all_bool = all_first && *first == Sort::Bool;
    let bitvector = all_first && matches!(first, Sort::BitVec(_));
    match name {
        "bvnot" | "bvneg" => (count == 1 && bitvector).then(|| first.clone()),
        "bvadd" | "bvsub" | "bvmul" | "bvand" | "bvor" | "bvxor" | "bvnand" | "bvnor"
        | "bvxnor" | "bvudiv" | "bvurem" | "bvsdiv" | "bvsrem" | "bvsmod" | "bvshl" | "bvlshr"
        | "bvashr" => (count == 2 && bitvector).then(|| first.clone()),
        "bvult" | "bvule" | "bvugt" | "bvuge" | "bvslt" | "bvsle" | "bvsgt" | "bvsge" => {
            (count == 2 && bitvector).then_some(Sort::Bool)
        }
        "select" => match sorts {
            [Sort::Array(array), index] if array.index_sort == *index => {
                Some(array.element_sort.clone())
            }
            _ => None,
        },
        "store" => match sorts {
            [array_sort @ Sort::Array(array), index, element]
                if array.index_sort == *index && array.element_sort == *element =>
            {
                Some(array_sort.clone())
            }
            _ => None,
        },
        "mkbv" if all_bool => u32::try_from(count)
            .ok()
            .and_then(|width| Context::checked_bitvector_sort(width).ok()),
        "concat" => match sorts {
            [Sort::BitVec(high), Sort::BitVec(low)] => high
                .width
                .checked_add(low.width)
                .and_then(|width| Context::checked_bitvector_sort(width).ok()),
            _ => None,
        },
        "not" => (count == 1 && all_bool).then_some(Sort::Bool),
        "and" | "or" | "=>" => (count >= 2 && all_bool).then_some(Sort::Bool),
        "xor" => (count == 2 && all_bool).then_some(Sort::Bool),
        "=" | "distinct" => (count >= 2 && all_first).then_some(Sort::Bool),
        "ite" => {
            (count == 3 && sorts[0] == Sort::Bool && sorts[1] == sorts[2]).then(|| sorts[1].clone())
        }
        "+" | "*" => (count >= 2 && numeric).then(|| first.clone()),
        "-" => numeric.then(|| first.clone()),
        "<" | "<=" | ">" | ">=" => (count >= 2 && numeric).then_some(Sort::Bool),
        "div" | "mod" => (count == 2 && all_first && *first == Sort::Int).then_some(Sort::Int),
        "abs" => (count == 1 && *first == Sort::Int).then_some(Sort::Int),
        _ => None,
    }
}

impl Context {
    /// The sort of a skipped subterm when a read-only check can vouch that
    /// the elaborator accepts it and that it holds no label, `None` when it
    /// cannot. `scope` holds the variables bound inside the subterm, innermost
    /// last.
    pub(super) fn skipped_term_sort(
        &self,
        term: &ParsedTerm,
        env: &HashMap<String, TermId>,
        scope: &mut Vec<(String, Sort)>,
    ) -> Option<Sort> {
        stacker::maybe_grow(PARSE_STACK_RED_ZONE, PARSE_STACK_SIZE, || match term {
            ParsedTerm::Const(constant) => self.checked_constant_sort(constant),
            ParsedTerm::Symbol(name) => self.skipped_symbol_sort(name, env, scope),
            ParsedTerm::App(name, args) if !args.is_empty() => {
                let mut sorts = Vec::with_capacity(args.len());
                for arg in args {
                    sorts.push(self.skipped_term_sort(arg, env, scope)?);
                }
                self.skipped_application_sort(name, &sorts, env, scope)
            }
            ParsedTerm::Let(bindings, body) if !bindings.is_empty() => {
                // Values are read before any of the let's own names is bound.
                let mut values: Vec<(String, Sort)> = Vec::with_capacity(bindings.len());
                for (name, value) in bindings {
                    if values.iter().any(|(bound, _)| bound == name) {
                        return None;
                    }
                    values.push((name.clone(), self.skipped_term_sort(value, env, scope)?));
                }
                self.skipped_body_sort(values, body, env, scope)
            }
            ParsedTerm::Forall(vars, body) | ParsedTerm::Exists(vars, body) if !vars.is_empty() => {
                let mut binders: Vec<(String, Sort)> = Vec::with_capacity(vars.len());
                for (name, sort) in vars {
                    if binders.iter().any(|(bound, _)| bound == name) {
                        return None;
                    }
                    binders.push((name.clone(), binder_sort(sort)?));
                }
                let sort = self.skipped_body_sort(binders, body, env, scope)?;
                (sort == Sort::Bool).then_some(sort)
            }
            _ => None,
        })
    }

    /// The sort of a literal the read-only check vouches for: a Boolean, a
    /// bit-vector literal or a numeral.
    pub(in crate::elaborate) fn checked_constant_sort(
        &self,
        constant: &ParsedConstant,
    ) -> Option<Sort> {
        match constant {
            ParsedConstant::True | ParsedConstant::False => Some(Sort::Bool),
            ParsedConstant::Hexadecimal(digits) => {
                bitvector_literal_sort(digits.trim_start_matches("#x"), 4)
            }
            ParsedConstant::Binary(digits) => {
                bitvector_literal_sort(digits.trim_start_matches("#b"), 1)
            }
            ParsedConstant::Numeral(_) => Some(if self.numeral_as_real {
                Sort::Real
            } else {
                Sort::Int
            }),
            _ => None,
        }
    }

    /// The sort of a quantified variable written as `sort`, when it is Bool,
    /// Int, Real, a bit-vector sort or a declared sort in scope, read without
    /// changing the context.
    pub(in crate::elaborate) fn checked_declared_sort(&self, sort: &ParsedSort) -> Option<Sort> {
        match sort {
            ParsedSort::Simple(name) => match name.as_str() {
                "Bool" | "Int" | "Real" => binder_sort(sort),
                // Theory sorts the elaborator resolves before declarations.
                "bool" | "Proof" | "String" | "RegLan" | "Float16" | "Float32" | "Float64"
                | "Float128" | "RoundingMode" => None,
                other => self.sort_defs.get(other).cloned().and_then(checked_sort),
            },
            ParsedSort::Indexed(name, indices) if name == "BitVec" => match indices.as_slice() {
                [width] => width
                    .as_numeral()
                    .and_then(|width| width.parse().ok())
                    .and_then(|width| Self::checked_bitvector_sort(width).ok()),
                _ => None,
            },
            _ => None,
        }
    }

    /// The sort of `body` with `binders` in scope.
    fn skipped_body_sort(
        &self,
        binders: Vec<(String, Sort)>,
        body: &ParsedTerm,
        env: &HashMap<String, TermId>,
        scope: &mut Vec<(String, Sort)>,
    ) -> Option<Sort> {
        let mark = scope.len();
        scope.extend(binders);
        let sort = self.skipped_term_sort(body, env, scope);
        scope.truncate(mark);
        sort
    }

    /// The sort of a bare symbol, resolved in the elaborator's order: local
    /// variables, labels bound earlier in the command, nullary definitions,
    /// then declarations.
    pub(in crate::elaborate) fn skipped_symbol_sort(
        &self,
        name: &str,
        env: &HashMap<String, TermId>,
        scope: &[(String, Sort)],
    ) -> Option<Sort> {
        if let Some((_, sort)) = scope.iter().rev().find(|(bound, _)| bound == name) {
            return checked_sort(sort.clone());
        }
        if let Some(&id) = env.get(name) {
            return checked_sort(self.terms.sort(id).clone());
        }
        if let Some(sort) = self.pending_label_sort(name) {
            return checked_sort(sort);
        }
        if let Some((params, sort, _)) = self.fun_defs.get(name) {
            return if params.is_empty() {
                checked_sort(sort.clone())
            } else {
                None
            };
        }
        if self.internal_symbols.contains(name) || self.has_user_polymorphic_declaration(name) {
            return None;
        }
        let Some(info) = self.resolve_bare_declared_symbol(name).ok()? else {
            return (is_negative_numeral(name) && !self.numeral_as_real).then_some(Sort::Int);
        };
        if info.public_sort != PublicSort::from_engine(&info.sort) {
            return None;
        }
        checked_sort(info.sort)
    }

    /// The sort of an application of `name` to arguments of `sorts`.
    pub(in crate::elaborate) fn skipped_application_sort(
        &self,
        name: &str,
        sorts: &[Sort],
        env: &HashMap<String, TermId>,
        scope: &[(String, Sort)],
    ) -> Option<Sort> {
        // A variable or a label cannot be applied.
        if scope.iter().any(|(bound, _)| bound == name)
            || env.contains_key(name)
            || self.pending_label_sort(name).is_some()
        {
            return None;
        }
        if self.internal_symbols.contains(name) || self.has_user_polymorphic_declaration(name) {
            return None;
        }
        if !self.has_symbol_binding(name) {
            return builtin_application_sort(name, sorts);
        }
        if let Some((params, result, _)) = self.fun_defs.get(name) {
            let exact = params.len() == sorts.len()
                && params
                    .iter()
                    .zip(sorts)
                    .all(|((_, param), sort)| param == sort);
            return if exact {
                checked_sort(result.clone())
            } else {
                None
            };
        }
        // One declaration of exactly these argument sorts: a declared
        // function, or a member of a declared datatype.
        if self.overloaded_symbols.contains_key(name) {
            return None;
        }
        let info = self.symbols.get(name)?;
        let plain_signature = info.public_sort == PublicSort::from_engine(&info.sort)
            && info.public_arg_sorts.len() == info.arg_sorts.len()
            && info
                .public_arg_sorts
                .iter()
                .zip(&info.arg_sorts)
                .all(|(public, engine)| *public == PublicSort::from_engine(engine));
        if !plain_signature || info.arg_sorts.as_slice() != sorts {
            return None;
        }
        checked_sort(info.sort.clone())
    }
}
