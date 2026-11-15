// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Validation of a SAT model against the well-formedness of the free symbols
//! its goal reaches (see the parent module).
//!
//! A value is checked exactly against its public sort: an engine `Int` of a
//! `Char` or finite-domain sort must lie in the sort's range, through array
//! defaults and stores, sequence elements and datatype fields (a recursive
//! datatype's own values included). A value the snapshot cannot show whole
//! (an unparsed array, a symbolic function else) is undecided, never valid.

use ay_dpll::api::{DatatypeSort, Model, ModelValue, Sort};
use num_bigint::BigInt;
use num_traits::Signed;

use super::{mentions_bounded_scalar, WfCheck, WfObligations};
use crate::z3_compat::model_params::{model_func_interps, FuncInterp};
use crate::z3_compat::{bounded_sort_hi, Z3Context};

/// Values nested deeper than this are undecided.
const MAX_VALUE_DEPTH: u32 = 64;

/// Whether a model value is a value of its public sort.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Wf {
    Valid,
    Invalid,
    Undecided,
}

impl Wf {
    fn and(self, other: Wf) -> Wf {
        match (self, other) {
            (Wf::Invalid, _) | (_, Wf::Invalid) => Wf::Invalid,
            (Wf::Undecided, _) | (_, Wf::Undecided) => Wf::Undecided,
            _ => Wf::Valid,
        }
    }
}

/// What a SAT answer does once its model is validated.
#[derive(Debug, PartialEq, Eq)]
pub(crate) enum WfVerdict {
    /// Every reached symbol's value is a value of its public sort: the model
    /// is a model of the goal and of every guard, so the SAT stands.
    Accept,
    /// A value is not, or cannot be shown to be, a value of its sort, and the
    /// check left quantified guards out: re-check with every guard asserted.
    Retry(String),
    /// A value is not a value of its sort and no re-check can assert a guard
    /// that would change that: the goal is not decided.
    Refuse(String),
}

fn in_range(value: &BigInt, hi: i64) -> bool {
    !value.is_negative() && *value <= BigInt::from(hi)
}

/// Whether `value` is a value of the public sort `sort`. `enclosing` holds
/// the datatypes being descended, which a recursive field names by
/// `Uninterpreted(name)`.
fn value_wf<'a>(
    value: &ModelValue,
    sort: &'a Sort,
    enclosing: &mut Vec<&'a DatatypeSort>,
    depth: u32,
) -> Wf {
    if depth > MAX_VALUE_DEPTH {
        return Wf::Undecided;
    }
    if let Some(hi) = bounded_sort_hi(sort) {
        return match value {
            ModelValue::Int(code) if in_range(code, hi) => Wf::Valid,
            ModelValue::Int(_) => Wf::Invalid,
            _ => Wf::Undecided,
        };
    }
    if let Sort::Uninterpreted(name) = sort {
        if let Some(&dt) = enclosing.iter().rev().find(|dt| dt.name == *name) {
            return datatype_value_wf(value, dt, enclosing, depth);
        }
    }
    if !mentions_bounded_scalar(sort, &mut std::collections::HashSet::new()) {
        return Wf::Valid;
    }
    match (sort, value) {
        (Sort::Array(array), ModelValue::Array { default, stores }) => stores.iter().fold(
            value_wf(default, &array.element_sort, enclosing, depth + 1),
            |wf, (_, stored)| wf.and(value_wf(stored, &array.element_sort, enclosing, depth + 1)),
        ),
        (Sort::Seq(element), ModelValue::Seq(items)) => items.iter().fold(Wf::Valid, |wf, item| {
            wf.and(value_wf(item, element, enclosing, depth + 1))
        }),
        (Sort::Seq(element), ModelValue::String(text)) if element.is_char() => {
            let max = bounded_sort_hi(element).unwrap_or(0);
            if text.chars().all(|ch| i64::from(u32::from(ch)) <= max) {
                Wf::Valid
            } else {
                Wf::Invalid
            }
        }
        (Sort::Datatype(dt), _) => datatype_value_wf(value, dt, enclosing, depth),
        _ => Wf::Undecided,
    }
}

fn datatype_value_wf<'a>(
    value: &ModelValue,
    dt: &'a DatatypeSort,
    enclosing: &mut Vec<&'a DatatypeSort>,
    depth: u32,
) -> Wf {
    let ModelValue::Datatype { constructor, args } = value else {
        return Wf::Undecided;
    };
    let Some(ctor) = dt
        .constructors
        .iter()
        .find(|ctor| ctor.name == *constructor)
    else {
        return Wf::Undecided;
    };
    if ctor.fields.len() != args.len() {
        return Wf::Undecided;
    }
    enclosing.push(dt);
    let wf = ctor
        .fields
        .iter()
        .zip(args)
        .fold(Wf::Valid, |wf, (field, arg)| {
            wf.and(value_wf(arg, &field.sort, enclosing, depth + 1))
        });
    enclosing.pop();
    wf
}

/// Whether the model's value of `check`'s symbol is a value of its sort. A
/// symbol the model leaves out is completed with its sort's default (`0`, a
/// constant array of it, the first constructor), which is one.
fn symbol_wf(
    ctx: &mut Z3Context,
    check: &WfCheck,
    model: Option<&Model>,
    text: Option<&str>,
    interps: &mut Option<Vec<FuncInterp>>,
) -> Wf {
    let Some(model) = model else {
        return Wf::Undecided;
    };
    if !check.function {
        return match model.value_by_name(&check.name) {
            Some(value) => value_wf(&value, &check.sort, &mut Vec::new(), 0),
            None => Wf::Valid,
        };
    }
    let Some(text) = text else {
        return Wf::Undecided;
    };
    let interps = interps.get_or_insert_with(|| model_func_interps(&mut ctx.solver, text));
    let Some(interp) = interps.iter().find(|interp| interp.name == check.name) else {
        return Wf::Valid;
    };
    if interp.else_term.is_some() {
        return Wf::Undecided;
    }
    interp.rows.iter().fold(
        value_wf(&interp.else_value, &check.sort, &mut Vec::new(), 0),
        |wf, (_, value)| wf.and(value_wf(value, &check.sort, &mut Vec::new(), 0)),
    )
}

/// Validate a SAT model of a goal with `obligations` (see [`WfVerdict`]).
/// `guards_asserted` says whether the check asserted the quantified guards,
/// which makes the engine's own model satisfy them, and `may_recheck`
/// whether the goal may be checked again with them.
///
/// A symbol without a guard (only a goal without a binder reaches one, see
/// `wf_obligations`) whose value cannot be decided keeps the policy it had
/// before validation existed: the published-model backstop decides.
pub(crate) fn validate_wf_model(
    ctx: &mut Z3Context,
    obligations: &WfObligations,
    model: Option<&Model>,
    text: Option<&str>,
    guards_asserted: bool,
    may_recheck: bool,
) -> WfVerdict {
    let retry = may_recheck && !guards_asserted && !obligations.lazy.is_empty();
    let mut interps = None;
    for check in &obligations.checks {
        if check.guarded && guards_asserted {
            continue;
        }
        let wf = symbol_wf(ctx, check, model, text, &mut interps);
        let what = match wf {
            Wf::Valid => continue,
            Wf::Undecided if !check.guarded => continue,
            Wf::Invalid => "is not a value of",
            Wf::Undecided => "cannot be shown to be a value of",
        };
        let shown = crate::z3_compat::ffi_surface_text(ctx, &check.name);
        let sort = crate::z3_compat::render_public_sort(ctx, &check.sort);
        let reason = format!("the model's value of {shown} {what} its sort {sort}");
        if retry {
            return WfVerdict::Retry(reason);
        }
        let why = if check.guarded {
            String::new()
        } else {
            format!(" (it has no well-formedness guard: {})", check.reason)
        };
        return WfVerdict::Refuse(format!(
            "{reason}{why}; sat is not published with a model that is not one of the public \
             sorts"
        ));
    }
    WfVerdict::Accept
}

#[cfg(test)]
mod tests {
    use super::*;
    use ay_dpll::api::{DatatypeConstructor, DatatypeField};

    fn int(n: i64) -> ModelValue {
        ModelValue::Int(BigInt::from(n))
    }

    #[test]
    fn char_and_finite_domain_values_are_checked_against_their_range() {
        let fd = Sort::FiniteDomain("S".to_string(), 3);
        assert_eq!(
            value_wf(&int(196607), &Sort::Char, &mut Vec::new(), 0),
            Wf::Valid
        );
        assert_eq!(
            value_wf(&int(196608), &Sort::Char, &mut Vec::new(), 0),
            Wf::Invalid
        );
        assert_eq!(
            value_wf(&int(-1), &Sort::Char, &mut Vec::new(), 0),
            Wf::Invalid
        );
        assert_eq!(value_wf(&int(2), &fd, &mut Vec::new(), 0), Wf::Valid);
        assert_eq!(value_wf(&int(3), &fd, &mut Vec::new(), 0), Wf::Invalid);
        let unknown = ModelValue::Unknown;
        assert_eq!(
            value_wf(&unknown, &Sort::Char, &mut Vec::new(), 0),
            Wf::Undecided
        );
    }

    #[test]
    fn array_defaults_and_stores_are_checked() {
        let sort = Sort::array(Sort::Int, Sort::Char);
        let array = |default: i64, stored: i64| ModelValue::Array {
            default: Box::new(int(default)),
            stores: vec![(int(3), int(stored))],
        };
        assert_eq!(
            value_wf(&array(0, 65), &sort, &mut Vec::new(), 0),
            Wf::Valid
        );
        assert_eq!(
            value_wf(&array(0, 196608), &sort, &mut Vec::new(), 0),
            Wf::Invalid
        );
        assert_eq!(
            value_wf(&array(-5, 65), &sort, &mut Vec::new(), 0),
            Wf::Invalid
        );
        let blob = ModelValue::ArraySmtlib("(_ as-array f)".to_string());
        assert_eq!(value_wf(&blob, &sort, &mut Vec::new(), 0), Wf::Undecided);
    }

    #[test]
    fn recursive_datatype_values_are_checked_through_their_self_references() {
        // List of Char: nil | cons(head: Char, tail: List).
        let list = DatatypeSort::new(
            "L",
            vec![
                DatatypeConstructor::new("nil", vec![]),
                DatatypeConstructor::new(
                    "cons",
                    vec![
                        DatatypeField::new("head", Sort::Char),
                        DatatypeField::new("tail", Sort::Uninterpreted("L".to_string())),
                    ],
                ),
            ],
        );
        let sort = Sort::Datatype(list);
        let nil = ModelValue::Datatype {
            constructor: "nil".to_string(),
            args: vec![],
        };
        let cons = |head: i64, tail: ModelValue| ModelValue::Datatype {
            constructor: "cons".to_string(),
            args: vec![int(head), tail],
        };
        let good = cons(97, cons(98, nil.clone()));
        let bad = cons(97, cons(196608, nil));
        assert_eq!(value_wf(&good, &sort, &mut Vec::new(), 0), Wf::Valid);
        assert_eq!(value_wf(&bad, &sort, &mut Vec::new(), 0), Wf::Invalid);
    }

    #[test]
    fn values_of_sorts_without_bounded_components_are_valid() {
        let value = ModelValue::Real(num_rational::BigRational::from_integer(BigInt::from(7)));
        assert_eq!(value_wf(&value, &Sort::Real, &mut Vec::new(), 0), Wf::Valid);
    }
}
