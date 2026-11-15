// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![cfg(test)]

use super::*;

pub(super) fn array(at_false: bool, at_true: bool) -> SmtValue {
    SmtValue::ArrayMap {
        default: Box::new(SmtValue::Bool(false)),
        entries: vec![
            (SmtValue::Bool(false), SmtValue::Bool(at_false)),
            (SmtValue::Bool(true), SmtValue::Bool(at_true)),
        ],
    }
}

pub(super) fn apply(interpretation: &PredicateInterpretation, values: &[SmtValue]) -> bool {
    assert_eq!(interpretation.vars.len(), values.len());
    // Instantiate by POSITION onto independent call symbols, like the model
    // consumer. Binding source names directly would hide repeated-formal bugs.
    let mut model = FxHashMap::default();
    let substitutions: Vec<_> = interpretation
        .vars
        .iter()
        .zip(values)
        .enumerate()
        .map(|(index, (formal, value))| {
            let actual = ChcVar::new(format!("probe_arg{index}"), formal.sort.clone());
            model.insert(actual.name.clone(), value.clone());
            (formal.clone(), ChcExpr::var(actual))
        })
        .collect();
    let instantiated = interpretation.formula.substitute(&substitutions);
    match crate::expr::evaluate_expr(&instantiated, &model) {
        Some(SmtValue::Bool(value)) => value,
        other => panic!("closed finite interpretation must evaluate exactly: {other:?}"),
    }
}
