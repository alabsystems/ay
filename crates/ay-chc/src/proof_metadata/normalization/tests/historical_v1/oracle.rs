// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Frozen pre-callback identity implementation, used only as a byte oracle.
#![cfg(test)]

use crate::proof_metadata::{json_string, sha256_hex, NORMALIZED_CHC_INPUT_SCHEMA};
use crate::{ChcExpr, ChcOp, ChcProblem, ChcSort, ClauseHead, HornClause, PredicateId};
use sha2::{Digest, Sha256};
use std::collections::BTreeMap;

/// Return deterministic normalized CHC/PDR input text for replay binding.
pub(super) fn normalized_chc_input(problem: &ChcProblem) -> String {
    let pred_names = canonical_predicate_names(problem);
    let mut out = String::new();
    out.push_str(NORMALIZED_CHC_INPUT_SCHEMA);
    out.push('\n');
    out.push_str(&format!(
        "fixedpoint={}\n",
        if problem.is_fixedpoint_format() {
            "true"
        } else {
            "false"
        }
    ));

    out.push_str("datatypes\n");
    for (name, constructors) in sorted_datatypes(problem) {
        let ctor_parts: Vec<_> = constructors
            .iter()
            .map(|(ctor, selectors)| {
                let selector_parts: Vec<_> = selectors
                    .iter()
                    .map(|(selector, sort)| {
                        format!("{}:{}", json_string(selector), normalized_sort(sort))
                    })
                    .collect();
                format!("{}({})", json_string(ctor), selector_parts.join(","))
            })
            .collect();
        out.push_str(&format!(
            "datatype {}={}\n",
            json_string(&name),
            ctor_parts.join("|")
        ));
    }

    out.push_str("actions\n");
    let mut actions: Vec<_> = problem
        .action_names()
        .iter()
        .map(|name| json_string(name))
        .collect();
    actions.sort();
    for action in actions {
        out.push_str(&format!("action {action}\n"));
    }

    out.push_str("predicates\n");
    let mut predicates: Vec<_> = problem
        .predicates()
        .iter()
        .map(|predicate| {
            let canonical = pred_names
                .get(&predicate.id.index())
                .cloned()
                .unwrap_or_else(|| fallback_predicate_name(predicate.id));
            let sorts: Vec<_> = predicate.arg_sorts.iter().map(normalized_sort).collect();
            format!(
                "predicate {canonical} name={} args=[{}]",
                json_string(&predicate.name),
                sorts.join(",")
            )
        })
        .collect();
    predicates.sort();
    for predicate in predicates {
        out.push_str(&predicate);
        out.push('\n');
    }

    out.push_str("clauses\n");
    let mut clauses: Vec<_> = problem
        .clauses()
        .iter()
        .map(|clause| normalized_clause(problem, clause, &pred_names))
        .collect();
    clauses.sort();
    for clause in clauses {
        out.push_str(&clause);
        out.push('\n');
    }

    out
}

/// Return SHA-256 of [`normalized_chc_input`], lowercase hex.
pub(super) fn normalized_chc_input_sha256(problem: &ChcProblem) -> String {
    sha256_hex(normalized_chc_input(problem).as_bytes())
}

/// Return an order-sensitive SHA-256 overlay for source-clause indices.
///
/// [`normalized_chc_input`] intentionally sorts clauses and each clause's body
/// predicate applications because its identity is semantic. Ground derivations
/// instead name clauses and premises positionally, so their durable artifact
/// additionally binds this indexed, position-preserving view.
pub(super) fn ordered_chc_clause_sequence_sha256(problem: &ChcProblem) -> String {
    let pred_names = canonical_predicate_names(problem);
    let mut digest = Sha256::new();
    digest.update(b"ay.chc-source-clause-sequence/v1\0");
    digest.update((problem.clauses().len() as u64).to_le_bytes());

    fn update_field(digest: &mut Sha256, value: &str) {
        digest.update((value.len() as u64).to_le_bytes());
        digest.update(value.as_bytes());
    }

    for (clause_index, clause) in problem.clauses().iter().enumerate() {
        digest.update((clause_index as u64).to_le_bytes());
        match clause.source_query_ordinal {
            Some(ordinal) => {
                digest.update([1]);
                digest.update((ordinal as u64).to_le_bytes());
            }
            None => digest.update([0]),
        }
        match clause
            .action_id
            .and_then(|action| problem.action_name(action))
        {
            Some(action) => {
                digest.update([1]);
                update_field(&mut digest, action);
            }
            None => digest.update([0]),
        }
        digest.update((clause.body.predicates.len() as u64).to_le_bytes());
        for (predicate, arguments) in &clause.body.predicates {
            update_field(
                &mut digest,
                &normalized_predicate_app(*predicate, arguments, &pred_names),
            );
        }
        let constraint = clause
            .body
            .constraint
            .as_ref()
            .map(|expression| normalized_expr(expression, &pred_names))
            .unwrap_or_else(|| "true".to_string());
        let head = match &clause.head {
            ClauseHead::False => "false".to_string(),
            ClauseHead::Predicate(predicate, arguments) => {
                normalized_predicate_app(*predicate, arguments, &pred_names)
            }
        };
        update_field(&mut digest, &constraint);
        update_field(&mut digest, &head);
    }

    let digest = digest.finalize();
    let mut hex = String::with_capacity(digest.len() * 2);
    const DIGITS: &[u8; 16] = b"0123456789abcdef";
    for byte in digest {
        hex.push(DIGITS[(byte >> 4) as usize] as char);
        hex.push(DIGITS[(byte & 0x0f) as usize] as char);
    }
    hex
}

fn canonical_predicate_names(problem: &ChcProblem) -> BTreeMap<usize, String> {
    let mut signatures: Vec<_> = problem
        .predicates()
        .iter()
        .map(|predicate| {
            let sorts: Vec<_> = predicate.arg_sorts.iter().map(normalized_sort).collect();
            (
                json_string(&predicate.name),
                sorts.join(","),
                predicate.id.index(),
            )
        })
        .collect();
    signatures.sort();

    signatures
        .into_iter()
        .enumerate()
        .map(|(idx, (_, _, original_idx))| (original_idx, format!("p{idx}")))
        .collect()
}

fn sorted_datatypes(problem: &ChcProblem) -> Vec<(String, Vec<(String, Vec<(String, ChcSort)>)>)> {
    let mut datatypes: Vec<_> = problem
        .datatype_defs()
        .iter()
        .map(|(name, constructors)| (name.clone(), constructors.clone()))
        .collect();
    datatypes.sort_by(|(lhs, _), (rhs, _)| lhs.cmp(rhs));
    datatypes
}

fn normalized_clause(
    problem: &ChcProblem,
    clause: &HornClause,
    pred_names: &BTreeMap<usize, String>,
) -> String {
    let mut body_predicates: Vec<_> = clause
        .body
        .predicates
        .iter()
        .map(|(pred, args)| normalized_predicate_app(*pred, args, pred_names))
        .collect();
    body_predicates.sort();

    let constraint = clause
        .body
        .constraint
        .as_ref()
        .map(|expr| normalized_expr(expr, pred_names))
        .unwrap_or_else(|| "true".to_string());
    let head = match &clause.head {
        ClauseHead::False => "false".to_string(),
        ClauseHead::Predicate(pred, args) => normalized_predicate_app(*pred, args, pred_names),
    };
    let action = clause
        .action_id
        .and_then(|action| problem.action_name(action).map(json_string))
        .unwrap_or_else(|| "none".to_string());

    format!(
        "clause action={action} body=[{}] constraint={constraint} head={head}",
        body_predicates.join(",")
    )
}

fn normalized_predicate_app(
    pred: PredicateId,
    args: &[ChcExpr],
    pred_names: &BTreeMap<usize, String>,
) -> String {
    let pred = pred_names
        .get(&pred.index())
        .cloned()
        .unwrap_or_else(|| fallback_predicate_name(pred));
    let args: Vec<_> = args
        .iter()
        .map(|arg| normalized_expr(arg, pred_names))
        .collect();
    format!("{pred}({})", args.join(","))
}

fn normalized_expr(expr: &ChcExpr, pred_names: &BTreeMap<usize, String>) -> String {
    match expr {
        ChcExpr::ArrayLambda(_) => {
            panic!("array lambda is outside the frozen historical oracle grammar")
        }
        ChcExpr::Bool(value) => format!("bool:{value}"),
        ChcExpr::Int(value) => format!("int:{value}"),
        ChcExpr::Real(numer, denom) => format!("real:{numer}/{denom}"),
        ChcExpr::BitVec(value, width) => format!("bv{width}:{value}"),
        ChcExpr::Var(var) => {
            format!(
                "var:{}:{}",
                json_string(&var.name),
                normalized_sort(&var.sort)
            )
        }
        ChcExpr::Op(op, args) => {
            let mut children: Vec<_> = args
                .iter()
                .map(|arg| normalized_expr(arg, pred_names))
                .collect();
            if is_commutative_op(*op) {
                children.sort();
            }
            format!("op:{op:?}({})", children.join(","))
        }
        ChcExpr::PredicateApp(name, pred, args) => {
            let pred = pred_names
                .get(&pred.index())
                .cloned()
                .unwrap_or_else(|| fallback_predicate_name(*pred));
            let args: Vec<_> = args
                .iter()
                .map(|arg| normalized_expr(arg, pred_names))
                .collect();
            format!("pred-expr:{pred}:{}({})", json_string(name), args.join(","))
        }
        ChcExpr::FuncApp(name, sort, args) => {
            let args: Vec<_> = args
                .iter()
                .map(|arg| normalized_expr(arg, pred_names))
                .collect();
            format!(
                "func:{}:{}({})",
                json_string(name),
                normalized_sort(sort),
                args.join(",")
            )
        }
        ChcExpr::ConstArrayMarker(sort) => {
            format!("const-array-marker:{}", normalized_sort(sort))
        }
        ChcExpr::IsTesterMarker(name) => format!("is-tester:{}", json_string(name)),
        ChcExpr::ConstArray(key_sort, value) => format!(
            "const-array:{}:{}",
            normalized_sort(key_sort),
            normalized_expr(value, pred_names)
        ),
    }
}

fn is_commutative_op(op: ChcOp) -> bool {
    matches!(
        op,
        ChcOp::And
            | ChcOp::Or
            | ChcOp::Iff
            | ChcOp::Add
            | ChcOp::Mul
            | ChcOp::Eq
            | ChcOp::Ne
            | ChcOp::BvAdd
            | ChcOp::BvMul
            | ChcOp::BvAnd
            | ChcOp::BvOr
            | ChcOp::BvXor
            | ChcOp::BvNand
            | ChcOp::BvNor
            | ChcOp::BvXnor
    )
}

fn normalized_sort(sort: &ChcSort) -> String {
    match sort {
        ChcSort::Bool => "Bool".to_string(),
        ChcSort::Int => "Int".to_string(),
        ChcSort::Real => "Real".to_string(),
        ChcSort::BitVec(width) => format!("BitVec({width})"),
        ChcSort::Array(key, value) => {
            format!("Array({},{})", normalized_sort(key), normalized_sort(value))
        }
        ChcSort::Uninterpreted(name) => format!("Uninterpreted({})", json_string(name)),
        ChcSort::Datatype { name, constructors } => {
            let ctor_parts: Vec<_> = constructors
                .iter()
                .map(|constructor| {
                    let selectors: Vec<_> = constructor
                        .selectors
                        .iter()
                        .map(|selector| {
                            format!(
                                "{}:{}",
                                json_string(&selector.name),
                                normalized_sort(&selector.sort)
                            )
                        })
                        .collect();
                    format!(
                        "{}({})",
                        json_string(&constructor.name),
                        selectors.join(",")
                    )
                })
                .collect();
            format!("Datatype({};{})", json_string(name), ctor_parts.join("|"))
        }
    }
}

fn fallback_predicate_name(pred: PredicateId) -> String {
    format!("p?{}", pred.index())
}
