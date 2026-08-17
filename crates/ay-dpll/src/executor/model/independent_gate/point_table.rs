// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Exact reconstruction of printer-authenticated point tables.

use ay_core::kani_compat::DetHashSet as HashSet;
use ay_core::term::{Constant, TermData};
use ay_core::{Sort, TermId};
use num_bigint::BigInt;

use crate::executor::Executor;

/// One reconstructed printer-visible function interpretation: resolved rows
/// in first-match order, excluding the final row whose result is the `else`.
pub(super) struct QuantifiedGateUfInterp {
    pub(super) rows: Vec<(Vec<TermId>, TermId)>,
    pub(super) else_value: TermId,
}

/// The large-table threshold inherited from the original quantified-gate
/// normalization. Small tables retain their existing search structure.
const MIN_EXACT_INT_POINT_TABLE_ROWS: usize = 256;

/// Rebuild one application of an authenticated printer table. The narrow
/// point-table theorem runs before the generic first-match ITE expansion; an
/// unproved shape follows the byte-equivalent generic path.
pub(super) fn rewrite_application(
    executor: &mut Executor,
    actual_args: &[TermId],
    interp: &QuantifiedGateUfInterp,
) -> TermId {
    if let Some(collapsed) = collapse_single_true_int_point_table(executor, actual_args, interp) {
        return collapsed;
    }

    let mut acc = interp.else_value;
    for (row_args, row_result) in interp.rows.iter().rev() {
        let mut conditions = Vec::with_capacity(actual_args.len());
        for (&actual, &expected) in actual_args.iter().zip(row_args.iter()) {
            conditions.push(executor.ctx.terms.mk_eq(actual, expected));
        }
        let condition = if conditions.len() == 1 {
            conditions[0]
        } else {
            executor.ctx.terms.mk_and(conditions)
        };
        acc = executor.ctx.terms.mk_ite(condition, *row_result, acc);
    }
    acc
}

/// Collapse an exact unary `Int -> Bool` table with false default and one true
/// numeral point to that point equality.
///
/// Let the true row be `x = k*`. Every other row is required to use a distinct
/// integer numeral and return false. Thus, when `x = k*`, every earlier false
/// guard is disproved by distinct-numeral arithmetic and the true row fires.
/// When `x != k*`, no row can return true and the default is false. This proves
/// the complete first-match ITE equivalent to `x = k*` without sampling.
///
/// Any duplicate, nonliteral, wrong-sort, multi-true, or datatype-context
/// shape declines to the generic builder. The high-fanout guard preserves the
/// established small-table and datatype certificate routes.
fn collapse_single_true_int_point_table(
    executor: &mut Executor,
    actual_args: &[TermId],
    interp: &QuantifiedGateUfInterp,
) -> Option<TermId> {
    if executor.ctx.datatype_iter().next().is_some()
        || interp.rows.len() < MIN_EXACT_INT_POINT_TABLE_ROWS
        || actual_args.len() != 1
        || executor.ctx.terms.sort(actual_args[0]) != &Sort::Int
        || bool_literal(executor, interp.else_value) != Some(false)
    {
        return None;
    }

    let mut seen_points: HashSet<BigInt> = HashSet::default();
    let mut true_point = None;
    for (row_args, row_result) in &interp.rows {
        let [point_term] = row_args.as_slice() else {
            return None;
        };
        let point = int_literal(executor, *point_term)?;
        if !seen_points.insert(point) {
            return None;
        }
        match bool_literal(executor, *row_result)? {
            false => {}
            true if true_point.is_some() => return None,
            true => true_point = Some(*point_term),
        }
    }

    Some(executor.ctx.terms.mk_eq(actual_args[0], true_point?))
}

fn int_literal(executor: &Executor, term: TermId) -> Option<BigInt> {
    match executor.ctx.terms.get(term) {
        TermData::Const(Constant::Int(value)) => Some(value.clone()),
        _ => None,
    }
}

fn bool_literal(executor: &Executor, term: TermId) -> Option<bool> {
    match executor.ctx.terms.get(term) {
        TermData::Const(Constant::Bool(value)) => Some(*value),
        _ => None,
    }
}

#[cfg(test)]
mod tests {
    use ay_frontend::parse;

    use super::super::QuantifiedGateCheckedGroundDecision;
    use super::*;
    use crate::executor::quantifier_loop::result_mapping::CheckedGroundDecision;

    const TRUE_POINT: i64 = 300;

    fn table_fixture() -> (Executor, Vec<TermId>, QuantifiedGateUfInterp, TermId) {
        let mut executor = Executor::new();
        let actual = executor
            .ctx
            .terms
            .mk_fresh_var("qmg!point-table", Sort::Int);
        let false_term = executor.ctx.terms.false_term();
        let true_term = executor.ctx.terms.true_term();
        let mut rows = Vec::with_capacity((TRUE_POINT + 1) as usize);
        for value in 0..=TRUE_POINT {
            let point = executor.ctx.terms.mk_int(BigInt::from(value));
            let result = if value == TRUE_POINT {
                true_term
            } else {
                false_term
            };
            rows.push((vec![point], result));
        }
        let true_point = executor.ctx.terms.mk_int(BigInt::from(TRUE_POINT));
        (
            executor,
            vec![actual],
            QuantifiedGateUfInterp {
                rows,
                else_value: false_term,
            },
            true_point,
        )
    }

    fn assert_declines(
        label: &str,
        edit: impl FnOnce(&mut Executor, &mut Vec<TermId>, &mut QuantifiedGateUfInterp),
    ) {
        let (mut executor, mut actual_args, mut interp, _) = table_fixture();
        edit(&mut executor, &mut actual_args, &mut interp);
        assert!(
            collapse_single_true_int_point_table(&mut executor, &actual_args, &interp).is_none(),
            "unproved table shape must decline: {label}"
        );
    }

    #[test]
    fn quantified_gate_bool_uf_discharge_is_repeatable() {
        for iteration in 0..16 {
            let (mut executor, actual_args, interp, true_point) = table_fixture();
            let table = rewrite_application(&mut executor, &actual_args, &interp);
            let definition = executor.ctx.terms.mk_eq(actual_args[0], true_point);
            assert_eq!(table, definition, "iteration {iteration}: exact collapse");
            let agreement = executor.ctx.terms.mk_eq(table, definition);
            let obligation = executor.ctx.terms.mk_not(agreement);
            assert_eq!(obligation, executor.ctx.terms.false_term());

            let checked = executor
                .quantified_gate_checked_ground_solve(vec![obligation])
                .expect("literal false must have checked UNSAT authority");
            let QuantifiedGateCheckedGroundDecision { decision, roots } = checked;
            let CheckedGroundDecision::Unsat(proof) = decision else {
                panic!("literal false cannot have a checked SAT model");
            };
            assert!(
                proof.consume(&mut executor, &roots),
                "iteration {iteration}: exact checked authority must remain current"
            );
        }
    }

    #[test]
    fn point_table_collapse_preserves_size_and_datatype_guards() {
        assert_declines("small table", |_, _, interp| {
            let true_row = interp.rows.pop().expect("fixture ends with its true row");
            interp.rows.truncate(MIN_EXACT_INT_POINT_TABLE_ROWS - 2);
            interp.rows.push(true_row);
            assert_eq!(interp.rows.len(), MIN_EXACT_INT_POINT_TABLE_ROWS - 1);
        });
        assert_declines("datatype context", |executor, _, _| {
            let commands = parse("(declare-datatype D ((mkD)))").expect("valid datatype");
            for command in &commands {
                assert!(
                    executor.execute(command).expect("datatype loads").is_none(),
                    "fixture has no query"
                );
            }
            assert!(executor.ctx.datatype_iter().next().is_some());
        });
    }

    #[test]
    fn point_table_collapse_accepts_exact_size_boundary() {
        let (mut executor, actual_args, mut interp, true_point) = table_fixture();
        let true_row = interp.rows.pop().expect("fixture ends with its true row");
        interp.rows.truncate(MIN_EXACT_INT_POINT_TABLE_ROWS - 1);
        interp.rows.push(true_row);
        assert_eq!(interp.rows.len(), MIN_EXACT_INT_POINT_TABLE_ROWS);

        let collapsed = collapse_single_true_int_point_table(&mut executor, &actual_args, &interp);
        let expected = executor.ctx.terms.mk_eq(actual_args[0], true_point);
        assert_eq!(collapsed, Some(expected));
    }

    #[test]
    fn point_table_collapse_rejects_signature_and_literal_ambiguity() {
        assert_declines("no actual argument", |_, actual_args, _| {
            actual_args.clear();
        });
        assert_declines("two actual arguments", |_, actual_args, _| {
            actual_args.push(actual_args[0]);
        });
        assert_declines("non-Int actual", |executor, actual_args, _| {
            actual_args[0] = executor
                .ctx
                .terms
                .mk_fresh_var("qmg!bool-actual", Sort::Bool);
        });
        assert_declines("wrong row arity", |_, _, interp| {
            interp.rows[0].0.clear();
        });
        assert_declines("nonliteral point", |executor, _, interp| {
            interp.rows[0].0[0] = executor
                .ctx
                .terms
                .mk_fresh_var("qmg!symbolic-point", Sort::Int);
        });
        assert_declines("wrong-sort point", |executor, _, interp| {
            interp.rows[0].0[0] = executor.ctx.terms.true_term();
        });
        assert_declines("nonliteral row result", |executor, _, interp| {
            interp.rows[0].1 = executor
                .ctx
                .terms
                .mk_fresh_var("qmg!symbolic-result", Sort::Bool);
        });
        assert_declines("wrong-sort row result", |executor, _, interp| {
            interp.rows[0].1 = executor.ctx.terms.mk_int(BigInt::from(0));
        });
        assert_declines("nonliteral else", |executor, _, interp| {
            interp.else_value = executor
                .ctx
                .terms
                .mk_fresh_var("qmg!symbolic-else", Sort::Bool);
        });
    }

    #[test]
    fn point_table_collapse_rejects_truth_and_point_ambiguity() {
        assert_declines("true default", |executor, _, interp| {
            interp.else_value = executor.ctx.terms.true_term();
        });
        assert_declines("no true row", |executor, _, interp| {
            interp.rows[TRUE_POINT as usize].1 = executor.ctx.terms.false_term();
        });
        assert_declines("multiple true rows", |executor, _, interp| {
            interp.rows[0].1 = executor.ctx.terms.true_term();
        });
        assert_declines("duplicate false point", |_, _, interp| {
            interp.rows[0].0[0] = interp.rows[1].0[0];
        });
        assert_declines("false row at true point", |_, _, interp| {
            interp.rows[0].0[0] = interp.rows[TRUE_POINT as usize].0[0];
        });
    }
}
