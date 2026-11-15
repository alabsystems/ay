// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Keep extracted scalar UF interpretations fixed during scalar cosmetics.

#[cfg(test)]
mod promotion_tests;

use ay_core::{Sort, TermId};

use super::super::{EvalValue, Model};
use crate::executor::Executor;

type RawRows = Vec<(Vec<String>, String)>;

/// The exact first-match row list and else value the printer publishes.
#[derive(Debug, Clone)]
pub(in crate::executor) struct MaterializedScalarFunction {
    raw_rows: RawRows,
    declaration_id: ay_frontend::DeclarationId,
    arg_sorts: Vec<Sort>,
    result_sort: Sort,
    rows: Vec<(Vec<EvalValue>, EvalValue)>,
}

impl MaterializedScalarFunction {
    /// Refuse stale data if another phase changed the table or its signature.
    pub(in crate::executor::model) fn evaluate(
        &self,
        exec: &Executor,
        model: &Model,
        name: &str,
        args: &[TermId],
        result_sort: &Sort,
    ) -> Option<EvalValue> {
        let current = model.euf_model.as_ref()?.function_tables.get(name)?;
        if *current != self.raw_rows
            || *result_sort != self.result_sort
            || args.len() != self.arg_sorts.len()
            || args
                .iter()
                .zip(&self.arg_sorts)
                .any(|(&term, sort)| exec.ctx.terms.sort(term) != sort)
        {
            return None;
        }
        let values: Vec<_> = args
            .iter()
            .map(|&term| exec.evaluate_term(model, term))
            .collect();
        if values
            .iter()
            .zip(&self.arg_sorts)
            .any(|(value, sort)| !value_has_sort(value, sort))
        {
            return None;
        }
        self.rows
            .iter()
            .find(|(point, _)| *point == values)
            .or_else(|| self.rows.last())
            .map(|(_, value)| value.clone())
    }
}

fn scalar_sort(sort: &Sort) -> bool {
    matches!(sort, Sort::Bool | Sort::Int | Sort::Real | Sort::BitVec(_))
}

fn value_has_sort(value: &EvalValue, sort: &Sort) -> bool {
    match (sort, value) {
        (Sort::Bool, EvalValue::Bool(_)) | (Sort::Real, EvalValue::Rational(_)) => true,
        (Sort::Int, EvalValue::Rational(number)) => number.is_integer(),
        (Sort::BitVec(sort), EvalValue::BitVec { value, width }) => {
            sort.width == *width
                && *width > 0
                && value.sign() != num_bigint::Sign::Minus
                && value.bits() <= u64::from(*width)
        }
        _ => false,
    }
}

fn read_rows(
    exec: &Executor,
    arg_sorts: &[Sort],
    result_sort: &Sort,
    rows: &[(Vec<String>, String)],
) -> Option<Vec<(Vec<EvalValue>, EvalValue)>> {
    let read = |raw: &str, sort: &Sort| {
        let value = exec.parse_model_value_string(raw, &Some(sort.clone()));
        value_has_sort(&value, sort).then_some(value)
    };
    rows.iter()
        .map(|(args, result)| {
            let point = args
                .iter()
                .zip(arg_sorts)
                .map(|(raw, sort)| read(raw, sort))
                .collect::<Option<Vec<_>>>()?;
            Some((point, read(result, result_sort)?))
        })
        .collect()
}

impl Executor {
    /// Refuse stale owned data before any public absent-value recovery.
    pub(in crate::executor) fn materialized_scalar_functions_current(&self, model: &Model) -> bool {
        model
            .materialized_scalar_functions
            .iter()
            .all(|(identity, function)| {
                model
                    .euf_model
                    .as_ref()
                    .and_then(|euf| euf.function_tables.get(identity))
                    == Some(&function.raw_rows)
                    && self.ctx.symbol_iter().any(|(surface, info)| {
                        self.ctx.symbol_identity_name(surface, info) == identity
                            && info.declaration_id() == &function.declaration_id
                            && info.arg_sorts == function.arg_sorts
                            && info.sort == function.result_sort
                    })
            })
    }

    /// Resolve table placeholders before changing scalar values. New argument
    /// points then read the same fixed, printable total functions. Unresolved
    /// or unsupported rows decline cosmetics without changing the model.
    pub(super) fn materialize_scalar_function_rows(&mut self) -> bool {
        if self.original_problem_had_quantifiers {
            return false;
        }
        let Some(model) = self.last_model.as_ref() else {
            return true;
        };
        let Some(euf) = model.euf_model.as_ref() else {
            return true;
        };
        let mut updates = Vec::new();
        for (surface, info) in self.ctx.symbol_iter() {
            if self.solve_deadline.expired() {
                return false;
            }
            let identity = self.ctx.symbol_identity_name(surface, info);
            let Some(rows) = euf.function_tables.get(identity) else {
                continue;
            };
            if rows.is_empty()
                || self.ctx.is_internal_symbol(surface)
                || self.ctx.is_defined_fun(surface)
            {
                continue;
            }
            if info.arg_sorts.is_empty()
                || !info.arg_sorts.iter().all(scalar_sort)
                || !scalar_sort(&info.sort)
            {
                return false;
            }
            let mut fixed = Vec::with_capacity(rows.len());
            for (args, result) in rows {
                if self.solve_deadline.expired() || args.len() != info.arg_sorts.len() {
                    return false;
                }
                let args = args
                    .iter()
                    .zip(&info.arg_sorts)
                    .map(|(raw, sort)| self.resolve_table_value(raw, sort, model))
                    .collect::<Result<Vec<_>, _>>();
                let result = self.resolve_table_value(result, &info.sort, model);
                let (Ok(args), Ok(result)) = (args, result) else {
                    return false;
                };
                fixed.push((args, result));
            }
            let Ok(printed) =
                self.printed_uf_table_rows(identity, &info.arg_sorts, &info.sort, &fixed, model)
            else {
                return false;
            };
            let Some(typed) = read_rows(self, &info.arg_sorts, &info.sort, &printed) else {
                return false;
            };
            updates.push((
                identity.to_string(),
                MaterializedScalarFunction {
                    raw_rows: fixed,
                    declaration_id: info.declaration_id().clone(),
                    arg_sorts: info.arg_sorts.clone(),
                    result_sort: info.sort.clone(),
                    rows: typed,
                },
            ));
        }
        if updates.is_empty() {
            return true;
        }
        if let Some(model) = self.last_model.as_mut() {
            if let Some(euf) = model.euf_model.as_mut() {
                for (identity, function) in updates {
                    // Raw row order and source-term alignment are unchanged.
                    euf.function_tables
                        .insert(identity.clone(), function.raw_rows.clone());
                    model
                        .materialized_scalar_functions
                        .insert(identity, function);
                }
            }
        }
        super::super::eval_memo_clear();
        true
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::executor_types::SolveResult;

    fn executor_with_materialized_function() -> Executor {
        let mut executor = Executor::new();
        executor.set_timeout(Some(std::time::Duration::from_secs(10)));
        executor.set_resource_limit(Some(400_000));
        executor.counterexample_style = crate::CounterexampleStyle::Readable;
        let commands = ay_frontend::parse(
            "(set-option :produce-models true) (declare-const x Int)
             (declare-fun f (Int) Int)
             (assert (= (f x) 1)) (assert (= (f 0) 0)) (check-sat)",
        )
        .expect("script parses");
        let outputs = executor.execute_all(&commands).expect("script executes");
        assert_eq!(outputs.last().map(String::as_str), Some("sat"));
        assert!(executor.materialize_scalar_function_rows());
        assert!(!executor
            .last_model
            .as_ref()
            .expect("model")
            .materialized_scalar_functions
            .is_empty());
        executor
    }

    fn assert_public_reads_refuse_stale(executor: &mut Executor) {
        assert!(executor
            .model()
            .contains("materialized scalar function model is stale"));
        let commands = ay_frontend::parse("(get-value ((f x)))").expect("getter parses");
        let outputs = executor.execute_all(&commands).expect("getter executes");
        assert!(outputs
            .last()
            .expect("getter response")
            .contains("materialized scalar function model is stale"));
    }

    #[test]
    fn replaced_rows_refuse_public_recovery_from_assertions() {
        let mut executor = executor_with_materialized_function();
        let model = executor.last_model.as_mut().expect("model");
        model
            .euf_model
            .as_mut()
            .expect("EUF model")
            .function_tables
            .get_mut("f")
            .expect("f table")[0]
            .1 = "7".to_string();
        assert_public_reads_refuse_stale(&mut executor);
    }

    #[test]
    fn cloned_function_metadata_rejects_same_signature_redeclaration() {
        let mut executor = executor_with_materialized_function();
        let model = executor.last_model.clone();
        let commands = ay_frontend::parse(
            "(reset) (set-option :produce-models true)
             (declare-const x Int) (declare-fun f (Int) Int)",
        )
        .expect("redeclaration parses");
        executor
            .execute_all(&commands)
            .expect("redeclaration executes");
        executor.last_model = model;
        executor.last_result = Some(SolveResult::Sat);
        executor.last_model_validated = true;
        assert_public_reads_refuse_stale(&mut executor);
    }

    #[test]
    fn aggressive_minimization_preserves_int_and_bool_function_reads() {
        std::thread::Builder::new()
            .stack_size(64 * 1024 * 1024)
            .spawn(|| {
                for (sort, at_x, at_zero) in [("Int", "1", "0"), ("Bool", "true", "false")] {
                    let mut executor = Executor::new();
                    executor.set_timeout(Some(std::time::Duration::from_secs(10)));
                    executor.set_resource_limit(Some(400_000));
                    // Per-executor term ceiling, not `set_memory_limit`:
                    // that bound reads the whole-process footprint, and
                    // this lib test binary's footprint under parallel
                    // solver tests exceeds 512 MiB through no fault of
                    // this query (measured: `unknown` in the full run on
                    // clean origin/main, `sat` in isolation). Same
                    // pattern as `structural_preprocess::tests::setup`.
                    executor.set_term_memory_limit(Some(512 * 1024 * 1024));
                    executor.counterexample_style = crate::CounterexampleStyle::Readable;
                    let script = format!(
                        "(set-option :produce-models true) (set-logic QF_UFLIA)
                         (declare-const x Int) (declare-fun f (Int) {sort})
                         (assert (<= 0 x)) (assert (= (f x) {at_x}))
                         (assert (= (f 0) {at_zero})) (check-sat)"
                    );
                    let outputs = executor
                        .execute_all(&ay_frontend::parse(&script).expect("query parses"))
                        .expect("query executes");
                    assert_eq!(outputs.last().map(String::as_str), Some("sat"));
                    executor.aggressive_minimize_model();
                    assert!(executor
                        .last_model
                        .as_ref()
                        .expect("model")
                        .materialized_scalar_functions
                        .contains_key("f"));
                    assert!(matches!(
                        executor.confirm_sat_with_independent_gate(),
                        ay_model_check::GateVerdict::ConfirmedSat
                    ));
                    for (term, expected) in [("(f x)", at_x), ("(f 0)", at_zero)] {
                        let query = format!("(get-value ({term}))");
                        let values = executor
                            .execute_all(&ay_frontend::parse(&query).expect("getter parses"))
                            .expect("getter executes");
                        assert!(values
                            .last()
                            .expect("value")
                            .contains(&format!(" {expected})")));
                    }
                    assert!(!executor.model().contains("error"));
                }
            })
            .expect("start solver test thread")
            .join()
            .expect("solver test succeeds");
    }
}
