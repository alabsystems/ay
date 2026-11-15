// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Exact frozen-table semantics, not execution of IEEE floating-point operations.

use super::*;
use num_bigint::BigUint;

mod fixtures;
mod oracle;
use fixtures::{source, Cells, Table};

#[test]
fn wide_source_keys_keep_every_tag_bit_and_the_full_bv64_fill_premise() {
    oracle::check_sources();
}

#[test]
fn canonical_wide_source_roundtrip_preserves_declarations_and_quantified_premises() {
    for table in [Table::Float32, Table::Call, Table::Float64] {
        let original = source(table, Cells::Filled, 9);
        let replayed = QuantifiedChcProblem::parse_smtlib(original.source_smtlib()).unwrap();
        // Re-ingress alpha-freshens binders again; compare typed source meaning,
        // not the spelling or identity of that independently parsed source.
        oracle::check_source(&replayed, table, Cells::Filled, true);
        assert_eq!(
            replayed.source_problem().predicates()[0].arg_sorts,
            original.source_problem().predicates()[0].arg_sorts
        );
        assert_eq!(replayed.premises()[0][0].binder().sort, ChcSort::BitVec(64));
        assert_eq!(replayed.premises()[0][0].binder_count(), 1);
        assert_eq!(
            replayed.source_problem().predicates()[0].arg_sorts[1],
            ChcSort::BitVec(table.width())
        );
        let changed = source(table, Cells::Filled, 7);
        assert_ne!(changed.source_sha256(), original.source_sha256());
    }
}

fn native(table: Table) {
    let _memory = SmtContext::scoped_thread_term_memory_budget(Some(TERM_BUDGET));
    let deadline = Instant::now() + Duration::from_secs(120);
    let _deadline = ScopedSmtDeadline::install_until(deadline);
    let token = CancellationToken::new();
    let problem = source(table, Cells::Filled, 9);
    let evidence = require_unsafe(&problem, deadline, &token);
    assert_eq!(evidence.clause_indices(), &[0, 1]);
    assert_eq!(evidence.premise_steps(), &[vec![], vec![0]]);
    assert_eq!(
        evidence.replay_obligation().matches("(forall ((").count(),
        1
    );
    assert!(evidence.replay_obligation().contains("(_ bv65 64)"));
    assert!(evidence.recheck(&problem, remaining(deadline), &token));
    let trace = evidence
        .concrete_trace(&problem, remaining(deadline), &token)
        .expect("complete wide keys and ordered array values");
    assert_eq!(trace.bindings().len(), 8);
    assert_eq!(trace.clause_indices(), &[0, 1]);
    let (low, high) = table.keys();
    for occurrence in 0..2 {
        let arguments = oracle::arguments(&problem, occurrence);
        let values: Vec<_> = arguments
            .iter()
            .map(|argument| {
                let ChcExpr::Var(variable) = argument else {
                    panic!("original local")
                };
                trace
                    .bindings()
                    .iter()
                    .find(|binding| {
                        binding.occurrence() == occurrence && binding.variable() == variable
                    })
                    .unwrap()
                    .value()
            })
            .collect();
        assert_eq!(oracle::unsigned(values[1]), (low.clone(), table.width()));
        assert_eq!(oracle::unsigned(values[2]), (high.clone(), table.width()));
        assert_eq!(oracle::read(values[0], values[1]), SmtValue::BitVec(7, 8));
        assert_eq!(oracle::read(values[0], values[2]), SmtValue::BitVec(9, 8));
        assert_eq!(
            oracle::read(values[3], &SmtValue::BitVec(64, 64)),
            SmtValue::BitVec(7, 8)
        );
        if table.width() > 128 {
            assert!(matches!(values[1], SmtValue::BigBitVec(_, 136)));
            assert!(matches!(values[2], SmtValue::BigBitVec(_, 136)));
        }
    }
    let pin = if table.width() > 128 {
        format!(
            "#b{:0>width$}",
            high.to_str_radix(2),
            width = table.width() as usize
        )
    } else {
        format!("(_ bv{high} {})", table.width())
    };
    assert!(trace.replay_obligation().contains(&pin));
    assert!(trace.recheck(&problem, remaining(deadline), &token));
    assert!(!trace.recheck(
        &source(table, Cells::Filled, 7),
        remaining(deadline),
        &token
    ));
    assert!(Instant::now() < deadline);
}

#[test]
#[timeout(180000)]
fn native_float32_table_keys_preserve_all_seventy_two_bits() {
    native(Table::Float32);
}

#[test]
#[timeout(180000)]
fn native_call_table_keys_preserve_the_top_bit_at_width_one_twenty_eight() {
    native(Table::Call);
}

#[test]
#[timeout(180000)]
fn native_float64_table_stores_above_bit_one_twenty_seven_remain_distinct_in_pins() {
    native(Table::Float64);
}

#[test]
#[timeout(180000)]
fn wide_search_cannot_drop_a_false_original_fill_premise_or_change_the_query() {
    let _memory = SmtContext::scoped_thread_term_memory_budget(Some(TERM_BUDGET));
    let deadline = Instant::now() + Duration::from_secs(120);
    let _deadline = ScopedSmtDeadline::install_until(deadline);
    for problem in [
        source(Table::Float64, Cells::CorruptLast, 9),
        source(Table::Float64, Cells::Filled, 7),
    ] {
        assert!(!matches!(
            problem.solve(
                remaining(deadline).min(Duration::from_secs(40)),
                Some(TERM_BUDGET),
                &CancellationToken::new()
            ),
            QuantifiedChcResult::Unsafe(_)
        ));
    }
}
