// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::quantified::QuantifiedChcResult;
use crate::smt::ScopedSmtDeadline;
use ntest::timeout;

const TERM_BUDGET: usize = 128 * 1024 * 1024;

fn prove(table: Table) {
    let _memory = SmtContext::scoped_thread_term_memory_budget(Some(TERM_BUDGET));
    let end = Instant::now() + Duration::from_secs(120);
    let _deadline = ScopedSmtDeadline::install_until(end);
    let source = fixtures::source(table, Change::None);
    let token = CancellationToken::new();
    let QuantifiedChcResult::Safe(evidence) =
        source.solve(Duration::from_secs(80), Some(TERM_BUDGET), &token)
    else {
        panic!("wide readonly table congruence and separate BV64 resize must synthesize Safe");
    };
    assert_eq!(evidence.source_smtlib(), source.source_smtlib());
    assert_eq!(evidence.replay_obligations().len(), 4);
    let first = &evidence.replay_obligations()[0].smtlib;
    assert!(first.contains(&InvariantModel::expr_to_smtlib(
        source.premises()[0][0].matrix()
    )));
    assert!(first.contains(&format!(
        "(Array (_ BitVec {}) (_ BitVec {}))",
        table.key_width(),
        table.cell_width()
    )));
    assert!(evidence.replay_obligations()[1]
        .smtlib
        .contains("(forall ("));
    assert!(evidence.recheck(
        &source,
        end.saturating_duration_since(Instant::now()),
        &token
    ));
    for change in [
        Change::IndependentTable,
        Change::OtherTag,
        Change::MissingSuffix,
    ] {
        let changed = fixtures::source(table, change);
        assert!(!evidence.recheck(
            &changed,
            end.saturating_duration_since(Instant::now()),
            &token
        ));
    }
    assert!(Instant::now() < end);
}

#[test]
#[timeout(180000)]
fn readonly_float32_table_and_quantified_resize_synthesize_source_safe() {
    prove(Table::Float32);
}

#[test]
#[timeout(180000)]
fn readonly_float64_table_and_quantified_resize_synthesize_source_safe() {
    prove(Table::Float64);
}

#[test]
#[timeout(180000)]
fn table_havoc_tag_change_and_missing_resize_premise_never_certify() {
    let _memory = SmtContext::scoped_thread_term_memory_budget(Some(TERM_BUDGET));
    let end = Instant::now() + Duration::from_secs(120);
    let _deadline = ScopedSmtDeadline::install_until(end);
    for (index, change) in [
        Change::IndependentTable,
        Change::OtherTag,
        Change::MissingSuffix,
    ]
    .into_iter()
    .enumerate()
    {
        let source = fixtures::source(Table::Float64, change);
        assert!(oracle::bad_state(&source, Table::Float64, change));
        let remaining = end.saturating_duration_since(Instant::now());
        assert!(!remaining.is_zero());
        assert!(!matches!(
            source.solve(
                remaining / u32::try_from(3 - index).unwrap(),
                Some(TERM_BUDGET),
                &CancellationToken::new(),
            ),
            QuantifiedChcResult::Safe(_)
        ));
    }
}

#[test]
#[timeout(90000)]
fn ieee_named_add_table_retains_non_ieee_cell_and_source_bound_controls() {
    let _memory = SmtContext::scoped_thread_term_memory_budget(Some(TERM_BUDGET));
    let end = Instant::now() + Duration::from_secs(60);
    let _deadline = ScopedSmtDeadline::install_until(end);
    let token = CancellationToken::new();
    let source = fixtures::ieee_named_add_source(fixtures::AddTable::Arbitrary);
    let constrained = fixtures::ieee_named_add_source(fixtures::AddTable::ThreeAtInput);
    let remaining = || end.saturating_duration_since(Instant::now());
    let QuantifiedChcResult::Unsafe(evidence) =
        source.solve(Duration::from_secs(15), Some(TERM_BUDGET), &token)
    else {
        panic!("arbitrary ADD table must admit a checked zero cell for 1.0 and 2.0");
    };
    assert_eq!(evidence.source_smtlib(), source.source_smtlib());
    assert_eq!(evidence.clause_indices(), &[0, 1, 2]);
    assert!(evidence.recheck(&source, remaining(), &token));
    let trace = evidence
        .concrete_trace(&source, remaining(), &token)
        .expect("complete original-source zero-cell assignment");
    let ClauseHead::Predicate(_, args) = &source.source_problem().clauses()[0].head else {
        panic!("original P fact");
    };
    let ChcExpr::Var(table) = &args[0] else {
        panic!("original table variable");
    };
    assert_eq!(table.name, "float_binop_tbl_f32");
    assert_eq!(
        table.sort,
        ChcSort::Array(Box::new(ChcSort::BitVec(72)), Box::new(ChcSort::BitVec(32)))
    );
    for (position, bits) in [(1, 0x3f80_0000), (2, 0x4000_0000), (3, 0)] {
        let ChcExpr::Var(variable) = &args[position] else {
            panic!("original scalar argument");
        };
        let binding = trace
            .bindings()
            .iter()
            .find(|binding| binding.occurrence() == 0 && binding.variable() == variable)
            .expect("complete original fact binding");
        assert_eq!(binding.value(), &SmtValue::BitVec(bits, 32));
    }
    assert!(trace.recheck(&source, remaining(), &token));
    assert!(!trace.recheck(&constrained, remaining(), &token));
    assert!(!evidence.recheck(&constrained, remaining(), &token));

    // This source explicitly fixes the same point to 3.0. Require a real
    // checked Safe result: Unknown is not a successful negative control.
    let QuantifiedChcResult::Safe(safe) = constrained.solve(
        remaining().min(Duration::from_secs(15)),
        Some(TERM_BUDGET),
        &token,
    ) else {
        panic!("the explicit 3.0 point constraint must exclude the zero-cell query");
    };
    assert_eq!(safe.source_smtlib(), constrained.source_smtlib());
    assert!(safe.recheck(&constrained, remaining(), &token));
    assert!(!safe.recheck(&source, remaining(), &token));
    assert!(Instant::now() < end);
}
