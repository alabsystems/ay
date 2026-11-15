// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

#![cfg(test)]

use super::*;
use ntest::timeout;

mod stores;
mod witnesses;

const TERM_BUDGET: usize = 128 * 1024 * 1024;
const ROW_LENGTH: &str = "(fld_len (select (fld_data outer) row))";
const CELL: &str = "(select (fld_data (select (fld_data outer) row)) col)";

#[derive(Clone, Copy)]
enum Premise {
    Full,
    Diagonal,
    Missing,
}

#[derive(Clone, Copy)]
enum Query {
    SameRow,
    OtherRowLength,
    ShiftedFill,
}

fn script(premise: Premise, query: Query) -> String {
    // Authored composition of the retained Vec layouts, not a compiler export.
    // Both levels retain ptr/len/cap/data. The inner index is independent of
    // the outer row even though both use the producer's BV64 pointer sort.
    let inner_column = match premise {
        Premise::Diagonal => "r",
        _ => "c",
    };
    let matrix = format!(
        "(=> (and (bvult r (fld_len outer))
                  (bvult {inner_column} (fld_len (select (fld_data outer) r))))
              (= (select (fld_data (select (fld_data outer) r)) {inner_column}) fill))"
    );
    let premise = match premise {
        Premise::Full => format!("(forall ((r (_ BitVec 64)) (c (_ BitVec 64))) {matrix})"),
        Premise::Diagonal => format!("(forall ((r (_ BitVec 64))) {matrix})"),
        Premise::Missing => "true".to_owned(),
    };
    let length = match query {
        Query::OtherRowLength => "(fld_len (select (fld_data outer) other))",
        _ => ROW_LENGTH,
    };
    let value = match query {
        Query::ShiftedFill => "(bvadd fill (_ bv1 8))",
        _ => "fill",
    };
    format!(
        "(set-logic HORN)
         (declare-datatype Inner ((mkInner
           (fld_ptr (_ BitVec 64)) (fld_len (_ BitVec 64))
           (fld_cap (_ BitVec 64)) (fld_data (Array (_ BitVec 64) (_ BitVec 8))))))
         (declare-datatype Outer ((mkOuter
           (fld_ptr (_ BitVec 64)) (fld_len (_ BitVec 64))
           (fld_cap (_ BitVec 64)) (fld_data (Array (_ BitVec 64) Inner)))))
         (declare-fun P (Outer (_ BitVec 8)) Bool)
         (assert (forall ((outer Outer) (fill (_ BitVec 8)))
           (=> {premise} (P outer fill))))
         (assert (forall ((outer Outer) (fill (_ BitVec 8))
                          (row (_ BitVec 64)) (col (_ BitVec 64)) (other (_ BitVec 64)))
           (=> (and (P outer fill)
                    (bvuge row (_ bv32 64)) (bvuge col (_ bv32 64))
                    (bvult row (fld_len outer)) (bvult col {length})
                    (distinct {CELL} {value})) false)))
         (check-sat)"
    )
}

fn source(premise: Premise, query: Query) -> QuantifiedChcProblem {
    QuantifiedChcProblem::parse_smtlib(&script(premise, query))
        .expect("bounded nested Vec source admission")
}

#[test]
fn nested_cell_source_preserves_both_vec_schemas_and_independent_indices() {
    let source = source(Premise::Full, Query::SameRow);
    assert_eq!(source.source_problem().datatype_defs().len(), 2);
    assert_eq!(source.source_problem().predicates()[0].arg_sorts.len(), 2);
    assert_eq!(source.premises()[0][0].binder_count(), 2);
    // The explicit parser alpha-renames lexical binders, including the outer
    // clause binders. Inspect preserved structure rather than input spellings.
    assert!(source
        .source_smtlib()
        .contains("(select (fld_data (select (fld_data "));
    assert!(source
        .source_smtlib()
        .contains("(fld_len (select (fld_data "));
    assert_eq!(source.source_smtlib().matches("(bvuge ").count(), 2);
    let roundtrip = QuantifiedChcProblem::parse_smtlib(source.source_smtlib()).unwrap();
    assert_eq!(
        roundtrip.source_problem().datatype_defs(),
        source.source_problem().datatype_defs()
    );
    assert_eq!(roundtrip.source_problem().clauses().len(), 2);
    assert_eq!(roundtrip.premises()[0][0].binder_count(), 2);
}

#[test]
fn nested_cell_negative_controls_have_concrete_finite_store_witnesses() {
    for (premise, query) in [
        (Premise::Diagonal, Query::SameRow),
        (Premise::Missing, Query::SameRow),
        (Premise::Full, Query::OtherRowLength),
        (Premise::Full, Query::ShiftedFill),
    ] {
        let problem = source(premise, query);
        witnesses::check(&problem, premise, query);
    }
}

#[test]
#[timeout(180000)]
fn nested_vec_independent_indices_seal_and_recheck_the_complete_original_source() {
    let _memory = SmtContext::scoped_thread_term_memory_budget(Some(TERM_BUDGET));
    let deadline = Instant::now() + Duration::from_secs(90);
    let _deadline = ScopedSmtDeadline::install_until(deadline);
    let source = source(Premise::Full, Query::SameRow);
    let cancellation = CancellationToken::new();
    let QuantifiedChcResult::Safe(evidence) =
        source.solve(Duration::from_secs(45), Some(TERM_BUDGET), &cancellation)
    else {
        panic!("joint row/column observations must prove the nested Vec read");
    };
    assert_eq!(evidence.source_smtlib(), source.source_smtlib());
    let obligations = evidence.replay_obligations();
    assert_eq!(obligations.len(), 2);
    for (index, obligation) in obligations.iter().enumerate() {
        assert_eq!(obligation.clause_index, index);
        assert!(obligation.smtlib.contains("Inner"));
        assert!(obligation.smtlib.contains("Outer"));
        assert!(!obligation.smtlib.contains("(declare-fun fld_data"));
        assert!(obligation.smtlib.ends_with("(check-sat)\n"));
    }
    let premise = &source.premises()[0][0];
    assert!(obligations[0]
        .smtlib
        .contains(&crate::InvariantModel::expr_to_smtlib(premise.matrix())));
    let query = source.source_problem().clauses()[1]
        .body
        .constraint
        .as_ref()
        .unwrap();
    assert!(obligations[1]
        .smtlib
        .contains(&crate::InvariantModel::expr_to_smtlib(query)));
    assert!(evidence.recheck(
        &source,
        deadline.saturating_duration_since(Instant::now()),
        &cancellation,
    ));
    for (premise, query) in [
        (Premise::Diagonal, Query::SameRow),
        (Premise::Full, Query::OtherRowLength),
        (Premise::Full, Query::ShiftedFill),
    ] {
        let changed = self::source(premise, query);
        assert!(!evidence.recheck(
            &changed,
            deadline.saturating_duration_since(Instant::now()),
            &cancellation,
        ));
    }
    assert!(Instant::now() < deadline);
}

#[test]
#[timeout(180000)]
fn nested_vec_diagonal_missing_wrong_row_and_shifted_fill_never_certify() {
    let _memory = SmtContext::scoped_thread_term_memory_budget(Some(TERM_BUDGET));
    // Concrete controls: outer.len=100,row=33,col=64,fill=7. A diagonal-only
    // premise allows cell[33][64]=9; a missing premise allows any cell. For
    // wrong-row bounds take len(row33)=1,len(other34)=100 and cell[33][64]=9.
    // Full valid cells all equal 7 and differ from the shifted expected 8.
    let deadline = Instant::now() + Duration::from_secs(120);
    let _deadline = ScopedSmtDeadline::install_until(deadline);
    for (premise, query) in [
        (Premise::Diagonal, Query::SameRow),
        (Premise::Missing, Query::SameRow),
        (Premise::Full, Query::OtherRowLength),
        (Premise::Full, Query::ShiftedFill),
    ] {
        let problem = source(premise, query);
        assert!(!matches!(
            problem.solve(
                deadline
                    .saturating_duration_since(Instant::now())
                    .min(Duration::from_secs(30)),
                Some(TERM_BUDGET),
                &CancellationToken::new(),
            ),
            QuantifiedChcResult::Safe(_)
        ));
    }
}
