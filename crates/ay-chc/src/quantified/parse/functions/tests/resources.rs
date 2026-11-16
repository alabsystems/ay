// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

fn parser() -> Parser<'static> {
    Parser {
        declarations: ChcProblem::new(),
        functions: FunctionState::default(),
        records: Default::default(),
        clauses: Vec::new(),
        bindings: Default::default(),
        reserved: Default::default(),
        fresh: 0,
        qf: Default::default(),
        budget: Budget::default(),
        dialect: Dialect::Unset,
        phase: Phase::Declarations,
        logic_seen: false,
    }
}

fn sexp(text: &str) -> SExpr {
    ay_frontend::sexp::parse_sexps(text).unwrap().pop().unwrap()
}

fn declare(parser: &mut Parser<'_>) -> ChcResult<()> {
    parser.function_declaration(
        &sexp("f"),
        &sexp("(Bool (_ BitVec 136))"),
        &sexp("(_ BitVec 136)"),
    )
}

#[test]
fn signature_copy_limits_are_exact_atomic_and_shared_with_prior_parse_work() {
    let mut measured = parser();
    declare(&mut measured).unwrap();
    let (work, bytes) = (measured.budget.work, measured.budget.bytes);
    assert!(work > 3 && bytes > 256);
    for (work_short, bytes_short) in [(0, 0), (1, 0), (0, 1)] {
        let mut parser = parser();
        parser.budget = Budget {
            work: super::super::super::MAX_WORK - work + work_short,
            bytes: super::super::super::MAX_COPY_BYTES - bytes + bytes_short,
        };
        assert_eq!(
            declare(&mut parser).is_ok(),
            work_short == 0 && bytes_short == 0
        );
        assert_eq!(
            parser.functions.declarations.len(),
            usize::from(work_short == 0 && bytes_short == 0)
        );
        if work_short + bytes_short > 0 {
            assert!(!parser.functions.contains("f"));
            assert!(declare(&mut parser).is_err());
        }
    }
    let mut malformed = parser();
    assert!(malformed
        .function_declaration(
            &sexp("bad"),
            &sexp("(Bool (_ BitVec 136) Int)"),
            &sexp("(_ BitVec 8)")
        )
        .is_err());
    assert_eq!(
        malformed.functions.declarations,
        [] as [QuantifiedChcFunction; 0]
    );
    assert!(!malformed.functions.contains("bad"));
    assert!(declare(&mut parser()).is_ok());
}

fn application(parser: &mut Parser<'_>) -> ChcResult<(Arc<ChcExpr>, ChcSort)> {
    parser.function_application(
        "f",
        vec![
            Arc::new(ChcExpr::Bool(true)),
            Arc::new(ChcExpr::BitVec(0, 136)),
        ],
        &[ChcSort::Bool, ChcSort::BitVec(136)],
    )
}

#[test]
fn every_application_name_and_recorded_sort_copy_uses_the_same_allowance() {
    let mut measured = parser();
    declare(&mut measured).unwrap();
    let (before_work, before_bytes) = (measured.budget.work, measured.budget.bytes);
    let expected = application(&mut measured).unwrap();
    let (work, bytes) = (
        measured.budget.work - before_work,
        measured.budget.bytes - before_bytes,
    );
    assert!(work > 3 && bytes > 256);
    for (work_short, bytes_short) in [(0, 0), (1, 0), (0, 1)] {
        let mut parser = parser();
        declare(&mut parser).unwrap();
        parser.budget = Budget {
            work: super::super::super::MAX_WORK - work + work_short,
            bytes: super::super::super::MAX_COPY_BYTES - bytes + bytes_short,
        };
        let actual = application(&mut parser);
        if work_short + bytes_short == 0 {
            assert_eq!(actual.unwrap(), expected);
        } else {
            assert!(actual.is_err());
        }
        assert!(application(&mut parser).is_err());
        assert_eq!(parser.functions.declarations.len(), 1);
    }
}

#[test]
fn functions_and_relations_share_the_existing_declaration_limit_without_new_arity_cap() {
    let maximum = super::super::super::super::source::MAX_DECLARATIONS;
    let mut declarations = "(declare-fun f () (_ BitVec 8))".to_owned();
    for index in 0..maximum - 1 {
        declarations.push_str(&format!("(declare-rel p{index} ())"));
    }
    let problem = parsed(&format!("{declarations}(query p0)"));
    assert_eq!(
        problem.function_declarations().len() + problem.source_problem().predicates().len(),
        maximum
    );
    refuses(&format!("{declarations}(declare-rel extra ())(query p0)"));
    refuses(&format!(
        "{declarations}(declare-fun extra () (_ BitVec 8))(query p0)"
    ));
    let arguments = vec!["Bool"; 129].join(" ");
    let problem = parsed(&format!(
        "(declare-fun many ({arguments}) (_ BitVec 8))
      (declare-rel error ())(query error)"
    ));
    assert_eq!(problem.function_declarations()[0].arg_sorts().len(), 129);
}
