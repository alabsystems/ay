// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::super::{ChcReplayObligationKind, InvariantModel, PredicateInterpretation};
use crate::smt::executor_adapter::smtlib_first_verdict_via_executor;
use crate::{ChcExpr, ChcParser, ChcProblem};
use std::time::Duration;

/// A MODEL_CHECKER_CONSUMER-shaped datatype whose sort name needs SMT-LIB quoting.
fn datatype_problem() -> ChcProblem {
    ChcParser::parse(
        "(set-logic HORN)\n\
         (declare-datatype |A::B| ((|A::B_mk| (f Int))))\n\
         (declare-fun inv (|A::B|) Bool)\n\
         (assert (forall ((d |A::B|)) (=> (= d (|A::B_mk| 0)) (inv d))))\n\
         (assert (forall ((d |A::B|)) (=> (and (inv d) (< (f d) 0)) false)))\n\
         (check-sat)\n",
    )
    .expect("datatype fixture parses")
}

/// `inv(d) := not (f d < 0)` (exact) or `inv(d) := (f d < 0)` (wrong), over
/// the query clause's own variable and constraint.
fn model(problem: &ChcProblem, exact: bool) -> InvariantModel {
    let query = problem.queries().next().expect("fixture has a query");
    let [(inv, args)] = query.body.predicates.as_slice() else {
        panic!("query has one body predicate");
    };
    let [ChcExpr::Var(d)] = args.as_slice() else {
        panic!("query applies inv to its variable");
    };
    let bad = query.body.constraint.clone().expect("query constraint");
    let formula = if exact { ChcExpr::not(bad) } else { bad };
    let mut model = InvariantModel::new();
    model.set(*inv, PredicateInterpretation::new(vec![d.clone()], formula));
    model
}

fn verdict(smt: &str) -> Option<String> {
    smtlib_first_verdict_via_executor(smt, Some(Duration::from_secs(10)))
}

#[test]
fn datatype_obligations_are_self_contained_and_quote_their_sort_names() {
    let problem = datatype_problem();
    assert!(problem.has_datatype_sorts());
    let model = model(&problem, true);
    let definitions = model.to_smtlib(&problem);
    assert!(definitions.contains("(d |A::B|)"), "{definitions}");
    assert!(!definitions.contains(" A::B)"), "{definitions}");
    for printed in [
        model.to_certificate(&problem),
        model.to_spacer_format(&problem),
    ] {
        assert!(printed.contains("(d |A::B|)"), "{printed}");
    }
    let obligations = model.replay_obligations(&problem).expect("obligations");
    assert_eq!(obligations.len(), 2);
    for obligation in &obligations {
        let smt = &obligation.smtlib;
        let declared = smt.find("(declare-datatypes ((|A::B| 0))").expect(smt);
        let first_use = smt.find("|A::B|)").expect(smt);
        assert!(declared < first_use, "{smt}");
        assert_eq!(smt.matches("(declare-datatypes").count(), 1, "{smt}");
        assert!(
            !smt.contains(" A::B)"),
            "an unquoted sort is not SMT-LIB: {smt}"
        );
        if obligation.kind == ChcReplayObligationKind::Safety {
            assert!(smt.contains("(declare-const d |A::B|)"), "{smt}");
        }
        // Before the declaration this script did not parse (`unknown sort`).
        assert_eq!(verdict(smt).as_deref(), Some("unsat"), "{smt}");
    }
}

#[test]
fn a_wrong_datatype_model_still_fails_its_now_parseable_obligation() {
    let problem = datatype_problem();
    let obligations = model(&problem, false)
        .replay_obligations(&problem)
        .expect("obligations");
    let initiation = obligations
        .iter()
        .find(|obligation| obligation.kind == ChcReplayObligationKind::Initiation)
        .expect("initiation obligation");
    assert_eq!(verdict(&initiation.smtlib).as_deref(), Some("sat"));
}

#[test]
fn scalar_obligations_receive_no_datatype_declaration() {
    let problem = ChcParser::parse(
        "(set-logic HORN)\n\
         (declare-fun inv (Int) Bool)\n\
         (assert (forall ((x Int)) (=> (= x 0) (inv x))))\n\
         (assert (forall ((x Int)) (=> (and (inv x) (< x 0)) false)))\n\
         (check-sat)\n",
    )
    .expect("scalar fixture parses");
    let model = model(&problem, true);
    for obligation in model.replay_obligations(&problem).expect("obligations") {
        assert!(!obligation.smtlib.contains("declare-datatype"));
        if obligation.kind == ChcReplayObligationKind::Safety {
            assert!(obligation.smtlib.contains("(declare-const x Int)"));
        }
        assert_eq!(verdict(&obligation.smtlib).as_deref(), Some("unsat"));
    }
}
