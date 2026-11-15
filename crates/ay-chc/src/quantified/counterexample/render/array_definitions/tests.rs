// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::CancellationToken;
use ay_core::time::Instant;
use std::sync::Arc;
use std::time::Duration;

fn premise(recursive: bool, reverse: bool) -> UniversalPremise {
    let key = ChcSort::BitVec(64);
    let sort = ChcSort::Array(Box::new(key.clone()), Box::new(ChcSort::BitVec(8)));
    let binder = ChcVar::new("i", key);
    let w = ChcExpr::var(ChcVar::new("w", sort.clone()));
    let d = if recursive {
        w.clone()
    } else {
        ChcExpr::var(ChcVar::new("d", sort))
    };
    let i = ChcExpr::var(binder.clone());
    let (lhs, rhs) = (ChcExpr::select(w, i.clone()), ChcExpr::select(d, i));
    let sides = if reverse {
        vec![rhs, lhs]
    } else {
        vec![lhs, rhs]
    };
    UniversalPremise::new(
        binder,
        ChcExpr::Op(ChcOp::Eq, sides.into_iter().map(Arc::new).collect()),
    )
}

#[test]
fn exact_definition_and_reversed_equality_use_one_lambda() {
    let token = CancellationToken::new();
    let control = SourceControl::new(Instant::now() + Duration::from_secs(30), &token);
    for reverse in [false, true] {
        let p = premise(false, reverse);
        let definition = recognize(&p, &control)
            .expect("funded scan")
            .expect("definition");
        let mut output = Output::new(&control);
        definition.write(&mut output).expect("funded output");
        let text = output.finish();
        let expected = if reverse {
            "(= d (lambda ((i (_ BitVec 64))) (select w i)))"
        } else {
            "(= w (lambda ((i (_ BitVec 64))) (select d i)))"
        };
        assert_eq!(text, expected);
        assert_eq!(text.matches("lambda").count(), 1);
    }
}

#[test]
fn recursive_or_grouped_matrices_keep_the_original_forall_route() {
    let token = CancellationToken::new();
    let control = SourceControl::new(Instant::now() + Duration::from_secs(30), &token);
    assert!(recognize(&premise(true, false), &control)
        .expect("scan")
        .is_none());
    let p = premise(false, false);
    let grouped = UniversalPremise::with_binders(
        vec![p.binder().clone(), ChcVar::new("j", ChcSort::BitVec(64))],
        p.matrix().clone(),
    )
    .expect("binder group");
    assert!(recognize(&grouped, &control).expect("scan").is_none());
}

#[test]
fn expired_cancelled_and_spent_controls_cannot_choose_a_definition() {
    let token = CancellationToken::new();
    let past = SourceControl::new(Instant::now(), &token);
    assert!(recognize(&premise(false, false), &past).is_err());
    let control = SourceControl::new(Instant::now() + Duration::from_secs(30), &token);
    assert!(control.bytes(usize::MAX).is_none());
    assert!(recognize(&premise(false, false), &control).is_err());
    let cancelled = CancellationToken::new();
    cancelled.cancel();
    let control = SourceControl::new(Instant::now() + Duration::from_secs(30), &cancelled);
    assert!(recognize(&premise(false, false), &control).is_err());
}

#[test]
fn guarded_definition_is_never_strengthened_into_total_definition() {
    let token = CancellationToken::new();
    let control = SourceControl::new(Instant::now() + Duration::from_secs(30), &token);
    let p = premise(false, false);
    let guarded = UniversalPremise::new(
        p.binder().clone(),
        ChcExpr::implies(
            ChcExpr::eq(ChcExpr::var(p.binder().clone()), ChcExpr::BitVec(0, 64)),
            p.matrix().clone(),
        ),
    );
    assert!(recognize(&guarded, &control).expect("scan").is_none());
}

#[test]
fn lexical_binder_shadow_does_not_capture_a_clause_value() {
    use crate::quantified::{QuantifiedChcProblem, QuantifiedHornClause};
    use crate::{ChcProblem, ClauseBody, ClauseHead, HornClause};
    let binder = ChcVar::new("i", ChcSort::BitVec(64));
    let outer = ChcExpr::var(ChcVar::new("i", ChcSort::BitVec(8)));
    let array = ChcExpr::var(ChcVar::new(
        "w",
        ChcSort::Array(Box::new(ChcSort::BitVec(64)), Box::new(ChcSort::BitVec(8))),
    ));
    let source = QuantifiedChcProblem::new(
        ChcProblem::new(),
        vec![QuantifiedHornClause::new(
            HornClause::new(
                ClauseBody::constraint(ChcExpr::eq(outer, ChcExpr::BitVec(9, 8))),
                ClauseHead::False,
            ),
            vec![UniversalPremise::new(
                binder.clone(),
                ChcExpr::eq(
                    ChcExpr::select(array, ChcExpr::var(binder)),
                    ChcExpr::BitVec(7, 8),
                ),
            )],
        )],
    )
    .expect("original lexical shadow source");
    let token = CancellationToken::new();
    let control = SourceControl::new(Instant::now() + Duration::from_secs(30), &token);
    let text = super::super::render_advice(&source, &[0], &[vec![]], &control)
        .expect("funded exact scope");
    assert!(text.contains("(declare-const ay_qcex_0 (_ BitVec 8))"));
    assert!(text.contains("(lambda ((i (_ BitVec 64))) (_ bv7 8))"));
    assert!(text.contains("(= i (_ bv9 8))"));
    assert_eq!(text.matches("(lambda ").count(), 1);
}

#[test]
fn canonical_original_forall_and_advice_are_separate_with_identical_local_inventory() {
    let source = crate::quantified::QuantifiedChcProblem::parse_smtlib(include_str!(
        "../../../complete_solve/tests/range_write_refutes_stale_lane_1.smt2"
    ))
    .unwrap();
    let token = CancellationToken::new();
    let control = SourceControl::new(Instant::now() + Duration::from_secs(20), &token);
    let canonical =
        super::super::render_complete(&source, &[0, 1], &[vec![], vec![0]], &control).unwrap();
    let advice =
        super::super::render_advice(&source, &[0, 1], &[vec![], vec![0]], &control).unwrap();
    assert_eq!(canonical.original.obligation.matches("(forall ").count(), 1);
    assert!(!canonical.original.obligation.contains("(lambda "));
    assert_eq!(advice.matches("(lambda ").count(), 1);
    assert!(!advice.contains("(forall "));
    assert_eq!(
        advice.matches("(assert ").count(),
        canonical.original.obligation.matches("(assert ").count()
    );
    for binding in &canonical.original.bindings {
        assert!(advice.contains(&format!("(declare-const {} ", binding.symbol)));
    }
    for payload in &canonical.assertions {
        assert!(
            canonical.original.obligation[payload.clone()].contains("let")
                || &canonical.original.obligation[payload.clone()] == "true"
        );
    }
}

#[test]
fn mutual_definition_equations_are_retained_without_substitution_or_unfolding() {
    use crate::quantified::{QuantifiedChcProblem, QuantifiedHornClause};
    use crate::{ChcProblem, ClauseBody, ClauseHead, HornClause};
    let first = premise(false, false);
    let second = premise(false, true);
    let source = QuantifiedChcProblem::new(
        ChcProblem::new(),
        vec![QuantifiedHornClause::new(
            HornClause::new(
                ClauseBody::constraint(ChcExpr::Bool(true)),
                ClauseHead::False,
            ),
            vec![first, second],
        )],
    )
    .unwrap();
    let token = CancellationToken::new();
    let control = SourceControl::new(Instant::now() + Duration::from_secs(20), &token);
    let original = super::super::render_derivation(&source, &[0], &[vec![]], &control).unwrap();
    let advice = super::super::render_advice(&source, &[0], &[vec![]], &control).unwrap();
    assert_eq!(original.matches("(forall ").count(), 2);
    assert_eq!(advice.matches("(lambda ").count(), 2);
    assert!(advice.contains("(= w (lambda ((i (_ BitVec 64))) (select d i)))"));
    assert!(advice.contains("(= d (lambda ((i (_ BitVec 64))) (select w i)))"));
}

#[test]
#[ntest::timeout(30000)]
fn original_full_forall_refuses_wrong_complete_lane_pin_without_deleting_source() {
    let end = Instant::now() + Duration::from_secs(20);
    let _wall = crate::smt::ScopedSmtDeadline::install_until(end);
    let source = crate::quantified::QuantifiedChcProblem::parse_smtlib(include_str!(
        "../../../complete_solve/tests/range_write_refutes_stale_lane_1.smt2"
    ))
    .unwrap();
    let token = CancellationToken::new();
    let control = SourceControl::new(end, &token);
    let rendered =
        super::super::render_with_bindings(&source, &[0, 1], &[vec![], vec![0]], &control).unwrap();
    let query = rendered
        .bindings
        .iter()
        .find(|binding| binding.occurrence == 1)
        .unwrap();
    let body = rendered.obligation.strip_suffix("(check-sat)\n").unwrap();
    control
        .bytes(
            body.len()
                .checked_add(query.symbol.len())
                .unwrap()
                .checked_add(128)
                .unwrap()
                .checked_mul(2)
                .unwrap(),
        )
        .unwrap();
    let wrong = format!(
        "{body}(assert (= (select {} (_ bv1 64)) (_ bv7 8)))\n(check-sat)\n",
        query.symbol
    );
    assert!(wrong.contains("(forall "));
    assert!(wrong.contains("(_ bv9 8)"));
    assert!(!super::super::super::replay::validate(
        &wrong,
        end,
        Some(128 * 1024 * 1024),
        &token,
        &control
    ));
}
