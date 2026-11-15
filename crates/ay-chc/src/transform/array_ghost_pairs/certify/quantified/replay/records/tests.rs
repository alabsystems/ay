// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
#![allow(clippy::unwrap_used)]

use super::*;

fn source(record: bool) -> QuantifiedChcProblem {
    let record = if record {
        "(declare-datatype UnusedRecord ((makeRecord (field (_ BitVec 8)))))"
    } else {
        ""
    };
    QuantifiedChcProblem::parse_smtlib(&format!(
        "(set-logic HORN){record}
      (declare-fun f ((_ BitVec 64)) (_ BitVec 8))
      (declare-fun matrix_only ((_ BitVec 64)) (_ BitVec 8))
      (declare-fun unused () (_ BitVec 136))
      (assert (forall ((x (_ BitVec 64)))
        (=> (and (= (f x) #x01)
          (forall ((i (_ BitVec 64))) (= (matrix_only i) #x01))) false)))
      (check-sat)"
    ))
    .unwrap()
}

fn control(token: &CancellationToken) -> SourceControl<'_> {
    SourceControl::new(Instant::now() + Duration::from_secs(30), token)
}

fn rendered(
    source: &QuantifiedChcProblem,
    hints: &[ChcExpr],
    control: &SourceControl<'_>,
) -> Option<String> {
    let registry = Registry::new(source.source_problem()).ok()?;
    let interpretation = GhostPairModel {
        spec: GhostPairSpec::analyze(source.source_problem(), 1),
        model: InvariantModel::new(),
        executor_term_memory_limit: Some(64 * 1024 * 1024),
    };
    let clause = &source.source_problem().clauses()[0];
    let premises = &source.premises()[0];
    let variables = source_premises::clause_variables(clause, premises, control)?;
    render(
        source,
        &registry,
        &interpretation,
        clause,
        &variables,
        &[],
        None,
        &mut FxHashSet::default(),
        hints,
        premises,
        control,
    )
}

#[test]
fn ordinary_and_record_headers_keep_every_uninterpreted_signature_once() {
    let token = CancellationToken::new();
    for record in [false, true] {
        let source = source(record);
        let text = rendered(&source, &[], &control(&token)).unwrap();
        let mut previous = 0;
        for declaration in [
            "(declare-fun f ((_ BitVec 64)) (_ BitVec 8))",
            "(declare-fun matrix_only ((_ BitVec 64)) (_ BitVec 8))",
            "(declare-fun unused () (_ BitVec 136))",
        ] {
            assert_eq!(text.matches(declaration).count(), 1);
            let position = text.find(declaration).unwrap();
            assert!(position >= previous);
            previous = position;
        }
        assert!(!text.contains("define-fun"));
        assert_eq!(
            text.matches("(declare-datatypes").count(),
            usize::from(record)
        );
        assert!(text.contains(&InvariantModel::expr_to_smtlib(
            source.premises()[0][0].matrix()
        )));
        assert_eq!(text.matches("(forall ((").count(), 1);
        assert_eq!(text.matches("(check-sat)").count(), 1);
    }
}

#[test]
fn declaration_disagreement_in_finite_hints_cannot_change_original_replay() {
    let source = source(true);
    let token = CancellationToken::new();
    for (name, result, argument) in [
        ("f", ChcSort::BitVec(9), ChcExpr::BitVec(0, 64)),
        ("f", ChcSort::BitVec(8), ChcExpr::BitVec(0, 32)),
        ("invented", ChcSort::BitVec(8), ChcExpr::BitVec(0, 64)),
    ] {
        let app = ChcExpr::FuncApp(name.into(), result.clone(), vec![Arc::new(argument)]);
        let bad = ChcExpr::Op(crate::ChcOp::Eq, vec![Arc::new(app.clone()), Arc::new(app)]);
        // Even a reflexive hint must authenticate both complete applications.
        assert!(rendered(&source, &[bad], &control(&token)).is_none());
    }
    let unchanged = rendered(&source, &[], &control(&token)).unwrap();
    let changed = QuantifiedChcProblem::parse_smtlib(&source.source_smtlib().replace(
        "(declare-fun unused () (_ BitVec 136))",
        "(declare-fun unused () (_ BitVec 128))",
    ))
    .unwrap();
    assert_ne!(
        unchanged,
        rendered(&changed, &[], &control(&token)).unwrap()
    );
}

#[test]
fn controlled_replay_refuses_before_partial_declaration_output_can_escape() {
    let source = source(false);
    let token = CancellationToken::new();
    let exhausted = control(&token);
    exhausted.bytes(64 * 1024 * 1024).unwrap();
    assert!(rendered(&source, &[], &exhausted).is_none());
    assert!(exhausted.poll().is_none());
    let stopped = control(&token);
    token.cancel();
    assert!(rendered(&source, &[], &stopped).is_none());
    token.reset();
    assert!(rendered(&source, &[], &stopped).is_none());
    assert!(rendered(&source, &[], &control(&token)).is_some());
}

#[test]
#[ntest::timeout(90_000)]
fn fabricated_forwarding_and_false_finite_query_cannot_discharge_a_sat_uf_obligation() {
    const MEMORY: usize = 128 * 1024 * 1024;
    let _memory = SmtContext::scoped_thread_term_memory_budget(Some(MEMORY));
    let deadline = Instant::now() + Duration::from_secs(60);
    let _deadline = crate::smt::ScopedSmtDeadline::install_until(deadline);
    let source = source(false);
    let token = CancellationToken::new();
    let live = SourceControl::new(deadline, &token);
    let interpretation = GhostPairModel {
        spec: GhostPairSpec::analyze(source.source_problem(), 1),
        model: InvariantModel::new(),
        executor_term_memory_limit: Some(MEMORY),
    };
    let prepared = super::super::prepare(&source, &interpretation, 0, &live, None).unwrap();
    assert!(std::ptr::eq(prepared.source, &source));
    assert_eq!(
        prepared.obligation.smtlib.matches("(declare-fun ").count(),
        3
    );
    // The complete counter-obligation is SAT: take f and matrix_only to be
    // constantly #x01, with any x and any interpretation for unused. Confirm
    // this natively so refusal cannot pass vacuously on an unsupported fixture.
    let verdict = crate::smt::executor_adapter::smtlib_first_verdict_via_executor_with_limit(
        &prepared.obligation.smtlib,
        crate::smt::executor_adapter::ReplayLimit::Cancellable {
            deadline,
            cancellation: &live.replay_cancellation,
        },
        Some(MEMORY),
    );
    assert_eq!(verdict.as_deref(), Some("sat"));
    drop(prepared);
    for forwarding in [false, true] {
        let mut prepared = super::super::prepare(&source, &interpretation, 0, &live, None).unwrap();
        // White-box corruption only. Neither the finite contradiction alone,
        // nor the additional forwarding shortcut, may replace full UF replay.
        prepared.finite_query = ChcExpr::Bool(false);
        prepared.forwarding = forwarding;
        assert!(!super::super::discharge(prepared, 1, &live));
        assert!(live.poll().is_some());
    }
    assert!(Instant::now() < deadline);
}
