// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

const MEMORY: usize = 128 * 1024 * 1024;

fn remaining(deadline: Instant) -> Duration {
    deadline.saturating_duration_since(Instant::now())
}

fn evidence(
    source: &QuantifiedChcProblem,
    deadline: Instant,
    token: &CancellationToken,
) -> QuantifiedChcCounterexample {
    match source.solve(
        remaining(deadline).min(Duration::from_secs(30)),
        Some(MEMORY),
        token,
    ) {
        QuantifiedChcResult::Unsafe(evidence) => evidence,
        other => panic!("expected full-source counterexample: {other:?}"),
    }
}

fn wide_source() -> QuantifiedChcProblem {
    // Authored scalar summary shape; not real floating-point execution or an
    // authenticated callee implementation. The distinguishing bit is 130.
    QuantifiedChcProblem::parse_smtlib(
        "(set-logic HORN)
         (declare-fun uf_call_0_summary (Bool (_ BitVec 136)) (_ BitVec 136))
         (declare-fun nullary () (_ BitVec 136))
         (declare-fun unused ((_ BitVec 136)) (_ BitVec 136))
         (declare-fun P ((_ BitVec 136) (_ BitVec 136)) Bool)
         (assert (forall ((x (_ BitVec 136)) (y (_ BitVec 136)))
           (=> (and (= x (concat (_ bv4 8) (_ bv5 128)))
                    (= y (concat (_ bv4 8) (_ bv9 128)))
                    (= (uf_call_0_summary true x) y)
                    (= nullary y)
                    (forall ((i (_ BitVec 64)))
                      (=> (bvult i (_ bv65 64)) (= x x)))) (P x y))))
         (assert (forall ((x (_ BitVec 136)) (y (_ BitVec 136)))
           (=> (and (P x y) (= y (concat (_ bv4 8) (_ bv9 128)))) false)))
         (check-sat)",
    )
    .unwrap()
}

fn capture(
    script: &str,
    name: &str,
    deadline: Instant,
    token: &CancellationToken,
) -> ScalarFunctionModel {
    let control = SourceControl::new(deadline, token);
    let (locals, mut functions) = replay::extract(
        script,
        &[],
        &[name],
        deadline,
        Some(MEMORY),
        token,
        &control,
    )
    .expect("one real accepted native model, with complete typed definition");
    assert!(locals.is_empty());
    assert_eq!(functions.len(), 1);
    functions.remove(0)
}

#[test]
#[timeout(180000)]
fn wide_global_nullary_and_unused_functions_are_retained_once_in_source_order() {
    let _memory = SmtContext::scoped_thread_term_memory_budget(Some(MEMORY));
    let deadline = Instant::now() + Duration::from_secs(120);
    let _deadline = ScopedSmtDeadline::install_until(deadline);
    let token = CancellationToken::new();
    let source = wide_source();
    let base = evidence(&source, deadline, &token);
    let mut trace = base
        .concrete_trace(&source, remaining(deadline), &token)
        .unwrap();
    assert_eq!(trace.bindings().len(), 4);
    assert_eq!(trace.clause_indices(), &[0, 1]);
    let names: Vec<_> = trace
        .function_models()
        .iter()
        .map(ScalarFunctionModel::name)
        .collect();
    assert_eq!(names, ["uf_call_0_summary", "nullary", "unused"]);
    assert!(trace.function_models()[1].arg_sorts().is_empty());
    assert_eq!(
        trace.function_models()[0].arg_sorts(),
        &[ay_core::Sort::Bool, ay_core::Sort::bitvec(136)]
    );
    assert_eq!(trace.replay_obligation().matches("(define-fun ").count(), 3);
    assert_eq!(
        trace.replay_obligation().matches("(declare-fun ").count(),
        0
    );
    assert_eq!(trace.replay_obligation().matches("(forall ((").count(), 1);
    for binding in trace.bindings() {
        let SmtValue::BigBitVec(value, 136) = binding.value() else {
            panic!("exact wide local")
        };
        assert!(value.bit(130));
        assert!(value.bits() <= 136);
    }
    assert!(trace.recheck(&source, remaining(deadline), &token));
    let unused = trace.functions.pop().unwrap();
    assert!(!trace.recheck(&source, remaining(deadline), &token));
    trace.functions.push(unused);
    trace.functions.swap(0, 2);
    assert!(!trace.recheck(&source, remaining(deadline), &token));
    trace.functions.swap(0, 2);
    trace.functions.push(trace.functions[0].clone());
    assert!(!trace.recheck(&source, remaining(deadline), &token));
    trace.functions.pop();
    let changed = QuantifiedChcProblem::parse_smtlib(&source.source_smtlib().replace(
        "(declare-fun unused ((_ BitVec 136)) (_ BitVec 136))",
        "(declare-fun unused ((_ BitVec 136)) (_ BitVec 128))",
    ))
    .unwrap();
    assert_ne!(changed.source_smtlib(), source.source_smtlib());
    assert!(!trace.recheck(&changed, remaining(deadline), &token));
    token.cancel();
    assert!(!trace.recheck(&source, remaining(deadline), &token));
    token.reset();
    assert!(trace.recheck(&source, remaining(deadline), &token));
    assert!(Instant::now() < deadline);
}

#[test]
#[timeout(180000)]
fn a_different_complete_function_model_cannot_replace_the_retained_assignment() {
    let _memory = SmtContext::scoped_thread_term_memory_budget(Some(MEMORY));
    let deadline = Instant::now() + Duration::from_secs(120);
    let _deadline = ScopedSmtDeadline::install_until(deadline);
    let token = CancellationToken::new();
    let source = wide_source();
    let base = evidence(&source, deadline, &token);
    let mut trace = base
        .concrete_trace(&source, remaining(deadline), &token)
        .unwrap();
    let old = trace.functions[2].clone();
    let mut alternative = capture(
        "(set-logic ALL)\n(declare-fun unused ((_ BitVec 136)) (_ BitVec 136))
         (assert (= (unused (_ bv0 136)) (_ bv1 136))) (check-sat)",
        "unused",
        deadline,
        &token,
    );
    if alternative.definition_smtlib() == old.definition_smtlib() {
        alternative = capture(
            "(set-logic ALL)\n(declare-fun unused ((_ BitVec 136)) (_ BitVec 136))
             (assert (= (unused (_ bv0 136)) (_ bv2 136))) (check-sat)",
            "unused",
            deadline,
            &token,
        );
    }
    assert_ne!(alternative.definition_smtlib(), old.definition_smtlib());
    trace.functions[2] = alternative;
    let rendered = bound_render(&trace.base, &source, &control(&token)).unwrap();
    let registry = registry(&source, &control(&token)).unwrap();
    let changed = pins::render(
        &rendered,
        &trace.bindings,
        &trace.functions,
        &source,
        &registry,
        &control(&token),
    )
    .unwrap();
    // The unused interpretation can change while the source stays satisfiable,
    // but it is still not the exact assignment sealed by this trace.
    assert!(replay::validate(
        &changed,
        deadline,
        Some(MEMORY),
        &token,
        &SourceControl::new(deadline, &token)
    ));
    assert!(!trace.recheck(&source, remaining(deadline), &token));
    trace.functions[2] = old;
    assert!(trace.recheck(&source, remaining(deadline), &token));
    // Splice in a genuine model of a DIFFERENT solve that disagrees with the
    // retained local y. Even recomputing the script must not permit fallback.
    trace.functions[0] = capture(
        "(set-logic ALL)\n(declare-fun uf_call_0_summary (Bool (_ BitVec 136)) (_ BitVec 136))
         (assert (= (uf_call_0_summary true (concat (_ bv4 8) (_ bv5 128))) (_ bv0 136))) (check-sat)",
        "uf_call_0_summary", deadline, &token,
    );
    trace.pinned_obligation = pins::render(
        &rendered,
        &trace.bindings,
        &trace.functions,
        &source,
        &registry,
        &control(&token),
    )
    .unwrap();
    assert!(!trace.recheck(&source, remaining(deadline), &token));
    assert!(base.recheck(&source, remaining(deadline), &token));
}

#[test]
#[timeout(180000)]
fn a_bad_total_function_at_point64_cannot_hide_behind_a_matching_prefix() {
    let _memory = SmtContext::scoped_thread_term_memory_budget(Some(MEMORY));
    let deadline = Instant::now() + Duration::from_secs(120);
    let _deadline = ScopedSmtDeadline::install_until(deadline);
    let token = CancellationToken::new();
    let source = QuantifiedChcProblem::parse_smtlib(
        "(set-logic HORN)
         (declare-fun uf_range ((_ BitVec 64)) (_ BitVec 1))
         (declare-fun P () Bool)
         (assert (=> (forall ((i (_ BitVec 64)))
            (=> (bvult i (_ bv65 64)) (= (uf_range i) (_ bv1 1)))) P))
         (assert (=> P false)) (check-sat)",
    )
    .unwrap();
    let base = evidence(&source, deadline, &token);
    let mut trace = base
        .concrete_trace(&source, remaining(deadline), &token)
        .unwrap();
    assert!(trace.bindings().is_empty());
    assert_eq!(trace.function_models().len(), 1);
    assert_eq!(trace.replay_obligation().matches("(forall ((").count(), 1);
    assert!(trace.recheck(&source, remaining(deadline), &token));
    trace.functions[0] = capture(
        "(set-logic ALL)\n(declare-fun uf_range ((_ BitVec 64)) (_ BitVec 1))
         (assert (= (uf_range (_ bv0 64)) (_ bv1 1)))
         (assert (= (uf_range (_ bv64 64)) (_ bv0 1))) (check-sat)",
        "uf_range",
        deadline,
        &token,
    );
    let rendered = bound_render(&trace.base, &source, &control(&token)).unwrap();
    let registry = registry(&source, &control(&token)).unwrap();
    trace.pinned_obligation = pins::render(
        &rendered,
        &trace.bindings,
        &trace.functions,
        &source,
        &registry,
        &control(&token),
    )
    .unwrap();
    assert_eq!(trace.replay_obligation().matches("(forall ((").count(), 1);
    assert!(!trace.recheck(&source, remaining(deadline), &token));
    assert!(base.recheck(&source, remaining(deadline), &token));
}
