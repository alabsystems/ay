// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Stage-specific assertions preserve the original native admission conditions.

use super::*;
use ntest::timeout;

#[path = "stages/native.rs"]
mod native;

const WALL: Duration = Duration::from_secs(20);
const TERMS: usize = 128 * 1024 * 1024;
const STALE: &str =
    include_str!("../../../../complete_solve/tests/range_write_refutes_stale_lane_1.smt2");

fn validate_pins(
    pinned: &str,
    rendered: &render::CompleteRendered<'_>,
    end: Instant,
    memory: Option<usize>,
    token: &CancellationToken,
    owner: &SourceControl<'_>,
) {
    assert!(
        pinned.contains("(forall "),
        "canonical original universal premise retained"
    );
    for span in &rendered.assertions {
        assert!(
            pinned.contains(&rendered.original.obligation[span.clone()]),
            "stage original payload was omitted"
        );
    }
    let checked = native::accepted(
        "full-original-and-all-pins",
        pinned,
        end,
        memory,
        token,
        owner,
    );
    drop(checked);
    owner
        .poll()
        .expect("stage full pinned native check after native cleanup");
}

fn staged(text: &str) {
    let end = Instant::now() + WALL;
    let token = CancellationToken::new();
    let _wall = ScopedSmtDeadline::install_until(end);
    let context = SmtContext::new();
    let memory = solve::tighter_budget(context.term_memory_budget, Some(TERMS));
    drop(context);
    let _memory = SmtContext::scoped_thread_term_memory_budget(memory);
    let owner = SourceControl::new(end, &token);
    owner
        .bytes(text.len().checked_mul(2).unwrap())
        .expect("source copy admission");
    let problem = QuantifiedChcProblem::parse_smtlib(text).expect("stage source parse");
    let indices = [0, 1];
    let edges = [vec![], vec![0]];
    let rendered = render::render_complete(&problem, &indices, &edges, &owner)
        .expect("stage canonical full-source rendering");
    let advice = render::render_advice(&problem, &indices, &edges, &owner)
        .expect("stage equivalent advice rendering");
    let registry = registry(&problem, &owner).expect("stage source registry");
    let (names, function_names) =
        requests(&rendered.original, &problem, &owner).expect("stage exact original-name requests");
    assert!(
        function_names.is_empty(),
        "these exact two sources declare no scalar functions"
    );
    owner
        .bytes(24 * 1024 * 1024)
        .expect("same complete-batch source allowance");
    let solver = native::accepted("advice-native-model", &advice, end, memory, &token, &owner);
    let model = solver
        .try_get_named_values_complete(&names)
        .unwrap_or_else(|error| panic!("stage complete same-model batch refused: {error:?}"));
    assert_eq!(
        model.len(),
        rendered.original.bindings.len(),
        "stage complete batch census"
    );
    drop((solver, names, function_names));
    owner
        .poll()
        .expect("stage complete batch after native and request cleanup");
    let bindings = complete_bindings(&rendered.original, model, &registry, &owner)
        .expect("stage complete sort/source binding conversion");
    let pinned = pins::render(&rendered, &bindings, &[], &problem, &registry, &owner)
        .expect("stage all-array topology and full original pin rendering");
    validate_pins(&pinned, &rendered, end, memory, &token, &owner);
    // The real production factory, not a test-only unchecked constructor, must
    // repeat acquisition and full original validation on this SAME owner/end.
    let topology = derivation::fingerprint(&indices, &edges, &owner)
        .expect("stage original topology fingerprint");
    owner
        .bytes(4 * std::mem::size_of::<usize>() + 2 * std::mem::size_of::<Vec<usize>>())
        .expect("stage retained derivation copy admission");
    let derivation = derivation::Derivation {
        clause_indices: indices.to_vec(),
        premise_steps: edges.to_vec(),
    };
    drop((bindings, pinned, advice, rendered, registry));
    owner
        .poll()
        .expect("stage scratch cleanup before sealed Unsafe factory");
    let trace = QuantifiedChcCompleteTrace::from_discovery(
        &problem, derivation, topology, end, memory, &token, &owner,
    )
    .expect("stage production sealed complete Unsafe factory refused");
    assert_eq!(trace.source_smtlib(), problem.source_smtlib());
    assert_eq!(trace.clause_indices(), &indices);
    assert_eq!(trace.premise_steps(), &edges);
    assert!(trace.replay_obligation().contains("(forall "));
    drop((trace, problem));
    owner
        .poll()
        .expect("stage final admission after all result/source scratch cleanup");
    assert!(
        Instant::now() < end,
        "one original 20-second end, never renewed per stage"
    );
}

#[test]
#[timeout(30000)]
fn uniform_bv8_complete_unsafe_identifies_first_refused_native_stage() {
    staged(
        "(set-logic HORN)
      (declare-fun Filled ((Array (_ BitVec 64) (_ BitVec 8))) Bool)
      (assert (forall ((w (Array (_ BitVec 64) (_ BitVec 8))))
        (=> (forall ((i (_ BitVec 64))) (= (select w i) #x09)) (Filled w))))
      (assert (forall ((w (Array (_ BitVec 64) (_ BitVec 8))))
        (=> (and (Filled w) (= (select w #xffffffffffffffff) #x09)) false)))
      (check-sat)",
    );
}

#[test]
#[timeout(30000)]
fn original_copy_complete_unsafe_identifies_first_refused_native_stage() {
    staged(STALE);
}
