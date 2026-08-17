// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use crate::combined_solvers::combiner::{
    CrossTheoryEqualityReplay, EufArrayNotifyReplayEdge, EufArrayNotifyReplayState,
};
use ay_arrays::ArrayPropagatedEqualityReplay;
use ay_core::term::{TermId, TermStore};
use ay_core::ExpressionSplitRequest;

mod replay_cache;

fn arrays_check_count(combiner: &TheoryCombiner<'_>) -> u64 {
    arrays_stat(combiner, "arrays_checks")
}

fn arrays_stat(combiner: &TheoryCombiner<'_>, name: &str) -> u64 {
    let arrays = combiner
        .arrays
        .as_ref()
        .expect("test requires array solver");
    arrays
        .collect_statistics()
        .into_iter()
        .find_map(|(stat_name, value)| (stat_name == name).then_some(value))
        .unwrap_or_else(|| panic!("arrays solver should report {name}"))
}

#[test]
fn test_deferred_expression_split_batch_preempts_later_conflict_8785() {
    let mut deferred = Some(TheoryResult::NeedExpressionSplits(vec![
        ExpressionSplitRequest {
            disequality_term: TermId::new(10),
        },
        ExpressionSplitRequest {
            disequality_term: TermId::new(11),
        },
    ]));
    let conflict = TheoryResult::Unsat(vec![TheoryLit::new(TermId::new(12), true)]);

    let selected = take_deferred_before_later_conflict(&mut deferred, &conflict);

    match selected {
        Some(TheoryResult::NeedExpressionSplits(splits)) => {
            assert_eq!(
                splits.len(),
                2,
                "large expression-split batches should reach the SAT split loop before later one-clause conflicts"
            );
        }
        other => panic!("expected deferred expression split batch, got {other:?}"),
    }
    assert!(
        deferred.is_none(),
        "selected deferred batch should be consumed"
    );
}

#[test]
fn test_single_deferred_expression_split_does_not_preempt_later_conflict_8785() {
    let mut deferred = Some(TheoryResult::NeedExpressionSplit(ExpressionSplitRequest {
        disequality_term: TermId::new(20),
    }));
    let conflict = TheoryResult::Unsat(vec![TheoryLit::new(TermId::new(21), true)]);

    assert!(
        take_deferred_before_later_conflict(&mut deferred, &conflict).is_none(),
        "singleton split behavior should preserve the existing conflict-first policy"
    );
    assert!(
        matches!(deferred, Some(TheoryResult::NeedExpressionSplit(_))),
        "non-preempted deferred result should remain latched"
    );
}

#[test]
fn test_check_arrays_step_skips_quiescent_array_solver_6820() {
    use ay_core::term::Symbol;
    use ay_core::ArraySort;

    let mut terms = TermStore::new();
    // Create an array-related literal: (= a b) where a, b : (Array Int Int)
    let arr_sort = Sort::Array(Box::new(ArraySort::new(Sort::Int, Sort::Int)));
    let a = terms.mk_var("a", arr_sort.clone());
    let b = terms.mk_var("b", arr_sort);
    let arr_eq = terms.mk_app(Symbol::named("="), vec![a, b], Sort::Bool);
    // Create a non-array literal: a plain Bool variable
    let bool_lit = terms.mk_var("p", Sort::Bool);
    // Int-sorted equality: (= i j) — feeds array diseq_set via equality_cache
    let i = terms.mk_var("i", Sort::Int);
    let j = terms.mk_var("j", Sort::Int);
    let int_eq = terms.mk_app(Symbol::named("="), vec![i, j], Sort::Bool);

    let mut combiner = TheoryCombiner::auf_lia(&terms);

    assert_eq!(arrays_check_count(&combiner), 0);
    assert!(!combiner
        .check_arrays_step(false, 0)
        .expect("initial empty array step should succeed"));
    assert_eq!(arrays_check_count(&combiner), 1);

    assert!(!combiner
        .check_arrays_step(false, 1)
        .expect("quiescent array step should still succeed"));
    assert_eq!(
        arrays_check_count(&combiner),
        1,
        "second quiescent check must skip redundant arrays.check()"
    );

    // Non-array literal should NOT invalidate quiescence (#6820)
    combiner.assert_literal(bool_lit, true);
    assert!(!combiner
        .check_arrays_step(false, 2)
        .expect("non-array literal should not force re-check"));
    assert_eq!(
        arrays_check_count(&combiner),
        1,
        "non-array literal must not invalidate array quiescence"
    );

    // Array-related literal SHOULD invalidate quiescence
    combiner.assert_literal(arr_eq, true);
    assert!(!combiner
        .check_arrays_step(false, 3)
        .expect("array literal should re-run arrays.check()"));
    assert_eq!(arrays_check_count(&combiner), 2);

    // Int-sorted equality SHOULD invalidate quiescence (e87f539 broadened
    // involves_array to include all =/distinct — index equalities like
    // (= i j) feed the array solver's diseq_set through equality_cache).
    // First, re-establish quiescence.
    assert!(!combiner
        .check_arrays_step(false, 4)
        .expect("post-array quiescent step should succeed"));
    assert_eq!(
        arrays_check_count(&combiner),
        2,
        "should still be quiescent"
    );

    combiner.assert_literal(int_eq, true);
    assert!(!combiner
        .check_arrays_step(false, 5)
        .expect("Int equality should force re-check for diseq_set"));
    assert_eq!(
        arrays_check_count(&combiner),
        3,
        "Int equality must invalidate array quiescence — feeds diseq_set"
    );
}

#[test]
fn test_check_arrays_step_forwards_non_self_evidencing_array_equalities_8785() {
    let mut terms = TermStore::new();
    use ay_core::term::Symbol;

    let u_sort = Sort::Uninterpreted("U".to_string());
    let arr_sort = Sort::array(Sort::Int, Sort::Int);
    let x = terms.mk_var("x", u_sort.clone());
    let y = terms.mk_var("y", u_sort);
    let a = terms.mk_app(Symbol::named("f"), vec![x], arr_sort.clone());
    let b = terms.mk_app(Symbol::named("f"), vec![y], arr_sort);
    let i = terms.mk_var("i", Sort::Int);
    let j = terms.mk_var("j", Sort::Int);
    let v = terms.mk_var("v", Sort::Int);

    let select_a_j = terms.mk_select(a, j);
    let store_b_i_v = terms.mk_store(b, i, v);
    let select_store_b_j = terms.mk_select(store_b_i_v, j);
    let eq_xy = terms.mk_eq(x, y);
    let eq_ij = terms.mk_eq(i, j);
    let eq_sels = terms.mk_eq(select_store_b_j, select_a_j);

    let mut baseline = TheoryCombiner::array_euf(&terms);
    baseline.assert_literal(eq_ij, false);
    baseline.assert_literal(eq_sels, false);
    assert!(matches!(baseline.euf.check(), TheoryResult::Sat));
    assert!(
        !baseline
            .check_arrays_step(false, 0)
            .expect("without shared a=b, arrays should stay quiescent"),
        "without a shared array equality, cross-array ROW2 must not wake"
    );
    assert_eq!(arrays_check_count(&baseline), 1);
    assert!(
        !baseline
            .check_arrays_step(false, 1)
            .expect("quiescent baseline should skip a second array pass"),
        "baseline should remain quiescent without forwarded array equalities"
    );
    assert_eq!(
        arrays_check_count(&baseline),
        1,
        "without EUF-derived a=b, arrays.check() should stay quiescent on the next round"
    );

    let mut combiner = TheoryCombiner::array_euf(&terms);
    combiner.assert_literal(eq_xy, true);
    combiner.assert_literal(eq_ij, false);
    combiner.assert_literal(eq_sels, false);
    assert!(matches!(combiner.euf.check(), TheoryResult::Sat));

    // In the no-arithmetic combiner, check_arrays_step() first runs arrays.check()
    // and then forwards any pending EUF equalities into arrays. Here EUF has
    // derived `a = b` by congruence from `x = y`, so the forwarded equality is
    // independently justified rather than self-evidencing.
    assert!(
        combiner
            .check_arrays_step(false, 0)
            .expect("EUF-derived a=b should cross into arrays"),
        "non-self-evidencing EUF-derived array equality must be forwarded across the combiner boundary"
    );
    assert_eq!(arrays_check_count(&combiner), 1);

    assert!(
        !combiner
            .check_arrays_step(false, 1)
            .expect("forwarded array equality should wake a second array pass"),
        "second array pass should consume the wakeup without discovering more equalities"
    );
    assert_eq!(
        arrays_check_count(&combiner),
        2,
        "forwarded shared a=b must invalidate quiescence and rerun arrays.check()"
    );
}

#[test]
fn test_euf_array_notifications_use_spanning_forest_8785() {
    let mut terms = TermStore::new();
    let arr_sort = Sort::array(Sort::Int, Sort::Int);

    let a = terms.mk_var("a", arr_sort.clone());
    let b = terms.mk_var("b", arr_sort.clone());
    let c = terms.mk_var("c", arr_sort.clone());
    let d = terms.mk_var("d", arr_sort);

    let mut combiner = TheoryCombiner::array_euf(&terms);
    let first_batch = vec![
        DiscoveredEquality::new(a, b, Vec::new()),
        DiscoveredEquality::new(b, c, Vec::new()),
        DiscoveredEquality::new(a, c, Vec::new()),
    ];
    assert_eq!(
        combiner.notify_arrays_of_euf_equalities(&first_batch),
        2,
        "a three-term EUF array component should notify arrays with a spanning tree"
    );
    assert_eq!(
        combiner.notify_arrays_of_euf_equalities(&first_batch),
        0,
        "replayed EUF array equalities in an already-notified component should be skipped"
    );

    let second_batch = vec![
        DiscoveredEquality::new(c, d, Vec::new()),
        DiscoveredEquality::new(a, d, Vec::new()),
    ];
    assert_eq!(
        combiner.notify_arrays_of_euf_equalities(&second_batch),
        1,
        "connecting one fresh array term to an existing component needs one notification"
    );
    assert_eq!(
        combiner.notify_arrays_of_euf_equalities(&second_batch),
        0,
        "second replay of the enlarged component should be skipped"
    );

    combiner.push();
    combiner.pop();
    assert_eq!(
        combiner.notify_arrays_of_euf_equalities(&first_batch),
        2,
        "pop clears the notification cache because array pending state is rebuilt"
    );
}

#[test]
fn test_euf_array_notifications_use_canonical_batch_star_8785() {
    let mut terms = TermStore::new();
    let arr_sort = Sort::array(Sort::Int, Sort::Int);

    let a = terms.mk_var("a", arr_sort.clone());
    let b = terms.mk_var("b", arr_sort.clone());
    let c = terms.mk_var("c", arr_sort.clone());
    let d = terms.mk_var("d", arr_sort);

    let mut combiner = TheoryCombiner::array_euf(&terms);
    let batch = vec![
        DiscoveredEquality::new(b, c, Vec::new()),
        DiscoveredEquality::new(c, d, Vec::new()),
        DiscoveredEquality::new(a, d, Vec::new()),
    ];

    assert_eq!(
        combiner.notify_arrays_of_euf_equalities(&batch),
        3,
        "a four-term EUF array component still needs exactly a spanning tree"
    );
    assert_eq!(
        combiner.euf_array_notify_parent.get(&b),
        Some(&a),
        "batch replay should use the stable minimum term as component root"
    );
    assert_eq!(
        combiner.euf_array_notify_parent.get(&c),
        Some(&a),
        "batch replay should not preserve order-dependent intermediate roots"
    );
    assert_eq!(
        combiner.euf_array_notify_parent.get(&d),
        Some(&a),
        "batch replay should canonicalize every fresh component edge"
    );
    assert_eq!(
        combiner.notify_arrays_of_euf_equalities(&batch),
        0,
        "canonicalized component replay must still suppress warm duplicates"
    );
}

#[test]
fn test_euf_array_notification_replay_requires_current_reasons_8785() {
    let mut terms = TermStore::new();
    let arr_sort = Sort::array(Sort::Int, Sort::Int);

    let a = terms.mk_var("a", arr_sort.clone());
    let b = terms.mk_var("b", arr_sort.clone());
    let c = terms.mk_var("c", arr_sort);
    let guard_ab = terms.mk_var("guard_ab", Sort::Bool);
    let guard_bc = terms.mk_var("guard_bc", Sort::Bool);

    let mut first = TheoryCombiner::array_euf(&terms);
    let batch = vec![
        DiscoveredEquality::new(a, b, vec![TheoryLit::new(guard_ab, true)]),
        DiscoveredEquality::new(b, c, vec![TheoryLit::new(guard_bc, true)]),
    ];
    assert_eq!(first.notify_arrays_of_euf_equalities(&batch), 2);
    let edges = first.export_euf_array_notify_replay_edges();
    assert_eq!(
        edges.len(),
        2,
        "both reason-carrying notification edges should be persistable"
    );

    let mut stale = TheoryCombiner::array_euf(&terms);
    stale.import_euf_array_notify_replay_edges(&edges);
    stale.assert_literal(guard_ab, true);
    stale.assert_literal(guard_bc, false);
    assert_eq!(
        stale.replay_valid_euf_array_notifications(),
        1,
        "only the edge whose full reason is true in the fresh assignment may replay"
    );
    assert_eq!(stale.euf_array_notify_parent.get(&b), Some(&a));
    assert!(
        !stale.euf_array_notify_parent.contains_key(&c),
        "stale reason must not import the old array merge component"
    );

    let mut current = TheoryCombiner::array_euf(&terms);
    current.import_euf_array_notify_replay_edges(&edges);
    current.assert_literal(guard_ab, true);
    current.assert_literal(guard_bc, true);
    assert_eq!(
        current.replay_valid_euf_array_notifications(),
        2,
        "all reason-validated notification edges should replay in a matching assignment"
    );
    assert_eq!(current.euf_array_notify_parent.get(&b), Some(&a));
    assert_eq!(current.euf_array_notify_parent.get(&c), Some(&a));
}

#[test]
fn test_array_equality_replay_requires_current_reasons_8785() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let y = terms.mk_var("y", Sort::Int);
    let guard = terms.mk_var("guard", Sort::Bool);
    let replay = ArrayPropagatedEqualityReplay::new(x, y, vec![TheoryLit::new(guard, true)]);

    let mut stale = TheoryCombiner::array_euf(&terms);
    stale.import_array_equality_replays(std::slice::from_ref(&replay));
    stale.assert_literal(guard, false);
    assert_eq!(
        stale.replay_valid_array_equalities_to_euf(),
        0,
        "stale reasons must not replay old array-derived equalities"
    );
    assert!(
        stale.export_array_sent_equality_replays().is_empty(),
        "stale equality replay must not seed array propagation dedup state"
    );

    let mut current = TheoryCombiner::array_euf(&terms);
    current.import_array_equality_replays(std::slice::from_ref(&replay));
    current.assert_literal(guard, true);
    assert_eq!(
        current.replay_valid_array_equalities_to_euf(),
        1,
        "current reasons should replay one array-derived equality"
    );
    assert!(matches!(
        TheorySolver::check(&mut current.euf),
        TheoryResult::Sat
    ));
    assert!(
        current.euf.are_equal(x, y),
        "replayed array equality should be imported into EUF"
    );
    assert!(
        current
            .export_array_sent_equality_replays()
            .contains(&replay),
        "replayed equality should seed array propagation dedup state"
    );
}

#[test]
fn test_reasonless_array_equality_replay_is_unconditional_8785() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let y = terms.mk_var("y", Sort::Int);
    let replay = ArrayPropagatedEqualityReplay::new(x, y, Vec::new());

    let mut current = TheoryCombiner::array_euf(&terms);
    current.import_array_equality_replays(std::slice::from_ref(&replay));
    assert_eq!(
        current.replay_valid_array_equalities_to_euf(),
        1,
        "reasonless array-derived equalities are unconditional and should replay"
    );
    assert!(matches!(
        TheorySolver::check(&mut current.euf),
        TheoryResult::Sat
    ));
    assert!(
        current.euf.are_equal(x, y),
        "unconditional replay should be imported into EUF"
    );
    assert!(
        current
            .export_array_sent_equality_replays()
            .contains(&replay),
        "unconditional replay should seed array propagation dedup state"
    );
}

#[test]
fn test_export_array_equality_replays_includes_array_solver_sent_replays_8785() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let y = terms.mk_var("y", Sort::Int);
    let guard = terms.mk_var("guard", Sort::Bool);
    let replay = ArrayPropagatedEqualityReplay::new(x, y, vec![TheoryLit::new(guard, true)]);

    let mut sent = ay_core::kani_compat::DetHashSet::default();
    sent.insert(replay.clone());

    let mut combiner = TheoryCombiner::array_euf(&terms);
    combiner.import_array_sent_equality_replays(&sent);
    combiner.assert_literal(guard, true);

    let exported = combiner.export_array_equality_replays();
    assert!(
        exported.contains(&replay),
        "combiner export must include array solver sent replays from direct propagation paths"
    );

    let mut persisted = Vec::new();
    assert_eq!(
        combiner.append_current_array_equality_replays(&mut persisted),
        1,
        "append should see the array solver sent replay as exportable"
    );
    assert_eq!(persisted, vec![replay]);
}

#[test]
fn test_imported_array_equality_replay_survives_soft_reset_and_revalidates_8785() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let y = terms.mk_var("y", Sort::Int);
    let guard = terms.mk_var("guard", Sort::Bool);
    let replay = ArrayPropagatedEqualityReplay::new(x, y, vec![TheoryLit::new(guard, true)]);

    let mut current = TheoryCombiner::array_euf(&terms);
    current.import_array_equality_replays(std::slice::from_ref(&replay));
    current.soft_reset();
    current.assert_literal(guard, true);
    assert_eq!(
        current.replay_valid_array_equalities_to_euf(),
        1,
        "extension soft reset must preserve imported array equality replays for fresh validation"
    );
    assert!(matches!(
        TheorySolver::check(&mut current.euf),
        TheoryResult::Sat
    ));
    assert!(
        current.euf.are_equal(x, y),
        "freshly valid replay should be imported into EUF after soft reset"
    );
    assert!(
        current
            .export_array_sent_equality_replays()
            .contains(&replay),
        "freshly valid replay should reseed the array propagation dedup state"
    );

    let mut stale = TheoryCombiner::array_euf(&terms);
    stale.import_array_equality_replays(std::slice::from_ref(&replay));
    stale.soft_reset();
    stale.assert_literal(guard, false);
    assert_eq!(
        stale.replay_valid_array_equalities_to_euf(),
        0,
        "soft reset must revalidate imported array equality replay reasons against the fresh assignment"
    );
    assert!(
        stale.export_array_sent_equality_replays().is_empty(),
        "stale replay must not reseed array propagation dedup state after soft reset"
    );
}

#[test]
fn test_cross_theory_equality_replay_requires_current_reasons_8785() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let y = terms.mk_var("y", Sort::Int);
    let guard = terms.mk_var("guard", Sort::Bool);
    let replay = CrossTheoryEqualityReplay::new(x, y, vec![TheoryLit::new(guard, true)]);

    let mut stale = TheoryCombiner::uf_lia(&terms);
    stale.import_cross_theory_equality_replays(std::slice::from_ref(&replay));
    stale.assert_literal(guard, false);
    assert_eq!(
        stale.replay_valid_cross_theory_equalities(),
        0,
        "stale reasons must not replay old cross-theory equalities"
    );
    assert!(
        stale.export_cross_theory_equality_replays().is_empty(),
        "stale cross-theory replay must not be persisted locally"
    );

    let mut current = TheoryCombiner::uf_lia(&terms);
    current.import_cross_theory_equality_replays(std::slice::from_ref(&replay));
    current.assert_literal(guard, true);
    assert_eq!(
        current.replay_valid_cross_theory_equalities(),
        1,
        "current reasons should replay one cross-theory equality"
    );
    assert!(matches!(
        TheorySolver::check(&mut current.euf),
        TheoryResult::Sat
    ));
    assert!(
        current.euf.are_equal(x, y),
        "replayed cross-theory equality should seed EUF before N-O rediscovery"
    );
    assert!(
        current
            .export_cross_theory_equality_replays()
            .contains(&replay),
        "valid replay should persist locally for the next fresh combiner"
    );
}

#[test]
fn test_cross_theory_equality_replay_prunes_reason_supersets_8785() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let y = terms.mk_var("y", Sort::Int);
    let guard_a = terms.mk_var("guard_a", Sort::Bool);
    let guard_b = terms.mk_var("guard_b", Sort::Bool);
    let short = CrossTheoryEqualityReplay::new(x, y, vec![TheoryLit::new(guard_a, true)]);
    let redundant = CrossTheoryEqualityReplay::new(
        x,
        y,
        vec![TheoryLit::new(guard_a, true), TheoryLit::new(guard_b, true)],
    );

    let mut combiner = TheoryCombiner::uf_lia(&terms);
    combiner.assert_literal(guard_a, true);
    combiner.assert_literal(guard_b, true);
    combiner.record_cross_theory_equalities(&[DiscoveredEquality::new(
        x,
        y,
        redundant.reason.clone(),
    )]);
    combiner.record_cross_theory_equalities(&[DiscoveredEquality::new(x, y, short.reason.clone())]);

    assert_eq!(
        combiner.export_cross_theory_equality_replays(),
        vec![short.clone()],
        "the reason-minimal replay covers same-pair reason supersets"
    );

    let mut persisted = vec![redundant];
    combiner.prune_current_cross_theory_equality_replays(&mut persisted);
    combiner.append_current_cross_theory_equality_replays(&mut persisted);
    assert_eq!(
        persisted,
        vec![short],
        "persistent cross-theory replay state should keep one reason-minimal proof per pair"
    );
}

#[test]
fn test_cross_theory_equality_replay_prunes_transitive_complete_graph_8785() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::Int);
    let b = terms.mk_var("b", Sort::Int);
    let c = terms.mk_var("c", Sort::Int);
    let d = terms.mk_var("d", Sort::Int);
    let guard = terms.mk_var("guard", Sort::Bool);
    let reason = vec![TheoryLit::new(guard, true)];
    let mut persisted = vec![
        CrossTheoryEqualityReplay::new(a, b, reason.clone()),
        CrossTheoryEqualityReplay::new(a, c, reason.clone()),
        CrossTheoryEqualityReplay::new(a, d, reason.clone()),
        CrossTheoryEqualityReplay::new(b, c, reason.clone()),
        CrossTheoryEqualityReplay::new(b, d, reason.clone()),
        CrossTheoryEqualityReplay::new(c, d, reason),
    ];

    let mut combiner = TheoryCombiner::uf_lia(&terms);
    combiner.assert_literal(guard, true);
    combiner.prune_current_cross_theory_equality_replays(&mut persisted);

    assert_eq!(
        persisted.len(),
        3,
        "four equivalent terms need only a reason-covered spanning tree, not a complete graph"
    );
    assert_eq!(
        persisted,
        vec![
            CrossTheoryEqualityReplay::new(a, b, vec![TheoryLit::new(guard, true)]),
            CrossTheoryEqualityReplay::new(a, c, vec![TheoryLit::new(guard, true)]),
            CrossTheoryEqualityReplay::new(a, d, vec![TheoryLit::new(guard, true)]),
        ]
    );
}

#[test]
fn test_reasonless_cross_theory_store_congruence_records_current_arg_reasons_8785() {
    let mut terms = TermStore::new();
    let arr_sort = Sort::array(Sort::Int, Sort::Int);

    let a = terms.mk_var("a", arr_sort);
    let i = terms.mk_var("i", Sort::Int);
    let j = terms.mk_var("j", Sort::Int);
    let v = terms.mk_var("v", Sort::Int);
    let w = terms.mk_var("w", Sort::Int);
    let store_i_v = terms.mk_store(a, i, v);
    let store_j_w = terms.mk_store(a, j, w);
    let eq_ij = terms.mk_eq(i, j);
    let eq_vw = terms.mk_eq(v, w);

    let mut combiner = TheoryCombiner::auf_lia(&terms);
    combiner.assert_literal(eq_ij, true);
    combiner.assert_literal(eq_vw, true);
    combiner.record_cross_theory_equalities(&[DiscoveredEquality::new(
        store_i_v,
        store_j_w,
        Vec::new(),
    )]);

    let replays = combiner.export_cross_theory_equality_replays();
    assert_eq!(replays.len(), 1);
    assert_eq!(
        replays[0].reason,
        vec![TheoryLit::new(eq_ij, true), TheoryLit::new(eq_vw, true)],
        "reasonless structural congruence should persist with current SAT-visible argument equalities"
    );
}

#[test]
fn test_array_equality_replay_persistence_prunes_stale_reasons_8785() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let y = terms.mk_var("y", Sort::Int);
    let z = terms.mk_var("z", Sort::Int);
    let live_guard = terms.mk_var("live_guard", Sort::Bool);
    let stale_guard = terms.mk_var("stale_guard", Sort::Bool);
    let live = ArrayPropagatedEqualityReplay::new(x, y, vec![TheoryLit::new(live_guard, true)]);
    let stale = ArrayPropagatedEqualityReplay::new(y, z, vec![TheoryLit::new(stale_guard, true)]);
    let mut persisted = vec![stale.clone(), live.clone()];

    let mut combiner = TheoryCombiner::array_euf(&terms);
    combiner.assert_literal(live_guard, true);
    combiner.assert_literal(stale_guard, false);
    combiner.prune_current_array_equality_replays(&mut persisted);

    // Array equality replay pruning currently only drops stale or exact
    // duplicate entries; same-pair reason-superset pruning is supported for
    // EUF->array notification paths below, but not for these replay records.
    assert_eq!(persisted, vec![live]);
    assert!(
        !persisted.contains(&stale),
        "stale array equality replays must not persist into the next fresh solver"
    );
}

#[test]
fn test_euf_array_notification_persistence_prunes_reason_subset_paths_8785() {
    let mut terms = TermStore::new();
    let arr_sort = Sort::array(Sort::Int, Sort::Int);

    let a = terms.mk_var("a", arr_sort.clone());
    let b = terms.mk_var("b", arr_sort.clone());
    let c = terms.mk_var("c", arr_sort);
    let guard_ab = terms.mk_var("guard_ab", Sort::Bool);
    let guard_bc = terms.mk_var("guard_bc", Sort::Bool);
    let guard_ac = terms.mk_var("guard_ac", Sort::Bool);

    let edge_ab = EufArrayNotifyReplayEdge::new(a, b, vec![TheoryLit::new(guard_ab, true)]);
    let edge_bc = EufArrayNotifyReplayEdge::new(b, c, vec![TheoryLit::new(guard_bc, true)]);
    let redundant_ac = EufArrayNotifyReplayEdge::new(
        a,
        c,
        vec![
            TheoryLit::new(guard_ab, true),
            TheoryLit::new(guard_bc, true),
            TheoryLit::new(guard_ac, true),
        ],
    );

    assert!(
        TheoryCombiner::euf_array_notify_replay_edge_covered_by(
            &[edge_ab.clone(), edge_bc.clone()],
            &redundant_ac,
        ),
        "a path whose reasons are subsets of the candidate reason makes the candidate redundant"
    );

    let missing_reason_candidate = EufArrayNotifyReplayEdge::new(
        a,
        c,
        vec![
            TheoryLit::new(guard_ab, true),
            TheoryLit::new(guard_ac, true),
        ],
    );
    assert!(
        !TheoryCombiner::euf_array_notify_replay_edge_covered_by(
            &[edge_ab, edge_bc],
            &missing_reason_candidate,
        ),
        "an existing path guarded by a reason absent from the candidate must not cover it"
    );

    let self_edge = EufArrayNotifyReplayEdge::new(a, a, vec![TheoryLit::new(guard_ab, true)]);
    assert!(
        TheoryCombiner::euf_array_notify_replay_edge_covered_by(&[], &self_edge),
        "self-edges are always redundant"
    );
}

#[test]
fn test_euf_array_notification_export_prunes_current_paths_8785() {
    let mut terms = TermStore::new();
    let arr_sort = Sort::array(Sort::Int, Sort::Int);

    let a = terms.mk_var("a", arr_sort.clone());
    let b = terms.mk_var("b", arr_sort.clone());
    let c = terms.mk_var("c", arr_sort);
    let guard_ab = terms.mk_var("guard_ab", Sort::Bool);
    let guard_bc = terms.mk_var("guard_bc", Sort::Bool);
    let guard_ac = terms.mk_var("guard_ac", Sort::Bool);
    let stale_guard = terms.mk_var("stale_guard", Sort::Bool);

    let edge_ab = EufArrayNotifyReplayEdge::new(a, b, vec![TheoryLit::new(guard_ab, true)]);
    let edge_bc = EufArrayNotifyReplayEdge::new(b, c, vec![TheoryLit::new(guard_bc, true)]);
    let redundant_ac = EufArrayNotifyReplayEdge::new(
        a,
        c,
        vec![
            TheoryLit::new(guard_ab, true),
            TheoryLit::new(guard_bc, true),
            TheoryLit::new(guard_ac, true),
        ],
    );
    let stale_edge = EufArrayNotifyReplayEdge::new(a, c, vec![TheoryLit::new(stale_guard, true)]);

    let mut combiner = TheoryCombiner::array_euf(&terms);
    combiner.assert_literal(guard_ab, true);
    combiner.assert_literal(guard_bc, true);
    combiner.assert_literal(guard_ac, true);

    let mut persistent_edges = EufArrayNotifyReplayState::from_edges(&[
        redundant_ac.clone(),
        stale_edge,
        edge_bc.clone(),
        edge_ab.clone(),
        // Exact duplicate: must be dropped by the hash dedup.
        edge_ab.clone(),
    ]);
    combiner.prune_current_euf_array_notify_replay_edges(&mut persistent_edges);

    // #no-replay-quadratic M2 (superset retention): pruning drops edges whose
    // reasons no longer hold and exact duplicates, but intentionally KEEPS
    // reason-superset (covered) edges such as `redundant_ac` — replaying a
    // redundant true edge is a no-op union-find merge, while the covered-by
    // BFS that used to drop it was 100% of solver samples on cs_lazy.i_6.
    // Output is sorted by (reason length, target, source).
    assert_eq!(
        persistent_edges.to_edges(),
        vec![edge_ab, edge_bc, redundant_ac],
        "AUFLIA/ArrayEUF export should retain currently-valid replay edges (including covered ones) and drop stale or duplicate edges"
    );
}

#[test]
fn test_direct_array_assignment_seeds_euf_array_notify_parent_8785() {
    let mut terms = TermStore::new();
    let arr_sort = Sort::array(Sort::Int, Sort::Int);

    let a = terms.mk_var("a", arr_sort.clone());
    let b = terms.mk_var("b", arr_sort);
    let eq_ab = terms.mk_eq(a, b);

    let mut first = TheoryCombiner::array_euf(&terms);
    first.assert_literal(eq_ab, true);
    assert_eq!(
        first.euf_array_notify_parent.get(&b),
        Some(&a),
        "a direct SAT-assigned array equality should seed the combiner notification forest"
    );
    assert_eq!(
        first.notify_arrays_of_euf_equalities(&[DiscoveredEquality::new(a, b, Vec::new())]),
        0,
        "a later reasonless EUF replay of the same direct equality should be suppressed"
    );

    let edges = first.export_euf_array_notify_replay_edges();
    assert_eq!(edges.len(), 1);
    assert_eq!(edges[0].reason, vec![TheoryLit::new(eq_ab, true)]);

    let mut stale = TheoryCombiner::array_euf(&terms);
    stale.import_euf_array_notify_replay_edges(&edges);
    stale.assert_literal(eq_ab, false);
    assert_eq!(
        stale.replay_valid_euf_array_notifications(),
        0,
        "a persisted direct edge must not replay when the equality atom is false"
    );
    assert!(
        !stale.euf_array_notify_parent.contains_key(&b),
        "false direct equality must not import the old notification forest edge"
    );

    let mut current = TheoryCombiner::array_euf(&terms);
    current.import_euf_array_notify_replay_edges(&edges);
    current.assert_literal(eq_ab, true);
    assert_eq!(
        current.replay_valid_euf_array_notifications(),
        0,
        "the fresh direct assignment already materializes the notification edge before replay"
    );
    assert_eq!(current.euf_array_notify_parent.get(&b), Some(&a));
}

#[test]
fn test_reasonless_store_congruence_replay_uses_current_arg_equalities_8785() {
    let mut terms = TermStore::new();
    let arr_sort = Sort::array(Sort::Int, Sort::Int);

    let a = terms.mk_var("a", arr_sort);
    let i = terms.mk_var("i", Sort::Int);
    let j = terms.mk_var("j", Sort::Int);
    let v = terms.mk_var("v", Sort::Int);
    let w = terms.mk_var("w", Sort::Int);
    let store_i_v = terms.mk_store(a, i, v);
    let store_j_w = terms.mk_store(a, j, w);
    let eq_ij = terms.mk_eq(i, j);
    let eq_vw = terms.mk_eq(v, w);

    let mut first = TheoryCombiner::array_euf(&terms);
    first.assert_literal(eq_ij, true);
    first.assert_literal(eq_vw, true);
    assert_eq!(
        first.notify_arrays_of_euf_equalities(&[DiscoveredEquality::new(
            store_i_v,
            store_j_w,
            Vec::new(),
        )]),
        1,
        "reasonless store congruence should still notify arrays once"
    );

    let edges = first.export_euf_array_notify_replay_edges();
    assert_eq!(edges.len(), 1);
    assert_eq!(
        edges[0].reason,
        vec![TheoryLit::new(eq_ij, true), TheoryLit::new(eq_vw, true)],
        "the replay key should be the current SAT-visible store argument equalities"
    );

    let mut stale = TheoryCombiner::array_euf(&terms);
    stale.import_euf_array_notify_replay_edges(&edges);
    stale.assert_literal(eq_ij, true);
    stale.assert_literal(eq_vw, false);
    assert_eq!(
        stale.replay_valid_euf_array_notifications(),
        0,
        "stale argument equality must not replay the old store notification"
    );
    assert!(
        !stale.euf_array_notify_parent.contains_key(&store_j_w),
        "invalid replay must not import the old notification forest edge"
    );

    let mut current = TheoryCombiner::array_euf(&terms);
    current.import_euf_array_notify_replay_edges(&edges);
    current.assert_literal(eq_ij, true);
    current.assert_literal(eq_vw, true);
    assert_eq!(
        current.replay_valid_euf_array_notifications(),
        1,
        "matching argument equalities should replay the store notification"
    );
    assert_eq!(
        current.euf_array_notify_parent.get(&store_j_w),
        Some(&store_i_v)
    );
}

#[test]
fn test_reasoned_euf_array_notification_replays_after_pop_8785() {
    let mut terms = TermStore::new();
    let arr_sort = Sort::array(Sort::Int, Sort::Int);

    let a = terms.mk_var("a", arr_sort.clone());
    let b = terms.mk_var("b", arr_sort.clone());
    let c = terms.mk_var("c", arr_sort);
    let guard = terms.mk_var("guard", Sort::Bool);

    let mut current_reason = TheoryCombiner::array_euf(&terms);
    current_reason.assert_literal(guard, true);
    assert_eq!(
        current_reason.notify_arrays_of_euf_equalities(&[DiscoveredEquality::new(
            a,
            b,
            vec![TheoryLit::new(guard, true)],
        )]),
        1
    );
    current_reason.push();
    current_reason.pop();
    assert!(
        !current_reason.euf_array_notify_parent.contains_key(&b),
        "pop should still rebuild the in-memory notification forest"
    );
    assert_eq!(
        current_reason.replay_valid_euf_array_notifications(),
        1,
        "a reason-carrying notification may replay after pop when its reason remains true"
    );
    assert_eq!(current_reason.euf_array_notify_parent.get(&b), Some(&a));

    let mut stale_reason = TheoryCombiner::array_euf(&terms);
    stale_reason.push();
    stale_reason.assert_literal(guard, true);
    assert_eq!(
        stale_reason.notify_arrays_of_euf_equalities(&[DiscoveredEquality::new(
            a,
            c,
            vec![TheoryLit::new(guard, true)],
        )]),
        1
    );
    stale_reason.pop();
    assert_eq!(
        stale_reason.replay_valid_euf_array_notifications(),
        0,
        "a notification whose reason was popped must not replay"
    );
    assert!(
        !stale_reason.euf_array_notify_parent.contains_key(&c),
        "stale reason must not rebuild the old notification forest edge"
    );
}

#[test]
fn test_imported_reasoned_euf_array_notification_survives_soft_reset_8785() {
    replay_cache::assert_imported_replay_survives_soft_reset();
}

#[test]
fn test_group_activation_permutation_preserves_replay_connectivity() {
    replay_cache::assert_group_activation_permutation_preserves_connectivity();
}
