// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use crate::incremental_state::IncrementalSubsystem;

#[test]
fn test_quantifier_manager_creation() {
    let qm = QuantifierManager::new();
    assert_eq!(qm.round(), 0);
    assert!(!qm.has_deferred());
}

#[test]
fn test_quantifier_manager_round_increments() {
    let mut qm = QuantifierManager::new();
    let mut terms = TermStore::new();

    // Empty assertions - just verify round counter
    let _result = qm.run_ematching_round(&mut terms, &[], None, &|| false);
    assert_eq!(qm.round(), 1);

    let _result = qm.run_ematching_round(&mut terms, &[], None, &|| false);
    assert_eq!(qm.round(), 2);
}

#[test]
fn test_generation_tracker_persists() {
    use ay_core::term::Symbol;
    use ay_core::Sort;
    use num_bigint::BigInt;

    let mut qm = QuantifierManager::new();
    let mut terms = TermStore::new();

    // Create: forall x. P(x)
    // We use a simple pattern: forall x. P(x) which matches P(c) for any ground c
    let x = terms.mk_var("x", Sort::Int);
    let p_sym = Symbol::named("P");
    let px = terms.mk_app(p_sym.clone(), vec![x], Sort::Bool);
    let forall = terms.mk_forall(vec![("x".to_string(), Sort::Int)], px);

    // Create ground term P(1)
    let c1 = terms.mk_int(BigInt::from(1));
    let p1 = terms.mk_app(p_sym, vec![c1], Sort::Bool);

    // First round
    let assertions = vec![forall, p1];
    let _result1 = qm.run_ematching_round(&mut terms, &assertions, None, &|| false);

    // E-matching on `forall x. P(x)` with pattern P(x) should instantiate P(1)
    // However, the instantiation is the body P(1), and P(1) is already in assertions
    // The key thing is that the tracker's round counter advances
    assert_eq!(qm.round(), 1);

    // Second round with same assertions
    let _result2 = qm.run_ematching_round(&mut terms, &assertions, None, &|| false);

    // Generation tracker should persist - round counter should advance
    assert_eq!(qm.round(), 2);

    // Verify the tracker's current_round reflects multiple rounds
    assert_eq!(qm.generation_tracker().current_round(), 2);
}

#[test]
fn test_clear_resets_state() {
    let mut qm = QuantifierManager::new();
    let mut terms = TermStore::new();

    let _result = qm.run_ematching_round(&mut terms, &[], None, &|| false);
    assert_eq!(qm.round(), 1);

    qm.clear();

    assert_eq!(qm.round(), 0);
    assert!(!qm.has_deferred());
}

#[test]
fn test_push_pop_restores_state() {
    let mut qm = QuantifierManager::new();
    let mut terms = TermStore::new();

    // Run a round at the base scope
    let _result = qm.run_ematching_round(&mut terms, &[], None, &|| false);
    assert_eq!(qm.round(), 1);

    // Push and run another round in inner scope
    qm.push();
    let _result = qm.run_ematching_round(&mut terms, &[], None, &|| false);
    assert_eq!(qm.round(), 2);

    // Pop should restore the round counter and generation tracker
    qm.pop();
    assert_eq!(qm.round(), 1);
}

#[test]
fn test_reset_clears_scope_stack() {
    let mut qm = QuantifierManager::new();

    qm.push();
    qm.push();
    qm.reset();

    assert_eq!(qm.round(), 0);
    assert!(!qm.has_deferred());
    // Pop after reset should be a no-op (empty stack)
    qm.pop();
    assert_eq!(qm.round(), 0);
}

/// Helper: build `forall x. P(x)` (pattern P(x)) and a ground `P(n)`.
#[cfg(test)]
fn forall_px_and_ground(terms: &mut TermStore, n: i64) -> (TermId, TermId, TermId) {
    use ay_core::term::Symbol;
    use ay_core::Sort;
    use num_bigint::BigInt;

    let x = terms.mk_var("x", Sort::Int);
    let p_sym = Symbol::named("P");
    let px = terms.mk_app(p_sym.clone(), vec![x], Sort::Bool);
    let forall = terms.mk_forall(vec![("x".to_string(), Sort::Int)], px);
    let cn = terms.mk_int(BigInt::from(n));
    let pn = terms.mk_app(p_sym, vec![cn], Sort::Bool);
    (forall, pn, cn)
}

/// LI-3 (scope-pop truncation, the false-result canary): a (quant,binding)
/// produced ONLY inside a pushed scope must be FULLY forgotten on pop (from both
/// `seen` and `seen_order`), so a sibling/parent scope re-derives it. A stale
/// seen across pop is the only false-UNSAT/false-SAT vector.
#[test]
fn test_seen_truncated_on_pop_and_reproduced() {
    let mut qm = QuantifierManager::new();
    let mut terms = TermStore::new();

    let (forall, p1, _c1) = forall_px_and_ground(&mut terms, 1);

    // Base scope: forall x. P(x) + P(1). One round instantiates (forall, [1]).
    qm.begin_epoch();
    let assertions_base = vec![forall, p1];
    let _r = qm.run_ematching_round(&mut terms, &assertions_base, None, &|| false);
    assert_eq!(qm.seen_len(), 1, "base round should record one seen key");
    assert_eq!(qm.seen_order_len(), 1, "seen/seen_order must be 1:1");

    // Push, add P(2), run an inner round instantiating (forall, [2]).
    qm.push();
    let p_sym = ay_core::term::Symbol::named("P");
    let c2 = terms.mk_int(num_bigint::BigInt::from(2));
    let p2 = terms.mk_app(p_sym, vec![c2], ay_core::Sort::Bool);
    let assertions_inner = vec![forall, p1, p2];
    let _r = qm.run_ematching_round(&mut terms, &assertions_inner, None, &|| false);
    assert_eq!(
        qm.seen_len(),
        2,
        "inner round should add the (forall,[2]) key"
    );
    assert_eq!(qm.seen_order_len(), 2, "seen/seen_order must stay 1:1");

    // Pop: the inner (forall,[2]) key must be FULLY forgotten.
    assert!(qm.pop());
    assert_eq!(
        qm.seen_len(),
        1,
        "pop must drain the inner-scope seen key (LI-3)"
    );
    assert_eq!(
        qm.seen_order_len(),
        1,
        "seen/seen_order must stay 1:1 after pop"
    );

    // Re-running the inner round must RE-PRODUCE (forall,[2]) — proving no stale
    // suppression survived the pop.
    let r = qm.run_ematching_round(&mut terms, &assertions_inner, None, &|| false);
    assert!(
        r.instantiations.iter().any(|&t| t == p2) || qm.seen_len() == 2,
        "the popped (forall,[2]) instance must be re-derivable after pop"
    );
    assert_eq!(
        qm.seen_len(),
        2,
        "re-running the inner round re-records the key"
    );
    assert_eq!(qm.seen_order_len(), 2);
}

/// LI-4 (epoch reset): two `begin_epoch` cycles over the same forall (simulating
/// two check-sats with `restore_assertions` retracting instances between them)
/// must RE-INSTANTIATE — the seen memo from epoch #1 must not suppress epoch #2.
#[test]
fn test_seen_reset_across_epoch() {
    let mut qm = QuantifierManager::new();
    let mut terms = TermStore::new();
    let (forall, p1, _c1) = forall_px_and_ground(&mut terms, 1);
    let assertions = vec![forall, p1];

    // Epoch #1.
    qm.begin_epoch();
    let _r1 = qm.run_ematching_round(&mut terms, &assertions, None, &|| false);
    assert_eq!(qm.seen_len(), 1);

    // Epoch #2: begin_epoch drains the base-scope seen back to baseline (0 at base
    // scope), so the instance is re-instantiable.
    qm.begin_epoch();
    assert_eq!(
        qm.seen_len(),
        0,
        "begin_epoch at base scope must drain the seen memo (LI-4)"
    );
    let r2 = qm.run_ematching_round(&mut terms, &assertions, None, &|| false);
    assert!(
        r2.instantiations.iter().any(|&t| t == p1) || qm.seen_len() == 1,
        "epoch #2 must re-derive (forall,[1]) after the epoch drain"
    );
    assert_eq!(qm.seen_len(), 1);
}

/// LI-5 (has_uninstantiated flag does NOT flip on a cross-round seen hit). A
/// quantifier with exactly one binding is instantiated in round 1; in round 2
/// over the same assertions the persistent seen suppresses the duplicate WORK,
/// but the quantifier must STILL be reported instantiated (not in
/// uninstantiated_quantifiers). Without the move-insert-before-gate guard this
/// fails, proving it load-bearing for the conservative Unknown firewall.
#[test]
fn test_uninstantiated_flag_stable_across_rounds() {
    let mut qm = QuantifierManager::new();
    let mut terms = TermStore::new();
    let (forall, p1, _c1) = forall_px_and_ground(&mut terms, 1);
    let assertions = vec![forall, p1];

    qm.begin_epoch();
    let r1 = qm.run_ematching_round(&mut terms, &assertions, None, &|| false);
    assert!(
        !r1.uninstantiated_quantifiers.contains(&forall),
        "round 1: the forall is instantiated"
    );
    assert!(!r1.has_uninstantiated, "round 1: nothing uninstantiated");

    // Round 2 over the SAME assertions: the (forall,[1]) binding is now in the
    // persistent seen, so its WORK is skipped — but the flag must NOT flip.
    let r2 = qm.run_ematching_round(&mut terms, &assertions, None, &|| false);
    assert!(
        !r2.uninstantiated_quantifiers.contains(&forall),
        "LI-5: a cross-round seen hit must NOT mark the forall uninstantiated"
    );
    assert!(
        !r2.has_uninstantiated,
        "LI-5: has_uninstantiated must stay false across rounds"
    );
}

/// M4 (item 1) — DIRECT PARKED-QUEUE DRAIN + FRESH SEEN FRAME: parked -> fence ->
/// re-encounter -> asserts. The fence drains the whole parked queue VERBATIM
/// (bypassing the seen memo), then resets the seen frame so a parked binding
/// RE-ENCOUNTERED post-fence is NOT memo-suppressed — it re-asserts.
#[test]
fn test_demand_fence_reasserts_reencountered_parked_binding() {
    let mut qm = QuantifierManager::new();
    let mut terms = TermStore::new();
    let (forall, _p1, c1) = forall_px_and_ground(&mut terms, 1);

    qm.begin_epoch();
    // Arm the demand lane gating `forall`.
    let mut gated = ay_core::kani_compat::DetHashSet::<u32>::default();
    gated.insert(forall.0);
    qm.demand_arm(gated, 3);

    // Simulate the E-matcher having PARKED (forall,[c1]) over-frontier at
    // generation 5 AND recorded it in the seen memo (exactly what the park path
    // does: seen-insert then park).
    let binding = vec![c1];
    assert!(
        qm.demand_seen_insert_for_test(forall, binding.clone()),
        "precondition: the parked binding is freshly seen-inserted"
    );
    qm.demand_park_for_test(
        forall,
        binding.clone(),
        vec!["x".to_string()],
        5,
        "P".to_string(),
    );
    assert_eq!(qm.demand_parked_len(), 1);
    assert_eq!(qm.seen_len(), 1, "the parked binding is in the seen memo");

    // FENCE (LAW #2, M4-hardened): drain the whole parked queue directly.
    let drained = qm.demand_fence_drain(&mut terms);
    assert_eq!(
        drained.len(),
        1,
        "the fence drains the parked instance verbatim (bypassing the seen memo)"
    );
    assert_eq!(
        qm.demand_parked_len(),
        0,
        "the whole queue is drained (no ordering)"
    );
    assert_eq!(
        qm.seen_len(),
        0,
        "M4: the fence reset the seen frame to the epoch base (fresh seen frame)"
    );

    // RE-ENCOUNTER post-fence: the same (forall,[c1]) binding must NOT be
    // memo-suppressed — a fresh seen_insert succeeds (it would re-assert).
    assert!(
        qm.demand_seen_insert_for_test(forall, binding),
        "M4: a parked binding re-encountered post-fence must re-assert (fresh seen frame)"
    );
}

/// M4 (item 4) — CERTIFICATE / has_deferred DISCIPLINE (LAW #3): a parked-nonempty
/// state counts as deferred, so it can never finalize a Sat; after the fence
/// achieves a full grant-only flush the deferred flag clears.
#[test]
fn test_demand_parked_nonempty_is_deferred_until_flushed() {
    let mut qm = QuantifierManager::new();
    let mut terms = TermStore::new();
    let (forall, _p1, c1) = forall_px_and_ground(&mut terms, 1);

    qm.begin_epoch();
    let mut gated = ay_core::kani_compat::DetHashSet::<u32>::default();
    gated.insert(forall.0);
    qm.demand_arm(gated, 3);

    assert!(
        !qm.has_deferred(),
        "no deferred/parked yet — a Sat would be admissible"
    );

    // Park an over-frontier instance.
    qm.demand_park_for_test(forall, vec![c1], vec!["x".to_string()], 5, "P".to_string());
    assert!(
        qm.has_deferred(),
        "LAW #3: a parked-nonempty state MUST count as deferred (never finalize Sat)"
    );

    // Fence drain achieves the full grant-only flush -> queue empty -> not deferred.
    let drained = qm.demand_fence_drain(&mut terms);
    assert_eq!(drained.len(), 1);
    assert!(
        !qm.has_deferred(),
        "after a full grant-only flush the parked queue is empty (Sat now admissible)"
    );
}
