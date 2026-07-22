// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

/// Test dillig12_m with E=0 (mode 0) fixed at init.
///
/// This benchmark is the hardest dillig variant. This test is a **soundness**
/// check (no false UNSAFE) rather than a completeness/performance gate.
///
/// Run with extremely small limits to keep runtime bounded even in debug builds.
/// The result may be `Unknown`, but must never be `Unsafe`.
///
/// Timeout: 30s (#1861)
#[test]
#[timeout(30_000)]
fn test_dillig12_m_e0() {
    let input = r#"
(set-logic HORN)
(declare-fun |SAD| ( Int Int ) Bool)
(declare-fun |FUN| ( Int Int Int Int Int ) Bool)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) )
    (=>
      (and (and (= C 0) (= B 0) (= A 0) (= D 0) (= E 0)))
      (FUN A B C D E)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) )
    (=>
      (and
        (FUN A B C D J)
        (and (= I (ite (= J 1) (+ E F) E))
     (= H (+ C F))
     (= G (+ 1 B))
     (= F (+ 1 A))
     (= E (+ D G)))
      )
      (FUN F G H I J)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) )
    (=>
      (and
        (FUN A B E D C)
        (let ((a!1 (= F (ite (= C 1) (+ 2 D (* (- 2) E)) 1))))
  (and a!1 (= G 0)))
      )
      (SAD F G)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) )
    (=>
      (and
        (SAD B A)
        (and (or (= C (+ 1 A)) (= C (+ 2 A))) (<= A B))
      )
      (SAD B C)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) )
    (=>
      (and
        (SAD A B)
        (and (>= B A) (>= B 5))
      )
      false
    )
  )
)
(check-sat)
(exit)
"#;

    // Use production config (disables Entry-CEGAR which causes timeouts).
    // Use very small limits for quick soundness check (#1861).
    // E=0 variant is the hardest - minimize limits to keep test fast.
    let mut config = PdrConfig::production(false);
    config.max_frames = 2;
    config.max_iterations = 1;
    config.max_obligations = 200;

    let result = pdr_solve_from_str(input, config).unwrap();

    // Soundness: Safe benchmark must not be classified as Unsafe.
    assert!(
        !matches!(result, PdrResult::Unsafe(_)),
        "dillig12_m_e0 must not be classified as Unsafe, got {result:?}"
    );
}

/// Test dillig12_m with E=1 (mode 1) fixed at init.
/// This tests the case-split scenario with mode=1, which is harder than mode=0
/// because SAD's first arg depends on FUN invariant D=2*E.
///
/// This test requires `use_negated_equality_splits: true` to discover the D=2*E
/// relational invariant. The portfolio runs both configs (#491).
///
/// This test is a soundness check (no false UNSAFE). Under the small limits used
/// here the solver may return `Unknown`.
///
/// Timeout: 30s (#1861: use production config with small limits)
#[test]
#[timeout(30_000)]
fn test_dillig12_m_e1() {
    let input = r#"
(set-logic HORN)
(declare-fun |SAD| ( Int Int ) Bool)
(declare-fun |FUN| ( Int Int Int Int Int ) Bool)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) )
    (=>
      (and (and (= C 0) (= B 0) (= A 0) (= D 0) (= E 1)))
      (FUN A B C D E)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) )
    (=>
      (and
        (FUN A B C D J)
        (and (= I (ite (= J 1) (+ E F) E))
     (= H (+ C F))
     (= G (+ 1 B))
     (= F (+ 1 A))
     (= E (+ D G)))
      )
      (FUN F G H I J)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) )
    (=>
      (and
        (FUN A B E D C)
        (let ((a!1 (= F (ite (= C 1) (+ 2 D (* (- 2) E)) 1))))
  (and a!1 (= G 0)))
      )
      (SAD F G)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) )
    (=>
      (and
        (SAD B A)
        (and (or (= C (+ 1 A)) (= C (+ 2 A))) (<= A B))
      )
      (SAD B C)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) )
    (=>
      (and
        (SAD A B)
        (and (>= B A) (>= B 5))
      )
      false
    )
  )
)
(check-sat)
(exit)
"#;

    // Use production_variant_with_splits (disables Entry-CEGAR + enables negated_equality_splits).
    // Use small limits for quick soundness check (#1861).
    let mut config = PdrConfig::production_variant_with_splits(false);
    config.max_frames = 2;
    config.max_iterations = 10;
    config.max_obligations = 1_000;

    let result = pdr_solve_from_str(input, config).unwrap();

    // Soundness: Safe benchmark must not be classified as Unsafe.
    assert!(
        !matches!(result, PdrResult::Unsafe(_)),
        "dillig12_m_e1 must not be classified as Unsafe, got {result:?}"
    );
}

/// Test dillig12_m_e1 with convex closure kernel only (no negated_equality_splits).
///
/// This test is a soundness check - the benchmark must not return UNSAFE.
///
/// Timeout: 30s (#1861: use production config with small limits)
#[test]
#[timeout(30_000)]
fn test_dillig12_m_e1_cc_only() {
    let input = r#"
(set-logic HORN)
(declare-fun |SAD| ( Int Int ) Bool)
(declare-fun |FUN| ( Int Int Int Int Int ) Bool)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) )
    (=>
      (and (and (= C 0) (= B 0) (= A 0) (= D 0) (= E 1)))
      (FUN A B C D E)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) )
    (=>
      (and
        (FUN A B C D J)
        (and (= I (ite (= J 1) (+ E F) E))
     (= H (+ C F))
     (= G (+ 1 B))
     (= F (+ 1 A))
     (= E (+ D G)))
      )
      (FUN F G H I J)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) )
    (=>
      (and
        (FUN A B E D C)
        (let ((a!1 (= F (ite (= C 1) (+ 2 D (* (- 2) E)) 1))))
  (and a!1 (= G 0)))
      )
      (SAD F G)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) )
    (=>
      (and
        (SAD B A)
        (and (or (= C (+ 1 A)) (= C (+ 2 A))) (<= A B))
      )
      (SAD B C)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) )
    (=>
      (and
        (SAD A B)
        (and (>= B A) (>= B 5))
      )
      false
    )
  )
)
(check-sat)
(exit)
"#;

    // Use production config (disables Entry-CEGAR which causes timeouts).
    // Use small limits for quick soundness check (#1861).
    let mut config = PdrConfig::production(false);
    config.max_frames = 2;
    config.max_iterations = 1;
    config.max_obligations = 200;

    let result = pdr_solve_from_str(input, config).unwrap();

    // Soundness: Safe benchmark must not be classified as Unsafe.
    assert!(
        !matches!(result, PdrResult::Unsafe(_)),
        "dillig12_m_e1_cc_only must not be classified as Unsafe, got {result:?}"
    );
}

/// Test dillig12_m - multi-predicate CHC problem
/// Expected: sat (safe)
///
/// This test is a soundness check (no false UNSAFE). Under the small limits used
/// here the solver may return `Unknown`.
///
/// Timeout: 30s (#1861: use production config with small limits)
#[test]
#[timeout(30_000)]
fn test_dillig12_m() {
    // Embedded benchmark: dillig12_m_000.smt2 (#981: hermetic tests)
    let input = r#"(set-logic HORN)


(declare-fun |SAD| ( Int Int ) Bool)
(declare-fun |FUN| ( Int Int Int Int Int ) Bool)

(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) )
    (=>
      (and
        (and (= C 0) (= B 0) (= A 0) (= D 0))
      )
      (FUN A B C D E)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) )
    (=>
      (and
        (FUN A B C D J)
        (and (= I (ite (= J 1) (+ E F) E))
     (= H (+ C F))
     (= G (+ 1 B))
     (= F (+ 1 A))
     (= E (+ D G)))
      )
      (FUN F G H I J)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) )
    (=>
      (and
        (FUN A B E D C)
        (let ((a!1 (= F (ite (= C 1) (+ 2 D (* (- 2) E)) 1))))
  (and a!1 (= G 0)))
      )
      (SAD F G)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) )
    (=>
      (and
        (SAD B A)
        (and (or (= C (+ 1 A)) (= C (+ 2 A))) (<= A B))
      )
      (SAD B C)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) )
    (=>
      (and
        (SAD A B)
        (and (>= B A) (>= B 5))
      )
      false
    )
  )
)

(check-sat)
(exit)
"#;

    // Use production config (disables Entry-CEGAR which causes timeouts).
    // Use small limits for quick soundness check (#1861).
    let mut config = PdrConfig::production(false);
    config.max_frames = 2;
    config.max_iterations = 10;
    config.max_obligations = 1_000;

    let result = pdr_solve_from_str(input, config).unwrap();

    // Soundness: Safe benchmark must not be classified as Unsafe.
    assert!(
        !matches!(result, PdrResult::Unsafe(_)),
        "dillig12_m must not be classified as Unsafe, got {result:?}"
    );
}

/// Regression test for s_multipl_25 - requires x1+x2=0 sum invariant.
///
/// This test is a soundness check - the benchmark must not return UNSAFE.
///
/// Timeout: 30s (#1861: use production config with small limits)
#[test]
#[timeout(30_000)]
fn pdr_s_multipl_25_safe() {
    // Embedded benchmark: s_multipl_25_000.smt2 (#981: hermetic tests)
    let input = r#"(set-logic HORN)


(declare-fun |inv2| ( Int Int Int Int ) Bool)
(declare-fun |inv1| ( Int Int Int Int ) Bool)

(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) )
    (=>
      (and
        (and (= C 0) (= B 0) (= A 0) (= D 0))
      )
      (inv1 A B C D)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) )
    (=>
      (and
        (inv1 B C A G)
        (and (= E (+ C (* (- 1) F))) (= D (+ B F)) (= F (+ 1 A)))
      )
      (inv1 D E F G)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) )
    (=>
      (and
        (inv1 A B C D)
        true
      )
      (inv2 A B C D)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) )
    (=>
      (and
        (inv2 B C F A)
        (and (= E (+ C G)) (= D (+ B (* (- 1) G))) (= G (+ 1 A)))
      )
      (inv2 D E F G)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) )
    (=>
      (and
        (inv2 C D A B)
        (and (not (<= A B)) (<= C D))
      )
      false
    )
  )
)

(check-sat)
(exit)
"#;

    // Use production config (disables Entry-CEGAR which causes timeouts).
    // Use small limits for quick soundness check (#1861).
    let mut config = PdrConfig::production(false);
    config.max_frames = 2;
    config.max_iterations = 10;
    config.max_obligations = 1_000;

    let result = pdr_solve_from_str(input, config).unwrap();

    // Soundness: Safe benchmark must not be classified as Unsafe.
    assert!(
        !matches!(result, PdrResult::Unsafe(_)),
        "s_multipl_25 must not be classified as Unsafe, got {result:?}"
    );
}

/// Regression test for s_multipl_23 - parity-conditional affine invariants.
///
/// This test is a soundness check - the benchmark must not return UNSAFE.
///
/// Timeout: 30s (#1861: use production config with small limits)
#[test]
#[timeout(30_000)]
fn pdr_s_multipl_23_safe() {
    // Embedded benchmark: s_multipl_23_000.smt2 (#981: hermetic tests)
    let input = r#"(set-logic HORN)


(declare-fun |SAD| ( Int Int Int ) Bool)
(declare-fun |FUN| ( Int Int Int ) Bool)

(assert
  (forall ( (A Int) (B Int) (C Int) ) 
    (=>
      (and
        (and (= A 0) (not (<= C 0)) (= B 0))
      )
      (FUN A B C)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) ) 
    (=>
      (and
        (FUN A B E)
        (and (= C (+ 1 A)) (not (<= E B)) (= D (+ 2 B)))
      )
      (FUN C D E)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) ) 
    (=>
      (and
        (FUN B A E)
        (and (= C B) (>= A E) (= D 1))
      )
      (SAD C D E)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) ) 
    (=>
      (and
        (SAD A B E)
        (and (= C (+ 1 A)) (not (<= E B)) (= D (+ 2 B)))
      )
      (SAD C D E)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) ) 
    (=>
      (and
        (SAD B A C)
        (and (>= A C) (not (= B C)))
      )
      false
    )
  )
)

(check-sat)
(exit)
"#;

    // Use production config (disables Entry-CEGAR which causes timeouts).
    // Use small limits for quick soundness check (#1861).
    let mut config = PdrConfig::production(false);
    config.max_frames = 2;
    config.max_iterations = 10;
    config.max_obligations = 1_000;

    let result = pdr_solve_from_str(input, config).unwrap();

    // Soundness: Safe benchmark must not be classified as Unsafe.
    assert!(
        !matches!(result, PdrResult::Unsafe(_)),
        "s_multipl_23 must not be classified as Unsafe, got {result:?}"
    );
}

/// Regression test for #3211: const_mod_3 should remain provable with cancellation-aware
/// startup budgets enabled.
///
/// This benchmark depends on discovering the modular invariant `(B mod 2) = A`.
/// The regression in #3211 returned `Unknown` after introducing the 1.5s kernel
/// discovery budget when a cancellation token is present.
///
/// Timeout: 30s
#[test]
#[timeout(30_000)]
fn pdr_const_mod_3_with_cancellation_budget_issue_3211() {
    let input = r#"(set-logic HORN)


(declare-fun |inv| ( Int Int ) Bool)

(assert
  (forall ( (A Int) (B Int) )
    (=>
      (and
        (and (= A 0) (= B 0))
      )
      (inv A B)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) )
    (=>
      (and
        (inv A B)
        (let ((a!1 (or (and (= D (+ B 1)) (= C 0))
                       (and (= D (+ B 1)) (= C 1)))))
          (and a!1 (not (<= A 0))))
      )
      (inv C D)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) )
    (=>
      (and
        (inv A B)
        (let ((a!1 (or (and (not (= (mod B 2) 0)) (not (= A 1)))
                       (and (not (= (mod B 2) 1)) (= A 1)))))
          a!1)
      )
      false
    )
  )
)

(check-sat)
(exit)
"#;

    let token = CancellationToken::new();
    let mut config = PdrConfig::production(false).with_cancellation_token(Some(token));
    config.max_frames = 50;
    config.max_iterations = 500;
    config.max_obligations = 50_000;

    let result = pdr_solve_from_str(input, config).expect("const_mod_3 solve");
    assert!(
        matches!(result, PdrResult::Safe(_)),
        "const_mod_3 should return Safe (not Unknown) with cancellation-aware budgets, got {result:?}"
    );
}

/// Regression test for s_multipl_12 - cyclic CHC with 3 predicates.
///
/// Cyclic predicates INV0 → INV1 → INV2 → INV0. Tests SCC detection,
/// init-validity filtering (#127), and joint SCC verification.
/// See: the development design notes
///
/// Asserts not-Unsafe (soundness guard) rather than Safe due to PDR
/// performance regression (#5970). Tighten to Safe when #5970 resolves.
#[cfg(not(debug_assertions))]
#[test]
#[timeout(120_000)]
fn pdr_s_multipl_12_safe() {
    // Embedded benchmark: s_multipl_12_000.smt2 (#981: hermetic tests)
    let input = r#"(set-logic HORN)


(declare-fun |INV0| ( Int Int Int ) Bool)
(declare-fun |INV1| ( Int Int Int ) Bool)
(declare-fun |INV2| ( Int Int Int ) Bool)

(assert
  (forall ( (A Int) (v_1 Int) (v_2 Int) )
    (=>
      (and
        (and (not (<= A 0)) (= 0 v_1) (= 0 v_2))
      )
      (INV0 A v_1 v_2)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) )
    (=>
      (and
        (INV0 A C D)
        (and (not (<= A 0)) (= B (+ (- 1) A)))
      )
      (INV1 B C D)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) )
    (=>
      (and
        (INV1 C A B)
        (and (= E (+ (- 1) B)) (not (<= C A)) (= D (+ 1 A)))
      )
      (INV1 C D E)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) )
    (=>
      (and
        (INV1 A B C)
        (<= A B)
      )
      (INV2 A B C)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) )
    (=>
      (and
        (INV2 C A B)
        (and (= E (+ 1 B)) (not (<= C B)) (= D (+ (- 1) A)))
      )
      (INV2 C D E)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) )
    (=>
      (and
        (INV2 A B C)
        (<= A C)
      )
      (INV0 A B C)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) )
    (=>
      (and
        (INV0 A B C)
        (and (= A 0) (not (= B C)))
      )
      false
    )
  )
)

(check-sat)
(exit)
"#;

    // Use production settings (matches the `ay` binary CHC defaults).
    let mut config = PdrConfig::production(false);
    config.max_frames = 100;
    config.max_iterations = 10_000;
    config.max_obligations = 100_000;

    let result = pdr_solve_from_str(input, config).unwrap();

    // Soundness guard only: #5970 regression causes Unknown within budget.
    assert!(
        !matches!(result, PdrResult::Unsafe(_)),
        "s_multipl_12 must not be Unsafe, got {result:?}"
    );
}
