// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Regression test for #5805: `simplify_model` + `sanitize_free_variables`
//! could weaken an invariant to `Bool(true)`, turning a valid model into an
//! unsound one, and PDR reported Safe on an unsafe system.
//!
//! Benchmark: `O3_id_o20_false-unreach-call_000.smt2` from hcai-bench/svcomp/O3
//! (3 predicates, 6 clauses). z3: `unsat` (the system is unsafe). Pre-fix: Safe.
//! The O0 build of the same program is pinned in `kind_soundness.rs` (#6824);
//! this is the O3 build, which is what #5805 was found on.
//!
//! Ported from the pre-publication history (0ffa08f4b5, 2026-05-15), where
//! it existed only as a local variant and never reached the published tree.

use ay_chc::testing::pdr_solve_from_str;
use ay_chc::{PdrConfig, PdrResult};
use ntest::timeout;
use std::time::Duration;

/// O3_id_o20: multi-predicate unsafe CHC system.
/// Query clause: `main@id.exit.split => false`.
const O3_ID_O20_SMT2: &str = r#"
(set-logic HORN)
(declare-fun |main@entry| ( Int ) Bool)
(declare-fun |main@id.exit.split| ( ) Bool)
(declare-fun |main@tailrecurse.i| ( Int Int ) Bool)
(assert (forall ( (A Int) )
  (=> (and true) (main@entry A))))
(assert (forall ( (A Int) (B Int) (C Bool) (D Bool) (E Int) (F Int) (G Bool) (H Bool) (I Int) (J Int) (K Int) )
  (=> (and (main@entry B)
    (and (= A B) (or (not H) (not D) (not C)) (or (not H) (not G) (= F E))
     (or (not H) (not G) (= I 0)) (or (not H) (not G) (= J F))
     (or (not H) (not G) (= K I)) (or (not G) (and H G))
     (or (not H) (and H C)) (= G true) (= D (= E 0))))
    (main@tailrecurse.i J K))))
(assert (forall ( (A Int) (B Int) (C Bool) (D Int) (E Int) (F Int) (G Bool) (H Bool) (I Int) (J Int) (K Int) )
  (=> (and (main@tailrecurse.i A B)
    (and (= D (+ (- 1) A)) (= E (+ 1 B))
     (or (not H) (not G) (= F D)) (or (not H) (not G) (= I E))
     (or (not H) (not G) (= J F)) (or (not H) (not G) (= K I))
     (or (not H) (not G) (not C)) (or (not G) (and H G))
     (= G true) (= C (= D 0))))
    (main@tailrecurse.i J K))))
(assert (forall ( (A Int) (B Int) (C Int) (D Bool) (E Bool) (F Bool) (G Bool) (H Bool) (I Bool) )
  (=> (and (main@entry B)
    (and (= A B) (or (not H) (not E) (= G F)) (or (not H) (not E) D)
     (or (not H) (not F) (not E)) (or (not H) (and H E))
     (or (not H) G) (or (not I) (and I H)) (= I true) (= D (= C 0))))
    main@id.exit.split)))
(assert (forall ( (A Int) (B Int) (C Int) (D Bool) (E Int) (F Bool) (G Int) (H Int) (I Bool) (J Bool) (K Bool) (L Bool) (M Bool) (N Bool) )
  (=> (and (main@tailrecurse.i A B)
    (and (= C (+ (- 1) A)) (= E (+ 1 B))
     (or (not J) (not F) (= G E)) (or (not J) (not F) (= H G))
     (or (not J) (not F) D) (or (not M) (not J) (= L K))
     (or (not M) (not J) (= K I)) (or (not J) (= I (= H 20)))
     (or (not J) (and J F)) (or (not M) (and M J))
     (or (not M) L) (or (not N) (and N M)) (= N true) (= D (= C 0))))
    main@id.exit.split)))
(assert (forall ( (CHC_COMP_UNUSED Bool) )
  (=> (and main@id.exit.split true) false)))
(check-sat)
(exit)
"#;

/// PDR must not return Safe on this unsafe system (#5805). The fix re-verifies
/// the model after sanitization; Unsafe, Unknown or an error are all
/// acceptable, a Safe is the bug.
#[test]
#[timeout(60_000)]
fn test_simplify_model_does_not_create_false_safe_5805() {
    let mut config = PdrConfig::production(false);
    config.solve_timeout = Some(Duration::from_secs(3));
    match pdr_solve_from_str(O3_ID_O20_SMT2, config) {
        Ok(PdrResult::Safe(model)) => panic!(
            "SOUNDNESS BUG #5805: PDR returned Safe on the unsafe O3_id_o20 system: {model:?}"
        ),
        Ok(_) => {}
        Err(e) => eprintln!("PDR returned an error (not a wrong Safe): {e}"),
    }
}
