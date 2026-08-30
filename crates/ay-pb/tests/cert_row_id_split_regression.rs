// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Input-row ids in emitted certificates must respect VeriPB's `=` SPLIT.
//!
//! VeriPB's OPB loader imports `a·x = b` as TWO consecutive `f` constraints
//! (the `>=` half, then the `<=` half). So the id a `pol` step must cite for
//! `instance.constraints[i]` is `i + 1` ONLY while no equality precedes `i`;
//! otherwise it is shifted by the number of preceding equalities.
//!
//! `certify_opt_lin_direct_aggregation_floor` used `i + 1` unconditionally.
//! On `benchmarks/.../OPT-LIN/flexray/normalized-fx57.opb` — 3,286 rows, 57 of
//! them `=`, and the aggregation row is the LAST one — it cited id 3286 for the
//! row VeriPB had imported as 3343. Id 3286 is a real, unrelated row, so the
//! `pol` step PARSED and the failure surfaced only on the last line of the
//! file: the pinned checker rejected
//!
//!     Checking error at <proof>:6
//!     Caused by: Expected constraint is not syntactically implied by the
//!                constraint at the hint.
//!
//! next to AY's own `s OPTIMUM FOUND` — the one pairing the certified track
//! exists to make impossible. Changing that single id to 3343 turned the same
//! proof into `s VERIFIED BOUNDS 6 <= obj <= 6`.
//!
//! The instance below is the smallest formula with that shape: an equality
//! FIRST (ids 1 and 2), then the covering row that carries the whole floor (id
//! 3). Under the defect the emitter cites 2 — the equality's `<=` half — which
//! is a legal row and a legal `pol`, and only the conclusion's hint check
//! notices. Both halves of the test therefore matter: the first pins the id
//! WITHOUT a checker (so the regression is caught on any machine), the second
//! makes the pinned checker say so.

use ay_pb::proof::{certify_opt_lin_direct_aggregation_floor, veripb_input_row_ids};
use ay_pb::{parse_opb, PbInstance};
use ay_test_support::veripb;

const SUITE: &str = "cert_row_id_split_regression";

/// `min x3 + x4` subject to `x1 + x2 = 1` and `x3 + x4 >= 1`.
///
/// VeriPB ids: 1 = `x1 + x2 >= 1`, 2 = `-x1 - x2 >= -1`, 3 = `x3 + x4 >= 1`.
/// The aggregation floor is `x3 + x4 >= 1`, tight at the optimum 1, so the
/// emitter fires and must cite **3**.
const SPLIT_SHIFT_OPB: &str = "\
* #variable= 4 #constraint= 2
min: +1 x3 +1 x4 ;
+1 x1 +1 x2 = 1 ;
+1 x3 +1 x4 >= 1 ;
";

/// Incumbent `x1 x3` (`x2`, `x4` false): feasible, objective 1 = the optimum.
const INCUMBENT: [bool; 4] = [true, false, true, false];
const OPTIMUM: i128 = 1;

fn instance() -> PbInstance {
    parse_opb(SPLIT_SHIFT_OPB).expect("the regression formula must parse")
}

fn emitted_proof() -> String {
    certify_opt_lin_direct_aggregation_floor(&instance(), &INCUMBENT, OPTIMUM).expect(
        "the aggregation floor is tight here; the emitter must fire, or this test proves nothing",
    )
}

/// The `f` header and the `pol` hints must be read off the SAME map.
///
/// This is the property the defect broke: the header came from
/// `veripb_input_constraint_count` (which does double equalities, so `f 3` was
/// right) while the hint came from a private `idx + 1` (which does not). One
/// file, two mappings, one wrong.
#[test]
fn input_row_id_map_accounts_for_the_equality_split() {
    let instance = instance();
    let ids = veripb_input_row_ids(&instance).expect("row id map");
    assert_eq!(
        ids.iter().map(|id| id.get()).collect::<Vec<_>>(),
        vec![1, 3],
        "the equality at index 0 owns ids 1 AND 2, so index 1 starts at 3"
    );
    let count = ay_pb::veripb_input_constraint_count(&instance).expect("f count");
    assert_eq!(count, 3, "f header must count the equality twice");
    assert!(
        ids.iter().all(|id| id.get() <= count),
        "no cited id may exceed the imported formula"
    );
}

/// Checker-free half: the emitted `pol` must cite the covering row's REAL id.
///
/// Fails on the unfixed emitter with `pol 2 4 + ;` (the equality's `<=` half).
#[test]
fn aggregation_floor_cites_the_split_shifted_row_id() {
    let proof = emitted_proof();
    let pol: Vec<&str> = proof
        .lines()
        .filter(|line| line.starts_with("pol "))
        .collect();
    assert_eq!(
        pol,
        vec!["pol 3 4 + ;"],
        "the floor is input row 3 (the equality took ids 1 and 2) and the `soli` \
         row is 4; citing 2 is the fx57 defect\n{proof}"
    );
    assert!(
        !proof.contains("pol 2 4 + ;"),
        "the emitter cited the equality's `<=` half — this is the fx57 defect\n{proof}"
    );
}

/// The half that decides the claim: the PINNED checker must accept the proof.
///
/// On the unfixed emitter this fails exactly the way fx57 did — a checking
/// error on the `conclusion` line, because the hinted row does not imply the
/// bound.
#[test]
fn pinned_checker_accepts_the_aggregation_floor_over_a_split_formula() {
    let Some(checker) = veripb::require_checker(SUITE) else {
        return;
    };
    let proof = emitted_proof();
    let run = veripb::run_text(&checker, "cert-row-id-split", SPLIT_SHIFT_OPB, &proof, &[]);
    run.assert_verified(
        &veripb::Expect::bounds(OPTIMUM.to_string(), OPTIMUM.to_string()),
        "direct aggregation floor over a formula whose ids are shifted by an equality",
    );
}

/// Fail-closed the other way: a hint the checker CANNOT be given must not be
/// emitted at all. Mutating the accepted proof's single input-row id to any
/// other imported row must be REJECTED — which is what makes the test above
/// evidence rather than a coincidence.
#[test]
fn mutating_the_cited_row_id_is_rejected() {
    let Some(checker) = veripb::require_checker(SUITE) else {
        return;
    };
    let proof = emitted_proof();
    let emitted = proof
        .lines()
        .find(|line| line.starts_with("pol "))
        .expect("the emitter writes exactly one pol step here")
        .to_string();
    // The other imported rows, and the `soli` row doubled. Each is a
    // syntactically legal `pol` over a row that really is in the database, and
    // none of them establishes the bound.
    //
    // NOT in this list: `pol 3 3 + ;`. That doubles the genuine floor row to
    // `2x3 + 2x4 >= 2`, which still implies `obj >= 1` — the checker accepts it
    // and is RIGHT to. A mutation that preserves the truth is not evidence of
    // anything; only mutations that break the argument belong here.
    for wrong in ["pol 1 4 + ;", "pol 2 4 + ;", "pol 4 4 + ;"] {
        if wrong == emitted {
            continue;
        }
        let mutated = proof.replace(&emitted, wrong);
        assert_ne!(mutated, proof, "mutation must change the proof");
        let run = veripb::run_text(
            &checker,
            "cert-row-id-split-mut",
            SPLIT_SHIFT_OPB,
            &mutated,
            &[],
        );
        run.assert_rejected(&format!(
            "the aggregation floor citing the wrong input row ({wrong})"
        ));
    }
}
