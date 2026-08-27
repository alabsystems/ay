// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! A congruence/transitivity clause is spelled in EUF rules, not fused into a
//! datatype ground conflict that no external checker can name.
//!
//! `infer_dt_lemma_kind`'s recognizers each accept ONE schema, so a clause that
//! mixes congruence with transitivity matches none of them and falls through to
//! the datatype ground-conflict catch-all. That refuter closes it correctly, but
//! `dt_ground_conflict` has no rule in the pinned external calculus, so the step
//! renders as an honest `hole`, `unsat_proof_has_known_wire_gap` fires and
//! `decline_trust_bearing_unsat_under_strict_proofs` withholds the verdict —
//! `unknown (proof-trusted)` for a complete, trust-free, hole-free refutation.
//!
//! The clause is ordinary congruence plus transitivity, and the external checker
//! has `eq_congruent` and `eq_transitive`, so the fix spells it in those rules
//! rather than relaxing the wire policy. The strict-wire contract is unchanged:
//! a GENUINE datatype conflict still has no external rendering and is still
//! declined — pinned by `test_datatype_distinct_lemma_strict_wire_policy_fail_closes`.
//!
//! Shape: verification-consumer's `extern_spec` `Option::unwrap` obligation, reduced to the
//! bridge equality that produced the fused clause. Built through the native API
//! because that is the path a proof-carrying native replay takes.

use ay_dpll::api::{
    DatatypeConstructor, DatatypeField, DatatypeSort, Logic, Solver, Sort, StrictProofVerdict,
};
use ntest::timeout;

/// An opaque carrier sort bridged into a real datatype, where the refutation
/// needs `B(old) = B(opt)` congruence chained with `u(opt) = call0`.
fn solve_bridged_congruence(strict_wire: bool) -> (String, Option<StrictProofVerdict>) {
    let mut solver = Solver::try_new(Logic::All).expect("solver");
    solver.set_produce_proofs(true);
    if strict_wire {
        solver
            .try_set_option(":check-proofs-strict", "true")
            .expect("strict wire option");
    }

    let option_int = DatatypeSort {
        name: "OptionInt".to_string(),
        constructors: vec![
            DatatypeConstructor {
                name: "None".to_string(),
                fields: vec![],
            },
            DatatypeConstructor {
                name: "Some".to_string(),
                fields: vec![DatatypeField {
                    name: "option_some_value".to_string(),
                    sort: Sort::Int,
                }],
            },
        ],
    };
    solver.declare_datatype(&option_int);

    let option = Sort::Uninterpreted("Option".to_string());
    let bridge = solver.declare_fun("B", &[option.clone()], Sort::Datatype(option_int.clone()));
    let unwrap = solver.declare_fun("u", &[option.clone()], Sort::Int);
    let opt = solver.declare_const("opt", option.clone());
    let old_opt = solver.declare_const("old_opt", option);
    let res = solver.declare_const("res", Sort::Int);
    let call0 = solver.declare_const("call0", Sort::Int);

    let bridged_old = solver.apply(&bridge, &[old_opt]);
    let bridged_opt = solver.apply(&bridge, &[opt]);
    let some_res = solver.datatype_constructor(&option_int, "Some", &[res]);

    let old_is_some_res = solver.eq(bridged_old, some_res);
    let same_carrier = solver.eq(opt, old_opt);
    let bridges_equal = solver.eq(bridged_old, bridged_opt);
    let bridges_differ = solver.not(bridges_equal);
    let carrier_or_bridge = solver.or(same_carrier, bridges_differ);
    let opt_is_some_res = solver.eq(bridged_opt, some_res);
    let unwrapped_opt = solver.apply(&unwrap, &[opt]);
    let unwrap_is_res = solver.eq(unwrapped_opt, res);
    let call_is_res = solver.eq(call0, res);
    let unwrapped_old = solver.apply(&unwrap, &[old_opt]);
    let goal = solver.eq(call0, unwrapped_old);
    let negated_goal = solver.not(goal);

    for (index, assertion) in [
        old_is_some_res,
        carrier_or_bridge,
        opt_is_some_res,
        unwrap_is_res,
        call_is_res,
        negated_goal,
    ]
    .into_iter()
    .enumerate()
    {
        solver
            .try_assert_named(assertion, &format!("a{index}"))
            .expect("assert");
    }

    let details = solver.check_sat_with_details();
    let result = details.result.result().to_string();
    let verdict = solver
        .export_last_unsat_artifact()
        .map(|artifact| artifact.strict_verdict);
    (result, verdict)
}

/// Without the strict-wire option the refutation always published; this pins
/// that the query really is UNSAT so the strict case below is about publication
/// policy and not about solving.
#[test]
#[timeout(60_000)]
fn bridged_congruence_refutation_is_unsat() {
    let (result, _) = solve_bridged_congruence(false);
    assert_eq!(result, "unsat", "the bridged congruence query is refutable");
}

/// The regression: under `:check-proofs-strict` the same refutation must
/// publish, because its steps are spelled in externally checkable EUF rules.
#[test]
#[timeout(60_000)]
fn bridged_congruence_publishes_under_strict_wire_policy() {
    let (result, verdict) = solve_bridged_congruence(true);
    assert_eq!(
        result, "unsat",
        "a congruence/transitivity refutation is externally spellable, so the \
         strict-wire policy must not withhold it"
    );
    assert!(
        matches!(verdict, Some(StrictProofVerdict::Verified(_))),
        "the published artifact must carry a verified strict verdict, got {verdict:?}"
    );
}
