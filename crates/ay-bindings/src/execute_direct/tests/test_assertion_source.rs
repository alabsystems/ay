// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates

use super::*;
use ay_dpll::api::ProofAcceptanceMode;

#[test]
fn incremental_native_proof_keeps_submitted_conjunction() {
    let mut program = AYProgram::new();
    program.set_option("produce-proofs", "true");
    program.set_logic("QF_LIA");
    let x = program.declare_const("x", Sort::int());
    let bound = x.clone().int_gt(Expr::int(4));
    let assertion = Expr::and_many(vec![bound.clone(), x.int_le(Expr::int(4)), bound]);
    let source = assertion.to_string();
    program.assert(assertion);
    program.check_sat();
    let outcomes = execute_incremental(&program).unwrap();
    assert_eq!(outcomes.len(), 1);
    assert!(matches!(outcomes[0].result, ExecuteTypedResult::Verified));
    let proof = outcomes[0].unsat_proof.as_ref().unwrap();
    proof
        .accept_for_consumer(ProofAcceptanceMode::Strict)
        .unwrap();
    assert_eq!(proof.quality.trust_count, 0);
    assert!(proof.alethe.contains(&source), "{}", proof.alethe);
}

#[test]
fn changed_native_bound_remains_a_counterexample() {
    let mut program = AYProgram::new();
    program.set_option("produce-proofs", "true");
    program.set_logic("QF_LIA");
    let x = program.declare_const("x", Sort::int());
    program.assert(Expr::and_many(vec![
        x.clone().int_gt(Expr::int(4)),
        x.int_le(Expr::int(5)),
    ]));
    program.check_sat();
    let outcomes = execute_incremental(&program).unwrap();
    assert!(matches!(
        outcomes[0].result,
        ExecuteTypedResult::Counterexample(_)
    ));
    assert!(outcomes[0].unsat_proof.is_none());
}

#[test]
fn late_proof_request_retains_earlier_assertion_sources() {
    let mut program = AYProgram::new();
    program.set_option(":produce-proofs", "false");
    program.set_logic("QF_LIA");
    let x = program.declare_const("x", Sort::int());
    program.assert(x.clone().int_gt(Expr::int(4)));
    program.check_sat();
    program.push();
    program.assert(x.int_le(Expr::int(4)));
    program.add_constraint(crate::constraint::Constraint::set_option(
        ":produce-proofs",
        "true",
    ));
    program.check_sat();
    let outcomes = execute_incremental(&program).unwrap();
    assert_eq!(outcomes.len(), 2);
    assert!(matches!(
        outcomes[0].result,
        ExecuteTypedResult::Counterexample(_)
    ));
    assert!(outcomes[0].unsat_proof.is_none());
    assert!(matches!(outcomes[1].result, ExecuteTypedResult::Verified));
    let proof = outcomes[1].unsat_proof.as_ref().unwrap();
    proof
        .accept_for_consumer(ProofAcceptanceMode::Strict)
        .unwrap();
    assert!(proof.alethe.contains("(> x 4)"), "{}", proof.alethe);
    assert!(proof.alethe.contains("(<= x 4)"), "{}", proof.alethe);
}

#[test]
fn single_shot_execution_keeps_source_when_proofs_are_enabled_late() {
    let mut program = AYProgram::new();
    program.set_logic("QF_LIA");
    let x = program.declare_const("x", Sort::int());
    program.assert(x.clone().int_gt(Expr::int(4)));
    program.assert(x.int_le(Expr::int(4)));
    program.add_constraint(crate::constraint::Constraint::set_option(
        "produce-proofs",
        "true",
    ));
    program.check_sat();
    let details = execute_typed_with_details(&program).unwrap();
    assert!(matches!(details.result, ExecuteTypedResult::Verified));
    let proof = details.unsat_proof.unwrap();
    proof
        .accept_for_consumer(ProofAcceptanceMode::Strict)
        .unwrap();
    assert!(proof.alethe.contains("(> x 4)"), "{}", proof.alethe);
}

/// The retained source is the program's own `Display`; a negative constant
/// must print as the SMT-LIB term `(- n)` (a bare `-n` is a symbol), so the
/// authored assumption and every step over the bound agree with the term.
#[test]
fn negative_bounds_retain_smtlib_spelling_in_native_proofs() {
    let build = |upper: i64| {
        let mut program = AYProgram::new();
        program.set_option("produce-proofs", "true");
        program.set_logic("QF_LIA");
        let x = program.declare_const("x", Sort::int());
        let y = program.declare_const("y", Sort::int());
        program.assert(Expr::and_many(vec![
            Expr::int(-128_i64).int_le(x.clone()),
            x.clone().int_le(Expr::int(127_i64)),
            Expr::int(-128_i64).int_le(x.clone()),
            y.clone().eq(x.clone()),
            y.int_lt(Expr::int(upper)),
        ]));
        program.check_sat();
        program
    };
    let program = build(-128);
    assert!(program.to_string().contains("(<= (- 128) x)"), "{program}");
    assert!(!program.to_string().contains(" -128"), "{program}");
    let outcomes = execute_incremental(&program).unwrap();
    assert!(matches!(outcomes[0].result, ExecuteTypedResult::Verified));
    let proof = outcomes[0].unsat_proof.as_ref().unwrap();
    proof
        .accept_for_consumer(ProofAcceptanceMode::Strict)
        .unwrap();
    assert!(proof.alethe.contains("(<= (- 128) x)"), "{}", proof.alethe);

    let outcomes = execute_incremental(&build(-127)).unwrap();
    assert!(matches!(
        outcomes[0].result,
        ExecuteTypedResult::Counterexample(_)
    ));
}

/// An authored grouping must cost the query its SPELLING, never its artifact.
///
/// This is the exact program a verification frontend hands `execute_incremental`
/// for a branch-guarded overflow obligation (deductive-checksgen's LIA shape): one
/// `(assert (and RANGES (or LIVE DEAD)))` whose `DEAD` arm opens with a literal
/// `false`. Elaboration folds `(and false ..)` to `false`, `(or LIVE false)` to
/// `LIVE`, and flattens `LIVE`'s own conjuncts into the top-level conjunction,
/// so a bound such as `(<= x 1000)` is a canonical top-level conjunct while the
/// retained source still nests it two levels down inside the `or`. The proof's
/// `and_pos` steps index the canonical conjunction and the printer must project
/// them off the authored grouping.
///
/// HISTORY, AND WHAT THIS TEST IS NOW FOR — stated exactly, because the two are
/// no longer the same thing.
///
/// When this test was written, the printer had no `and_pos` / `cong` /
/// `comp_simplify` chain for that projection and refused the document, and
/// `export_last_unsat_artifact` turned the refusal into `None`: a UNSAT
/// `check_proof_strict` had accepted arrived at every strict consumer as
/// `Unknown`. That is what `export_last_unsat_artifact`'s canonical re-render
/// was built for.
///
/// MEASURED SINCE, on plain origin/main with the production change absent: this
/// test PASSES. Upstream taught the printer to project `and_pos` through this
/// grouping, so this particular shape no longer provokes a refusal and no
/// longer needs the rescue. This test does NOT reproduce a live bug and must
/// not be read as evidence that the rescue is load-bearing — the cell that
/// pins it is
/// `ay_dpll::api::tests::test_proof_artifact::a_rescued_authored_spelling_refusal_publishes_an_accepted_verdict`,
/// an authored constant-folded BV index the printer still refuses. (It used to
/// be the authored BV numeral of
/// `ay_dpll::api::tests::test_proof_artifact::qfabv_row1_derived_index_equality_is_strict_verified`;
/// the printer now bridges alternate spellings of one bit-vector literal with
/// `refl`, so that fixture prints without the rescue.)
///
/// It is kept because it is a valid guard on the OUTCOME, which is the part
/// that must hold however the printer evolves: this obligation, submitted the
/// way a frontend submits it, publishes a strict-checked artifact paired with
/// its problem transport. Whether it gets there by printing the authored
/// spelling or by the canonical re-render is the boundary's business and not
/// this test's; either route must end here.
#[test]
fn branch_guarded_overflow_keeps_its_strict_artifact() {
    let range = |value: &Expr, low: i64, high: i64| {
        Expr::int(low)
            .int_le(value.clone())
            .and(value.clone().int_le(Expr::int(high)))
    };
    // `guard` is the branch's own range bound: 1000 makes the overflow
    // disjunction unsatisfiable, `U32_MAX` leaves it reachable. The satisfiable
    // build is the negative control — without it this test would pass on a
    // solver that had stopped deciding the query at all.
    let build = |guard: i64| {
        const U32_MAX: i64 = 4_294_967_295;
        let mut program = AYProgram::new();
        program.set_option("produce-proofs", "true");
        program.set_logic("QF_LIA");
        let taken = program.declare_const("taken", Sort::bool());
        let x = program.declare_const("x", Sort::int());
        let y = program.declare_const("y", Sort::int());
        let sum = x.clone().int_add(y.clone());
        let overflows = sum
            .clone()
            .int_lt(Expr::int(0))
            .or(sum.int_gt(Expr::int(U32_MAX)));
        let arm = |head: Expr| {
            Expr::and_many(vec![
                head,
                range(&x, 0, guard),
                range(&y, 0, guard),
                Expr::and_many(vec![
                    range(&x, 0, U32_MAX),
                    range(&y, 0, U32_MAX),
                    overflows.clone(),
                ]),
            ])
        };
        program.assert(Expr::and_many(vec![
            range(&x, 0, U32_MAX),
            range(&y, 0, U32_MAX),
            // The dead arm's literal `false` is what folds the `or` away.
            arm(taken.not()).or(arm(Expr::false_())),
        ]));
        program.check_sat();
        program
    };

    let outcomes = execute_incremental(&build(1000)).unwrap();
    let outcome = outcomes.last().expect("one check-sat");
    assert!(
        matches!(outcome.result, ExecuteTypedResult::Verified),
        "{:?}",
        outcome.result
    );
    let proof = outcome
        .unsat_proof
        .as_ref()
        .expect("an UNSAT under :produce-proofs must carry a proof artifact");
    proof
        .accept_for_consumer(ProofAcceptanceMode::Strict)
        .expect("the artifact must be strict-checked");
    // The document is disclosed with the problem it is checked against.
    assert!(
        proof.alethe_problem_smt2.is_some(),
        "an exported Alethe document must ship its paired problem transport"
    );

    let outcomes = execute_incremental(&build(4_294_967_295)).unwrap();
    assert!(matches!(
        outcomes.last().expect("one check-sat").result,
        ExecuteTypedResult::Counterexample(_)
    ));
}

/// A repeated conjunct whose comparison operand elaboration reorients.
#[test]
fn duplicated_reoriented_conjunct_keeps_its_native_proof() {
    let build = |bound: i64| {
        let mut program = AYProgram::new();
        program.set_logic("QF_LIA");
        program.set_option("produce-proofs", "true");
        let flag = program.declare_const("flag", Sort::bool());
        let copy = program.declare_const("copy", Sort::int());
        let x = program.declare_const("x", Sort::int());
        let at_least = x.clone().int_ge(Expr::int(16));
        program.assert(Expr::and_many(vec![
            flag.clone().eq(at_least.clone()),
            at_least.clone().not(),
            x.clone().int_ge(Expr::int(0)),
            flag.eq(at_least),
            copy.clone().eq(x),
            copy.int_ge(Expr::int(bound)),
        ]));
        program.check_sat();
        program
    };
    let outcomes = execute_incremental(&build(16)).unwrap();
    assert!(matches!(outcomes[0].result, ExecuteTypedResult::Verified));
    outcomes[0]
        .unsat_proof
        .as_ref()
        .expect("strict artifact")
        .accept_for_consumer(ProofAcceptanceMode::Strict)
        .unwrap();
    let outcomes = execute_incremental(&build(15)).unwrap();
    assert!(matches!(
        outcomes[0].result,
        ExecuteTypedResult::Counterexample(_)
    ));
}

/// Trust's in-process shape for `a[(i & 1) as usize]` (deductive-checksgen
/// `uninhabited_arm_realmir`): one flattened conjunction whose literal `true`
/// elaboration drops, bitmask facts, and the authored
/// `(bv2int (bvand ((_ int2bv 8) i) ((_ int2bv 8) 1)))` that elaboration
/// rewrites to `(mod i 2)`. It was UNSAT with no strict artifact once the
/// source was retained; the refutation must publish one, and the twin whose
/// index may reach 1 must stay a counterexample.
#[test]
fn masked_low_bit_index_keeps_its_native_proof() {
    let build = |bound: i64| {
        let mut program = AYProgram::new();
        program.set_option("produce-proofs", "true");
        program.set_logic("ALL");
        let d = program.declare_const("__trust_mir__discr_x", Sort::int());
        let three = program.declare_const("_3", Sort::int());
        let four = program.declare_const("_4", Sort::int());
        let five = program.declare_const("_5", Sort::int());
        let six = program.declare_const("_6", Sort::int());
        let masked = |x: Expr| x.int2bv(8).bvand(Expr::int(1).int2bv(8)).bv2int();
        program.assert(Expr::and_many(vec![
            six.clone().int_le(Expr::int(1)),
            Expr::or_many(vec![
                d.clone().eq(Expr::int(0)),
                d.clone().eq(Expr::int(2)),
                d.clone().eq(Expr::int(3)),
            ]),
            three.clone().eq(d),
            three.eq(Expr::int(0)),
            Expr::bool_const(true),
            six.clone().eq(masked(four)),
            five.clone().eq(six),
            five.int_ge(Expr::int(bound)),
        ]));
        program.check_sat();
        program
    };
    let program = build(3);
    assert!(
        program
            .to_string()
            .contains("(bv2int (bvand ((_ int2bv 8) _4) ((_ int2bv 8) 1)))"),
        "{program}"
    );
    let outcomes = execute_incremental(&program).unwrap();
    assert!(matches!(outcomes[0].result, ExecuteTypedResult::Verified));
    let proof = outcomes[0]
        .unsat_proof
        .as_ref()
        .expect("the refutation publishes a strict artifact");
    proof
        .accept_for_consumer(ProofAcceptanceMode::Strict)
        .unwrap();
    assert!(
        proof.alethe.contains("((_ int2bv 8) 1)"),
        "the artifact assumes the authored conjunction: {}",
        proof.alethe
    );

    let outcomes = execute_incremental(&build(1)).unwrap();
    assert!(matches!(
        outcomes[0].result,
        ExecuteTypedResult::Counterexample(_)
    ));
}

/// Trust's `forall-bool` on the native lane: `(forall ((__trust_u_q Bool))
/// __trust_u_q)` is published by the nested-CEGQI expansion certificate,
/// whose proof replaced `last_proof` after the authored `assume` spellings
/// were restored. Its document assumed AY's freshened binder
/// (`__trust_u_q_0`), which Trust's Carcara gate refuses against Trust's own
/// problem text ("assumption not present in the problem"); it now assumes the
/// submitted source.
#[test]
fn native_expansion_certificate_assumes_the_submitted_binder() {
    let binder = "__trust_u_q";
    let mut program = AYProgram::new();
    program.set_option("produce-proofs", "true");
    program.set_logic("UF");
    program.assert(Expr::forall(
        vec![(binder.to_string(), Sort::bool())],
        Expr::var(binder, Sort::bool()),
    ));
    program.check_sat();
    let outcomes = execute_incremental(&program).unwrap();
    assert_eq!(outcomes.len(), 1);
    assert!(
        matches!(outcomes[0].result, ExecuteTypedResult::Verified),
        "{:?}",
        outcomes[0].result
    );
    let proof = outcomes[0].unsat_proof.as_ref().unwrap();
    let authored = format!("(assume t0 (forall (({binder} Bool)) {binder}))");
    assert_eq!(
        proof
            .alethe
            .lines()
            .find(|line| line.starts_with("(assume ")),
        Some(authored.as_str()),
        "{}",
        proof.alethe
    );
    assert!(
        !proof.alethe.contains(&format!("{binder}_")),
        "a freshened binder is left in the document:\n{}",
        proof.alethe
    );
    proof
        .accept_for_consumer(ProofAcceptanceMode::Strict)
        .unwrap();
}
