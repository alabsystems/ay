// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Public consumer regressions for assumption proofs and read-plan admission.
//! The AY libraries are ordinary dependencies of this integration target.

use ay_dpll::api::{Logic, SolveDetails, Solver, Sort, Term};
use ay_dpll::{CounterexampleStyle, Executor};
use ay_frontend::{Command, Context, SharedSurfaceLimits};

fn solver() -> Solver {
    let mut solver = Solver::try_new(Logic::All).expect("Core-selected logic");
    solver.set_counterexample_style(CounterexampleStyle::Readable);
    solver.set_produce_proofs(true);
    solver.set_produce_unsat_cores(true);
    solver.set_timeout(Some(std::time::Duration::from_millis(120_000)));
    solver.set_quantifier_deadline_backstop(false);
    solver
        .try_set_option("rlimit", "400000")
        .expect("Core conflict bound");
    let requested = 512_usize.saturating_mul(1024 * 1024);
    let memory = requested
        .max(ay_sys::default_memory_limit())
        .max(ay_sys::current_rss_bytes().saturating_add(requested));
    solver.set_memory_limit((memory > 0).then_some(memory));
    solver
}

fn with_named_assumption(boolean: bool) -> (Solver, Term, Term) {
    let mut solver = solver();
    let x = solver.declare_const("x", Sort::bitvec(32));
    let zero = solver.try_bv_const(0, 32).expect("signed zero");
    let assumption = if boolean {
        let ten = solver.try_bv_const(10, 32).expect("signed upper bound");
        let lower = solver.try_bvsle(zero, x).expect("0 <= x");
        let upper = solver.try_bvslt(x, ten).expect("x < 10");
        solver.try_and(lower, upper).expect("bounded interval")
    } else {
        solver.try_bvslt(zero, x).expect("0 < x")
    };
    solver
        .try_assert_named(assumption, "__deductive_checks_assumption_0")
        .expect("Core's native named assumption");
    (solver, x, zero)
}

fn require_strict_unsat(solver: &Solver, details: &SolveDetails) {
    assert!(details.result.is_unsat(), "{details:?}");
    assert!(details.result.was_unsat_strictly_verified(), "{details:?}");
    assert!(details
        .accept_for_consumer()
        .expect("checked UNSAT is consumable")
        .is_unsat());
    // This public accessor runs the ordinary live-query strict owner, including
    // its complete authored premise scope and existing resource controls.
    assert!(solver
        .last_strict_proof_quality()
        .expect("the current query retains its requested native proof")
        .expect("the actual native proof strictly checks")
        .is_complete());
}

fn check_native_history(boolean: bool) {
    {
        let (mut precheck, _, _) = with_named_assumption(boolean);
        let details = precheck.check_sat_with_details();
        assert!(details.result.is_sat(), "{details:?}");
        assert!(details
            .accept_for_consumer()
            .expect("satisfiable precheck")
            .is_sat());
    }
    let (mut solver, x, zero) = with_named_assumption(boolean);
    let target = if boolean {
        let ten = solver.try_bv_const(10, 32).expect("signed upper bound");
        let below = solver.try_bvslt(x, zero).expect("x < 0");
        let above = solver.try_bvsle(ten, x).expect("10 <= x");
        solver.try_or(below, above).expect("outside the interval")
    } else {
        solver.try_bvslt(x, zero).expect("x < 0")
    };
    solver.try_push().expect("Core target frame");
    solver
        .try_assert_term(target)
        .expect("Core's unnamed target");
    let primary = solver.check_sat_with_details();
    require_strict_unsat(&solver, &primary);
    solver.try_pop().expect("remove only the target frame");
    let restored = solver.check_sat_with_details();
    assert!(restored.result.is_sat(), "{restored:?}");
    assert!(restored
        .accept_for_consumer()
        .expect("restored base")
        .is_sat());
    let assumed = solver
        .try_check_sat_assuming_with_details(&[target])
        .expect("temporary contradictory assumption");
    require_strict_unsat(&solver, &assumed.solve);
    let after_assumption = solver.check_sat_with_details();
    assert!(after_assumption.result.is_sat(), "{after_assumption:?}");
    assert!(after_assumption
        .accept_for_consumer()
        .expect("no stale assumption")
        .is_sat());
    assert!(solver.last_strict_proof_quality().is_none());
}

#[test]
fn public_native_boolean_bounds_keep_temporary_assumption_proofs() {
    check_native_history(true);
}

#[test]
fn public_native_positive_bound_keeps_temporary_assumption_proofs() {
    check_native_history(false);
}

fn ground_limits() -> SharedSurfaceLimits {
    // Exact existing planner limits in proof_trust_surgery_surface_ground.rs.
    SharedSurfaceLimits {
        distinct_nodes: 16_384,
        depth: 96,
        node_visits: 1_048_576,
        token_visits: 8 * 1024 * 1024,
    }
}

fn assertion(text: &str) -> ay_frontend::command::Term {
    let commands = ay_frontend::parse(&format!("(assert {text})")).expect("source assertion");
    let Command::Assert(source) = &commands[0] else {
        panic!("assertion");
    };
    source.clone()
}

#[test]
fn public_read_plan_keeps_exact_source_sharing_and_canonical_equality_separate() {
    let source = assertion("(and (= (select a (bvadd x #x00)) (select a x)) (= (select a (bvadd x #x00)) (select a x)))");
    let mut context = Context::new();
    for command in ay_frontend::parse(
        "(declare-const x (_ BitVec 8))
         (declare-const a (Array (_ BitVec 8) (_ BitVec 8)))",
    )
    .expect("declarations")
    {
        context.process_command(&command).expect("declare");
    }
    let typed = context
        .elaborate_shared_surface_reading_array(&source, ground_limits(), |_| false)
        .expect("genuine source reads are admitted");
    assert!(typed.reads_array());
    let ay_frontend::command::Term::App(_, conjuncts) = &source else {
        panic!("and");
    };
    assert_eq!(
        typed.node_index(&context, &conjuncts[0]),
        typed.node_index(&context, &conjuncts[1])
    );
    let ay_frontend::command::Term::App(_, sides) = &conjuncts[0] else {
        panic!("equality");
    };
    assert_ne!(
        typed.node_index(&context, &sides[0]),
        typed.node_index(&context, &sides[1])
    );
    assert_eq!(
        typed.canonical(&context, &sides[0]).expect("offset read"),
        typed.canonical(&context, &sides[1]).expect("plain read")
    );
}

#[test]
fn public_no_select_decline_preserves_live_context_and_scoped_solving() {
    let mut executor = Executor::new();
    executor
        .execute_all(
            &ay_frontend::parse(
                "(set-option :produce-proofs true)
                 (set-option :check-proofs-strict true)
                 (set-logic QF_AUFBV)
                 (declare-const A (Array (_ BitVec 8) (_ BitVec 8)))
                 (declare-const B (Array (_ BitVec 8) (_ BitVec 8)))
                 (declare-const k (_ BitVec 8))
                 (declare-const v (_ BitVec 8))
                 (assert (= (ite true A (store B k v)) A))",
            )
            .expect("array source"),
        )
        .expect("initial source");
    assert!(executor.script_strict_proofs_requested());
    let source = executor.context().assertions_parsed()[0].clone();
    let before = (
        executor.terms().len(),
        executor.terms().checker_visible_metadata_generation(),
        executor.terms().var_counter(),
        executor.context().source_context_stamp(),
    );
    assert!(executor
        .context_mut()
        .elaborate_shared_surface_reading_array(&source, ground_limits(), |_| false)
        .is_none());
    assert!(
        before
            == (
                executor.terms().len(),
                executor.terms().checker_visible_metadata_generation(),
                executor.terms().var_counter(),
                executor.context().source_context_stamp(),
            )
    );
    assert!(executor.last_proof().is_none());
    assert_eq!(
        executor
            .execute_all(&ay_frontend::parse("(check-sat)").unwrap())
            .unwrap(),
        ["sat"]
    );
    assert_eq!(
        executor
            .execute_all(
                &ay_frontend::parse("(push 1)(assert (= A (store B k v)))(check-sat)").unwrap()
            )
            .unwrap(),
        ["sat"]
    );
    executor
        .execute_all(&ay_frontend::parse("(assert (not (= A (store B k v))))").unwrap())
        .unwrap();
    // Capture genuine authored roots before solving can add transient axioms.
    let authored = executor
        .context()
        .concrete_authored_assertion_terms_aligned_bounded(3)
        .expect("exact three authored assertions retain their own source rows");
    assert_eq!(authored.len(), 3);
    assert_eq!(
        executor
            .execute_all(&ay_frontend::parse("(check-sat)").unwrap())
            .unwrap(),
        ["unsat"]
    );
    let proof = executor.last_proof().expect("actual scoped native proof");
    assert!(ay_proof::check_proof_strict_with_context(
        proof,
        executor.terms(),
        None,
        None,
        Some(&authored),
    )
    .expect("strict proof checks against the independently captured authored roots")
    .is_complete());
    assert_eq!(
        executor
            .execute_all(&ay_frontend::parse("(pop 1)(check-sat)").unwrap())
            .unwrap(),
        ["sat"]
    );
    assert!(executor.last_proof().is_none());
}
