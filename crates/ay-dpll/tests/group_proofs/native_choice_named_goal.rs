//! Captured deductive-checks ChoiceRecommendation: actual named native hypotheses,
//! followed by the unnamed negated Boolean-UF goal. No SMT parser in native
//! controls; the parsed projection is a separate comparison control.

use ay_dpll::api::{Logic, ModelValue, Solver, Sort, Term};
use ay_dpll::{CounterexampleStyle, Executor};
use std::time::Duration;

fn assert_hypothesis(solver: &mut Solver, root: Term, index: usize, cores: bool) {
    if cores {
        solver
            .try_assert_named(root, &format!("qh{index}"))
            .expect("named native root");
    } else {
        solver.try_assert_term(root).expect("plain native root");
    }
}

fn native(cores: bool, keep_goal_hypothesis: bool) -> Solver {
    let mut solver = Solver::new(Logic::All);
    solver.set_counterexample_style(CounterexampleStyle::Readable);
    solver.set_produce_proofs(true);
    solver.set_produce_unsat_cores(true);
    solver.set_timeout(Some(Duration::from_millis(10_000)));
    solver.set_quantifier_deadline_backstop(false);
    solver
        .try_set_option("rlimit", "400000")
        .expect("original conflict budget");
    solver.set_memory_limit(Some(512 * 1024 * 1024));
    if !cores {
        solver.set_produce_unsat_cores(false);
    }
    let v0 = solver.declare_const("v0", Sort::Int);
    let _qb3 = solver.declare_const("qb3", Sort::Int);
    let sq0 = solver.declare_const("sq0", Sort::Int);
    for name in ["nl_mul", "nl_div", "nl_mod"] {
        solver
            .try_declare_fun(name, &[Sort::Int, Sort::Int], Sort::Int)
            .expect("native declaration");
    }
    for name in [
        "clip_u8_oob",
        "clip_u16_oob",
        "clip_u32_oob",
        "clip_u64_oob",
        "clip_u128_oob",
        "clip_i8_oob",
        "clip_i16_oob",
        "clip_i32_oob",
        "clip_i64_oob",
        "clip_i128_oob",
        "clip_nat_oob",
    ] {
        solver
            .try_declare_fun(name, &[Sort::Int], Sort::Int)
            .expect("native declaration");
    }
    for (name, result) in [
        ("sf0", Sort::Int),
        ("sf1", Sort::Bool),
        ("sf2", Sort::Bool),
        ("sf3", Sort::Int),
        ("rf3", Sort::Int),
    ] {
        solver
            .try_declare_fun(name, &[Sort::Int], result)
            .expect("native declaration");
    }
    let qa1 = solver
        .try_declare_fun("qa1", &[Sort::Int], Sort::Bool)
        .expect("native Boolean UF");
    let zero = solver.int_const(0);
    let h1 = solver.try_lt(zero, v0).expect("h1");
    assert_hypothesis(&mut solver, h1, 0, cores);
    let h2 = solver.bool_const(true);
    assert_hypothesis(&mut solver, h2, 1, cores);
    let predicate = solver.try_apply(&qa1, &[v0]).expect("qa1(v0)");
    let equality = solver.try_eq(sq0, v0).expect("sq0=v0");
    let qi3 = solver.try_implies(predicate, equality).expect("qi3");
    assert_hypothesis(&mut solver, qi3, 2, cores);
    if keep_goal_hypothesis {
        assert_hypothesis(&mut solver, predicate, 3, cores);
    }
    let negative_equality = solver.try_not(equality).expect("sq0!=v0");
    let either = solver
        .try_or(equality, negative_equality)
        .expect("equality excluded middle");
    let antecedent = solver.try_and(predicate, either).expect("qi5 antecedent");
    let negative_predicate = solver.try_not(predicate).expect("not qa1(v0)");
    let consequent = solver
        .try_implies(negative_predicate, negative_equality)
        .expect("qi5 consequent");
    let qi5 = solver.try_implies(antecedent, consequent).expect("qi5");
    // Build/assert each root in sequence, exactly like the fresh core parser
    // per hypothesis; named-core symbols therefore keep their allocation order.
    assert_hypothesis(&mut solver, qi5, 4, cores);
    solver
        .try_assert_term(negative_predicate)
        .expect("unnamed negated goal");
    solver
}

fn strict_unsat(mut solver: Solver, cores: bool) {
    let result = solver.check_sat();
    assert!(result.is_unsat(), "{result:?}");
    assert!(
        result.has_unsat_emission_witness() && result.was_unsat_strictly_verified(),
        "{result:?}"
    );
    assert!(!result.was_unsat_corroborated(), "{result:?}");
    assert!(result
        .accept_for_consumer()
        .expect("strict certified public UNSAT")
        .is_unsat());
    assert!(solver
        .last_strict_proof_quality()
        .expect("proof explicitly requested")
        .expect("independent strict proof check")
        .is_complete());
    if cores {
        let core = solver.try_get_unsat_core().expect("actual named core");
        assert!(
            core.iter().any(|name| name == "qh3"),
            "the direct goal assumption is necessary: {core:?}"
        );
        assert!(
            core.iter()
                .all(|name| ["qh0", "qh1", "qh2", "qh3", "qh4"].contains(&name.as_str())),
            "{core:?}"
        );
    }
}

#[test]
fn captured_native_named_choice_goal_has_a_strict_refutation() {
    strict_unsat(native(true, true), true);
}

#[test]
fn captured_native_plain_choice_goal_has_a_strict_refutation() {
    strict_unsat(native(false, true), false);
}

#[test]
fn removing_the_native_goal_hypothesis_keeps_a_checked_sat_model() {
    for cores in [true, false] {
        let mut solver = native(cores, false);
        let roots = solver.assertions();
        let result = solver.check_sat();
        assert!(
            result.is_sat() && result.has_sat_emission_witness() && result.was_model_validated(),
            "{result:?}"
        );
        assert!(result
            .accept_for_consumer()
            .expect("checked public SAT")
            .is_sat());
        for root in roots {
            assert!(matches!(
                solver.try_get_value(root),
                Ok(ModelValue::Bool(true))
            ));
        }
    }
}

const PARSED: &str = include_str!("native_choice_named_goal.smt2");

#[test]
fn parsed_projection_keeps_the_same_strict_goal_refutation() {
    let commands = ay_frontend::parse(PARSED).expect("actual parsed counterpart");
    let mut executor = Executor::new();
    let outputs = executor
        .execute_all(&commands)
        .expect("execute parsed counterpart");
    assert_eq!(
        outputs.first().map(String::as_str),
        Some("unsat"),
        "{outputs:?}"
    );
    let proof = executor.last_proof().expect("requested parsed proof");
    assert!(ay_proof::check_proof_strict(proof, executor.terms())
        .expect("strict parsed proof")
        .is_complete());
}

#[test]
fn parsed_projection_without_goal_hypothesis_is_sat() {
    let source = PARSED
        .replace("(assert (! (qa1 v0) :named qh3))\n", "")
        .replace("(get-proof)\n", "");
    let commands = ay_frontend::parse(&source).expect("parsed SAT twin");
    let mut executor = Executor::new();
    let outputs = executor
        .execute_all(&commands)
        .expect("execute parsed SAT twin");
    assert_eq!(
        outputs.last().map(String::as_str),
        Some("sat"),
        "{outputs:?}"
    );
}
