// Regression test for the model-checker consumer-boundary rejection of trivially-SAT
// models (surfaced by the model-checker consumer's nested-powerset solves).
// A trivially-SAT solve (declared free Bool, no assertions) must yield a
// consumer-acceptable model per #8456: the trivially-SAT fast path marks
// last_model_validated = true (vacuous validation is validation), so
// accept_for_consumer() no longer rejects it with SatModelNotValidated.

use ay_dpll::api::{Logic, Solver, Sort};

#[test]
fn trivially_sat_free_bool_model_is_consumer_acceptable() {
    let mut solver = Solver::try_new(Logic::QfLia).expect("solver");
    let _b = solver.declare_const("free_b", Sort::Bool);
    let result = solver.try_check_sat().expect("check_sat");
    let inner = result.into_inner();
    assert!(
        matches!(inner, ay_dpll::api::SolveResult::Sat),
        "expected Sat, got {inner:?}"
    );
    let model = solver.try_get_model_for_consumer();
    assert!(
        model.is_ok(),
        "consumer boundary rejected trivially-SAT model: {:?}",
        model.err()
    );
}
