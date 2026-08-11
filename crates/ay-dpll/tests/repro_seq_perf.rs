// Repro for the model-checker consumer's tla-ay BMC seq-Append perf regression (ed035b88 good -> 3f0ec101 bad).
//
// Mirrors ty test bmc::tests::compound_e2e::test_compound_e2e_seq_append_verify_head_and_len:
// a 1-step BMC instance over QF_AUFLIA where a bounded Int sequence is encoded as
// (Array Int Int) + Int length per step.
//
//   Init:  len0 = 1  /\  select(arr0, 1) = 10
//   Next:  arr1 = store(arr0, len0 + 1, 20)  /\  len1 = len0 + 1
//   Check: len1 = 2  /\  select(arr1, 1) = 10  /\  select(arr1, 2) = 20
//
// Expected: Sat, in well under 10 s. The distinctive feature vs. the fast sibling
// tests (Tail / UNCHANGED / literal) is the store at a SYMBOLIC index (len0 + 1)
// combined with selects at constant indices on the stored array.

use ay_dpll::api::{Logic, SolveResult, Solver, Sort};
use std::time::Instant;

#[test]
fn repro_seq_append_symbolic_store_index() {
    let mut solver = Solver::try_new(Logic::QfAuflia).expect("solver");
    let arr_sort = Sort::array(Sort::Int, Sort::Int);

    // declare_seq_var("s", Int, max_len=5) with bound k=1: two steps.
    let arr0 = solver.declare_const("s__arr__0", arr_sort.clone());
    let len0 = solver.declare_const("s__len__0", Sort::Int);
    let zero = solver.int_const(0);
    let five = solver.int_const(5);
    let ge0 = solver.try_ge(len0, zero).unwrap();
    let le0 = solver.try_le(len0, five).unwrap();
    solver.try_assert_term(ge0).unwrap();
    solver.try_assert_term(le0).unwrap();

    let arr1 = solver.declare_const("s__arr__1", arr_sort);
    let len1 = solver.declare_const("s__len__1", Sort::Int);
    let ge1 = solver.try_ge(len1, zero).unwrap();
    let le1 = solver.try_le(len1, five).unwrap();
    solver.try_assert_term(ge1).unwrap();
    solver.try_assert_term(le1).unwrap();

    // Init: s = <<10>>  ==>  (len0 = 1) /\ (select(arr0, 1) = 10)
    let one = solver.int_const(1);
    let ten = solver.int_const(10);
    let len0_eq = solver.try_eq(len0, one).unwrap();
    let sel0_1 = solver.try_select(arr0, one).unwrap();
    let sel0_1_eq = solver.try_eq(sel0_1, ten).unwrap();
    let init = solver.try_and(len0_eq, sel0_1_eq).unwrap();
    solver.try_assert_term(init).unwrap();

    // Next: s' = Append(s, 20)
    //   ==> (arr1 = store(arr0, len0 + 1, 20)) /\ (len1 = len0 + 1)
    let twenty = solver.int_const(20);
    let new_len = solver.try_add(len0, one).unwrap();
    let new_arr = solver.try_store(arr0, new_len, twenty).unwrap();
    let arr_eq = solver.try_eq(arr1, new_arr).unwrap();
    let len_eq = solver.try_eq(len1, new_len).unwrap();
    let next = solver.try_and(arr_eq, len_eq).unwrap();
    solver.try_assert_term(next).unwrap();

    // Check: Len(s') = 2
    let two = solver.int_const(2);
    let len1_eq = solver.try_eq(len1, two).unwrap();
    solver.try_assert_term(len1_eq).unwrap();

    // Check: s'[1] = 10
    let sel1_1 = solver.try_select(arr1, one).unwrap();
    let head_eq = solver.try_eq(sel1_1, ten).unwrap();
    solver.try_assert_term(head_eq).unwrap();

    // Check: s'[2] = 20
    let sel1_2 = solver.try_select(arr1, two).unwrap();
    let tail_eq = solver.try_eq(sel1_2, twenty).unwrap();
    solver.try_assert_term(tail_eq).unwrap();

    let t0 = Instant::now();
    let result = solver.check_sat().into_inner();
    let elapsed = t0.elapsed();
    eprintln!("repro_seq_append_symbolic_store_index: check_sat took {elapsed:?}");
    assert!(
        matches!(result, SolveResult::Sat),
        "expected Sat, got {result:?}"
    );
    assert!(
        elapsed.as_secs() < 10,
        "check_sat took {elapsed:?} (> 10 s) — perf regression"
    );
}
