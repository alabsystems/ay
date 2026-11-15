// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::executor::Executor;
use crate::executor_types::SolveResult;
use ay_frontend::parse;

mod controls;
mod original;

fn setup(script: &str) -> Executor {
    let mut executor = Executor::new();
    executor.execute_all(&parse(script).unwrap()).unwrap();
    executor
}

fn script(value: u8, output: u8, predicate: &str) -> String {
    format!(
        "(set-logic QF_BVFP)
         (declare-const x (_ BitVec 4))
         (declare-const f (_ FloatingPoint 5 11))
         (assert (fp.isZero f))
         (assert (= x (_ bv{value} 4)))
         (assert (= (ite ({predicate} x #x2) #x3 #x4) (_ bv{output} 4)))"
    )
}

#[test]
fn hidden_bv_guards_keep_both_branches_and_reject_the_wrong_branch() {
    for predicate in [
        "=", "distinct", "bvult", "bvule", "bvugt", "bvuge", "bvslt", "bvsle", "bvsgt", "bvsge",
    ] {
        for value in [1, 2, 3, 15] {
            let signed = if value < 8 {
                value as i8
            } else {
                value as i8 - 16
            };
            let condition = match predicate {
                "=" => value == 2,
                "distinct" => value != 2,
                "bvult" => value < 2,
                "bvule" => value <= 2,
                "bvugt" => value > 2,
                "bvuge" => value >= 2,
                "bvslt" => signed < 2,
                "bvsle" => signed <= 2,
                "bvsgt" => signed > 2,
                _ => signed >= 2,
            };
            for output in [3, 4] {
                let mut executor = setup(&script(value, output, predicate));
                let roots = executor.ctx.assertions.clone();
                let result = executor.solve_fp_stateless().unwrap();
                let expected = output == if condition { 3 } else { 4 };
                assert_eq!(
                    matches!(result, SolveResult::Sat),
                    expected,
                    "{predicate}, x={value}, output={output}: {result:?}"
                );
                assert_eq!(result.is_unsat(), !expected);
                assert_eq!(executor.ctx.assertions, roots);
            }
        }
    }
}

#[test]
fn seeding_is_definition_only_and_sharing_does_not_mint_new_names() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::bitvec(4));
    let y = terms.mk_var("y", Sort::bitvec(4));
    let condition = terms.mk_app(Symbol::named("bvult"), [x, y], Sort::Bool);
    let value = terms.mk_ite_raw(condition, x, y);
    let root = terms.mk_app(Symbol::named("="), [value, x], Sort::Bool);
    let executor = Executor::new();
    let stop = FpStop::from_executor(&executor);
    let mut tseitin = Tseitin::new(&terms);
    seed(&terms, [root, root], &mut tseitin, &stop, &|| {}).unwrap();
    let variables = tseitin.num_vars();
    assert!(tseitin.get_var_for_term(condition).is_some());
    assert!(
        tseitin.take_new_clauses().is_empty(),
        "no guard/root activation"
    );
    seed(&terms, [root], &mut tseitin, &stop, &|| {}).unwrap();
    assert_eq!(tseitin.num_vars(), variables);
    assert!(tseitin.take_new_clauses().is_empty());
    let result = tseitin.into_assertion_result();
    let mut sat = ay_sat::Solver::new(result.num_vars as usize);
    let guard = result.term_to_var[&condition] as i32;
    sat.add_clause(vec![crate::cnf_lit_to_sat(-guard)]);
    assert!(
        sat.solve().is_sat(),
        "a definition does not assert its guard"
    );
}

#[test]
fn boolean_composite_guards_keep_their_existing_fp_semantics() {
    for (x, output) in [(1, 3), (3, 4)] {
        let body = format!(
            "(set-logic QF_BVFP)
             (declare-const x (_ BitVec 4))
             (declare-const f (_ FloatingPoint 5 11))
             (assert (fp.isZero f)) (assert (= x (_ bv{x} 4)))
             (assert (= (ite (and (bvult x #x2) (not (= x #x0))) #x3 #x4)
                        (_ bv{output} 4)))"
        );
        let mut executor = setup(&body);
        assert!(matches!(
            executor.solve_fp_stateless().unwrap(),
            SolveResult::Sat
        ));
    }
}

#[test]
fn incremental_reuse_keeps_definitions_global_and_activations_scoped() {
    let mut executor = setup(&format!("{} (push 1)", script(3, 4, "bvult")));
    assert!(matches!(
        executor.try_solve_fp_incremental().unwrap(),
        Some(SolveResult::Sat)
    ));
    let initial = executor
        .incr_fp_state
        .as_ref()
        .unwrap()
        .tseitin_state
        .next_var;
    assert!(matches!(
        executor.try_solve_fp_incremental().unwrap(),
        Some(SolveResult::Sat)
    ));
    assert_eq!(
        executor
            .incr_fp_state
            .as_ref()
            .unwrap()
            .tseitin_state
            .next_var,
        initial
    );
    executor
        .execute_all(&parse("(push 1) (assert (= x #x1))").unwrap())
        .unwrap();
    let result = executor.try_solve_fp_incremental().unwrap();
    assert!(result.is_some_and(|result| result.is_unsat()));
    executor.execute_all(&parse("(pop 1)").unwrap()).unwrap();
    assert!(matches!(
        executor.try_solve_fp_incremental().unwrap(),
        Some(SolveResult::Sat)
    ));
    assert!(!executor.incr_fp_state.as_ref().unwrap().disabled);
}

#[test]
fn mixed_fp_to_real_sites_seed_hidden_guards_without_asserting_them() {
    use super::super::to_real::collect_fp_to_real_sites;
    let executor = setup(
        "(set-logic ALL)
         (declare-const x (_ BitVec 4))
         (declare-const f (_ FloatingPoint 5 11))
         (declare-const g (_ FloatingPoint 5 11))
         (assert (> (fp.to_real (ite (bvult x #x2) f g)) 0.0))",
    );
    let sites = collect_fp_to_real_sites(&executor.ctx.terms, &executor.ctx.assertions);
    assert_eq!(sites.len(), 1);
    let stop = FpStop::from_executor(&executor);
    let encoded = executor
        .encode_fp_assertions_controlled(&[], &sites, &stop, &|_| {})
        .unwrap();
    assert!(encoded.term_to_fp.contains_key(&sites[0].arg));
    assert!(!encoded.tseitin_result.term_to_var.is_empty());
    assert!(!encoded.congruence_incomplete);
}

#[test]
fn mixed_fp_to_real_sites_do_not_strip_guard_binder_boundaries() {
    use super::super::bitblast::FpRealEncodingError;
    use super::super::to_real::collect_fp_to_real_sites;
    for binder in ["forall", "exists"] {
        let executor = setup(&format!(
            "(set-logic ALL)
             (declare-const f (_ FloatingPoint 5 11))
             (declare-const g (_ FloatingPoint 5 11))
             (assert ({binder} ((x (_ BitVec 4)))
               (> (fp.to_real (ite (bvult x #x2) f g)) 0.0)))"
        ));
        let sites = collect_fp_to_real_sites(&executor.ctx.terms, &executor.ctx.assertions);
        assert_eq!(sites.len(), 1);
        let stop = FpStop::from_executor(&executor);
        let encoded = executor.encode_fp_assertions_controlled(&[], &sites, &stop, &|_| {});
        assert!(matches!(encoded, Err(FpRealEncodingError::EncodingGap)));
    }
}
