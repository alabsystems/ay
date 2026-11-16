// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use std::cell::Cell;

const WORDS: &str = "(declare-const x (_ BitVec 8)) (declare-const y (_ BitVec 8))";

fn fixture(declarations: &str, assertion: &str) -> (Executor, TermId, FrontendTerm) {
    let mut executor = Executor::new();
    executor
        .execute_all(&ay_frontend::parse(declarations).expect("declarations"))
        .expect("exact live source declarations");
    let parsed = ay_frontend::parse(&format!("(assert {assertion})")).expect("assertion");
    let [Command::Assert(surface)] = parsed.as_slice() else {
        panic!("one source root")
    };
    let surface = surface.clone();
    let root = executor
        .raw_intern_surface(&surface)
        .expect("raw source root");
    (executor, root, surface)
}

fn screened(executor: &Executor, root: TermId) -> bool {
    Screen::new(&executor.ctx, &executor.proof_source_work, &|| false).may_skip(root, &[root])
}

#[test]
fn six_exact_original_walker_division_roots_skip_only_their_singletons() {
    let declarations = "(declare-const |check_correct_ensures_walked::local_7_addr| (_ BitVec 64))
(declare-const |check_correct_ensures_walked::local_4_addr| (_ BitVec 64))
(declare-const |check_correct_ensures_walked::local_86_addr| (_ BitVec 64))";
    let originals = [
        "(= (bvudiv |check_correct_ensures_walked::local_7_addr| #x0000000000100000) (bvudiv (bvadd |check_correct_ensures_walked::local_7_addr| #x0000000000000003) #x0000000000100000))",
        "(= (bvudiv (bvsub |check_correct_ensures_walked::local_7_addr| #x0000000000000000) #x0000000000100000) (bvudiv (bvadd (bvsub |check_correct_ensures_walked::local_7_addr| #x0000000000000000) #x0000000000000004) #x0000000000100000))",
        "(= (bvudiv |check_correct_ensures_walked::local_4_addr| #x0000000000100000) (bvudiv (bvadd |check_correct_ensures_walked::local_4_addr| #x0000000000000003) #x0000000000100000))",
        "(= (bvudiv (bvsub |check_correct_ensures_walked::local_4_addr| #x0000000000000000) #x0000000000100000) (bvudiv (bvadd (bvsub |check_correct_ensures_walked::local_4_addr| #x0000000000000000) #x0000000000000004) #x0000000000100000))",
        "(= (bvudiv |check_correct_ensures_walked::local_86_addr| #x0000000000100000) (bvudiv (bvadd |check_correct_ensures_walked::local_86_addr| #x0000000000000007) #x0000000000100000))",
        "(= (bvudiv (bvsub |check_correct_ensures_walked::local_86_addr| #x0000000000000000) #x0000000000100000) (bvudiv (bvadd (bvsub |check_correct_ensures_walked::local_86_addr| #x0000000000000000) #x0000000000000008) #x0000000000100000))",
    ];
    for original in originals {
        let (executor, root, surface) = fixture(declarations, original);
        assert!(screened(&executor, root), "{original}");
        assert_eq!(
            candidate_selections(
                &[(root, &surface)],
                &[root],
                &executor.ctx,
                &executor.proof_source_work,
                &|| false
            ),
            [] as [Vec<(TermId, &ay_frontend::Term)>; 0]
        );
    }
}

#[test]
fn modular_reverse_wrap_and_commuted_offsets_have_exact_zero_quotient_witnesses() {
    for original in [
        "(= (bvudiv x #x10) (bvudiv (bvsub x #x01) #x10))",
        "(= (bvudiv (bvsub x #xff) #x10) (bvudiv (bvadd #x02 x) #x10))",
        "(= (bvudiv (bvadd x #xff) #x10) (bvudiv (bvsub x #x02) #x10))",
        "(= (bvudiv (bvadd (bvsub x #xff) #x02) #x10) (bvudiv (bvadd x #x04) #x10))",
        "(= (bvudiv x #x01) (bvudiv (bvadd x #x00) #x01))",
    ] {
        let (executor, root, _) = fixture(WORDS, original);
        assert!(screened(&executor, root), "{original}");
    }
}

#[test]
fn divisor_one_and_exact_boundary_failures_keep_legacy_singletons() {
    for original in [
        "(= (bvudiv x #x01) (bvudiv (bvadd x #x01) #x01))",
        "(= (bvudiv x #x10) (bvudiv (bvadd x #x10) #x10))",
        "(= (bvudiv x #x10) (bvudiv (bvsub x #x10) #x10))",
        "(= (bvudiv x #x80) (bvudiv (bvadd x #x80) #x80))",
    ] {
        let (executor, root, surface) = fixture(WORDS, original);
        assert!(!screened(&executor, root), "{original}");
        let selections = candidate_selections(
            &[(root, &surface)],
            &[root],
            &executor.ctx,
            &executor.proof_source_work,
            &|| false,
        );
        assert_eq!(selections.len(), 1);
        assert_eq!(selections[0][0].0, root);
    }
}

#[test]
fn unequal_variables_divisors_zero_and_nonliteral_divisors_never_gain_advice() {
    for original in [
        "(= (bvudiv x #x10) (bvudiv (bvadd y #x01) #x10))",
        "(= (bvudiv x #x10) (bvudiv (bvadd x #x01) #x11))",
        "(= (bvudiv x #x00) (bvudiv (bvadd x #x01) #x00))",
        "(= (bvudiv x y) (bvudiv (bvadd x #x01) y))",
    ] {
        let (executor, root, _) = fixture(WORDS, original);
        assert!(!screened(&executor, root), "{original}");
    }
}

#[test]
fn nonaffine_indexed_and_literal_minus_variable_inputs_keep_legacy_search() {
    for original in [
        "(= (bvudiv x #x10) (bvudiv (bvsub #x01 x) #x10))",
        "(= (bvudiv x #x10) (bvudiv (bvadd x x) #x10))",
        "(= (bvudiv x #x10) (bvudiv (bvadd x #x01 #x01) #x10))",
        "(= (bvudiv x #x10) (bvudiv ((_ rotate_left 0) x) #x10))",
        "(= (bvudiv x #x10) (bvudiv (bvmul x #x01) #x10))",
    ] {
        let (executor, root, _) = fixture(WORDS, original);
        assert!(!screened(&executor, root), "{original}");
    }
}

#[test]
fn native_aliases_builtin_shadow_and_popped_variables_are_not_source_witnesses() {
    let original = "(= (bvudiv x #x10) (bvudiv (bvadd x #x01) #x10))";
    let (mut executor, root, _) = fixture(WORDS, original);
    let x = executor.ctx.terms.find_var("x").expect("source x");
    executor.ctx.register_symbol("x".into(), x, Sort::bitvec(8));
    assert!(!screened(&executor, root));
    let (mut executor, root, _) = fixture(
        "(declare-const y (_ BitVec 8)) (push 1) (declare-const x (_ BitVec 8))",
        original,
    );
    executor
        .execute_all(&ay_frontend::parse("(pop 1)").expect("pop"))
        .expect("source pop");
    assert!(!screened(&executor, root));
    let (mut executor, root, _) = fixture(WORDS, original);
    let x = executor.ctx.terms.find_var("x").expect("source x");
    // Textual bvudiv redeclaration is rejected before screening. Inject the
    // native binding directly to exercise the independent screen refusal.
    executor
        .ctx
        .register_symbol("bvudiv".into(), x, Sort::bitvec(8));
    assert!(
        !screened(&executor, root),
        "native bound spelling is not builtin division"
    );
}

#[test]
fn malformed_constants_missing_terms_and_cycles_do_not_authorize_skipping() {
    let original = "(= (bvudiv x #x10) (bvudiv (bvadd x #x01) #x10))";
    let (mut executor, root, _) = fixture(WORDS, original);
    let TermData::App(_, sides) = executor.ctx.terms.get(root) else {
        panic!("equality")
    };
    let right = sides[1];
    let TermData::App(_, args) = executor.ctx.terms.get(right) else {
        panic!("division")
    };
    let numerator = args[0];
    let denominator = args[1];
    let entries = executor.ctx.terms.entries_snapshot();
    let counter = executor.ctx.terms.var_counter();
    for kind in 0..5 {
        let mut changed = entries.clone();
        match kind {
            0 => {
                changed[denominator.0 as usize].0 = TermData::Const(Constant::BitVec {
                    value: (-1).into(),
                    width: 8,
                })
            }
            1 => {
                changed[denominator.0 as usize].0 = TermData::Const(Constant::BitVec {
                    value: 256.into(),
                    width: 8,
                })
            }
            2 => {
                changed[denominator.0 as usize].0 = TermData::Const(Constant::BitVec {
                    value: 16.into(),
                    width: 7,
                })
            }
            3 => {
                changed[numerator.0 as usize].0 =
                    TermData::App(Symbol::named("bvadd"), vec![numerator, denominator])
            }
            _ => {
                changed[right.0 as usize].0 =
                    TermData::App(Symbol::named("bvudiv"), vec![TermId::SENTINEL, denominator])
            }
        }
        executor.ctx.terms = TermStore::from_entries(changed, None, None, counter);
        assert!(!screened(&executor, root), "malformed case {kind}");
    }
    assert!(!screened(&executor, TermId::SENTINEL));
}

#[test]
fn one_bit_and_maximum_supported_width_use_the_same_bounded_algebra() {
    for (declarations, original) in [
        (
            "(declare-const x (_ BitVec 1))",
            "(= (bvudiv x #b1) (bvudiv (bvadd x #b0) #b1))",
        ),
        (
            "(declare-const x (_ BitVec 4096))",
            "(= (bvudiv x (_ bv16 4096)) (bvudiv (bvadd x (_ bv1 4096)) (_ bv16 4096)))",
        ),
        (
            "(declare-const x (_ BitVec 4096))",
            "(= (bvudiv x (_ bv16 4096)) (bvudiv (bvsub x (_ bv1 4096)) (_ bv16 4096)))",
        ),
    ] {
        let (executor, root, _) = fixture(declarations, original);
        assert!(screened(&executor, root));
    }
    let (executor, root, _) = fixture(
        "(declare-const x (_ BitVec 4097))",
        "(= (bvudiv x (_ bv16 4097)) (bvudiv (bvadd x (_ bv1 4097)) (_ bv16 4097)))",
    );
    assert!(!screened(&executor, root));
}

#[test]
fn recovering_original_stop_is_sticky_for_affine_advice() {
    let (executor, root, _) = fixture(WORDS, "(= (bvudiv x #x10) (bvudiv (bvadd x #x01) #x10))");
    let calls = Cell::new(0usize);
    let healthy = || {
        calls.set(calls.get() + 1);
        false
    };
    assert!(
        Screen::new(&executor.ctx, &executor.proof_source_work, &healthy).may_skip(root, &[root])
    );
    let total = calls.get();
    for stop_at in [1, total / 2, total] {
        calls.set(0);
        let stop = || {
            calls.set(calls.get() + 1);
            calls.get() == stop_at
        };
        let mut screen = Screen::new(&executor.ctx, &executor.proof_source_work, &stop);
        assert!(!screen.may_skip(root, &[root]));
        assert!(!screen.may_skip(root, &[root]));
        assert_eq!(calls.get(), stop_at);
    }
}

#[test]
fn cumulative_original_work_and_terminal_exhaustion_keep_legacy_attempts() {
    let (executor, root, surface) =
        fixture(WORDS, "(= (bvudiv x #x10) (bvudiv (bvadd x #x01) #x10))");
    let before = executor.proof_source_work.remaining_for_test();
    assert!(screened(&executor, root));
    let used = before - executor.proof_source_work.remaining_for_test();
    executor.proof_source_work.set_remaining_for_test(used - 1);
    let choices = candidate_selections(
        &[(root, &surface), (root, &surface)],
        &[root],
        &executor.ctx,
        &executor.proof_source_work,
        &|| false,
    );
    assert_eq!(
        choices.len(),
        3,
        "both singletons and the unchanged joint remain"
    );
    let remainder = executor.proof_source_work.remaining_for_test();
    assert!(remainder < used, "no refund or fresh per-root allowance");
    assert!(!screened(&executor, root));
    assert!(executor.proof_source_work.remaining_for_test() <= remainder);
}

#[test]
fn jointly_contradictory_definitions_keep_all_affine_roots_and_strict_proof() {
    let declarations = "(declare-const x (_ BitVec 8))";
    let sources = [
        "(= x #x00)",
        "(= x #x01)",
        "(= (bvudiv x #x10) (bvudiv (bvadd x #x01) #x10))",
    ];
    let (mut executor, first, first_surface) = fixture(declarations, sources[0]);
    let second = ay_frontend::parse(&format!("(assert {})", sources[1])).expect("second");
    let third = ay_frontend::parse(&format!("(assert {})", sources[2])).expect("third");
    let [Command::Assert(second_surface)] = second.as_slice() else {
        panic!("second root")
    };
    let [Command::Assert(third_surface)] = third.as_slice() else {
        panic!("third root")
    };
    let second_root = executor
        .raw_intern_surface(second_surface)
        .expect("second raw root");
    let third_root = executor
        .raw_intern_surface(third_surface)
        .expect("third raw root");
    let roots = [
        (first, &first_surface),
        (second_root, second_surface),
        (third_root, third_surface),
    ];
    let scope = [first, second_root, third_root];
    let choices = candidate_selections(
        &roots,
        &scope,
        &executor.ctx,
        &executor.proof_source_work,
        &|| false,
    );
    assert_eq!(choices, vec![roots.to_vec()]);
    let script = format!(
        "(set-option :produce-proofs true) (set-logic QF_BV) {declarations}
(assert {}) (assert {}) (assert {}) (check-sat) (get-proof)",
        sources[0], sources[1], sources[2]
    );
    let mut production = Executor::new();
    let outputs = production
        .execute_all(&ay_frontend::parse(&script).expect("original joint input"))
        .expect("actual production solve");
    assert!(outputs.iter().any(|row| row == "unsat"));
    let document = outputs.last().expect("requested proof");
    assert!(
        !document.contains(":rule hole") && !document.contains(":rule trust"),
        "{document}"
    );
    let proof = production.last_proof.as_ref().expect("actual proof");
    assert!(production
        .check_proof_strict_with_datatypes(proof)
        .is_ok_and(|quality| quality.is_complete()));
    assert!(ay_proof::validate_reachable_assumes_in_problem_scope(
        proof,
        &production.proof_export_scope_assertions()
    )
    .is_ok());
}

#[test]
fn textual_builtin_division_redeclaration_is_rejected_before_singleton_screening() {
    let mut executor = Executor::new();
    let source = "(declare-const x (_ BitVec 8))
(declare-fun bvudiv ((_ BitVec 8) (_ BitVec 8)) (_ BitVec 8))";
    let commands = ay_frontend::parse(source).expect("original rejected declarations");
    let error = executor
        .execute_all(&commands)
        .expect_err("builtin division is reserved at elaboration");
    assert!(matches!(
        error,
        crate::ExecutorError::Elaborate(ay_frontend::ElaborateError::ReservedSymbol(ref name))
            if name == "bvudiv"
    ));
    assert!(!executor.ctx.has_symbol_binding("bvudiv"));
}
