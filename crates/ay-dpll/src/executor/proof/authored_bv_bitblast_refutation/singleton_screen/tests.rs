// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use std::cell::Cell;

const WORDS: &str = "(declare-const x (_ BitVec 8)) (declare-const y (_ BitVec 8))
                    (declare-const b Bool) (declare-const c Bool)";

fn fixture(declarations: &str, assertion: &str) -> (Executor, TermId, FrontendTerm) {
    let mut executor = Executor::new();
    let declarations = ay_frontend::parse(declarations).expect("source declarations");
    executor
        .execute_all(&declarations)
        .expect("declare original free symbols");
    let assertions =
        ay_frontend::parse(&format!("(assert {assertion})")).expect("source assertion");
    let [Command::Assert(surface)] = assertions.as_slice() else {
        panic!("one original root")
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
fn total_free_word_and_boolean_definitions_skip_only_their_singleton() {
    for source in [
        "(= x (bvadd y #x01))",
        "(= (bvsub y #x01) x)",
        "(= b (and c (bvult y #x0f)))",
        "(= x (ite c y #x00))",
        "(= x (bvudiv y #x00))",
        "(= x ((_ rotate_left 99) y))",
        "(= x (concat ((_ extract 7 4) y) ((_ extract 3 0) y)))",
    ] {
        let (executor, root, surface) = fixture(WORDS, source);
        assert!(screened(&executor, root), "{source}");
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
fn self_dependent_or_nondefinition_refutations_keep_the_legacy_attempt() {
    for source in [
        "(= x (bvadd x #x01))",
        "(= b (not b))",
        "(not (= (bvudiv x #x02) (bvlshr x #x01)))",
        "(bvult x y)",
        "(= x x)",
    ] {
        let (executor, root, surface) = fixture(WORDS, source);
        assert!(!screened(&executor, root), "{source}");
        let choices = candidate_selections(
            &[(root, &surface)],
            &[root],
            &executor.ctx,
            &executor.proof_source_work,
            &|| false,
        );
        assert_eq!(choices.len(), 1);
        assert_eq!(choices[0][0].0, root);
    }
}

#[test]
fn all_definition_roots_remain_ordered_and_complete_in_the_joint_attempt() {
    let (mut executor, first, first_surface) = fixture(WORDS, "(= x #x00)");
    let parsed = ay_frontend::parse("(assert (= x #x01))").expect("second source root");
    let [Command::Assert(second_surface)] = parsed.as_slice() else {
        panic!("one root")
    };
    let second = executor
        .raw_intern_surface(second_surface)
        .expect("second original root");
    let roots = [(first, &first_surface), (second, second_surface)];
    let choices = candidate_selections(
        &roots,
        &[first, second],
        &executor.ctx,
        &executor.proof_source_work,
        &|| false,
    );
    assert_eq!(choices.len(), 1);
    assert_eq!(choices[0], roots);
}

#[test]
fn actual_jointly_contradictory_definitions_still_require_strict_proof() {
    let mut executor = Executor::new();
    let commands = ay_frontend::parse(
        "(set-option :produce-proofs true) (set-logic QF_BV)
         (declare-const x (_ BitVec 8))
         (assert (= x #x00)) (assert (= x #x01)) (check-sat) (get-proof)",
    )
    .expect("joint contradiction");
    let outputs = executor
        .execute_all(&commands)
        .expect("actual production solve");
    assert!(outputs.iter().any(|row| row == "unsat"));
    let proof = outputs.last().expect("actual requested proof");
    assert!(proof.starts_with("(assume "));
    assert!(
        !proof.contains(":rule hole") && !proof.contains(":rule trust"),
        "{proof}"
    );
    let candidate = executor.last_proof.as_ref().expect("actual retained proof");
    assert!(executor
        .check_proof_strict_with_datatypes(candidate)
        .is_ok_and(|quality| quality.is_complete()));
    assert!(ay_proof::validate_reachable_assumes_in_problem_scope(
        candidate,
        &executor.proof_export_scope_assertions()
    )
    .is_ok());
}

#[test]
fn unbound_native_alias_and_popped_declarations_cannot_authorize_pruning() {
    let (mut executor, root, _) = fixture(WORDS, "(= x (bvadd y #x01))");
    let TermData::App(_, args) = executor.ctx.terms.get(root) else {
        panic!("equality")
    };
    let original_x = args[0];
    executor
        .ctx
        .register_symbol("x".into(), original_x, Sort::bitvec(8));
    assert!(
        !screened(&executor, root),
        "native registration is not source origin"
    );
    let (mut scoped, old, _) = fixture(
        "(declare-const y (_ BitVec 8)) (push 1) (declare-const x (_ BitVec 8))",
        "(= x y)",
    );
    scoped
        .execute_all(&ay_frontend::parse("(pop 1)").expect("pop source"))
        .expect("pop");
    assert!(!screened(&scoped, old));
}

#[test]
fn declared_builtin_spellings_and_ordinary_ufs_are_not_assigned_builtin_meaning() {
    for (decls, source) in [
        ("(declare-const x Bool) (declare-const y Bool) (declare-fun = (Bool Bool) Bool)", "(= x y)"),
        ("(declare-const b Bool) (declare-const c Bool) (declare-fun and (Bool Bool) Bool)", "(= b (and c c))"),
        ("(declare-const x (_ BitVec 8)) (declare-const y (_ BitVec 8)) (declare-fun f ((_ BitVec 8)) (_ BitVec 8))", "(= x (f y))"),
    ] {
        let (executor, root, _) = fixture(decls, source);
        assert!(!screened(&executor, root));
    }
}

#[test]
fn unsupported_integer_and_array_surfaces_keep_the_legacy_attempt() {
    for (decls, source) in [
        ("(declare-const x Int) (declare-const y Int)", "(= x (+ y 1))"),
        ("(declare-const x (Array (_ BitVec 8) (_ BitVec 8))) (declare-const y (Array (_ BitVec 8) (_ BitVec 8)))", "(= x y)"),
    ] {
        let (executor, root, _) = fixture(decls, source);
        assert!(!screened(&executor, root));
    }
}

#[test]
fn wrong_rank_missing_terms_and_cyclic_imports_never_skip_a_refutation() {
    let (mut executor, _, _) = fixture(WORDS, "(= b c)");
    let lhs = executor.ctx.terms.find_var("b").expect("source b");
    let original = executor.ctx.terms.entries_snapshot();
    let counter = executor.ctx.terms.var_counter();
    for kind in 0..6 {
        let mut entries = original.clone();
        let rhs = TermId(u32::try_from(entries.len()).expect("small original store"));
        let data = match kind {
            0 => TermData::Not(rhs),
            1 => TermData::Not(TermId::SENTINEL),
            2 => TermData::App(Symbol::named("bvadd"), vec![lhs, lhs]),
            3 => TermData::Forall(vec![("q".into(), Sort::Bool)], lhs, vec![]),
            4 => TermData::Exists(vec![("q".into(), Sort::Bool)], lhs, vec![]),
            _ => TermData::Let(vec![("q".into(), lhs)], lhs),
        };
        entries.push((data, Sort::Bool));
        let root = TermId(u32::try_from(entries.len()).expect("small original store"));
        entries.push((
            TermData::App(Symbol::named("="), vec![lhs, rhs]),
            Sort::Bool,
        ));
        executor.ctx.terms = TermStore::from_entries(entries, None, None, counter);
        assert!(!screened(&executor, root));
    }
}

#[test]
fn noncanonical_word_constants_and_mismatched_index_ranks_are_not_total_values() {
    let (mut executor, _, _) = fixture(WORDS, "(= x y)");
    let x = executor.ctx.terms.find_var("x").expect("source word");
    let y = executor.ctx.terms.find_var("y").expect("source word");
    let original = executor.ctx.terms.entries_snapshot();
    let counter = executor.ctx.terms.var_counter();
    for data in [
        TermData::Const(Constant::BitVec {
            value: (-1).into(),
            width: 8,
        }),
        TermData::Const(Constant::BitVec {
            value: 256.into(),
            width: 8,
        }),
        TermData::App(Symbol::indexed("extract", vec![8, 1]), vec![y]),
    ] {
        let mut entries = original.clone();
        let bad = TermId(u32::try_from(entries.len()).expect("small original store"));
        entries.push((data, Sort::bitvec(8)));
        let root = TermId(u32::try_from(entries.len()).expect("small original store"));
        entries.push((TermData::App(Symbol::named("="), vec![x, bad]), Sort::Bool));
        executor.ctx.terms = TermStore::from_entries(entries, None, None, counter);
        assert!(!screened(&executor, root));
    }
}

#[test]
fn source_scope_and_original_work_exhaustion_never_gain_fresh_per_root_credit() {
    let (executor, root, surface) = fixture(WORDS, "(= x (bvadd y #x01))");
    let before = executor.proof_source_work.remaining_for_test();
    assert!(screened(&executor, root));
    assert!(executor.proof_source_work.remaining_for_test() < before);
    assert!(
        !Screen::new(&executor.ctx, &executor.proof_source_work, &|| false).may_skip(root, &[])
    );
    executor.proof_source_work.set_remaining_for_test(0);
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
        "exhaustion retains both singleton attempts and the joint attempt"
    );
    assert_eq!(executor.proof_source_work.remaining_for_test(), 0);
}

#[test]
fn observed_original_stop_is_sticky_and_never_classifies_a_definition() {
    let (executor, root, _) = fixture(WORDS, "(= x (bvadd y #x01))");
    let calls = Cell::new(0usize);
    let healthy = || {
        calls.set(calls.get() + 1);
        false
    };
    assert!(
        Screen::new(&executor.ctx, &executor.proof_source_work, &healthy).may_skip(root, &[root])
    );
    let healthy_calls = calls.get();
    for stop_at in [1, healthy_calls / 2, healthy_calls] {
        calls.set(0);
        let stop = || {
            calls.set(calls.get() + 1);
            calls.get() == stop_at
        };
        let mut screen = Screen::new(&executor.ctx, &executor.proof_source_work, &stop);
        assert!(!screen.may_skip(root, &[root]));
        assert!(!screen.may_skip(root, &[root]));
        assert_eq!(
            calls.get(),
            stop_at,
            "the recovering callback must not be polled again"
        );
    }
}

#[test]
fn original_work_debits_are_cumulative_checked_and_never_refunded() {
    let owner = ProofSourceWorkEnvelope::default();
    owner.set_remaining_for_test(3);
    assert!(!owner.spend_canonical_scan_work(usize::MAX));
    assert_eq!(owner.remaining_for_test(), 3);
    assert!(owner.spend_canonical_scan_work(2));
    assert_eq!(owner.remaining_for_test(), 1);
    assert!(!owner.spend_canonical_scan_work(2));
    assert_eq!(owner.remaining_for_test(), 1);
    assert!(owner.spend_canonical_scan_work(1));
    assert!(!owner.spend_canonical_scan_work(1));
    assert_eq!(owner.remaining_for_test(), 0);
}

#[test]
fn exhaustion_on_the_original_terminal_poll_keeps_the_singleton() {
    let (executor, root, surface) = fixture(WORDS, "(= x (bvadd y #x01))");
    let before = executor.proof_source_work.remaining_for_test();
    assert!(screened(&executor, root));
    let consumed = before - executor.proof_source_work.remaining_for_test();
    executor
        .proof_source_work
        .set_remaining_for_test(consumed - 1);
    let choices = candidate_selections(
        &[(root, &surface)],
        &[root],
        &executor.ctx,
        &executor.proof_source_work,
        &|| false,
    );
    assert_eq!(choices.len(), 1);
    assert_eq!(executor.proof_source_work.remaining_for_test(), 0);
}

#[test]
fn ambiguous_nullary_and_same_spelling_impostor_variables_keep_singletons() {
    for name in ["x", "y"] {
        let (mut executor, root, _) = fixture(WORDS, "(= x y)");
        let declaration = ay_frontend::parse(&format!("(declare-const {name} Bool)"))
            .expect("a second nullary signature");
        executor
            .execute_all(&declaration)
            .expect("legal result-sort overloading");
        assert!(!screened(&executor, root));
    }
    let (mut executor, _, _) = fixture(WORDS, "(= x y)");
    let lhs = executor.ctx.terms.find_var("x").expect("exact original x");
    let counter = executor.ctx.terms.var_counter();
    let mut entries = executor.ctx.terms.entries_snapshot();
    let rhs = TermId(u32::try_from(entries.len()).expect("small original store"));
    entries.push((TermData::Var("y".into(), counter), Sort::bitvec(8)));
    let root = TermId(u32::try_from(entries.len()).expect("small original store"));
    entries.push((
        TermData::App(Symbol::named("="), vec![lhs, rhs]),
        Sort::Bool,
    ));
    executor.ctx.terms = TermStore::from_entries(entries, None, None, counter + 1);
    assert!(
        !screened(&executor, root),
        "same spelling is not the declared TermId"
    );
}
