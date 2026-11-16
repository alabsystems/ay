// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Necessary premises and actual charged lowering, without parser authority.

use super::*;
use std::time::Duration;

fn boolean(terms: &mut TermStore, name: &str, args: &[TermId]) -> TermId {
    terms.mk_app_structural(Symbol::named(name), args, Sort::Bool)
}

fn extension(terms: &mut TermStore, inner: TermId, extra: u32, width: u32) -> TermId {
    terms.mk_app_structural(
        Symbol::Indexed("zero_extend".into(), vec![extra]),
        [inner],
        Sort::bitvec(width),
    )
}

#[test]
fn native_conjunction_and_captured_implication_have_the_same_exact_wiring_premises() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::bitvec(8));
    let b = terms.mk_var("b", Sort::bitvec(8));
    let x = terms.mk_var("x", Sort::bitvec(32));
    let y = terms.mk_var("y", Sort::bitvec(32));
    let a32 = extension(&mut terms, a, 24, 32);
    let b32 = extension(&mut terms, b, 24, 32);
    let first = boolean(&mut terms, "=", &[a32, x]);
    let second = boolean(&mut terms, "=", &[y, b32]);
    let goal = terms.mk_var("goal", Sort::Bool);
    let guard = terms.mk_var("guard", Sort::Bool);
    let not_goal = terms.mk_not_raw(goal);
    let conjunction = boolean(&mut terms, "and", &[first, second, not_goal, guard]);
    let native = terms.mk_not_raw(conjunction);
    let aliases = boolean(&mut terms, "and", &[first, second]);
    let inner = boolean(&mut terms, "=>", &[aliases, goal]);
    let captured = boolean(&mut terms, "=>", &[guard, inner]);
    assert_eq!(
        hypothesis_equalities(&terms, &[native]),
        vec![(x, a32), (y, b32)]
    );
    assert_eq!(
        hypothesis_equalities(&terms, &[captured]),
        vec![(x, a32), (y, b32)]
    );
    let nary = boolean(&mut terms, "=>", &[guard, first, second, goal]);
    assert_eq!(
        hypothesis_equalities(&terms, &[nary]),
        vec![(x, a32), (y, b32)]
    );
}

#[test]
fn branch_polarities_never_grant_an_unconditional_equation() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::bitvec(4));
    let b = terms.mk_var("b", Sort::bitvec(4));
    let equality = boolean(&mut terms, "=", &[a, b]);
    let q = terms.mk_var("q", Sort::Bool);
    let not_equality = terms.mk_not_raw(equality);
    let positive_or = boolean(&mut terms, "or", &[equality, q]);
    let true_or = terms.mk_not_raw(positive_or);
    let false_and = boolean(&mut terms, "and", &[not_equality, q]);
    let implication = boolean(&mut terms, "=>", &[not_equality, q]);
    let true_implication = terms.mk_not_raw(implication);
    let ite = terms.mk_ite_raw(q, not_equality, equality);
    for clause in [equality, true_or, false_and, true_implication, ite] {
        assert_eq!(hypothesis_equalities(&terms, &[clause]), Vec::new());
    }
    let forced = boolean(&mut terms, "or", &[not_equality, q]);
    assert_eq!(hypothesis_equalities(&terms, &[forced]), vec![(a, b)]);
    let named_not = boolean(&mut terms, "not", &[equality]);
    assert_eq!(hypothesis_equalities(&terms, &[named_not]), vec![(a, b)]);
    let double_not = boolean(&mut terms, "not", &[named_not]);
    assert_eq!(hypothesis_equalities(&terms, &[double_not]), Vec::new());
}

#[test]
fn a_wiring_definition_requires_the_actual_index_arity_width_and_leaf() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::bitvec(4));
    let x = terms.mk_var("x", Sort::bitvec(8));
    let valid = extension(&mut terms, a, 4, 8);
    assert_eq!(definition(&terms, x, valid), Some((x, valid)));
    let invalid_width = extension(&mut terms, a, 5, 8);
    let invalid_indices = terms.mk_app_structural(
        Symbol::Indexed("zero_extend".into(), vec![4, 4]),
        [a],
        Sort::bitvec(8),
    );
    let invalid_arity = terms.mk_app_structural(
        Symbol::Indexed("zero_extend".into(), vec![4]),
        [a, a],
        Sort::bitvec(8),
    );
    let different_operator = terms.mk_app_structural(
        Symbol::Indexed("sign_extend".into(), vec![4]),
        [a],
        Sort::bitvec(8),
    );
    let one = terms.mk_bitvec(1.into(), 4);
    let sum = terms.mk_app_structural(Symbol::named("bvadd"), [a, one], Sort::bitvec(4));
    let compound = extension(&mut terms, sum, 4, 8);
    let flag = terms.mk_var("flag", Sort::Bool);
    let wrong_sort = extension(&mut terms, flag, 4, 8);
    let absent = TermId(u32::MAX);
    let missing_child = extension(&mut terms, absent, 4, 8);
    for rejected in [
        invalid_width,
        invalid_indices,
        invalid_arity,
        different_operator,
        compound,
        wrong_sort,
        missing_child,
    ] {
        assert_eq!(definition(&terms, x, rejected), None);
    }
    assert_eq!(definition(&terms, x, a), None);
    assert_eq!(definition(&terms, x, absent), None);
    let constant = terms.mk_bitvec(15.into(), 4);
    let extended_constant = extension(&mut terms, constant, 4, 8);
    assert_eq!(
        definition(&terms, x, extended_constant),
        Some((x, extended_constant))
    );
}

#[test]
fn duplicate_reordered_and_zero_extension_zero_aliases_keep_the_real_copy_census() {
    for reverse in [false, true] {
        let mut terms = TermStore::new();
        let x = terms.mk_var("x", Sort::bitvec(8));
        let y = terms.mk_var("y", Sort::bitvec(8));
        let x0 = extension(&mut terms, x, 0, 8);
        let y0 = extension(&mut terms, y, 0, 8);
        let first = boolean(&mut terms, "=", &[x, y0]);
        let second = boolean(&mut terms, "=", &[y, x0]);
        let goal = boolean(&mut terms, "=", &[x, y]);
        let not_goal = terms.mk_not_raw(goal);
        let definitions = if reverse {
            [second, first, second, not_goal]
        } else {
            [first, second, first, not_goal]
        };
        let root = boolean(&mut terms, "and", &definitions);
        let clause = [terms.mk_not_raw(root)];
        let mut lowerer = ProofProducingLowerer::new_for_lemma_validation(
            &terms,
            Instant::now() + Duration::from_secs(10),
        );
        let result = lowerer.lower_clause_read(
            &clause,
            Reading {
                hypotheses: true,
                case: None,
            },
        );
        assert!(result.is_ok(), "{result:?}");
        assert!(lowerer.constructed_expr_nodes > 0);
        assert!(lowerer.constructed_expr_nodes <= MAX_PROOF_PRODUCING_CONSTRUCTED_EXPR_NODES);
        lowerer.audit_census();
    }
}
