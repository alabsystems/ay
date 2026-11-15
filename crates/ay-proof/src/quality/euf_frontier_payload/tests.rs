// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

fn app(terms: &mut TermStore, op: &str, args: &[TermId], sort: Sort) -> TermId {
    terms.mk_app(Symbol::named(op), args, sort)
}

fn eq(terms: &mut TermStore, a: TermId, b: TermId) -> TermId {
    app(terms, "=", &[a, b], Sort::Bool)
}

fn fixture(depth: usize) -> (TermStore, Proof, Vec<TermId>, ProofId) {
    let mut terms = TermStore::new();
    let sort = Sort::array(Sort::bitvec(64), Sort::bitvec(8));
    let mut a = terms.mk_var("a", sort.clone());
    for index in 0..depth {
        let key = terms.mk_bitvec(index.into(), 64);
        let value = terms.mk_bitvec((index as u8).into(), 8);
        a = app(&mut terms, "store", &[a, key, value], sort.clone());
    }
    let b = terms.mk_var("b", sort.clone());
    let c = terms.mk_var("c", sort.clone());
    let d = terms.mk_var("d", sort);
    let ab = eq(&mut terms, a, b);
    let bc = eq(&mut terms, b, c);
    let cd = eq(&mut terms, c, d);
    let ad = eq(&mut terms, a, d);
    let not_ad = terms.mk_not_raw(ad);
    let mut proof = Proof::new();
    let units: Vec<_> = [ab, bc, cd, not_ad]
        .into_iter()
        .map(|term| proof.add_assume(term, None))
        .collect();
    let negatives: Vec<_> = [ab, bc, cd]
        .into_iter()
        .map(|term| terms.mk_not_raw(term))
        .collect();
    let mut clause = negatives;
    clause.push(ad);
    let lemma = proof.add_theory_lemma_with_kind("euf", clause, TheoryLemmaKind::EufTransitive);
    proof.add_rule_step(
        AletheRule::Resolution,
        vec![],
        vec![lemma, units[0], units[1], units[2], units[3]],
        vec![],
    );
    (terms, proof, vec![ab, bc, cd, not_ad], lemma)
}

#[test]
fn fixed_euf_frontier_is_independent_of_an_opaque_store_tree() {
    let mut measured = Vec::new();
    for depth in [0, 80] {
        let (terms, proof, scope, lemma) = fixture(depth);
        let payload = meter(&proof.steps[lemma.0 as usize], &terms, &[], &mut |_, _| {
            true
        })
        .unwrap()
        .unwrap();
        measured.push((payload.work, payload.bytes));
        assert!(
            check_proof_strict_with_context(&proof, &terms, None, None, Some(&scope))
                .unwrap()
                .is_complete()
        );
    }
    assert_eq!(
        measured[0], measured[1],
        "the validator never reads the equality operands' store trees"
    );
}

#[test]
fn frontier_does_not_authorize_a_wrong_chain_or_a_missing_input_assumption() {
    let (mut terms, mut proof, scope, lemma) = fixture(80);
    assert!(
        check_proof_strict_with_context(&proof, &terms, None, None, Some(&scope[1..])).is_err()
    );
    let foreign = terms.mk_var("foreign", terms.sort(scope[0]).clone());
    let wrong = eq(&mut terms, foreign, foreign);
    let ProofStep::TheoryLemma { clause, .. } = &mut proof.steps[lemma.0 as usize] else {
        unreachable!()
    };
    clause[3] = wrong;
    assert!(
        meter(&proof.steps[lemma.0 as usize], &terms, &[], &mut |_, _| {
            true
        })
        .unwrap()
        .is_some()
    );
    let error =
        check_proof_strict_with_context(&proof, &terms, None, None, Some(&scope)).unwrap_err();
    assert!(matches!(error,ProofCheckError::InvalidTheoryLemma { step,.. } if step==lemma));
}

#[test]
fn broader_congruence_packed_not_and_extra_premise_routes_keep_legacy_walks() {
    let (mut terms, proof, _, lemma) = fixture(1);
    let ProofStep::TheoryLemma { clause, .. } = &proof.steps[lemma.0 as usize] else {
        unreachable!()
    };
    let source_clause = clause.clone();
    let packed = app(&mut terms, "or", &source_clause, Sort::Bool);
    let mut variants = Vec::new();
    let mut p = Proof::new();
    p.add_theory_lemma_with_kind("euf", vec![packed], TheoryLemmaKind::EufTransitive);
    variants.push(p.steps.pop().unwrap());
    let mut long = source_clause.clone();
    long[0] = terms.mk_not_raw(long[0]);
    long[0] = terms.mk_not_raw(long[0]);
    p.add_theory_lemma_with_kind("euf", long, TheoryLemmaKind::EufTransitive);
    variants.push(p.steps.pop().unwrap());
    variants.push(ProofStep::Step {
        rule: AletheRule::Cong,
        clause: vec![source_clause[3]],
        premises: vec![],
        args: vec![],
    });
    variants.push(ProofStep::Step {
        rule: AletheRule::Trans,
        clause: vec![source_clause[3]],
        premises: vec![ProofId(0); 3],
        args: vec![],
    });
    for step in variants {
        assert!(meter(&step, &terms, &[], &mut |_, _| true)
            .unwrap()
            .is_none());
    }
}

#[test]
fn congruence_frontier_prices_the_actual_head_and_argument_vector() {
    let mut measured = Vec::new();
    for length in [1, 65_536] {
        let mut terms = TermStore::new();
        let x = terms.mk_var("x", Sort::bitvec(64));
        let y = terms.mk_var("y", Sort::bitvec(64));
        let xy = eq(&mut terms, x, y);
        let negative = terms.mk_not_raw(xy);
        let name = "f".repeat(length);
        let fx = app(&mut terms, &name, &[x], Sort::bitvec(64));
        let fy = app(&mut terms, &name, &[y], Sort::bitvec(64));
        let goal = eq(&mut terms, fx, fy);
        let mut proof = Proof::new();
        proof.add_theory_lemma_with_kind(
            "euf",
            vec![negative, goal],
            TheoryLemmaKind::EufCongruent,
        );
        let stats = meter(&proof.steps[0], &terms, &[], &mut |_, _| true)
            .unwrap()
            .unwrap();
        measured.push(stats.bytes);
    }
    assert!(
        measured[1] - measured[0] >= 2 * (65_536 - 1),
        "both cloned symbol heads must be charged"
    );
}

#[test]
fn frontier_preserves_live_cancellation_and_refused_admission() {
    let (terms, proof, _, lemma) = fixture(80);
    let step = &proof.steps[lemma.0 as usize];
    let mut calls = 0;
    let error = meter(step, &terms, &[], &mut |_, _| {
        calls += 1;
        false
    })
    .unwrap_err();
    assert!(matches!(error, ProofCheckError::ResourceLimit));
    assert_eq!(calls, 1);
    let mut paid = 0;
    assert!(meter(step, &terms, &[], &mut |_, bytes| {
        paid += bytes;
        paid < 64
    })
    .is_err());
}

fn bounded_app_congruence(
    depth: usize,
    arity: usize,
    extra: usize,
    name: &str,
) -> (
    TermStore,
    Proof,
    Vec<TermId>,
    ProofId,
    Vec<Option<Vec<TermId>>>,
) {
    let mut terms = TermStore::new();
    let array_sort = Sort::array(Sort::bitvec(64), Sort::bitvec(8));
    let mut left = terms.mk_var("large_operand", array_sort.clone());
    for i in 0..depth {
        let index = terms.mk_bitvec(i.into(), 64);
        let value = terms.mk_bitvec((i as u8).into(), 8);
        left = app(
            &mut terms,
            "store",
            &[left, index, value],
            array_sort.clone(),
        );
    }
    let mut lhs = Vec::new();
    let mut rhs = Vec::new();
    let mut equalities = Vec::new();
    for i in 0..arity {
        let a = if i == 0 {
            left
        } else {
            terms.mk_var(&format!("a{i}"), array_sort.clone())
        };
        let b = terms.mk_var(&format!("b{i}"), array_sort.clone());
        lhs.push(a);
        rhs.push(b);
        equalities.push(eq(&mut terms, a, b));
    }
    for i in 0..extra {
        let a = terms.mk_var(&format!("unused_a{i}"), array_sort.clone());
        let b = terms.mk_var(&format!("unused_b{i}"), array_sort.clone());
        equalities.push(eq(&mut terms, a, b));
    }
    let f = app(&mut terms, name, &lhs, Sort::bitvec(64));
    let g = app(&mut terms, name, &rhs, Sort::bitvec(64));
    let goal = eq(&mut terms, f, g);
    let mut proof = Proof::new();
    let mut scope = Vec::new();
    let mut clauses = Vec::new();
    let mut units = Vec::new();
    for &equality in &equalities {
        units.push(proof.add_assume(equality, None));
        scope.push(equality);
        clauses.push(Some(vec![equality]));
    }
    let negative = terms.mk_not_raw(goal);
    let contrary = proof.add_assume(negative, None);
    scope.push(negative);
    clauses.push(Some(vec![negative]));
    units.reverse();
    let lemma = proof.add_rule_step(AletheRule::Cong, vec![goal], units, vec![]);
    proof.add_resolution(vec![], goal, lemma, contrary);
    (terms, proof, scope, lemma, clauses)
}

#[test]
fn direct_app_congruence_prices_the_full_product_and_all_fresh_heads() {
    let mut measured = Vec::new();
    for depth in [0, 80] {
        let (terms, proof, scope, lemma, clauses) = bounded_app_congruence(depth, 4, 0, "f");
        let mut charged_work = 0;
        let payload = meter(
            &proof.steps[lemma.0 as usize],
            &terms,
            &clauses,
            &mut |work, _| {
                charged_work += work;
                true
            },
        )
        .unwrap()
        .unwrap();
        assert!(payload.work >= 128 + 4 * 4);
        assert_eq!(charged_work, payload.work);
        measured.push((payload.work, payload.bytes));
        assert!(
            check_proof_strict_with_context(&proof, &terms, None, None, Some(&scope))
                .unwrap()
                .is_complete()
        );
    }
    assert_eq!(
        measured[0], measured[1],
        "opaque descendants are globally authenticated, not cloned by cong"
    );
    let (terms, proof, scope, lemma, clauses) = bounded_app_congruence(80, 1, 3, "f");
    let payload = meter(
        &proof.steps[lemma.0 as usize],
        &terms,
        &clauses,
        &mut |_, _| true,
    )
    .unwrap()
    .unwrap();
    assert!(payload.work >= 128 + 4);
    assert!(
        check_proof_strict_with_context(&proof, &terms, None, None, Some(&scope))
            .unwrap()
            .is_complete(),
        "unused positive premises retain their existing semantics"
    );
}

#[test]
fn app_congruence_keeps_wide_extra_and_not_premises_on_legacy_routes() {
    for (arity, extra) in [(5usize, 0usize), (1, 4)] {
        let (terms, proof, _, lemma, clauses) = bounded_app_congruence(80, arity, extra, "f");
        assert!(meter(
            &proof.steps[lemma.0 as usize],
            &terms,
            &clauses,
            &mut |_, _| true
        )
        .unwrap()
        .is_none());
    }
    let (mut terms, proof, _, lemma, mut clauses) = bounded_app_congruence(1, 1, 0, "f");
    let old = clauses[0].as_ref().unwrap()[0];
    let once = terms.mk_not_raw(old);
    let twice = terms.mk_not_raw(once);
    clauses[0] = Some(vec![twice]);
    assert!(meter(
        &proof.steps[lemma.0 as usize],
        &terms,
        &clauses,
        &mut |_, _| true
    )
    .unwrap()
    .is_none());
}

#[test]
fn app_congruence_frontier_retains_actual_symbol_bytes_and_semantic_refusals() {
    let mut measured = Vec::new();
    for length in [1usize, 65_536] {
        let (terms, proof, _, lemma, clauses) =
            bounded_app_congruence(1, 1, 0, &"f".repeat(length));
        let payload = meter(
            &proof.steps[lemma.0 as usize],
            &terms,
            &clauses,
            &mut |_, _| true,
        )
        .unwrap()
        .unwrap();
        measured.push(payload.bytes);
    }
    assert!(measured[1] - measured[0] >= 2 * (65_536 - 1));
    let (mut terms, mut proof, scope, lemma, clauses) = bounded_app_congruence(1, 1, 0, "f");
    assert!(
        check_proof_strict_with_context(&proof, &terms, None, None, Some(&scope[1..])).is_err()
    );
    let ProofStep::Step { clause, .. } = &proof.steps[lemma.0 as usize] else {
        unreachable!()
    };
    let [left, right] = equality(&terms, clause[0]).unwrap();
    let TermData::App(_, args) = terms.get(right) else {
        unreachable!()
    };
    let args = args.clone();
    let wrong = app(&mut terms, "wrong_head", &args, Sort::bitvec(64));
    let goal = eq(&mut terms, left, wrong);
    let ProofStep::Step { clause, .. } = &mut proof.steps[lemma.0 as usize] else {
        unreachable!()
    };
    clause[0] = goal;
    assert!(meter(
        &proof.steps[lemma.0 as usize],
        &terms,
        &clauses,
        &mut |_, _| true
    )
    .unwrap()
    .is_some());
    let error =
        check_proof_strict_with_context(&proof, &terms, None, None, Some(&scope)).unwrap_err();
    assert!(matches!(error,ProofCheckError::InvalidBooleanRule{step,..} if step==lemma));
}

#[test]
fn app_congruence_charges_full_index_vectors_and_retains_global_type_authentication() {
    let mut sizes = Vec::new();
    for count in [1usize, 4096] {
        let mut terms = TermStore::new();
        let x = terms.mk_var("x", Sort::bitvec(64));
        let y = terms.mk_var("y", Sort::bitvec(64));
        let premise = eq(&mut terms, x, y);
        let symbol = Symbol::indexed("indexed_head", vec![0; count]);
        let f = terms.mk_app(symbol.clone(), [x], Sort::bitvec(64));
        let g = terms.mk_app(symbol, [y], Sort::bitvec(64));
        let goal = eq(&mut terms, f, g);
        let step = ProofStep::Step {
            rule: AletheRule::Cong,
            clause: vec![goal],
            premises: vec![ProofId(0)],
            args: vec![],
        };
        let stats = meter(&step, &terms, &[Some(vec![premise])], &mut |_, _| true)
            .unwrap()
            .unwrap();
        sizes.push(stats.bytes);
    }
    assert!(
        sizes[1] - sizes[0] >= 2 * (4096 - 1) * size_of::<u32>(),
        "both cloned indexed symbols count their complete vectors"
    );
    let (mut terms, mut proof, scope, lemma, clauses) = bounded_app_congruence(1, 1, 0, "f");
    let ProofStep::Step { clause, .. } = &proof.steps[lemma.0 as usize] else {
        unreachable!()
    };
    let [left, right] = equality(&terms, clause[0]).unwrap();
    let TermData::App(symbol, args) = terms.get(right) else {
        unreachable!()
    };
    let symbol = symbol.clone();
    let args = args.clone();
    let wrong = terms.mk_app(symbol, args, Sort::bitvec(32));
    let goal = eq(&mut terms, left, wrong);
    let ProofStep::Step { clause, .. } = &mut proof.steps[lemma.0 as usize] else {
        unreachable!()
    };
    clause[0] = goal;
    assert!(meter(
        &proof.steps[lemma.0 as usize],
        &terms,
        &clauses,
        &mut |_, _| true
    )
    .unwrap()
    .is_some());
    assert!(
        check_proof_strict_with_context(&proof, &terms, None, None, Some(&scope)).is_err(),
        "resource classification cannot replace global type authentication"
    );
}
