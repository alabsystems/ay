// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

fn chain(exec: &mut Executor, mut term: TermId, depth: usize) -> TermId {
    for _ in 0..depth {
        term = exec
            .ctx
            .terms
            .mk_app(Symbol::named("chain"), [term], Sort::bitvec(8));
    }
    term
}

fn aliased_chains() -> (Executor, GroundSearch, TermId, TermId, TermId) {
    let mut exec = Executor::new();
    let x = exec
        .ctx
        .terms
        .mk_app(Symbol::named("x"), [], Sort::bitvec(8));
    let y = exec
        .ctx
        .terms
        .mk_app(Symbol::named("y"), [], Sort::bitvec(8));
    let left = chain(&mut exec, x, 64);
    let right = chain(&mut exec, y, 64);
    let pin = exec
        .ctx
        .terms
        .mk_app(Symbol::named("="), [x, y], Sort::Bool);
    let mut search = GroundSearch::default();
    // The order that cost one outer round per ancestor in the old scan.
    exec.register_ground_subterms(&mut search.closure, left)
        .unwrap();
    exec.register_ground_subterms(&mut search.closure, right)
        .unwrap();
    (exec, search, pin, left, right)
}

#[test]
fn parent_revisit_proves_deep_congruence_from_earlier_edges() {
    let (mut exec, mut search, pin, left, right) = aliased_chains();
    let (x, y) = decode_eq_local(&exec.ctx.terms, pin).unwrap();
    assert!(search.closure.merge(x, y, EdgeReason::Authored(pin)));
    let mut work = SharedGroundWork::new(MAX_NODES * MAX_ROUNDS);
    exec.close_ground_congruence(&mut search.closure, &mut work)
        .unwrap();
    assert!(search.closure.same_class(left, right));
    let equality = exec
        .ctx
        .terms
        .mk_app(Symbol::named("="), [left, right], Sort::Bool);
    let root = exec.ctx.terms.mk_not_raw(equality);
    let proof = exec
        .emit_ground_closure_refutation(
            &search,
            ClosureConflict::Disequality {
                root,
                equality,
                lhs: left,
                rhs: right,
            },
        )
        .unwrap();
    assert!(Executor::proof_derives_empty_clause(&proof));
    assert!(exec
        .check_proof_strict_derivation_with_datatypes(&proof)
        .unwrap()
        .is_complete());
}

#[test]
fn parent_revisit_needs_argument_equality_and_declines_exhausted_work() {
    let (exec, mut search, pin, left, right) = aliased_chains();
    let mut work = SharedGroundWork::new(MAX_NODES * MAX_ROUNDS);
    exec.close_ground_congruence(&mut search.closure, &mut work)
        .unwrap();
    assert!(!search.closure.same_class(left, right));
    let (x, y) = decode_eq_local(&exec.ctx.terms, pin).unwrap();
    assert!(search.closure.merge(x, y, EdgeReason::Authored(pin)));
    assert!(exec
        .close_ground_congruence(&mut search.closure, &mut SharedGroundWork::new(0))
        .is_none());
    assert!(exec.last_proof_raw_original_assertions.is_empty());
    assert!(exec.last_proof.is_none());
}

#[test]
fn literal_unit_products_get_checked_edges_but_other_factors_do_not() {
    for width in [1, 8, 64] {
        for swapped in [false, true] {
            let mut exec = Executor::new();
            let value = exec
                .ctx
                .terms
                .mk_app(Symbol::named("x"), [], Sort::bitvec(width));
            let unit = exec.ctx.terms.mk_bitvec(BigInt::from(1), width);
            let other = exec.ctx.terms.mk_bitvec(BigInt::from(0), width);
            let args = if swapped {
                [unit, value]
            } else {
                [value, unit]
            };
            let product = exec
                .ctx
                .terms
                .mk_app(Symbol::named("bvmul"), args, Sort::bitvec(width));
            let nonunit =
                exec.ctx
                    .terms
                    .mk_app(Symbol::named("bvmul"), [value, other], Sort::bitvec(width));
            let equality = exec
                .ctx
                .terms
                .mk_app(Symbol::named("="), [product, value], Sort::Bool);
            let root = exec.ctx.terms.mk_not_raw(equality);
            let proof = exec.early_ground_closure_memory_candidate(root).unwrap();
            assert!(exec
                .check_proof_strict_derivation_with_datatypes(&proof)
                .unwrap()
                .is_complete());
            let nonidentity =
                exec.ctx
                    .terms
                    .mk_app(Symbol::named("="), [nonunit, value], Sort::Bool);
            let counterexample = exec.ctx.terms.mk_not_raw(nonidentity);
            assert!(exec
                .early_ground_closure_memory_candidate(counterexample)
                .is_none());
        }
    }
}

#[test]
fn a_large_refutation_proposal_declines_without_premise_authority() {
    let mut exec = Executor::new();
    let mut leaves = (0..MAX_NODES)
        .map(|index| {
            exec.ctx
                .terms
                .mk_app(Symbol::named(format!("v{index}")), [], Sort::bitvec(8))
        })
        .collect::<Vec<_>>();
    while leaves.len() > 1 {
        leaves = leaves
            .chunks(2)
            .map(|pair| {
                exec.ctx
                    .terms
                    .mk_app(Symbol::named("bvadd"), pair, Sort::bitvec(8))
            })
            .collect();
    }
    let zero = exec.ctx.terms.mk_bitvec(BigInt::from(0), 8);
    let equality = exec
        .ctx
        .terms
        .mk_app(Symbol::named("="), [leaves[0], zero], Sort::Bool);
    let negative = exec.ctx.terms.mk_not_raw(equality);
    // It has a satisfying assignment (v0 one and the other leaves zero).
    // The bounded producer must decline without adopting proof.
    assert!(exec
        .early_ground_closure_memory_candidate(negative)
        .is_none());
    assert!(exec.last_proof_raw_original_assertions.is_empty());
    assert!(exec.last_proof.is_none());
}
