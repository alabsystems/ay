// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! The lowering materializes each node once and is charged for exactly that.
//!
//! The source shape MODELS external-codegen's per-lane x86 `<16 x i8>` unsigned `ule`
//! obligation (its query before 7b81d2cb1): the ExternalCodegenIR lane-wise predicate
//! against the `pxor`-biased signed compare, sixteen lanes concatenated on
//! each side, the sign-bit bias spelled as sixteen `(_ bv128 8)` lanes. It
//! lowers to the real lemma's 7,523 occurrences of 674 distinct nodes
//! (measured 2026-09-29), but it is not the real lemma: the old rule charged
//! the real lemma 103,994 nodes and this model 96,840, under the budget
//! (d73917a2b's measurements). So these tests cannot catch a return to
//! charging whole subtrees; the `shared-lane-bias` rows of the
//! consumer-certificate corpus can.

use std::time::{Duration, Instant};

use super::*;

/// The x86 `<16 x i8>` cell.
const LANES: u32 = 16;

struct Builder<'t> {
    terms: &'t mut TermStore,
    lanes: u32,
}

impl Builder<'_> {
    fn app(&mut self, name: &str, args: &[TermId], width: u32) -> TermId {
        self.terms
            .mk_app(Symbol::named(name), args, Sort::bitvec(width))
    }

    fn predicate(&mut self, name: &str, args: &[TermId]) -> TermId {
        self.terms.mk_app(Symbol::named(name), args, Sort::Bool)
    }

    fn lane(&mut self, word: TermId, lane: u32) -> TermId {
        let low = 8 * lane;
        self.terms.mk_app(
            Symbol::indexed("extract", vec![low + 7, low]),
            [word],
            Sort::bitvec(8),
        )
    }

    fn mask(&mut self, condition: TermId) -> TermId {
        let ones = self.terms.mk_bitvec(255.into(), 8);
        let zero = self.terms.mk_bitvec(0.into(), 8);
        self.terms.mk_ite_raw(condition, ones, zero)
    }

    /// `(concat lane_15 (concat lane_14 ... lane_0))`, as external-codegen spells it.
    fn chain(&mut self, lane: impl Fn(&mut Self, u32) -> TermId) -> TermId {
        let mut word = lane(self, 0);
        for index in 1..self.lanes {
            let high = lane(self, index);
            word = self.app("concat", &[high, word], 8 * (index + 1));
        }
        word
    }

    /// Two halves, as external-codegen passes a vector register.
    fn word(&mut self, name: &str, width: u32) -> TermId {
        let half = Sort::bitvec(width / 2);
        let high = self.terms.mk_var(format!("{name}_hi"), half.clone());
        let low = self.terms.mk_var(format!("{name}_lo"), half);
        self.app("concat", &[high, low], width)
    }
}

/// `(= spec machine)` for the per-lane unsigned `ule` cell: the clause of the
/// bit-blast lemma AY must accept for a hole-free certificate.
fn per_lane_unsigned_le(terms: &mut TermStore, lanes: u32) -> TermId {
    let mut b = Builder { terms, lanes };
    let width = 8 * lanes;
    let lhs = b.word("lhs", width);
    let rhs = b.word("rhs", width);
    let bias = b.chain(|b, _| b.terms.mk_bitvec(128.into(), 8));
    let spec = b.chain(|b, lane| {
        let (l, r) = (b.lane(lhs, lane), b.lane(rhs, lane));
        let le = b.predicate("bvule", &[l, r]);
        b.mask(le)
    });
    let equal = b.chain(|b, lane| {
        let (l, r) = (b.lane(lhs, lane), b.lane(rhs, lane));
        let eq = b.predicate("=", &[l, r]);
        b.mask(eq)
    });
    let greater = b.chain(|b, lane| {
        let biased_rhs = b.app("bvxor", &[bias, rhs], width);
        let biased_lhs = b.app("bvxor", &[bias, lhs], width);
        let (r, l) = (b.lane(biased_rhs, lane), b.lane(biased_lhs, lane));
        let gt = b.predicate("bvsgt", &[r, l]);
        b.mask(gt)
    });
    let machine = b.app("bvor", &[greater, equal], width);
    b.predicate("=", &[spec, machine])
}

fn occurrences(expression: &BvExpr) -> usize {
    bv_expr_nodes_controlled(expression, &mut || Ok(())).unwrap()
}

#[test]
fn a_shared_source_dag_is_charged_for_the_nodes_it_materializes() {
    let mut terms = TermStore::new();
    let equality = per_lane_unsigned_le(&mut terms, LANES);
    let mut lowerer = ProofProducingLowerer::new(&terms, Instant::now() + Duration::from_secs(60));
    let lowered = lowerer.lower_bool(equality).unwrap();
    let tree = occurrences(&lowered);
    let copies: usize = lowerer
        .memo
        .keys()
        .map(|term| lowerer.memo_node_counts[term])
        .sum();

    // Everything that exists was charged: the returned tree and the memo's
    // copies of shared terms (plus clones built and dropped on the way, such
    // as the parts of a `concat` an `extract` takes apart). Before, every
    // term's whole subtree was charged (and copied), so the 16-lane chains
    // cost the sum of their prefixes. Now the charge is linear in what the
    // lowering builds: 8,053 here.
    let charged = lowerer.constructed_expr_nodes;
    assert!(charged >= tree + copies, "{charged} < {tree} + {copies}");
    assert!(charged < 2 * tree, "{charged} for a {tree}-node tree");
    assert!(
        copies < tree / 4,
        "only shared terms are copied: {copies} copies for a {tree}-node tree"
    );
    // The result walks are charged as work.
    assert!(lowerer.lowering_walk >= u64::try_from(tree).unwrap());
    assert!(lowerer.memo.keys().all(|term| lowerer.parents[term] > 1));
}

#[test]
fn the_per_lane_unsigned_compare_lemma_is_accepted_by_the_proof_producer() {
    let mut terms = TermStore::new();
    let equality = per_lane_unsigned_le(&mut terms, LANES);
    // The strict checker's `BvBitBlast` validation of `(cl (= spec machine))`:
    // bounded evaluation declines (256-bit operands), the proof producer
    // lowers, bit-blasts, refutes and replays it.
    validate_bv_bitblast(&terms, ProofId(1), &[equality], None).unwrap();
}

#[test]
fn memoizing_every_term_changes_the_copies_not_the_expression() {
    let mut terms = TermStore::new();
    // Eight lanes: memoizing every term of sixteen is over the budget.
    let equality = per_lane_unsigned_le(&mut terms, LANES / 2);
    let deadline = Instant::now() + Duration::from_secs(60);
    let mut shared_only = ProofProducingLowerer::new(&terms, deadline);
    let expected = shared_only.lower_bool(equality).unwrap();

    // A census the term caps stopped counts nothing further, and every term
    // it did not count is memoized: the policy before 2026-09-29.
    let mut every = ProofProducingLowerer::new(&terms, deadline);
    every.census_incomplete = true;
    every.census_seen.insert(equality);
    assert_eq!(every.lower_bool(equality).unwrap(), expected);
    let copies: usize = every
        .memo
        .keys()
        .map(|term| every.memo_node_counts[term])
        .sum();
    assert!(every.constructed_expr_nodes >= occurrences(&expected) + copies);
    assert!(every.memo.len() > shared_only.memo.len());
    assert!(every.constructed_expr_nodes > shared_only.constructed_expr_nodes);
}
