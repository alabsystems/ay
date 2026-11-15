// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates

//! The Merkle digests are linear in the term DAG plus the sort DAG, scoped
//! like the stack, and distinguish what the solver distinguishes.

use ntest::timeout;

use super::ScopeDigests;
use crate::{Expr, Sort};

fn digests() -> ScopeDigests {
    ScopeDigests::new("QF_LIA", &[])
}

/// A record nested `depth` times whose two fields share ONE sort allocation:
/// a sort DAG of `depth + 1` nodes whose unfolded tree has `2^depth` leaves.
fn nested_pair(depth: usize) -> Sort {
    let mut sort = Sort::int();
    for level in 0..depth {
        sort = Sort::struct_type(
            format!("Pair{level}"),
            [("a", sort.clone()), ("b", sort.clone())],
        );
    }
    sort
}

/// Measured before the digest hashed sorts by allocation: `Debug` of the
/// depth-18 pair is 50 MB, formatted once per node. Here every distinct sort
/// is hashed once, so depth 64 (a tree of 2^64 leaves) is 65 sort digests.
#[test]
#[timeout(60_000)]
fn a_deep_shared_record_sort_is_digested_once_per_sort_node() {
    let depth = 64;
    let value = Expr::var("pair_value", nested_pair(depth));
    let mut digests = digests();
    digests.assert(&value.clone().eq(value));
    assert_eq!(
        digests.digested_sorts(),
        depth + 2,
        "Int, the {depth} record levels, and Bool"
    );
}

/// A 1,000-field record is hashed once, not once per node that carries it:
/// the digested sorts are the record, its one shared field sort, and the
/// Boolean results of the 201 nodes — measured before the fix, `Debug` of one
/// `(= v v)` shell over this record was 98 KB.
#[test]
fn a_wide_record_sort_is_hashed_once_for_every_node_that_carries_it() {
    let field = Sort::int();
    let wide = Sort::struct_type(
        "Wide",
        (0..1_000).map(|index| (format!("field{index}"), field.clone())),
    );
    let value = Expr::var("wide_value", wide);
    let mut digests = digests();
    let mut chain = value.clone().eq(value.clone());
    for _ in 0..100 {
        chain = chain.and(value.clone().eq(value.clone()));
    }
    digests.assert(&chain);
    assert!(
        digests.digested_sorts() <= 2 + 201 + 1,
        "{} sorts digested",
        digests.digested_sorts()
    );
}

#[test]
fn different_nodes_with_one_rendering_have_different_digests() {
    let digests = digests();
    let negative_literal = Expr::int(-1);
    let negated_one = Expr::int(1).int_neg();
    assert_ne!(digests.node(&negative_literal), digests.node(&negated_one));
    let int_var = Expr::var("same_name", Sort::int());
    let real_var = Expr::var("same_name", Sort::real());
    assert_ne!(digests.node(&int_var), digests.node(&real_var));
    let rebuilt = Expr::var("same_name", Sort::int());
    assert_eq!(
        digests.node(&int_var),
        digests.node(&rebuilt),
        "the digest is structural: separately built equal nodes agree"
    );
}

#[test]
fn truncating_remainder_digest_binds_its_operation_and_ordered_operands() {
    let digests = digests();
    let x = Expr::var("x", Sort::fp(8, 24));
    let y = Expr::var("y", Sort::fp(8, 24));
    let z = Expr::var("z", Sort::fp(8, 24));
    let remainder = x.clone().fp_truncating_rem(y.clone());
    let digest = digests.node(&remainder);
    assert_ne!(digest, digests.node(&x.clone().fp_rem(y.clone())));
    assert_ne!(
        digest,
        digests.node(&y.clone().fp_truncating_rem(x.clone()))
    );
    assert_ne!(
        digest,
        digests.node(&z.clone().fp_truncating_rem(y.clone()))
    );
    assert_ne!(digest, digests.node(&x.clone().fp_truncating_rem(z)));
    assert_eq!(digest, digests.node(&x.fp_truncating_rem(y)));
}

#[test]
fn range_copy_digest_binds_each_of_its_five_ordered_operands() {
    let digests = digests();
    let array = Sort::array(Sort::bitvec(64), Sort::bitvec(8));
    let operands = [
        Expr::var("dst", array.clone()),
        Expr::var("src", array),
        Expr::var("lo", Sort::bitvec(64)),
        Expr::var("hi", Sort::bitvec(64)),
        Expr::var("src_start", Sort::bitvec(64)),
    ];
    let copy = |args: &[Expr; 5]| {
        args[0]
            .clone()
            .try_array_range_copy(
                args[1].clone(),
                args[2].clone(),
                args[3].clone(),
                args[4].clone(),
            )
            .unwrap()
    };
    let digest = digests.node(&copy(&operands));
    for index in 0..operands.len() {
        let mut changed = operands.clone();
        changed[index] = Expr::var("changed", operands[index].sort().clone());
        assert_ne!(digest, digests.node(&copy(&changed)), "operand {index}");
    }
    let mut swapped = operands.clone();
    swapped.swap(0, 1);
    assert_ne!(digest, digests.node(&copy(&swapped)));
    swapped = operands.clone();
    swapped.swap(2, 3);
    assert_ne!(digest, digests.node(&copy(&swapped)));
    assert_eq!(digest, digests.node(&copy(&operands)));
}

/// Asking for a digest leaves the session's tables as they were, and a popped
/// scope's digests are dropped with it.
#[test]
fn digests_follow_the_stack_and_queries_do_not_grow_it() {
    let x = Expr::var("x", Sort::int());
    let mut digests = digests();
    digests.assert(&x.clone().int_ge(Expr::int(0)));
    let (nodes, sorts) = (digests.digested_nodes(), digests.digested_sorts());
    let _ = digests.node(&x.clone().int_le(Expr::int(7)));
    assert_eq!(
        (digests.digested_nodes(), digests.digested_sorts()),
        (nodes, sorts)
    );
    let outer = digests.scope();
    digests.push();
    digests.assert(&x.int_le(Expr::int(9)));
    assert!(digests.digested_nodes() > nodes);
    digests.pop();
    assert_eq!(digests.digested_nodes(), nodes);
    assert_eq!(digests.scope(), outer);
}
