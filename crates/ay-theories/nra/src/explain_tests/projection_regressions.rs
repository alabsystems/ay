// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

/// Pin degree growth on a concrete resultant.
#[test]
fn test_projection_raises_degree() {
    let p = bip(&[&[(2, -1)], &[], &[(0, 1)]]);
    let q = bip(&[&[(2, 1), (0, -4)], &[], &[(0, 1)]]);
    let proj = project(&[p, q], &[(0, 1)]).expect("projected");
    assert_eq!(proj.in_max_total_degree, 2);
    assert!(
        proj.out_max_total_degree > proj.in_max_total_degree,
        "projection must raise degree: {} -> {}",
        proj.in_max_total_degree,
        proj.out_max_total_degree
    );
}

/// `relevant_pairs` keeps ADJACENT owners and drops the pair separated by a
/// third polynomial's root.
#[test]
fn test_relevant_pairs_adjacency() {
    // roots at 0 (lit 1), 1 (lit 2), 2 (lit 3): 1-2 and 2-3 adjacent, 1-3 not.
    let ls = vec![
        lit(1, &[0, 1], SignCond::Eq, vec![Anum::rational(rat(0))]),
        lit(2, &[-1, 1], SignCond::Eq, vec![Anum::rational(rat(1))]),
        lit(3, &[-2, 1], SignCond::Eq, vec![Anum::rational(rat(2))]),
    ];
    let pairs = relevant_pairs(&ls).expect("computed");
    assert!(pairs.contains(&(0, 1)));
    assert!(pairs.contains(&(1, 2)));
    assert!(
        !pairs.contains(&(0, 2)),
        "0 and 2 are separated by literal 2's root; their crossing is covered"
    );
}

#[test]
fn test_relevant_pairs_no_roots_no_pairs() {
    let ls = vec![lit(1, &[1, 0, 1], SignCond::Gt, vec![])];
    assert_eq!(relevant_pairs(&ls), Some(vec![]));
}

#[test]
fn test_degree_in_and_lc_sign() {
    let p = MPolyZ::from_terms(vec![(Mono::var_pow(0, 3), BigInt::one())]);
    assert_eq!(degree_in(&p, 0), 3);
    assert_eq!(degree_in(&p, 1), 0);
    assert_eq!(lc_sign(&ints(&[1, 2, -3])), -1);
    assert_eq!(lc_sign(&ints(&[1, 2, 3])), 1);
    assert_eq!(lc_sign(&ints(&[0, 0])), 0);
}
