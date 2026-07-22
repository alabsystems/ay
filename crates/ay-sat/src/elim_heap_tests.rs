// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

#[test]
fn test_elim_score_maps_pure_literal_to_zero() {
    let x0 = Variable::new(0);
    let mut occ = OccList::new(2);
    occ.add_clause(0, &[Literal::positive(x0)]);
    occ.add_clause(
        1,
        &[Literal::positive(x0), Literal::positive(Variable::new(1))],
    );

    assert_eq!(ElimHeap::elim_score(x0, &occ, &[]), 0);
}

#[test]
fn test_heap_pops_pure_literal_before_non_pure_candidate() {
    let x0 = Variable::new(0);
    let x1 = Variable::new(1);
    let mut occ = OccList::new(2);

    occ.add_clause(0, &[Literal::positive(x0), Literal::positive(x1)]);
    occ.add_clause(1, &[Literal::positive(x0), Literal::negative(x1)]);

    let mut heap = ElimHeap::new(2);
    heap.push(x1, &occ, &[]);
    heap.push(x0, &occ, &[]);

    assert_eq!(heap.pop(&occ, &[]), Some(x0));
    assert_eq!(heap.pop(&occ, &[]), Some(x1));
}
